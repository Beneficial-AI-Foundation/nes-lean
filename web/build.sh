#!/usr/bin/env bash
# Build the browser player: Play.Core + Nes (Lean → C), Lean's runtime and the Init/Std modules
# they import (rebuilt for wasm32), and Play/app.c over Emscripten's SDL3 port.
#
#   web/build.sh            → .lake/web/site/{index.html,nes.js,nes.wasm}
#   web/build.sh --serve    → also serve it at http://localhost:8000
#
# Needs: elan (the pinned Lean), Emscripten (`brew install emscripten`), git, python3.
# Everything intermediate lives in .lake/web (gitignored); later builds reuse it.
#
# Lean v4.36.0 ships no WebAssembly runtime, so this builds one from the tagged source:
# single-threaded (no -pthread, so no cross-origin-isolation headers are needed), no GMP
# (Lean's own bignums), no mimalloc, libuv with Lean's Emscripten patch. Two fixes to the
# runtime's untested Emscripten-only code are applied below.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
W=$ROOT/.lake/web
SITE=$W/site
VER=$(sed 's/.*:v//' "$ROOT/lean-toolchain")   # e.g. 4.36.0
L=$W/lean4/src
INC=$W/rt/include
mkdir -p "$W" "$SITE"
command -v emcc > /dev/null || { echo "emcc not found: install Emscripten" >&2; exit 1; }
JOBS=$(sysctl -n hw.ncpu 2> /dev/null || nproc)

# --- 1. Lean sources at the pinned version -----------------------------------------------
if [ ! -d "$W/lean4" ]; then
  echo "== fetching Lean v$VER sources"
  git clone -q --depth 1 --branch "v$VER" https://github.com/leanprover/lean4.git "$W/lean4"
fi
LEAN_SHA=$(git -C "$W/lean4" rev-parse HEAD)

# --- 2. runtime (libleanrt.a, libuv.a) -----------------------------------------------------
if [ ! -f "$W/rt/libleanrt.a" ]; then
  echo "== building Lean runtime for wasm32"
  mkdir -p "$INC/lean" "$W/rt/obj"
  cp "$L"/include/lean/*.h "$INC/lean/"
  IFS=. read -r MAJ MIN PAT <<< "$VER"
  cat > "$INC/lean/version.h" << EOF
#pragma once
#define LEAN_VERSION_MAJOR $MAJ
#define LEAN_VERSION_MINOR $MIN
#define LEAN_VERSION_PATCH $PAT
#define LEAN_VERSION_IS_RELEASE 1
#define LEAN_SPECIAL_VERSION_DESC ""
#define LEAN_VERSION_STRING "$VER"
#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"
#define LEAN_MANUAL_ROOT ""
EOF
  printf '#pragma once\n#include <lean/version.h>\n#define LEAN_IS_STAGE0 false\n' > "$INC/lean/config.h"
  echo "#define LEAN_GITHASH \"$LEAN_SHA\"" > "$W/rt/githash.h"

  # libuv at the version Lean pins, with Lean's Emscripten patch (src/CMakeLists.txt)
  if [ ! -d "$W/libuv" ]; then
    git clone -q --depth 1 --branch v1.48.0 https://github.com/libuv/libuv "$W/libuv"
    python3 - "$W/libuv/CMakeLists.txt" << 'EOF'
import sys
p = sys.argv[1]; s = open(p).read()
anchor = 'if(CMAKE_SYSTEM_NAME STREQUAL "Linux")\n  list(APPEND uv_defines _GNU_SOURCE'
assert anchor in s, "libuv CMakeLists.txt changed"
s = s.replace(anchor, 'if(CMAKE_SYSTEM_NAME STREQUAL "Emscripten")\n  list(APPEND uv_sources\n'
              '       src/unix/no-proctitle.c)\nendif()\n\n' + anchor, 1)
open(p, 'w').write(s)
EOF
  fi
  (cd "$W/libuv" && emcmake cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
     -DLIBUV_BUILD_TESTS=OFF -DLIBUV_BUILD_SHARED=OFF > "$W/rt/libuv.log" 2>&1 &&
   cmake --build build -j"$JOBS" >> "$W/rt/libuv.log" 2>&1)
  cp "$W/libuv/build/libuv.a" "$W/rt/libuv.a"

  # Fix 1: an Emscripten-only stub's signature drifted from its header (v4.36.0).
  sed -i.bak 's/lean_obj_res lean_uv_os_get_group() {/lean_obj_res lean_uv_os_get_group(uint64_t) {/' \
    "$L/runtime/uv/system.cpp"
  # Fix 2 (flag below): the single-threaded path of thread.h uses std::adopt_lock_t without
  # including <mutex>.
  RT_FLAGS="-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -std=c++20 -include mutex"
  RT_FLAGS="$RT_FLAGS -I$INC -I$L -I$W/rt -I$W/libuv/include -Wno-everything"
  for s in debug thread mpz utf8 object apply exception interrupt memory stackinfo compact \
           init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow \
           process object_ref mpn mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp \
           uv/udp uv/dns uv/system uv/signal openssl cadical; do
    echo "$L/runtime/$s.cpp $W/rt/obj/$(echo "$s" | tr / _ | sed "s/^\\.//").o"
  done | xargs -P "$JOBS" -n 2 sh -c 'em++ '"$RT_FLAGS"' -c "$0" -o "$1"'
  emar rcs "$W/rt/libleanrt.a" "$W"/rt/obj/*.o
fi

# --- 3. Lean → C for Nes and Play.Core ----------------------------------------------------
echo "== lake build PlayCore"
(cd "$ROOT" && lake build PlayCore 2>&1 | grep -E "^error" && exit 1 || true)
IR=$ROOT/.lake/build/ir

# --- 4. Lean → C for the Init/Std modules they import -------------------------------------
# Roots: every external module the generated C initializes (`initialize_Init`, ...).
ROOTS=$(grep -rhoE "lean_object\* initialize_[A-Z][A-Za-z0-9_]*\(uint8_t" "$IR/Nes" "$IR/Nes.c" \
          "$IR/Play" | sed 's/lean_object\* initialize_//; s/(uint8_t//' | sort -u)
python3 - "$L" "$W/stdlib-modules.txt" $ROOTS << 'EOF'
import os, re, sys
src, out, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
def path(m): return os.path.join(src, *m.split('.')) + '.lean'
def resolve(sym):  # Std_Tactic_BVDecide → Std.Tactic.BVDecide (underscores are dots or literal)
    parts = sym.split('_'); cands = ['']
    for i, p in enumerate(parts):
        cands = [c + ('.' if c else '') + p for c in cands] + ([c + '_' + p for c in cands if c] if i else [])
    hits = [c for c in cands if os.path.exists(path(c))]
    if len(hits) != 1: sys.exit(f"cannot resolve module for initialize_{sym}: {hits}")
    return hits[0]
seen, stack = set(), [resolve(r) for r in roots]
while stack:
    m = stack.pop()
    if m in seen or not os.path.exists(path(m)): continue
    seen.add(m)
    for line in open(path(m), encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)', line)
        if mm: stack += [t for t in mm.group(1).split() if re.match(r'^[A-Z][\w.]*$', t)]
open(out, 'w').write('\n'.join(sorted(seen)) + '\n')
print(f"== {len(seen)} Init/Std modules")
EOF
export LEAN_PATH; LEAN_PATH=$(dirname "$(cd "$ROOT" && elan which lean)")/../lib/lean
export LEAN_BIN; LEAN_BIN=$(cd "$ROOT" && elan which lean)
export L W
while read -r m; do
  rel=${m//./\/}
  [ -f "$W/stdc/$rel.c" ] || echo "$m"
done < "$W/stdlib-modules.txt" | xargs -P "$JOBS" -n 1 sh -c '
  rel=$(echo "$0" | tr . /); mkdir -p "$W/stdc/$(dirname "$rel")"
  "$LEAN_BIN" --root="$L" "$L/$rel.lean" -c "$W/stdc/$rel.c" > /dev/null 2>&1 || { echo "FAIL $0"; exit 1; }'

# --- 5. compile C → wasm objects (cached by timestamp) ------------------------------------
CFLAGS="-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I$INC -Wno-everything"
mkdir -p "$W/obj"
# One "<source> <object>" line per current input; only these objects are linked, so objects
# left over from deleted modules (or restored from a CI cache) never are.
{
  while read -r m; do echo "$W/stdc/${m//./\/}.c"; done < "$W/stdlib-modules.txt"
  find "$IR/Nes" "$IR/Play" -name '*.c'; echo "$IR/Nes.c"
} | while read -r c; do
  echo "$c $W/obj/$(echo "${c#"$ROOT"/}" | tr / _ | sed "s/^\\.//").o"
done > "$W/objects.txt"
while read -r c o; do [ "$o" -nt "$c" ] || echo "$c $o"; done < "$W/objects.txt" \
  | xargs -P "$JOBS" -n 2 sh -c 'emcc '"$CFLAGS"' -c "$0" -o "$1"'
cut -d' ' -f2 "$W/objects.txt" > "$W/link.rsp"

# --- 6. bundled demo ROM ------------------------------------------------------------------
# nes15 by Mathew Brenaman (BSD-style licence: redistribution allowed with the notice, which
# ships next to it and is credited on the page). It comes from the test data
# (scripts/fetch-testdata.sh), never from git. Without it the page only offers "open a ROM".
NES15=$ROOT/testdata/nes-test-roms/nes15-1.0.0
mkdir -p "$SITE/roms"
if [ -f "$NES15/nes15-NTSC.nes" ]; then
  cp "$NES15/nes15-NTSC.nes" "$SITE/roms/nes15.nes"
  cp "$NES15/LICENSE" "$SITE/roms/nes15-LICENSE.txt"
else
  echo "== note: $NES15 missing (run scripts/fetch-testdata.sh --cpu-only); no demo ROM bundled"
  rm -f "$SITE/roms/nes15.nes" "$SITE/roms/nes15-LICENSE.txt"
fi

# --- 7. link ------------------------------------------------------------------------------
echo "== linking"
emcc $CFLAGS -Werror=implicit-function-declaration -sUSE_SDL=3 -c "$ROOT/Play/app.c" -o "$W/app.o"
em++ -O3 -fwasm-exceptions -sUSE_SDL=3 @"$W/link.rsp" "$W/app.o" "$W/rt/libleanrt.a" "$W/rt/libuv.a" \
  -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=8MB -sFORCE_FILESYSTEM=1 ${WEB_LINK_FLAGS:-} \
  -sEXPORTED_RUNTIME_METHODS=FS,ccall,UTF8ToString \
  --shell-file "$ROOT/web/shell.html" -o "$SITE/index.html" 2>&1 \
  | { grep -vE "lean_io_create_temp(file|dir)$|^>>> defined as" || true; }
ls -la "$SITE"

if [ "${1:-}" = "--serve" ]; then
  echo "== serving http://localhost:8000"
  cd "$SITE" && exec python3 -m http.server 8000
fi
