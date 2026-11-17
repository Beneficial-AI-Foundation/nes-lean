#!/usr/bin/env bash
# Fetch third-party test data into testdata/ (gitignored; never commit it).
#
#   testdata/nes-test-roms/   christopherpow/nes-test-roms (nestest + blargg suites)
#   testdata/ProcessorTests/  SingleStepTests/ProcessorTests, sparse: nes6502/ only
#
# Every source is pinned to a commit; the script verifies HEAD == pin.
# Idempotent: repos already at the pinned commit are left alone.
#
# Usage: scripts/fetch-testdata.sh [--cpu-only|--no-harte] [--harte-only]
#   --no-harte / --cpu-only  skip the large SingleStepTests nes6502 set (CI fast subset)
#   --harte-only             fetch only the SingleStepTests nes6502 set
#
# Policy: only freely redistributable test ROMs; no commercial ROMs, ever.
set -euo pipefail

NES_TEST_ROMS_URL="https://github.com/christopherpow/nes-test-roms.git"
NES_TEST_ROMS_SHA="95d8f621ae55cee0d09b91519a8989ae0e64753b"

PROCESSOR_TESTS_URL="https://github.com/SingleStepTests/ProcessorTests.git"
PROCESSOR_TESTS_SHA="bb11756436da8fd16cce86aef63dc6725f48836f"
PROCESSOR_TESTS_SPARSE="nes6502"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TESTDATA="$ROOT/testdata"

want_roms=1
want_harte=1
for arg in "$@"; do
  case "$arg" in
    --cpu-only|--no-harte) want_harte=0 ;;
    --harte-only) want_roms=0 ;;
    -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

log() { printf '[fetch-testdata] %s\n' "$*"; }

# fetch_pinned DIR URL SHA [SPARSE_DIR]
# Ensures DIR is a git checkout of URL at SHA. With SPARSE_DIR, uses a
# blobless partial clone + cone sparse-checkout so only that dir is downloaded.
fetch_pinned() {
  local dir="$1" url="$2" sha="$3" sparse="${4:-}"

  if [ -d "$dir/.git" ] && [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" = "$sha" ]; then
    if [ -n "$sparse" ]; then
      git -C "$dir" sparse-checkout set "$sparse"
    fi
    log "$(basename "$dir"): already at $sha"
    return 0
  fi

  if [ ! -d "$dir/.git" ]; then
    rm -rf "$dir"
    git init -q "$dir"
    git -C "$dir" remote add origin "$url"
  fi

  if [ -n "$sparse" ]; then
    git -C "$dir" config remote.origin.promisor true
    git -C "$dir" config remote.origin.partialclonefilter blob:none
    git -C "$dir" sparse-checkout set "$sparse"
  fi

  log "$(basename "$dir"): fetching $sha"
  if [ -n "$sparse" ]; then
    git -C "$dir" fetch -q --depth 1 --filter=blob:none origin "$sha"
  else
    git -C "$dir" fetch -q --depth 1 origin "$sha"
  fi
  git -C "$dir" -c advice.detachedHead=false checkout -q --force "$sha"

  local head
  head="$(git -C "$dir" rev-parse HEAD)"
  if [ "$head" != "$sha" ]; then
    echo "error: $dir HEAD is $head, expected pinned $sha" >&2
    exit 1
  fi
}

require() {
  if [ ! -e "$1" ]; then
    echo "error: expected file missing: $1" >&2
    exit 1
  fi
}

mkdir -p "$TESTDATA"

if [ "$want_roms" = 1 ]; then
  fetch_pinned "$TESTDATA/nes-test-roms" "$NES_TEST_ROMS_URL" "$NES_TEST_ROMS_SHA"
  R="$TESTDATA/nes-test-roms"
  require "$R/other/nestest.nes"
  require "$R/other/nestest.log"
  for d in instr_test-v5 cpu_interrupts_v2 cpu_dummy_reads cpu_dummy_writes \
           ppu_vbl_nmi sprite_hit_tests_2005.10.05 sprite_overflow_tests \
           ppu_read_buffer oam_read oam_stress apu_test dmc_dma_during_read4 \
           apu_reset MMC1_A12 mmc3_test_2 mmc3_irq_tests; do
    require "$R/$d"
  done
fi

if [ "$want_harte" = 1 ]; then
  fetch_pinned "$TESTDATA/ProcessorTests" "$PROCESSOR_TESTS_URL" "$PROCESSOR_TESTS_SHA" "$PROCESSOR_TESTS_SPARSE"
  require "$TESTDATA/ProcessorTests/nes6502/v1/a9.json"
fi

log "summary:"
if [ "$want_roms" = 1 ]; then
  log "  nes-test-roms   @ $NES_TEST_ROMS_SHA  ($(du -sh "$TESTDATA/nes-test-roms" | cut -f1))"
  log "    nestest:      testdata/nes-test-roms/other/nestest.{nes,log}"
fi
if [ "$want_harte" = 1 ]; then
  log "  ProcessorTests  @ $PROCESSOR_TESTS_SHA  ($(du -sh "$TESTDATA/ProcessorTests" | cut -f1))"
  log "    nes6502:      testdata/ProcessorTests/nes6502/v1/*.json"
else
  log "  ProcessorTests  skipped (--cpu-only)"
fi
