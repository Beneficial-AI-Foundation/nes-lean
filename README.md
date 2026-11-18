# nes-lean

A formally verified NES emulator in Lean 4. The emulator is a pure state machine whose
specification and proofs live in the `Nes` library; the product is the native binary
Lean's C backend produces from it.

- [PLAN.md](PLAN.md) — architecture, theorems, milestones, and project decisions.
- [PROGRESS.md](PROGRESS.md) — current milestone, checklists, benchmarks, gotchas.

## Requirements

- [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`
  (Lean v4.36.0) and installed automatically on first build.
- `git` and `bash` for fetching test data.

## Build

```bash
lake build
```

This builds the `Nes` library and the `nes` executable (compiled with `-O3`) at
`.lake/build/bin/nes`.

## Run

```bash
.lake/build/bin/nes
```

`nes run <rom.nes>` runs a ROM headless (PNG/PPM frames, frame hashes, WAV audio, scripted
input); `nes --help` lists the options.

## Play (live window, keyboard, sound)

`nes-play` opens a window, plays the sound, and reads the keyboard as controller 1. It needs
SDL3 (`brew install sdl3`, or `libsdl3-dev`), so it is not built by plain `lake build`:

```bash
lake build nes-play
```

```bash
.lake/build/bin/nes-play testdata/nes-test-roms/nes15-1.0.0/nes15-NTSC.nes
```

Keys: arrows = D-pad, X = A, Z = B, Enter = Start, Right Shift / Tab = Select, P = pause,
R = reset, Esc = quit. `--scale N` sets the window size (default 3×). Speed follows the
audio clock (44 100 samples per emulated NTSC second).

## Test

```bash
lake test
```

`lake test` builds and runs the `Test` driver. Building it also runs the axiom check in
`Test/Axioms.lean`: every theorem in its registry must exist and use only the standard
axioms (no `sorryAx`, no `native_decide`), or the build fails.

Test data (SingleStepTests `nes6502`, `nestest`, blargg's test ROMs) is not in the repo.
Fetch it at pinned commits into the gitignored `testdata/`:

```bash
scripts/fetch-testdata.sh
```

Pass `--cpu-only` to skip the ~1.2 GB SingleStepTests set.

## Repository rules

- No `sorry`, `native_decide`, `partial`, `unsafe`, `panic!` or `IO` under `Nes/`.
- No commercial ROMs in the repository, ever.

## License

See [LICENSE](LICENSE).
