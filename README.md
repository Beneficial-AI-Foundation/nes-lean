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

The headless CLI (run a ROM for N frames, write PNG/PPM and frame hashes) arrives in M3.

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
