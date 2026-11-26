# Contributing to nes-lean

Thanks for your interest in contributing. nes-lean is a formally verified NES
emulator in Lean 4: the emulator is a pure state machine whose specification and
proofs live in the `Nes` library, and the product is the native binary Lean's C
backend produces from it. This guide covers how to build it, the standards we hold
code to, and how to send a change. It follows the shared contribution standard used
across the [Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation)
Lean projects.

See [PLAN.md](PLAN.md) for the architecture, theorems and milestones, and
[PROGRESS.md](PROGRESS.md) for the current state and gotchas.

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project uses,
so you don't install Lean by hand:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

`git` and `bash` are needed to fetch test data. The live window (`nes-play`)
additionally needs **SDL3** (`brew install sdl3`, or `libsdl3-dev`), and the browser
player needs Emscripten (`brew install emscripten`).

## Building

```sh
lake build          # the Nes library and the `nes` emulator at .lake/build/bin/nes
```

`nes` is the headless emulator and needs no SDL. The live window is a separate,
non-default target that links SDL3:

```sh
lake build nes-play # window, keyboard and sound; requires SDL3
```

The native emulator builds on Linux and macOS; released binaries are published for
both. The same player also compiles to WebAssembly and is deployed to GitHub Pages.

## Testing

```sh
lake test           # builds and runs the `Test` driver (incl. the axiom check)
```

`lake test` fetches pinned test ROMs and CPU vectors via `scripts/fetch-testdata.sh`
and runs the fast subset. Continuous integration (`.github/workflows/ci.yml`) runs the
`sorry`/`native_decide` grep, the build and `lake test` on Linux; `.github/workflows/pages.yml`
builds the browser player on every PR. Please make sure these pass locally before
opening a PR.

## Proof discipline

Correctness here comes from machine-checked proofs, so the sources must stay free of
proof escape hatches:

- **No `sorry` or `native_decide` under `Nes/`.** CI greps for them and fails on a hit;
  artifacts must also be portable, so never pass `-march=native` in CI (see PLAN.md).
- The axiom check is an elaboration-time check in `Test/Axioms.lean`, compiled as part
  of the `Test` driver, so a disallowed axiom (`sorryAx`, `Lean.ofReduceBool`, …)
  reachable from a spec fails `lake test`.

## Submitting a change

1. **Branch** off `main` (or fork the repository). Milestone PRs may be stacked on
   non-`main` bases; CI runs on any branch and base.
2. Keep each pull request focused, and add or update a spec/test for behaviour you
   change — tests are theorems here.
3. Make sure `lake build` and `lake test` pass, and that CI is green.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (MIT, see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest ROM or input that reproduces it. Security-sensitive reports can be sent
privately to **support@beneficialaifoundation.org** instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.
