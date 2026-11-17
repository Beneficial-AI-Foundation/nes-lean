# PROGRESS — nes-lean

Single source of truth for the autonomous loop (`/loop /nes-loop`). Read this file first
on every tick; read [PLAN.md](PLAN.md) only for the section the current item needs.
Keep this file small: trim the tick log, never paste build output here.

## Resume here

- **Current milestone:** M1
- **Current branch:** `m1-cpu-isa`
- **Next action:** M1 batch: `Cpu/Types.lean` ∥ `Cpu/Decode.lean` ∥ Harte JSON loader (stub `State`) ∥ nestest log formatter (stub `State`).
- **Blocked:** no

## Milestones → stacked PRs

Each milestone is one PR. Branch from the previous milestone's branch; PR base = that
branch (M0's base is `main`). The draft PR is opened at milestone start — right after the
`M<k>: start milestone` bootstrap commit, before any code — every commit is pushed to it
as it lands, its body mirrors the checklist below, and it is marked ready for review only
when the milestone's definition of done holds.

| M | Title | Plan phases | Branch | Base | PR | Status |
|---|---|---|---|---|---|---|
| M0 | Scaffold | 0 | `m0-scaffold` | `main` | #1 | ready for review |
| M1 | nestest green | 1 | `m1-cpu-isa` | `m0-scaffold` | #2 | in progress |
| M2 | Cycle-exact and proved | 2 | `m2-cpu-micro` | `m1-cpu-isa` | — | not started |
| M3 | First frame | 3, 4 | `m3-ppu` | `m2-cpu-micro` | — | not started |
| M4 | Playable | 5, 7, 9 | `m4-system` | `m3-ppu` | — | not started |
| M5 | Sounds right | 6 | `m5-apu` | `m4-system` | — | not started |
| M6 | The PPU theorem | 8 | `m6-ppu-theorem` | `m5-apu` | — | not started |
| M7 | Verified 6502 programs | 10 | `m7-hoare` | `m6-ppu-theorem` | — | not started |

Milestone definition of done (all milestones): `lake build` clean; `lake test` green;
no `sorry` and no `native_decide` under `Nes/`; axiom check passes for every theorem in
the registry; headline theorem(s) of the milestone closed (not deferred); PROGRESS.md
updated; PR body summarises what was built, which theorems closed, which were deferred.

## Checklists (one item ≈ one commit; a tick runs up to 4 independent items in parallel via subagents)

Items are independent when they touch disjoint files and neither needs the other's
output. "Parallel tracks" lists what the plan expects to run side by side; order within
a milestone is otherwise a suggestion. "PR ready" is always last.

### M0 — Scaffold
Parallel tracks: after items 1–2 land (they define the Lake layout), items 3–7 are all independent.
- [x] `lake init` layout: `lakefile.toml` with lib `Nes` (`precompileModules = true`), exe `nes` (`Main.lean`) built with `moreLeancArgs = ["-O3", "-DNDEBUG"]`, test driver `Test`; `lean-toolchain` = latest stable (v4.36.0; fall back to installed v4.35.0 if the download fails)
- [x] Batteries dependency pinned to the tag matching the toolchain; `lake update`; `lake build` green
- [x] `Nes/Prelude/Bits.lean`: first `UInt8`/`UInt16` ↔ `BitVec`/`Nat` bridging lemmas, one `bv_decide` and one `omega` smoke proof
- [x] `Test/Axioms.lean`: theorem-name registry + `#print axioms` check that fails on `sorryAx` / `Lean.ofReduceBool`; wired into `lake test`
- [x] `scripts/fetch-testdata.sh`: SingleStepTests `nes6502`, `nestest.nes` + `nestest.log`, blargg suites; pinned commits; `testdata/` gitignored
- [x] GitHub Actions: build, test, axiom check, `grep -rn sorry Nes/` must be empty; `.lake` cache
- [x] README: build/run/test instructions; link PLAN.md and PROGRESS.md
- [x] CI green on the draft PR → mark ready. Create `m1-cpu-isa` from here.

### M1 — nestest green (Phase 1)
Parallel tracks: {Types → Alu → Alu proofs} ∥ {Decode → Decode proofs} ∥ {Harte JSON loader, Nestest log formatter (against a stub `State`)}; then Isa (needs Alu + Decode) → Isa proofs ∥ Harte sweep ∥ nestest; T-CPU-8 ∥ benchmark.
- [ ] `Cpu/Types.lean`: registers, `Flags` structure ↔ `UInt8` packing with round-trip lemma, `State`
- [ ] `Cpu/Alu.lean`: `spec` and `fast` versions of adc/sbc/cmp/asl/lsr/rol/ror/bit/inc/dec and the N/Z setters
- [ ] `Cpu/Proofs/Alu.lean`: T-CPU-1, T-CPU-2, T-REF-2 (ALU) via `bv_decide`
- [ ] `Cpu/Decode.lean`: `Instr`, `AddrMode`, 256-entry table (official + unofficial + 12 JAM), base cycles, page-cross flag
- [ ] `Cpu/Proofs/Decode.lean`: T-CPU-3 (totality, JAM set, `aaabbbcc` agreement on official), T-CPU-4 (cycle table)
- [ ] `Cpu/Isa.lean`: operand resolution per mode with page-cross detection; execution; `step : State → Mem → State × Mem × Nat`
- [ ] `Cpu/Proofs/Isa.lean`: T-CPU-5 (zero-page wrap, page-cross condition, `JMP ($xxFF)` bug, PC wrap)
- [ ] `Test/Harte.lean`: JSON loader for `nes6502` (flat 64 KiB memory), final-state diff; fast subset in `lake test`
- [ ] Harte final-state sweep 256/256 green (fix the spec until green; log every hardware surprise as a gotcha)
- [ ] `Test/Nestest.lean`: automated mode from `$C000`, log formatter, diff against golden log → green
- [ ] Benchmark ISA `step` (instr/s) in the native `nes --bench` binary (not `#eval`); inspect the generated C for `step` in `.lake/build/ir/` for boxing/allocation; record below
- [ ] T-CPU-8: one Harte case per instruction class proved by `decide`
- [ ] PR M1 ready. Create `m2-cpu-micro`.

### M2 — Cycle-exact and proved (Phase 2)
Parallel tracks: {Micro → Harte trace runner} ∥ {Interrupts}; then T-REF-1 prefix lemmas ∥ suffix lemmas (one subagent per lemma group, disjoint files `Proofs/Refinement/Prefix*.lean`, `Suffix*.lean`) ∥ T-CPU-6 ∥ T-CPU-7 ∥ blargg CPU suites; then table discharge.
- [ ] `Cpu/Micro.lean`: `MicroOp` inductive, mode-prefix and instruction-suffix programs, one-`BusOp`-per-cycle interpreter, instruction-boundary detection
- [ ] Harte per-cycle trace runner (addr, value, r/w incl. dummy reads and RMW double write) → 256/256
- [ ] `Cpu/Interrupts.lean`: NMI edge, IRQ level + `I`, RESET, polling point, CLI/SEI/PLP delay, BRK/NMI hijack
- [ ] `Cpu/Proofs/Refinement.lean` T-REF-1: 13 addressing-prefix lemmas
- [ ] T-REF-1: ~20 instruction-suffix lemmas
- [ ] T-REF-1: table discharge; `#print axioms` clean
- [ ] `Cpu/Proofs/Stack.lean` T-CPU-6
- [ ] `Cpu/Proofs/Interrupts.lean` T-CPU-7
- [ ] blargg `cpu_*`, `instr_test-v5`, `cpu_interrupts_v2`, `cpu_dummy_reads/writes` green (a minimal NROM bus may be pulled forward from Phase 3)
- [ ] PR M2 ready. Create `m3-ppu`.

### M3 — First frame (Phases 3, 4)
Parallel tracks: {Bus + proofs} ∥ {Cart/Ines + NROM + proofs} ∥ {Controller} ∥ {PPU Types/Registers/Loopy + T-PPU-2} ∥ {PPU Timing + T-PPU-1}; then {Background} ∥ {Sprites + Render} ∥ {$2007 buffer + NMI + proofs}; then System clocking → blargg PPU suites ∥ CLI/PNG.
- [ ] `Bus/Map.lean`, `Bus/OpenBus.lean`; `Bus/Proofs/Mirroring.lean` T-BUS-1; T-BUS-2
- [ ] `Cart/Ines.lean` + serializer; T-CART-1; `Cart/Mapper.lean` interface; `Mappers/NROM.lean`; T-CART-2 (NROM)
- [ ] `Input/Controller.lean`
- [ ] `Ppu/Types.lean`, `Ppu/Registers.lean`, `Ppu/Loopy.lean`; `Ppu/Proofs/Loopy.lean` T-PPU-2
- [ ] `Ppu/Timing.lean` (dot/scanline, vblank, odd-frame skip); T-PPU-1
- [ ] `Ppu/Background.lean` fetch pipeline + shifters
- [ ] `Ppu/Sprites.lean` evaluation (overflow bug) + fetch; `Ppu/Render.lean` priority/mux
- [ ] `$2007` read buffer + T-PPU-7; NMI line + T-PPU-5
- [ ] Minimal `System` clocking sufficient to run blargg `ppu_vbl_nmi`, `sprite_hit_tests`, `sprite_overflow_tests`, `ppu_read_buffer` → green
- [ ] CLI: run N frames → PNG/PPM; first homebrew title screen; commit its frame hash as golden (never the ROM)
- [ ] PR M3 ready. Create `m4-system`.

### M4 — Playable (Phases 5, 7, 9)
Parallel tracks: {System stepCycle/Frame + T-SYS-1/3} ∥ {DMA + T-SYS-2} ∥ {SaveState/input + T-REF-3/4} ∥ {MMC1, UxROM, CNROM, AxROM — one agent per mapper} ∥ {MMC3 + A12 IRQ}; then golden hashes ∥ perf pass.
- [ ] `System/Nes.lean` `stepCycle`, `runDots`, `runFrame`; interrupt wiring; T-SYS-1, T-SYS-3
- [ ] `Bus/Dma.lean` OAM DMA (513/514) ; T-SYS-2
- [ ] `System/SaveState.lean` + T-REF-3; input script + T-REF-4; T-SYS-4
- [ ] Mappers: MMC1 (+T-CART-3), UxROM, CNROM, AxROM (+T-CART-2 each)
- [ ] MMC3 with A12 IRQ (+T-CART-2, T-CART-4); MMC3 IRQ test ROMs green
- [ ] Golden frame hashes for 3+ homebrew ROMs across mappers
- [ ] Performance pass on the native binary: profile `stepCycle`, read its generated C, remove boxing/allocation/closures per PLAN.md §4 "Performance"; target ≥ real time (60 fps) on a homebrew ROM; record numbers (3-tick budget, then move on)
- [ ] PR M4 ready. Create `m5-apu`.

### M5 — Sounds right (Phase 6)
Parallel tracks: {FrameCounter + T-APU-1 + DMC DMA wiring} ∥ {pulse/triangle/noise units} ∥ {Dmc + T-APU-3} ∥ {Mixer + T-APU-2}; then WAV output → blargg APU suites.
- [ ] `Apu/FrameCounter.lean` (4/5-step, IRQ) + T-APU-1; DMC DMA cycle stealing wired into `stepCycle`
- [ ] Pulse ×2, triangle, noise, length counters, envelopes, sweeps
- [ ] `Apu/Dmc.lean` + T-APU-3
- [ ] `Apu/Mixer.lean` + T-APU-2; WAV output in CLI
- [ ] blargg `apu_test`, `dmc_dma_during_read4`, `apu_reset` green
- [ ] PR M5 ready. Create `m6-ppu-theorem`.

### M6 — The PPU theorem (Phase 8)
Parallel tracks: {Declarative renderer → shifter invariant → background half} ∥ {T-PPU-3} ∥ {T-PPU-4}; then sprite half + mux (needs all three).
- [ ] `Ppu/Declarative.lean` reference renderer
- [ ] Shifter invariant lemma (shifter contents = pattern bits of tile at `v` + 2)
- [ ] Background half of T-PPU-6
- [ ] T-PPU-3 sprite evaluation spec
- [ ] T-PPU-4 sprite-0 hit
- [ ] Sprite half + priority mux of T-PPU-6; `#print axioms` clean
- [ ] PR M6 ready. Create `m7-hoare`.

### M7 — Verified 6502 programs (Phase 10)
Parallel tracks: Logic → Rules (sequential); then the four verified routines, one agent each.
- [ ] `Hoare/Logic.lean`: triples over `Cpu.Isa`, memory separation predicate, soundness
- [ ] Rules: sequencing, consequence, branch, loop (fuel), JSR/RTS frame rule
- [ ] Verified routines: 16-bit add, `memcpy`, 8×8→16 multiply
- [ ] One routine lifted from an open-source homebrew game
- [ ] PR M7 ready. **Loop stops here.**

## Benchmarks
_(fill in: ISA instr/s at M1; frames/s at M4 and after the perf pass)_

## Deferred theorems
_(theorem id — why — what would unblock it)_

## Gotchas (append-only, newest last)
Format: `YYYY-MM-DD [area] symptom → fix/lesson`. Record anything that cost more than one
attempt: Lean API names, tactic behaviour, Lake quirks, hardware facts that contradicted
the docs, test-harness surprises.

- 2026-11-17 [lean] `v4.35.0` is installed locally; `elan` resolves `stable` to `v4.36.0` and will download it on first use.
- 2026-11-17 [lean] v4.36.0 downloaded fine via `elan toolchain install`; Batteries has a matching `v4.36.0` tag. Lake `testDriver = "Test"` points at the `Test` lean_exe (root `Test.Main`).
- 2026-11-17 [tests] The `nes6502` SingleStepTests assume a flat 64 KiB RAM with no NES bus; feed the CPU models a plain memory in the Harte harness.
- 2026-11-17 [lean] Lake only builds modules owned by some `lean_lib`; an exe importing `Test.Axioms` fails with "object file … does not exist" → added lib `TestSuite` (`globs = ["Test.+"]`).
- 2026-11-17 [lean] v4.36: `bv_decide` no longer uses `Lean.ofReduceBool` (constant gone); it adds a per-theorem axiom `<thm>._native.bv_decide.ax_*`. `native_decide` likewise adds `<thm>._native.native_decide.ax_*`. Axiom check allowlists only the bv_decide ones.
- 2026-11-17 [lean] Inside `namespace Nes`, `UInt16.foo` resolves to `Nes.UInt16.foo`; core lemmas need `_root_.` (e.g. `_root_.UInt8.toNat_add`).
- 2026-11-17 [lean] `simp [defs]` may close goals and leave `bv_decide` with "No goals"; use `simp only [UInt*.toBitVec_*]` then `bv_decide`. `bv_decide` handles `UInt8` goals (incl. `.toBitVec.msb`) directly.
- 2026-11-17 [testdata] ProcessorTests `nes6502` = 256 JSON files, ~1.2 GB on disk (~54 s); `fetch-testdata.sh --cpu-only` skips it for fast CI.

## Decisions log
- 2026-11-17 PLAN.md §10 decisions confirmed (Batteries only, NTSC only, unofficial opcodes from M1, `Vector` memory everywhere, no commercial ROMs).
- 2026-11-17 Phase 9 (performance) folded into M4; M0 added as its own PR so CI exists before M1.
- 2026-11-17 `bv_decide` (named in PLAN.md §4 as the bit-level proof tool) is accepted even though in v4.36 it trusts compiled evaluation via a per-theorem `_native.bv_decide` axiom; `native_decide` stays banned. The trust is confined to `allowedNativeTactics` in `Test/Axioms.lean`.
- 2026-11-17 The product is the native binary from Lean's C backend with `-O3`; hot-path rules in PLAN.md §4 apply from M1 (PLAN.md §10 decision 6).

## Tick log (keep the last 20 lines only)
_(`YYYY-MM-DD HH:MM  M<k>  <what happened in ≤ 1 line>`)_
- 2026-11-17  M0  started milestone (draft PR #1); Lake layout on v4.36.0 + Batteries v4.36.0, build/test/exe green
- 2026-11-17  M0  4 agents: Bits lemmas, axiom check (lib TestSuite), fetch-testdata (pinned), CI workflow; build/test green
- 2026-11-17  M0  README written; first CI run on push green (37 s)
- 2026-11-17  M0  CI green on 7835771; definition of done holds; PR #1 marked ready
- 2026-11-17  M1  started milestone (draft PR #2, base `m0-scaffold`)
