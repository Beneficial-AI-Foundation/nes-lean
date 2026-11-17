# PROGRESS — nes-lean

Single source of truth for the autonomous loop (`/loop /nes-loop`). Read this file first
on every tick; read [PLAN.md](PLAN.md) only for the section the current item needs.
Keep this file small: trim the tick log, never paste build output here.

## Resume here

- **Current milestone:** M3
- **Current branch:** `m3-ppu`
- **Next action:** M3 batch: Bus/Map+OpenBus+T-BUS-1/2 ∥ Cart/Ines+NROM+T-CART-1/2 ∥ Input/Controller ∥ PPU Types/Registers/Loopy+T-PPU-2; then PPU Timing+T-PPU-1, Background, Sprites+Render, $2007/NMI.
- **Blocked:** no

## Milestones → stacked PRs

Each milestone is one PR. Branch from the previous milestone's branch; PR base = that
branch (M0's base is `main`). The draft PR is opened at milestone start — right after the
`M<k>: start milestone` bootstrap commit, before any code — every commit is pushed to it
as it lands, its body mirrors the checklist below, and it is marked ready for review only
when the milestone's definition of done holds.

| M | Title | Plan phases | Branch | Base | PR | Status |
|---|---|---|---|---|---|---|
| M0 | Scaffold | 0 | `m0-scaffold` | `main` | #1 | merged |
| M1 | nestest green | 1 | `m1-cpu-isa` | `main` | #2 | ready for review |
| M2 | Cycle-exact and proved | 2 | `m2-cpu-micro` | `m1-cpu-isa` | #3 | ready for review |
| M3 | First frame | 3, 4 | `m3-ppu` | `m2-cpu-micro` | — | in progress |
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
- [x] `Cpu/Types.lean`: registers, `Flags` structure ↔ `UInt8` packing with round-trip lemma, `State`
- [x] `Cpu/Alu.lean`: `spec` and `fast` versions of adc/sbc/cmp/asl/lsr/rol/ror/bit/inc/dec and the N/Z setters
- [x] `Cpu/Proofs/Alu.lean`: T-CPU-1, T-CPU-2, T-REF-2 (ALU) via `bv_decide`
- [x] `Cpu/Decode.lean`: `Instr`, `AddrMode`, 256-entry table (official + unofficial + 12 JAM), base cycles, page-cross flag
- [x] `Cpu/Proofs/Decode.lean`: T-CPU-3 (totality, JAM set, `aaabbbcc` agreement on official), T-CPU-4 (cycle table)
- [x] `Cpu/Isa.lean`: operand resolution per mode with page-cross detection; execution; `step : State → Mem → State × Mem × Nat`
- [x] `Cpu/Proofs/Isa.lean`: T-CPU-5 (zero-page wrap, page-cross condition, `JMP ($xxFF)` bug, PC wrap)
- [x] `Test/Harte.lean`: JSON loader for `nes6502` (flat 64 KiB memory), final-state diff; fast subset in `lake test`
- [x] Harte final-state sweep 256/256 green (fix the spec until green; log every hardware surprise as a gotcha)
- [x] `Test/Nestest.lean`: automated mode from `$C000`, log formatter, diff against golden log → green
- [x] Benchmark ISA `step` (instr/s) in the native `nes --bench` binary (not `#eval`); inspect the generated C for `step` in `.lake/build/ir/` for boxing/allocation; record below
- [x] T-CPU-8: one Harte case per instruction class proved by `decide`
- [x] PR M1 ready. Create `m2-cpu-micro`.

### M2 — Cycle-exact and proved (Phase 2)
Parallel tracks: {Micro → Harte trace runner} ∥ {Interrupts}; then T-REF-1 prefix lemmas ∥ suffix lemmas (one subagent per lemma group, disjoint files `Proofs/Refinement/Prefix*.lean`, `Suffix*.lean`) ∥ T-CPU-6 ∥ T-CPU-7 ∥ blargg CPU suites; then table discharge.
- [x] `Cpu/Micro.lean`: `MicroOp` inductive, mode-prefix and instruction-suffix programs, one-`BusOp`-per-cycle interpreter, instruction-boundary detection
- [x] Harte per-cycle trace runner (addr, value, r/w incl. dummy reads and RMW double write) → 256/256
- [x] `Cpu/Interrupts.lean`: NMI edge, IRQ level + `I`, RESET, polling point, CLI/SEI/PLP delay, BRK/NMI hijack
- [x] Wire `Interrupts` into `Micro`: `sampleCycle` every cycle (poll = `isPollCycle`/`branchPollCycle`, I via `pollIFlag`), `atBoundary` → `ack` + `requestInterrupt`, `vectorFetch` before cycle 5's sample (hijack); needed by T-CPU-7 and the blargg interrupt suites
- [x] `Cpu/Proofs/Refinement.lean` T-REF-1: 13 addressing-prefix lemmas
- [x] T-REF-1: ~20 instruction-suffix lemmas
- [x] T-REF-1: table discharge; `#print axioms` clean
- [x] `Cpu/Proofs/Stack.lean` T-CPU-6
- [x] `Cpu/Proofs/Interrupts.lean` T-CPU-7 (IRQ masked, entry/BRK/B-bit/hijack over `Core`, NMI latch, 8-cycle boundary bound)
- [x] T-CPU-7 NMI latency end-to-end over `Core` (≤ `maxInstrCycles + 7` cycles from edge): relate `Core.runCycles` to `MicroState.runInstr`; show every instruction polls before its boundary — closed in attempt 2 for an edge sampled in the fetch cycle / already latched (`T_CPU_7_nmi_latency`: ≤ 8 + 7 = 15 cycles)
- [x] T-CPU-7 NMI latency for an edge arriving mid-instruction — closed in attempt 3: `T_CPU_7_nmi_latency_edge` (edge in cycle j of an instruction or BRK: ≤ (8 − (j−1)) + 15 cycles), `_edge_irq` (edge in an IRQ sequence), `_mid` (invariant form); edge inside an NMI sequence deferred
- [x] T-CPU-7 hijack with an NMI edge in BRK cycles 2–4 and NMI consumed at the core layer (needs a per-cycle line-schedule runner); IRQ-masked core theorem derived from the opcode instead of assumed I=1 (closed in attempt 2: `T_CPU_7_hijack_mid/late`, `T_CPU_7_irq_masked_opcode`, line-schedule runner `runSched`)
- [x] blargg `cpu_*`, `instr_test-v5`, `cpu_interrupts_v2`, `cpu_dummy_reads/writes` green (a minimal NROM bus may be pulled forward from Phase 3) — 28/28 on test-only NROM/MMC1/CNROM bus + crude PPU/APU timing (`Test/Blargg.lean`); re-validate on the real PPU/APU in M3/M5
- [x] PR M2 ready. Create `m3-ppu`.

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
- 2026-11-17 M1 ISA `step`, `nes --bench` (-O3, Apple M5 Max arm64, synthetic loop of LDA/ADC/STA abs,X/ROL/CMP/JSR/RTS/INX/DEX/BNE): **~35 M instr/s, ~115 M cycles/s, ~64× NTSC realtime** (median of 3).
  Generated C (`.lake/build/ir/Nes/Cpu/Isa.c`): memory written in place (`lean_array_fset`, no copies); per instruction ~3–4 small allocs: 2 `Prod` cells for `State × Mem × Nat` (Isa.lean:280), 1 pair from `exec` (Isa.lean:156), fresh `State` in `setZN` join points (65 sites), `Alu.RC` from `shiftOp` lambdas (Isa.lean:143); `Mem = Vector UInt8` is an array of boxed scalars (8 B/byte, `lean_unbox` per read); `AddrMode` `==` goes through `lean_nat_dec_eq`. M4 fixes: flat `StepOut` struct, `UInt` cycles, inline `exec`/`setZN`, enum shift op, `ByteArray`-backed memory with a `Vector` spec view, `match` instead of derived `BEq`.

## Deferred theorems
_(theorem id — why — what would unblock it)_
- T-CPU-7 (sub-case): NMI edge during cycles 1–4 of an NMI sequence — the interrupt model absorbs it (documented gap in `Cpu/Interrupts.lean`), so no latency bound holds there as modelled. Unblock: model the per-cycle NMI edge detector during sequences to match hardware, then extend `lat_dispatch`. Also: latency bounds are not tight (branch case is 17, proved bound 22) and assume no JAM fetched.

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
- 2026-11-17 [cpu] SingleStepTests record JAM opcodes as 3 cycles (opcode fetch + 2 reads, PC unchanged), not the conventional 2. Decode table uses 3.
- 2026-11-17 [lean] A 256-entry `Array` literal: `#v[...]` and `⟨arr, rfl⟩` hit `maxRecDepth`; build the `Vector` as `⟨tableArray, by decide +kernel⟩`. Facts over all 256 entries by `decide +kernel` take ~3 s total.
- 2026-11-17 [lean] `bv_decide` does not understand `!=` on `UInt8` (treats it as an atom → "potentially spurious counterexample"); rewrite with `bne_iff_ne`/`ne_eq` first (see `flag_bv` macro in `Cpu/Types.lean`).
- 2026-11-17 [lean] v4.36 strings: `String.trim/take/drop` now go through `String.Slice`; `String.mk` deprecated → `String.ofList`; `if_true/if_false` deprecated → `ite_true/ite_false`. `Json.getNat?` does not range-check.
- 2026-11-17 [tests] nestest copies code into RAM at `$0300` (log line 3349), so the trace's opcode bytes must be read from the model's memory — the nestest diff also checks writes.
- 2026-11-17 [cpu] `State.p` stores the raw byte; PLP/RTI must decide bits 4/5 (6502: B ignored, U reads as 1) — settle against Harte in `Isa`.
- 2026-11-17 [git] PR #1 was rebase-merged (new SHAs on `main`); restack with `git rebase --onto origin/main <old m0 tip> m1-cpu-isa`, not plain `git rebase main`.
- 2026-11-17 [proofs] One-operand ALU equivalences (`∀ v : UInt8, fast.asl v = spec.asl v`) close by plain `decide` in ~0.4 s; `fast.adc = spec.adc` needs bridging lemmas (`UInt16.toNat_toUInt8`, `toNat_and`) or `bv_decide` on `toBitVec`.
- 2026-11-17 [cpu] Harte ground truth: PHP/BRK push `P | $30`; PLP/RTI load `(v & $CF) | $20`. JAM leaves all registers incl. PC unchanged (3 cycles). XAA: `A := (A | $EE) & X & imm`; LAX #imm: `A,X := (A | $EE) & imm`. SHY/SHX/AHX/TAS store `reg & (H+1)` (H = base high byte) and on page cross that value replaces the address high byte; TAS sets `SP := A & X`. ARR: C = bit 6, V = bit 6 ^ bit 5.
- 2026-11-17 [tests] Full Harte sweep (2.56 M cases, final state + cycle count) takes ~2m54 in the native `Test` exe (`lake test -- --full`) vs ~3m40 interpreted; fast subset + nestest ~6 s.
- 2026-11-17 [cpu] `Isa.exec` reads `m.read ea` even for stores/implied modes — harmless on pure memory, but must not leak into the M3 bus (side-effecting reads).
- 2026-11-17 [proofs] Kernel `decide` on a concrete 64 KiB `Vector` is hopeless (Array ops reduce via `List`: one LDA #imm case 9 s, STA abs 30 s). T-CPU-8 instead proves each case for *all* memories agreeing on the listed cells: unfold `step`, rewrite reads with the hypotheses + read-after-write lemma, per-case `decode 0xNN = … := rfl`, `decide` the residue (~0.08 s/theorem).
- 2026-11-17 [ci] The CI `grep -rnw native_decide Nes/` also matches comments and docstrings — never write the word under `Nes/`, even in prose.
- 2026-11-17 [lean] `(256 : UInt16).toNat` doesn't reduce for omega; add `show (256 : UInt16).toNat = 256 from rfl`.
- 2026-11-17 [cpu] Micro bus-trace facts from Harte: JAM reads PC, PC+1, PC+1 then restores PC; taken branches dummy-read the next instruction, then (page cross) target-low with the old high byte; unstable stores dummy-read with the un-indexed base high byte. Halted CPU reads `$FFFF` each cycle (our choice; untested by Harte).
- 2026-11-17 [tests] Full native `Test --full` (ISA sweep + per-cycle Micro sweep, 2 × 2.56 M cases) takes ~6m20.
- 2026-11-17 [cpu] Interrupts: call `ack` when taking an interrupt (else the poll latch refires); `vectorFetch` must run before cycle 5's `sampleCycle` (hijack window); `State.init` already has SP=$FD — power-on RESET from it would give $FA.
- 2026-11-17 [proofs] T-REF-1 design: compositional. Prefix lemma `runInstr (f+k) ms m = bump k (runInstr f ms' m)` (same `m` ⇒ no writes); class proof = fetch + prefix + suffix via `runInstr_last`, an `exec_<class>` lemma, and a `<class>_table` fact by `decide +kernel`. ~0.1 s per prefix lemma via `cyc`/`cyc_skip`/`skp` tactics. `Isa.exec` is only meaningful on table entries — `exec_<class>` lemmas need instruction guards tied to `classify` by table facts.
- 2026-11-17 [lean] Rewriting with `runInstr_last`: name `p` explicitly and leave `hu` as a side goal — unifying `?ms.op` with a concrete op hits max recursion. Unfold micro `exec` in `h1` before `generalize decode (m.read s.pc)`.
- 2026-11-17 [proofs] Step lemmas for fixed opcodes: `obtain ⟨..⟩ := s; subst hh` before `simp only [step, …]`, or simp rewrites `halted` on the RHS too. PHA;PLA / PHP;PLP need `s.pc + 1 ≠ stackAddr s.sp` in flat memory (the push could overwrite the next opcode).
- 2026-11-17 [cpu] Core power-on: `Core.powerOn s` sets SP := $00 then runs RESET (ends SP=$FD, I set, PC from $FFFC); warm reset leaves SP−3. A JAM-halted core only accepts RESET.
- 2026-11-17 [cpu] **Spec bug found by proof:** JSR reads the target high byte *after* pushing PCH/PCL. With JSR at `$01FC`, SP=`$FE`, the PCH push overwrites the operand byte `$01FE`; `Isa.exec` used the stale byte. Random Harte cases never hit it. Fixed in `Isa.exec`.
- 2026-11-17 [proofs] T-REF-1 suffix tactics: wrap each cycle as its own `ms.cycle m = (ms', m')` fact + `runInstr_cyc` (unfolding several cycles with `runInstr_succ` explodes); `runInstr 7` in one simp times out; case-split PLA/PLP before the big simp; keep programs as literal `#[...]` in `hu` (an `abbrev` blocks `Array.getD` reduction); `show f + 2 = f + 1 + 1 from rfl` when Lean normalised the fuel. ROL/ROR/RRA/ISC need `State.c`/`State.getBit` in the simp set; BRK needs `State.setI`/`setBit`.
- 2026-11-17 [proofs] `T_REF_1` depends on one `_native.bv_decide` axiom through `Nes.UInt16.ofLoHi_lo_hi` (Bits); everything else in T-REF-1 is standard axioms only. Replacing that one lemma's proof would make T-REF-1 fully kernel-checked.
- 2026-11-17 [tests] blargg vs SingleStepTests disagree on unstable `$AB` (LAX/ATX #imm): blargg expects `A,X := #imm` (magic $FF), Harte `(A|$EE) & #imm`. Per PLAN §10.3 we follow Harte; `all_instrs.nes`, `03-immediate.nes`, `nes_cpu_test5/cpu.nes` are excluded from the blargg run list for that reason only.
- 2026-11-17 [tests] Crude PPU timing in `Test/Blargg.lean`: 2 PPU dots before the CPU bus access and 1 after (`ppuPre := 2`) — 3 breaks cpu_interrupts test 3, 1 breaks test 2. Useful prior for the real `stepCycle` ordering in M4.
- 2026-11-17 [tests] blargg harness: MMC1 ignores serial writes on consecutive cycles; `$81` handled by asserting RESET ~200k cycles later; ROMs without the `$6000` protocol are judged by nametable text. Test-exe -O3 C compile of `Test.Blargg` ~3 min; full blargg list runs ~33 s.
- 2026-11-17 [proofs] T-CPU-7 tactics: don't unfold `IntState.sampleCycle` in multi-cycle `Core` runs — use field lemmas (`sc_nmiPending`, `vf_fst`, `boundary_cpu/pos`); leaving `pushOp` out of simp makes it time out; illegal RMW (ind),Y/(ind,X) are 8 cycles (the 8-cycle boundary bound needs a separate RMW case); no `interval_cases` without Mathlib — use an `omega` disjunction.
- 2026-11-17 [proofs] `State.flags_set*` lemmas use `bv_decide` (native axiom); to keep a theorem on standard axioms re-prove the flag fact by `decide` over the 256 status bytes. `let` in theorem statements caused whnf timeouts when used with `exact` — `dsimp only` goal and hypothesis first.
- 2026-11-17 [cpu] NMI latency from the *edge* is not `maxInstrCycles + 7`: a taken branch without page cross polls only in cycle 1, so an edge in its cycle 2 waits for the next instruction (2 + 8 + 7 = 17 cycles). Bound from the instruction start (edge in fetch cycle) is 15 and is proved.
- 2026-11-17 [lean] `rfl`/`apply` on goals containing `uops ms.op` hits max recursion — `dsimp only` then `refine` with explicit args, or `generalize`.
- 2026-11-17 [lean] Don't wrap a line schedule like `hjNmiFrom j (fun _ => irq)` in an `abbrev`: checking `runSched 7 (abbrev…)` against `runSched 7 (hjNmiFrom…)` unfolds `runSched` and hits whnf heartbeat limits — write it out.

## Decisions log
- 2026-11-17 PLAN.md §10 decisions confirmed (Batteries only, NTSC only, unofficial opcodes from M1, `Vector` memory everywhere, no commercial ROMs).
- 2026-11-17 Phase 9 (performance) folded into M4; M0 added as its own PR so CI exists before M1.
- 2026-11-17 `bv_decide` (named in PLAN.md §4 as the bit-level proof tool) is accepted even though in v4.36 it trusts compiled evaluation via a per-theorem `_native.bv_decide` axiom; `native_decide` stays banned. The trust is confined to `allowedNativeTactics` in `Test/Axioms.lean`.
- 2026-11-17 The product is the native binary from Lean's C backend with `-O3`; hot-path rules in PLAN.md §4 apply from M1 (PLAN.md §10 decision 6).
- 2026-11-17 T-CPU-8 is proved by `simp` + `decide` over a universally quantified memory rather than kernel `decide` on a concrete 64 KiB memory (infeasible in the kernel). The statement is stronger than the plan's (holds for every memory agreeing with the case).
- 2026-11-17 Spec-vs-hardware mismatch (JSR operand read order) found by the T-REF-1 proof rather than a test: fixed the spec (`Isa.exec`) per the loop rule; T-CPU-6's direct JSR;RTS theorem gained two no-overlap hypotheses (the general form is unchanged).
- 2026-11-17 Unstable opcode `$AB`: SingleStepTests behaviour kept (PLAN §10.3) over blargg's; the three blargg ROMs that test it are excluded from the run list.

## Tick log (keep the last 20 lines only)
_(`YYYY-MM-DD HH:MM  M<k>  <what happened in ≤ 1 line>`)_
- 2026-11-17  M0  started milestone (draft PR #1); Lake layout on v4.36.0 + Batteries v4.36.0, build/test/exe green
- 2026-11-17  M0  4 agents: Bits lemmas, axiom check (lib TestSuite), fetch-testdata (pinned), CI workflow; build/test green
- 2026-11-17  M0  README written; first CI run on push green (37 s)
- 2026-11-17  M0  CI green on 7835771; definition of done holds; PR #1 marked ready
- 2026-11-17  M1  started milestone (draft PR #2, base `m0-scaffold`)
- 2026-11-17  M1  4 agents: Types, Decode (cycles validated vs all Harte files), Harte loader, nestest harness; build/test green
- 2026-11-17  M1  PR #1 merged → rebased M1 onto main; Alu (spec+fast) and T-CPU-3/T-CPU-4 proved; 8 theorems in registry
- 2026-11-17  M1  Isa.step: Harte 2,560,000/2,560,000 (+cycles), nestest 8991/8991; ALU proofs T-CPU-1/2, T-REF-2 (22 theorems); CI fetches testdata
- 2026-11-17  M1  T-CPU-5 (11 thms), T-CPU-8 (31 Harte cases as theorems), bench 35 M instr/s; 65 theorems in registry; all M1 items but PR-ready ticked
- 2026-11-17  M1  CI green on 7897ff6; definition of done holds; PR #2 marked ready
- 2026-11-17  M2  started milestone (draft PR #3, base `m1-cpu-isa`)
- 2026-11-17  M2  Interrupts logic; Micro (41 uops) passes 2,560,000/2,560,000 Harte cases incl. exact bus traces and Isa agreement; trace runner in lake test
- 2026-11-17  M2  T-CPU-6 (6 thms); interrupts wired in Cpu.Core (18/18 scenarios); T-REF-1 framework + 13 prefixes + 4/15 classes (160/256 opcodes); 77 theorems
- 2026-11-17  M2  T-REF-1 CLOSED for all 256 opcodes (15 classes); proof exposed and fixed an Isa JSR bug; 90 theorems in registry
- 2026-11-17  M2  T-CPU-7 (11 thms; latency + mid-BRK hijack open); blargg CPU suites 28/28 in lake test; full sweeps green after JSR fix; 101 theorems
- 2026-11-17  M2  T-CPU-7 attempt 2: mid-BRK hijack, opcode-derived IRQ masking, NMI latency from instruction start (15 cycles); 109 theorems; mid-instruction-edge latency left for attempt 3
- 2026-11-17  M2  T-CPU-7 attempt 3: mid-instruction NMI latency (≤ rest + 15) incl. BRK/IRQ sequences; NMI-in-NMI-sequence sub-case deferred; 112 theorems; all M2 work items ticked
- 2026-11-17  M2  CI green on f45bd06; definition of done holds (T-REF-1 closed); PR #3 marked ready
- 2026-11-17  M3  started milestone (branch `m3-ppu`, base `m2-cpu-micro`)
