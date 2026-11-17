# nes-lean — Implementation & Verification Plan

A cycle-accurate NES (NTSC, 2A03 CPU + 2C02 PPU) emulator written in Lean 4, where the
emulator *is* the formal model: the same definitions are compiled to run games and are
the objects of the theorems.

---

## 1. Goals and non-goals

**Goals**

1. An executable emulator that runs real NES software (NROM/MMC1/UxROM/CNROM/MMC3/AxROM
   covers ~90 % of the library) at or near real time on a laptop. **The shipped product is
   the native binary produced by Lean's C backend** (`lake build nes` →
   `.lake/build/bin/nes`), compiled with release flags — never the interpreter or `#eval`.
   The whole design is chosen so that the compiled C is fast (Section 4, "Performance").
2. A readable, instruction-level *specification* of the 2A03 and a per-dot specification of
   the 2C02, written as plain Lean functions.
3. Machine-checked theorems connecting the fast/cycle-level implementation to those
   specifications, plus a catalogue of "the hardware behaves like this" facts
   (Section 6).
4. A validation harness that grounds the specification in hardware-derived data
   (SingleStepTests, nestest, blargg's test ROMs).

**Non-goals (for now)**

- PAL / Dendy timing, Famicom expansion audio, Zapper, 4-player adapters.
- Analog-level PPU quirks that are only observable on a CRT (NTSC artifacts, colour
  emphasis fidelity). We model digital pixel output: a 256×240 array of 6-bit palette
  indices (+ emphasis bits).
- Verifying the Lean compiler or the C frontend. Those are in the trusted base.

---

## 2. What "formally verified emulator" means here

There is no formal specification of the NES to verify against, so correctness is split:

| Layer | How it is established |
|---|---|
| ISA-level CPU spec, per-dot PPU spec, memory map, mappers | **Validated** against hardware-derived tests (Section 7). These definitions are the trusted spec. They are kept small, direct and table-driven so they can be read and audited. |
| Cycle-level CPU microcode, optimized data representations, lookup tables, bit tricks, the frame loop, DMA, save states | **Verified** by refinement/equivalence theorems against the spec layer. |
| Behavioural facts (timing constants, mirroring laws, flag arithmetic, interrupt latency, ...) | **Proved** about the spec layer. These double as executable documentation and catch spec typos. |

Trusted computing base: Lean's kernel, the spec-layer definitions, Lean's compiler
(unverified, as always), the C FFI frontend (not part of the library), and the test data.
`native_decide` is **not** allowed in the theorem set; a CI check runs `#print axioms` on
every exported theorem and fails if anything beyond `propext`, `Classical.choice`,
`Quot.sound` appears (`sorryAx` and `Lean.ofReduceBool` included).

The payoff of this split: every test only has to validate the small spec; the
optimizations and the cycle machinery cannot introduce bugs the tests do not see.

---

## 3. Architecture

### 3.1 Purely functional state machine

```
structure Nes where
  cpu   : Cpu.State          -- A X Y SP PC P + micro-state (cycle-level)
  ppu   : Ppu.State          -- regs, v/t/x/w, OAM, secondary OAM, shifters, dot/scanline
  apu   : Apu.State
  cart  : Cart.State         -- mapper regs + PRG/CHR RAM; PRG/CHR ROM are immutable fields
  ram   : Vector UInt8 2048
  ciram : Vector UInt8 2048  -- nametable RAM
  pal   : Vector UInt8 32
  pads  : Input.State
  bus   : OpenBus            -- last value seen on the data bus
  clock : Clock              -- master-cycle counter, odd/even CPU cycle, dot counter
```

- No `IO`, no `partial`, no `panic!`, no `unsafe` in `Nes/`. Everything terminates
  structurally or by fuel (`runDots (n : Nat)`).
- Memories are `Vector UInt8 n` (core Lean): O(1) indexing with `Fin`, in-place update when
  uniquely referenced, and a good `simp` set (`getElem_set`, `set_set`, `ext`).
  Out-of-bounds access is impossible by typing, so "no OOB" is free, and the interesting
  statement becomes "every mapper bank computation produces an in-range `Fin`".
- Memory is addressed through a **bus trace** type so device side effects are explicit:

```
inductive BusOp | read (a : UInt16) | write (a : UInt16) (v : UInt8)
```

### 3.2 Clocking

Master step = one CPU cycle = 3 PPU dots (NTSC). `stepCycle : Nes → Nes` runs one CPU
micro-cycle (producing exactly one `BusOp`, as the real 6502 does), then three PPU dots,
then one APU half-cycle, then resolves DMA/IRQ/NMI lines. A frame is `runDots 89342`
(89341 on odd frames with rendering enabled). This is the only loop in the system; it is
fuel-based.

### 3.3 Two CPU models

- **`Cpu.Isa.step`** — instruction level. Memory as `UInt16 → UInt8`. One big, obviously
  correct `match` on `(instr, mode)`. Returns new state, new memory, and the cycle count.
  This is the trusted spec and what nestest/Harte "final state" tests validate.
- **`Cpu.Micro`** — microcode as *data*: `uops : Opcode → MicroProgram`, interpreted one
  cycle at a time by a tiny machine that emits one `BusOp` per cycle (dummy reads and the
  RMW double-write included). This is what the emulator actually runs.

Theorem **T-REF-1** (Section 6) states that running the micro-program of an opcode to
completion against pure memory equals `Isa.step`, and that it takes exactly the documented
number of cycles. Because microcode is data, cycle-count facts are `decide`-able.

### 3.4 Two PPU views

- **`Ppu.Dot.step`** — the per-dot pipeline (fetch shifters, sprite evaluation, v/t/x/w
  updates, vblank/NMI, odd-frame skip, `$2007` read buffer). The real thing.
- **`Ppu.Declarative.pixel`** — a non-pipelined function `State → x → y → PaletteIndex`
  computing each pixel directly from nametables, attributes, pattern tables, OAM, and the
  frame-start scroll. Used only as a spec in theorem **T-PPU-6** ("if nothing writes to
  the PPU during a frame, the pipeline renders exactly this").

### 3.5 Module layout

```
lakefile.toml, lean-toolchain
Nes.lean
Nes/
  Prelude/      Bits.lean (UInt8/16 ↔ BitVec/Nat lemmas), Vec.lean, Fin.lean
  Cpu/          Types, Flags, Alu, Decode, Isa, Micro, Interrupts
  Cpu/Proofs/   Alu, Decode, Cycles, Refinement, Stack, Interrupts, Quirks
  Bus/          Map (address decode), OpenBus, Dma
  Bus/Proofs/   Mirroring, RomImmutable
  Cart/         Ines (header), Mapper (interface), Mappers/{NROM,MMC1,UxROM,CNROM,MMC3,AxROM}
  Cart/Proofs/  Ines (parse/serialize), Banks (in-range), MMC1 (shift reg), MMC3 (IRQ counter)
  Ppu/          Types, Registers, Loopy, Background, Sprites, Render, Timing, Declarative
  Ppu/Proofs/   Loopy, Timing, Sprites, Vblank, StaticFrame
  Apu/          FrameCounter, Pulse, Triangle, Noise, Dmc, Mixer
  Apu/Proofs/   FrameCounter, Mixer, Dmc
  Input/        Controller
  System/       Nes (machine + stepCycle), Frame, SaveState, Determinism
  System/Proofs/ Clock, Dma, SaveState, Determinism
  Hoare/        (stretch) program logic over Cpu.Isa
Test/           Harte, Nestest, Blargg, Golden, Main (lake test)
Main.lean       headless CLI: run ROM N frames with an input script → PNG/PPM + frame hashes
frontend/       (later) C/SDL2 shim calling the compiled library; not part of the library
scripts/        fetch-testdata.sh, check-axioms.lean
testdata/       gitignored; fetched by script
```

Proof files import definition files, never the reverse, so a `lake build Nes.Cpu.Isa`
never elaborates proofs — keeps the edit/run loop fast.

---

## 4. Toolchain and conventions

- **Lean**: pin `lean-toolchain` to the latest stable (`v4.36.0`; `v4.35.0` is already
  installed locally and also fine). Core already provides `Vector`, `BitVec`, `UInt*`
  lemma sets, `omega`, `bv_decide` (SAT with verified LRAT checking), `grind`, `decide
  +kernel`, and `Std.Do`/`mvcgen` for Hoare-style proofs about `do` blocks.
- **Dependencies**: Batteries only. No Mathlib unless a concrete need appears (keeps full
  builds in minutes). Revisit if the Hoare-logic layer wants Mathlib's order/lattice
  library.
- **Numbers**: registers are `UInt8`/`UInt16`; proofs go through `toBitVec` (→
  `bv_decide`) for bit-level facts and `toNat` (→ `omega`) for arithmetic facts. A
  `Nes.Prelude.Bits` file collects the bridging lemmas we end up needing.
- **Tables**: opcode/cycle/addressing tables are `Vector`/`Fin 256 → _` constants built
  with `#[...]` literals, so `decide +kernel` can check universally quantified facts over
  all 256 opcodes.
- **Style**: spec definitions get `@[simp]`/`@[grind]` attributes deliberately, not by
  default. Each proof file has a `Spec` section stating the theorem in prose first.
- **Performance (compiled C)**: Lean compiles every definition to C and then to native
  code via `leanc`/clang. The `nes` executable is built with `moreLeancArgs := #["-O3",
  "-DNDEBUG"]` (plus `-march=native` for local benchmarks only, never in CI), and the
  library sets `precompileModules := true` so the test harness and `#eval` also run native
  code. Hot-path rules, enforced from M1 onward: scalars are `UInt8/16/32/64` (unboxed in
  the C backend), never `Nat`/`Int` outside proofs; state structures are updated with
  `{ s with … }` on uniquely referenced values so the compiler reuses the allocation;
  `Vector`/`ByteArray` writes happen through functions that keep the array uniquely
  referenced (no sharing across the step), so they are in-place `memcpy`-free stores; no
  closures, `List`s, or `Option` allocations inside `stepCycle`; lookup tables are
  top-level `Vector` constants; `@[inline]` on the micro-op interpreter and `@[specialize]`
  on anything polymorphic in the hot loop. Proofs are erased and cost nothing at runtime;
  `Fin n` is a `Nat` at runtime and small `Nat`s are unboxed, so `Fin`-indexed access
  compiles to a bounds-check-free array load. The Phase 9 pass reads the generated C
  (`.lake/build/ir/*.c`) for the hot functions and fixes anything that boxes or allocates.
- **CI** (GitHub Actions, `lean-action`): `lake build`, `lake test` (fast subset:
  nestest + one Harte opcode per class + blargg CPU tests), axiom check, no-`sorry`
  check. Full Harte sweep (2.56 M cases) nightly / on demand.

---

## 5. Component designs

### 5.1 CPU (2A03)

- 2A03 = 6502 **without decimal mode**: the D flag is storable but ADC/SBC ignore it.
  This removes the ugliest part of 6502 verification.
- Decoder: a `Fin 256 → Entry` table where `Entry = (Instr × AddrMode × cycles ×
  pageCrossPenalty)`. All 256 entries are defined: 151 official, the stable unofficial
  ones (NOP variants, LAX, SAX, DCP, ISC, SLO, RLA, SRE, RRA, ANC, ALR, ARR, SBC `$EB`,
  LAS), the "unstable" ones with the canonical behaviour the SingleStepTests encode
  (XAA, AHX, SHY, SHX, TAS, LAX #imm), and the 12 JAM opcodes
  (`$x2` for x ∈ {0,1,2,3,4,5,6,7,9,B,D,F}) modelled as a `halted` state.
- ALU in `Cpu/Alu.lean` has **two** definitions per operation: `spec` (integer arithmetic:
  carry = sum ≥ 256, overflow = signed sum ∉ [−128,127]) and `fast` (bit tricks). The
  executable uses `fast`; T-CPU-1 proves them equal.
- Interrupts: NMI edge detector, IRQ level with `I` mask, RESET; polling happens at the
  documented point (last cycle of an instruction, with the one-instruction delay after
  CLI/SEI/PLP); BRK/NMI hijack modelled.
- Micro-programs: ~30 micro-ops (`fetchOpcode`, `fetchLo`, `fetchHi`, `readZpIndexed`,
  `indexedFixup` (conditionally takes a cycle), `rmwDummyWrite`, `push`, `pull`,
  `branchTakenFixup`, ...). Each addressing mode is one shared prefix program; each
  instruction class one suffix.

### 5.2 Bus, cartridge, mappers

- Address decode is a pure function `UInt16 → Target` where
  `Target = ram (Fin 2048) | ppuReg (Fin 8) | apuIo (Fin 24) | cart UInt16`. Mirroring is
  therefore a *theorem about this function*, not scattered masks.
- Open bus: reads of unmapped addresses (and the unreadable bits of `$2002`, `$4016`)
  return the last bus value.
- `Cart.Mapper` is a structure of functions `{ cpuRead, cpuWrite, ppuRead, ppuWrite,
  ppuA12 : Bool → State → State, irq : State → Bool }` over a per-mapper state. PRG-ROM
  and CHR-ROM live in immutable fields; writes can only touch mapper registers and
  PRG/CHR RAM. Bank arithmetic returns `Fin romSize` so range safety is by construction.
- iNES / NES 2.0 header parser with a serializer, so round-trip is provable.
- Controller: strobe + 8-bit shift register, returns 1 after 8 reads (official-controller
  behaviour).

### 5.3 PPU (2C02)

- State: `ctrl`, `mask`, `status`, `oamAddr`, loopy `v t : BitVec 15`, `x : BitVec 3`,
  `w : Bool`, read buffer, OAM (256 B), secondary OAM (32 B), background shifters,
  sprite shifters/latches/counters, `dot : Fin 341`, `scanline : Fin 262`, `frameOdd`,
  NMI output line, plus the `$2002`-read-at-vblank suppression state.
- `Ppu.Dot.step` is a `match` on `(scanline, dot)` ranges driving the documented fetch
  schedule (NT, AT, PT-lo, PT-hi every 8 dots; sprite fetches at 257–320; the two
  pre-fetch tiles at 321–336), sprite evaluation (dots 65–256, with the overflow bug
  reproduced), and the v/t updates (incX every 8 dots, incY at 256, copyX at 257,
  copyY at 280–304 on the pre-render line).
- Output: `frame : Vector (BitVec 6) (256*240)` plus emphasis bits; a palette table maps
  to RGB only in the CLI/frontend.
- Mapper hook: the PPU exposes its A12 line each dot so MMC3's IRQ counter is driven
  properly.

### 5.4 APU

Frame counter (4/5-step, IRQ) and DMC DMA come first because they affect CPU timing and
games' IRQ usage. Then pulse ×2 / triangle / noise / DMC channels, length counters,
envelopes, sweeps, and the nonlinear mixer. Audio output is a `Float`/`Rat`
sample stream at 1 sample per CPU cycle, downsampled in the frontend. Mixer uses the
nesdev lookup formulas as rational functions so monotonicity/bounds are provable.

### 5.5 System

- `stepCycle` (Section 3.2), `runDots`, `runFrame`, `runFrames rom inputs n`.
- OAM DMA (`$4014`): halts CPU 513 or 514 cycles (parity), copies page → OAM, with DMC
  DMA interleaving modelled as documented.
- Save state = the `Nes` structure itself. `serialize : Nes → ByteArray` and
  `deserialize` with a round-trip theorem.
- Input script: `List (Fin frames → Buttons)`; the whole run is a pure function of
  `(rom, script)`.

### 5.6 Frontend (non-verified, minimal)

`Main.lean` headless runner (PNG/PPM frames, WAV audio, per-frame hash) is enough for
all testing. An SDL2 window via a 50-line C shim comes after Phase 5, in a separate Lake
target so the library keeps zero FFI.

---

## 6. Theorems we will prove

Tags: technique in brackets; effort S/M/L/XL.

### 6.1 Refinement (the headline results)

- **T-REF-1 Cycle model refines ISA model.** For every opcode and every state with no
  pending interrupt, running `Micro` to the end of the instruction against pure memory
  yields exactly `Isa.step`'s registers and memory, and emits exactly `cycles(op)`
  (+ page-cross/branch penalties) bus operations. [per-(class,mode) lemmas + `decide`
  over the table] **XL** — the single most valuable theorem: it makes the thing that
  runs games trustworthy relative to the thing that is easy to read and test.
- **T-REF-2 Every optimization is equal to its spec.** `Alu.fast* = Alu.spec*`, decode
  LUT = structured `aaabbbcc` decoder on official opcodes, bit-twiddled loopy updates =
  field-level updates, etc. [`bv_decide`, `decide +kernel`] **M**
- **T-REF-3 Save-state round trip.** `deserialize (serialize s) = some s`, and
  `serialize` is injective. [structural induction, `simp`] **M**
- **T-REF-4 Determinism / replay.** `runFrames rom script n` is a function (trivially)
  and, more usefully, *prefix-stable*: the first `k` frames depend only on the first `k`
  entries of the input script. Gives TAS-replay reproducibility as a corollary. [induction
  on `n`] **S**

### 6.2 CPU

- **T-CPU-1 Flag arithmetic.** For ADC: `A' = (A+M+C) mod 256`, `C' ↔ A+M+C ≥ 256`,
  `V' ↔ sA+sM+C ∉ [−128,127]`, `Z' ↔ A' = 0`, `N' ↔ A' ≥ 128`; SBC = ADC of the
  complement (`sbc a m c = adc a (~~~m) c`); CMP/CPX/CPY flags are those of
  subtraction with borrow. [`bv_decide` / `omega`] **S**
- **T-CPU-2 Shift/rotate algebra.** `ror ∘ rol = id` on `(value, carry)`; ASL is
  `×2 mod 256` with carry = old bit 7; LSR is `/2` with carry = old bit 0. [`bv_decide`]
  **S**
- **T-CPU-3 Decoder totality and structure.** Every byte decodes; the JAM set is exactly
  the 12 listed opcodes; on official opcodes the table agrees with the `aaabbbcc`
  structural decoder. [`decide +kernel`] **S**
- **T-CPU-4 Cycle table.** `(uops op).baseCycles = documentedTable op` for all 256 and
  the page-cross penalty applies to exactly the documented (instr, mode) pairs. [`decide`]
  **S**
- **T-CPU-5 Addressing-mode laws.** Zero-page indexed never leaves page 0; the
  page-cross penalty condition equals `(base + idx) / 256 ≠ base / 256`; `JMP ($xxFF)`
  fetches its high byte from `$xx00` (the bug, stated precisely); PC wraps `$FFFF → $0000`.
  [`omega`/`bv_decide`] **S**
- **T-CPU-6 Stack discipline.** `pull (push s v) = (s, v)`; SP stays in `$0100–$01FF`;
  `JSR` then any code that restores SP and ends with `RTS` returns to the instruction
  after the `JSR`; `PHA; PLA` and `PHP; PLP` are identities on `(A, SP)` / `(P, SP)`
  modulo the B/unused bits. [`simp` + stack lemmas] **M**
- **T-CPU-7 Interrupt semantics.** With `I` set, IRQ is never taken; NMI is taken within
  `maxInstrCycles + 7` cycles of its edge; taking any interrupt pushes `PC` and `P`,
  sets `I`, and loads the right vector; the B bit is set only in the pushed copy for
  BRK/PHP; an NMI arriving during BRK hijacks to the NMI vector but still consumes the
  BRK's cycles. [simulation over `Micro`] **L**
- **T-CPU-8 ISA-level conformance is decidable per test case.** A Harte test case is a
  `Prop` the kernel can decide; CI proves a sampled subset *as theorems* (not just
  `#eval`), so part of the test suite lives inside the trusted-theorem set. [`decide`]
  **S** (nice, cheap, unusual)

### 6.3 Bus / cartridge

- **T-BUS-1 Mirroring laws.** `decode (a + 0x800) = decode a` for RAM; `decode (0x2000 +
  k) = decode (0x2000 + k % 8)` for `k < 0x2000`; palette aliases `$3F10/14/18/1C ↔
  $3F00/04/08/0C`; nametable mirroring functions are idempotent and land in CIRAM.
  [`decide`/`omega`] **S**
- **T-BUS-2 ROM immutability.** No sequence of bus operations changes PRG-ROM or CHR-ROM
  (they are not even fields of the mutable state — the theorem is that `cpuWrite`/`ppuWrite`
  preserve the ROM projection). [structural] **S**
- **T-CART-1 Header round trip.** `parse (serialize h) = some h`; `parse` rejects
  non-"NES\x1A" input. [`simp`] **S**
- **T-CART-2 Banks in range.** For every mapper and every register state, the computed
  PRG/CHR offsets are `< size`. [`Fin` arithmetic, `omega`] **S** per mapper
- **T-CART-3 MMC1 shift register.** Five consecutive writes with bit 7 clear commit the
  5-bit value to the register selected by `addr[14:13]` and reset the shift state; any
  write with bit 7 set resets the shift state and forces PRG mode 3. [`simp`] **M**
- **T-CART-4 MMC3 IRQ counter.** Fires exactly on the A12 rising edge that brings the
  counter to 0 while IRQs are enabled; reload semantics as documented; the A12 filter
  ignores edges closer than the documented gap. [simulation] **M**

### 6.4 PPU

- **T-PPU-1 Timing constants.** A frame is 262 scanlines × 341 dots = 89 342 dots;
  odd frames with rendering on are 89 341; vblank flag set at (241,1), cleared at (261,1);
  CPU cycles per frame = 29 780 ⅔ as a `Rat` identity, frame rate ≈ 60.0988 Hz.
  [`decide`, `norm_num`-free `Rat` reasoning] **S**
- **T-PPU-2 Loopy algebra.** `incX` 32 times = toggle bit 10 and coarse X back to 0;
  `incY` from (fineY=7, coarseY=29) toggles bit 11 and resets coarse Y; from coarseY=31
  wraps without toggling; `copyX`/`copyY` move exactly the documented bit fields;
  `$2005/$2006` write pairs set `t` and `x` as documented, and `w` toggles. [`bv_decide`
  on `BitVec 15`] **S**
- **T-PPU-3 Sprite evaluation.** On a scanline, the sprites placed in secondary OAM are
  exactly the first ≤8 OAM entries (in OAM order) whose vertical range covers the line;
  the overflow flag equals the buggy hardware predicate (also specified declaratively).
  [induction over the 64-entry evaluation loop, `mvcgen`] **L**
- **T-PPU-4 Sprite-0 hit.** Set at dot `x+2`… iff an opaque sprite-0 pixel overlaps an
  opaque background pixel at `x ≠ 255`, rendering enabled, respecting the left-8-pixel
  mask bits; never set outside the visible region. [simulation] **M**
- **T-PPU-5 NMI generation.** NMI line goes low at (241,1) iff `ctrl.nmiEnable`; toggling
  `nmiEnable` on during vblank retriggers; reading `$2002` on (241,1) suppresses the flag
  and the NMI for that frame. [simulation] **M**
- **T-PPU-6 Static-frame rendering theorem.** If no PPU register/VRAM/OAM writes occur
  during a frame and rendering is enabled, then for all `x < 256, y < 240`,
  `(runFrame s).frame[y][x] = Declarative.pixel s x y`, where the declarative renderer is
  a 40-line direct lookup through scroll → nametable → attribute → pattern → palette with
  the 8-sprite limit and priority rules. [invariant over 89 342 dots: shifter contents =
  pattern bits of the tile at (v + 2 tiles); `mvcgen`] **XL** — the crown jewel for the
  PPU; raster effects are precisely the cases where the hypothesis fails.
- **T-PPU-7 `$2007` buffer semantics.** Reads below `$3F00` return the previous buffered
  value; the buffer updates on every read; palette reads bypass but still fill the buffer
  from the underlying nametable address. [`simp`] **S**

### 6.5 APU

- **T-APU-1 Frame counter.** Step times and sequence length match the nesdev constants for
  4- and 5-step modes; the IRQ flag is set only in 4-step mode with inhibit clear; writing
  `$4017` with bit 7 set clocks all units immediately. [`decide`/simulation] **M**
- **T-APU-2 Mixer bounds and monotonicity.** `mix p1 p2 t n d ∈ [0,1]` and is monotone in
  each input. [`Rat` inequalities] **S**
- **T-APU-3 DMC addressing.** Sample address wraps from `$FFFF` to `$8000`; the bytes
  remaining counter hits 0 exactly after `length` fetches; DMC DMA steals the documented
  number of cycles. [`omega`] **S**

### 6.6 System

- **T-SYS-1 Clock invariant.** After any number of `stepCycle`s, `ppuDots = 3 · cpuCycles`
  and `apuHalfCycles = cpuCycles`. [induction] **S**
- **T-SYS-2 OAM DMA postcondition.** After `$4014 ← p`, `OAM = page p` (read through the
  mapper, so it also holds for cartridge RAM), CPU is halted for 513 cycles if the write
  landed on an even CPU cycle, 514 if odd, and the PPU advanced `3 ×` that. [simulation]
  **M**
- **T-SYS-3 Frame progress.** `runFrame` advances the frame counter by exactly 1 and
  returns to (0,0) [with the odd-frame skip], hence `runFrames n` emits `n` frames.
  [arith] **S**
- **T-SYS-4 Interrupt delivery.** NMI asserted by the PPU is observed by the CPU within
  the T-CPU-7 bound measured in system cycles; the mapper IRQ line ORed with APU IRQs is
  what the CPU samples. [composition of T-CPU-7 + T-PPU-5] **M**

### 6.7 Stretch: a program logic for 6502 code

Build a small Hoare logic over `Cpu.Isa` (`{P} code {Q}` with a memory separation
predicate), prove the standard rules once, and use it to verify real 6502 routines:
a 16-bit add, a `memcpy`, an 8×8→16 multiply, and ideally a routine lifted from an
open-source homebrew game. This shows the spec is not only *testable* but *usable* as
a semantics, and would be the first verified-program results on a 6502 in Lean.

---

## 7. Testing and validation

| Suite | What it validates | How |
|---|---|---|
| [SingleStepTests `nes6502`](https://github.com/SingleStepTests/ProcessorTests) (10 000 cases/opcode, MIT) | ISA spec final state **and** the per-cycle bus trace of `Micro` (addresses, values, read/write, dummy accesses, RMW double writes) | `Test/Harte.lean`: parse JSON with `Lean.Json`, run both models, diff. Fast subset in CI; full sweep nightly. A sample is also proved by `decide` (T-CPU-8). |
| `nestest.nes` + golden `nestest.log` | ISA model + decoder + cycle counts + bus basics | Automated-mode run from `$C000`, line-by-line log diff. First milestone. |
| blargg `cpu_*`, `instr_test-v5`, `cpu_interrupts_v2`, `cpu_dummy_reads/writes` | Interrupt timing, dummy accesses, unofficial opcodes | Run until `$6000` status byte ≠ `$80`; assert `$00`. |
| blargg `ppu_vbl_nmi`, `sprite_hit_tests`, `sprite_overflow_tests`, `ppu_read_buffer`, `oam_read/stress` | PPU timing and quirks | Same `$6000` protocol / screen-text OCR via the nametable. |
| blargg `apu_test`, `dmc_dma_during_read4`, `apu_reset` | APU frame counter, DMC DMA | `$6000` protocol. |
| Mapper tests (MMC1/MMC3 IRQ suites, holy mapperel) | Banking and IRQ | Screen/`$6000` protocol. |
| Golden frame hashes of homebrew ROMs | End-to-end regression | `Test/Golden.lean`. No commercial ROMs in the repo. |
| Performance | Real-time target | `Main.lean --bench`: frames/sec; tracked in CI output. |

Test data is fetched by `scripts/fetch-testdata.sh` into `testdata/` (gitignored); the
script pins commit hashes.

---

## 8. Phases and milestones

Each phase lists definitions, proofs, tests, and a definition of done. Effort is relative.

| # | Phase | Effort | Depends on |
|---|---|---|---|
| 0 | Scaffold: `lake init`, toolchain pin, Batteries, `Nes.Prelude`, CI, axiom check, test-data script | S | — |
| 1 | **CPU ISA spec** (`Types`, `Flags`, `Alu` spec+fast, `Decode`, `Isa`) + T-CPU-1..5, T-REF-2(ALU) + Harte final-state + nestest | M | 0 |
| 2 | **CPU micro model** (`Micro`, interrupts) + **T-REF-1**, T-CPU-6/7 + Harte cycle traces, blargg CPU suites | XL | 1 |
| 3 | **Bus & cartridge**: decode, open bus, iNES, NROM, controller + T-BUS-1/2, T-CART-1/2 | M | 1 |
| 4 | **PPU**: registers, loopy, background, sprites, timing, NMI, `$2007` + T-PPU-1/2/7 (5 and 3/4 start here) + blargg PPU suites, first PNG | L | 3 |
| 5 | **System**: clocking, DMA, interrupt wiring, frame loop, save state, CLI + T-SYS-1..4, T-REF-3/4 → **first game playable headless** | M | 2, 4 |
| 6 | **APU**: frame counter/IRQ + DMC DMA first, then channels and mixer, WAV output + T-APU-1..3 | L | 5 |
| 7 | **Mappers**: MMC1, UxROM, CNROM, MMC3 (+A12 IRQ), AxROM + T-CART-3/4 | M | 5 |
| 8 | **PPU static-frame theorem T-PPU-6** and T-PPU-3/4 completion | XL | 4 |
| 9 | **Performance** pass on the compiled C (profile the native binary, read the generated C for `stepCycle`, remove boxing/allocation, `Vector`/`ByteArray` in-place paths, `@[inline]`/`@[specialize]`) with refinement proofs for anything changed; SDL frontend | M | 5 |
| 10 | **Program logic** (Section 6.7) | L | 1 |

Milestones (what a demo looks like):

1. **M1 — "nestest green"**: Phase 1 done; Harte final-state sweep 256/256 opcodes; the
   flag-arithmetic and decoder theorems checked.
2. **M2 — "cycle-exact and proved"**: Phase 2; Harte cycle traces 256/256; T-REF-1 closed
   with `#print axioms` clean.
3. **M3 — "first frame"**: Phase 4; a homebrew ROM's title screen as PNG; blargg vbl/nmi
   suites pass.
4. **M4 — "playable"**: Phase 5 (+7 for MMC1/MMC3 games); input script runs a game;
   determinism and save-state theorems closed.
5. **M5 — "sounds right"**: Phase 6.
6. **M6 — "the PPU theorem"**: Phase 8.
7. **M7 — "verified 6502 programs"**: Phase 10.

Phases 3 and 2 are independent and can proceed in parallel; so can 6, 7, 8, 9 after 5.

---

## 9. Risks and mitigations

- **Case explosion in T-REF-1** (256 opcodes × modes). Mitigation: factor by
  `(instrClass, addrMode)`; prove ~13 addressing-prefix lemmas and ~20 instruction-suffix
  lemmas; discharge the table with `decide`. Never prove per-opcode.
- **Performance of compiled Lean.** Mitigation: benchmark the ISA step at the end of
  Phase 1 (target ≥ 20 M instr/s single core, which leaves headroom for 1.79 M
  cycles/s + PPU); design the hot path around uniquely-referenced `Vector`s and
  unboxed `UInt`s from day one; keep an escape hatch (`ByteArray` + proven representation
  lemma).
- **Kernel `decide` too slow on big tables.** Mitigation: `decide +kernel`, split tables,
  or prove via `Fin.forall_iff`-style enumeration lemmas; `bv_decide` for anything
  bit-vector-shaped.
- **UInt lemma gaps in core.** Mitigation: `Nes.Prelude.Bits`; bridge to `BitVec` early.
- **PPU accuracy rabbit hole.** Mitigation: scope = behaviours covered by blargg's suites
  and nesdev's documented timing; no Visual2C02 analogue modelling.
- **Harte JSON volume** (~GBs). Mitigation: per-opcode files, streamed; or a one-off
  Python converter to a compact binary in `scripts/` if `Lean.Json` is too slow.
- **Mid-frame-write cases make T-PPU-6 look weak.** It is honest: the theorem's
  hypothesis *characterises* raster effects. A follow-up can generalise to piecewise
  static scanlines (split-screen status bars), which covers most real games.

---

## 10. Project decisions (confirmed 2026-11-17)

1. **No Mathlib** — Batteries only, for build speed. Revisit only if the Hoare-logic
   layer (Phase 10) needs it.
2. **NTSC only** initially. PAL/Dendy timing is a later, additive change to the
   `Clock`/`Ppu.Timing` constants.
3. **Unofficial opcodes in scope from Phase 1**, with the canonical behaviour the
   SingleStepTests `nes6502` set encodes for the unstable ones.
4. **`Vector UInt8 n` is the one memory representation** for spec and implementation.
   Function-valued memory (`UInt16 → UInt8`) appears only inside proofs via `Vector.get`.
   No duplicated spec/impl copies of components; refinement proofs are local to what is
   actually optimized (ALU bit tricks, LUTs, microcode).
5. **Repo policy**: no commercial ROMs, ever; test ROMs and the Harte suite are fetched by
   `scripts/fetch-testdata.sh` into the gitignored `testdata/`.
6. **The product is the native binary from Lean's C backend**, built with release flags;
   the hot path follows the compiled-C rules in Section 4. Real-time speed is a milestone
   criterion (M4), not an afterthought.

---

## 11. Prior art and references

- No existing Lean 4 formalisation of the 6502 or NES was found. Closest Lean 4
  machine models: [risc0-lean4](https://reservoir.lean-lang.org/@risc0/risc0-lean4)
  (RV32IM executable model) and [tvm-lean](https://reservoir.lean-lang.org/@Gusarich/tvm-lean)
  (TON VM); the Sail→Lean RISC-V translation used by
  [Jolt-QED](https://eprint.iacr.org/2026/2157.pdf) is the nearest "verified against an
  ISA spec" precedent.
- Test data: [SingleStepTests 65x02 / ProcessorTests `nes6502`](https://github.com/SingleStepTests)
  — per-instruction JSON with full before/after state and per-cycle bus trace; MIT
  licensed; the `nes6502` set assumes a flat 64 KiB RAM, which our Harte harness provides
  directly to the CPU models (no NES bus).
- Hardware documentation: nesdev wiki (CPU, PPU rendering, PPU frame timing, APU, mappers),
  the 64doc cycle tables, Visual6502 results for dummy accesses.
