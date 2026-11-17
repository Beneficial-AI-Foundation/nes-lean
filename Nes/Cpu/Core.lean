import Nes.Cpu.Micro
import Nes.Cpu.Interrupts

/-!
# `Nes.Cpu.Core` — the clocked CPU core: `Micro` + `Interrupts`

`Core` is what the system clocks: the cycle-level micro-machine (`MicroState`) plus the
interrupt detectors (`IntState`) and the per-instruction bookkeeping needed to drive them as
documented in `Nes.Cpu.Interrupts`. `Micro` itself is untouched; the interrupt hook it exposes
(`requestInterrupt`, the `vec` field read by the vector fetch) is all this layer needs.

## Two-phase API (mirrors `MicroState`)

* `Core.busOp c` — the bus operation of this cycle (= `c.ms.busOp`).
* `Core.complete c lines v` — finish the cycle with the byte read `v` (ignored for writes) and
  the interrupt lines `lines` as they stand in this cycle's φ2. It
  1. completes the micro-op (`MicroState.complete`) and counts the cycle (`cyc`, 1-based,
     reset to 1 on the cycle taken at a boundary);
  2. on a boundary cycle records the sequence kind (`kind`: the hardware kind decided at the
     previous boundary, `.brk` when opcode `$00` was fetched, else `.none`) and `iBefore`;
  3. in cycle 5 of a 7-cycle sequence (`kind ≠ none`: NMI/IRQ/RESET/BRK), *before* this
     cycle's sample: `(vec, ints) := vectorFetch ints kind` and `ms.vec := vec` (the vector
     is read in cycles 6–7, so this is the hijack point);
  4. `ints := sampleCycle ints lines iFlag poll`, with `poll = false` inside sequences and on
     halted cycles; for branches `branchPollCycle cyc (taken && crossed)`; otherwise
     `isPollCycle cyc total` with `total = e.cycles + (e.pageCross && crossed)` — exact, since
     `crossed` is known by the end of every read's poll cycle (`fetchHiX/Y`, `ptrHiY` are at
     or before it). `iFlag = pollIFlag instr iBefore iNow` where `iNow` is the I flag after
     the micro-op (at a poll cycle it equals the instruction's final I for every instruction
     except CLI/SEI/PLP, which `pollIFlag` maps to `iBefore`);
  5. if the machine is now at a boundary: `k := atBoundary ints` (RESET > NMI > IRQ; only RESET
     when the CPU is halted by JAM); if `k ≠ none`, `ints := ack ints`,
     `ms := ms.requestInterrupt k.vector k.suppressWrites`, `kind := k`.
* `Core.cycle` / `Core.cycleEv` / `Core.runCycles` run against flat memory (tests).

## Power-on

`Core.ofState s` is a core at an instruction boundary that starts executing at `s.pc` with all
detectors idle (Harte cases, nestest). `Core.powerOn s` requests RESET instead: the CPU starts
with the RESET sequence at the first cycle. Since that sequence decrements `SP` by 3 and the
real 2A03 comes up with `SP = $00` internally, `powerOn` sets `SP := $00` first so the sequence
ends with `SP = $FD` (NESdev power-up state); `State.init`'s `SP = $FD` would give `$FA`, which
is what a *warm* reset (`Core.reset`, RESET line) correctly produces.
-/

namespace Nes.Cpu

/-- Is the instruction a conditional branch? -/
@[inline] def Instr.isBranch : Instr → Bool
  | .BPL | .BMI | .BVC | .BVS | .BCC | .BCS | .BNE | .BEQ => true
  | _ => false

/-- Is this a 7-cycle interrupt-entry sequence (BRK included) rather than an instruction? -/
@[inline] def IntKind.isSeq : IntKind → Bool
  | .none => false
  | _ => true

/-- The clocked CPU core. -/
structure Core where
  /-- The cycle-level micro-machine. -/
  ms : MicroState
  /-- Interrupt detectors. -/
  ints : IntState := IntState.init
  /-- 1-based cycle within the current instruction/sequence (cycles completed so far). -/
  cyc : UInt8 := 0
  /-- Kind of the current (or, at a boundary with `ms.intPending`, the next) sequence;
  `.none` for an ordinary instruction. -/
  kind : IntKind := .none
  /-- I flag at the start of the current instruction (for `pollIFlag`). -/
  iBefore : Bool := false
  deriving Repr, Inhabited

namespace Core

/-- A core at an instruction boundary that will fetch its next opcode at `s.pc`. -/
@[inline] def ofState (s : State) : Core := { ms := MicroState.ofState s }

/-- Decide at an instruction boundary: start an interrupt sequence if one is selected. -/
@[inline] def boundary (c : Core) : Core :=
  let k := c.ints.atBoundary
  let k := if c.ms.cpu.halted && k != .reset then IntKind.none else k
  if k.isSeq then
    { c with ints := c.ints.ack, kind := k,
             ms := c.ms.requestInterrupt k.vector k.suppressWrites }
  else c

/-- A core whose next cycle starts the RESET sequence (warm reset: `SP` decrements by 3). -/
@[inline] def reset (c : Core) : Core :=
  boundary { c with ints := { c.ints with resetPending := true } }

/-- Power-on: `s` with `SP := $00`, then RESET (ends with `SP = $FD`, I set, PC from $FFFC). -/
@[inline] def powerOn (s : State) : Core :=
  reset (ofState { s with sp := 0 })

/-- The bus operation of this cycle. -/
@[inline] def busOp (c : Core) : BusOp := c.ms.busOp

/-- Is the cycle just completed (`cyc`, machine now `ms`) an instruction's polling cycle? -/
@[inline] def pollAt (ms : MicroState) (cyc : UInt8) : Bool :=
  let e := decode ms.op
  if e.instr.isBranch then
    branchPollCycle cyc (branchCond ms.cpu e.instr && ms.crossed)
  else
    isPollCycle cyc (e.cycles + (if e.pageCross && ms.crossed then 1 else 0))

/-- Finish the cycle announced by `busOp c` given the byte read `v` (ignored for writes) and
the interrupt lines of this cycle. -/
@[inline] def complete (c : Core) (lines : IntLines) (v : UInt8) : Core :=
  let ms0 := c.ms
  let start := ms0.pos == 0
  let ms := ms0.complete v
  let halted := start && ms.pos == 0
  let cyc : UInt8 := if start then 1 else c.cyc + 1
  let kind :=
    if start then
      if ms0.intPending then c.kind
      else if !halted && ms.op == 0 then IntKind.brk
      else IntKind.none
    else c.kind
  let iBefore := if start then ms0.cpu.i else c.iBefore
  let (ms, ints) :=
    if kind.isSeq && cyc == 5 then
      let (vec, st) := c.ints.vectorFetch kind
      ({ ms with vec := vec }, st)
    else (ms, c.ints)
  let poll := !kind.isSeq && !halted && pollAt ms cyc
  let iFlag := pollIFlag (decode ms.op).instr iBefore ms.cpu.i
  let ints := ints.sampleCycle lines iFlag poll
  let c' : Core := { ms, ints, cyc, kind, iBefore }
  if ms.pos == 0 then c'.boundary else c'

/-- One cycle against flat memory. -/
@[inline] def cycle (c : Core) (lines : IntLines) (m : Mem) : Core × Mem :=
  match c.busOp with
  | .read a => (c.complete lines (m.read a), m)
  | .write a v => (c.complete lines v, m.write a v)

/-- One cycle against flat memory, also returning the bus event. -/
@[inline] def cycleEv (c : Core) (lines : IntLines) (m : Mem) : Core × Mem × BusEvent :=
  match c.busOp with
  | .read a => let v := m.read a; (c.complete lines v, m, ⟨a, v, false⟩)
  | .write a v => (c.complete lines v, m.write a v, ⟨a, v, true⟩)

/-- Run `fuel` cycles with constant interrupt lines. -/
def runCycles : Nat → Core → IntLines → Mem → Core × Mem
  | 0, c, _, m => (c, m)
  | fuel + 1, c, lines, m =>
    let (c', m') := c.cycle lines m
    runCycles fuel c' lines m'

/-- All interrupt lines idle. -/
@[inline] def idle : IntLines := { nmi := false, irq := false, reset := false }

end Core

end Nes.Cpu
