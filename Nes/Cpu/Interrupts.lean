import Nes.Cpu.Decode

/-!
# `Nes.Cpu.Interrupts` — NMI/IRQ/RESET detection, polling and vector selection

Pure decision logic for the 2A03 interrupt inputs. It does not run any bus cycles: the
cycle-level CPU (`Nes.Cpu.Micro`) calls these functions once per cycle and at instruction
boundaries, and runs the 7-cycle interrupt-entry micro-program itself. Everything here is
closure-free `Bool`/`UInt` code so it compiles to scalar operations on the hot path.

Source for every timing rule: NESdev wiki, "CPU interrupts" (which summarises Visual 6502
traces). Cycles are numbered from 1 = the opcode fetch.

## Line convention

`IntLines` gives the *asserted* state of each input this cycle: `true` = asserted (the
active-low `/NMI`, `/IRQ`, `/RESET` pins are pulled low). `irq` is the wired-OR of all IRQ
sources (APU frame counter, DMC, mapper).

## Timing rules modelled

1. **NMI edge detector.** Every cycle (φ2) the `/NMI` level is sampled; a not-asserted →
   asserted transition sets `nmiPending`, which stays set until the NMI is serviced (the
   vector is fetched). Holding the line asserted does not retrigger (`nmiPrev`).
2. **IRQ level detector.** Every cycle the `/IRQ` level is sampled into `irqPending` (no
   latching: if the line drops before the poll, the IRQ is not seen).
3. **Polling point.** The detector outputs are polled at the end of the *second-to-last*
   cycle of each instruction (equivalently "during the last cycle, from the signal that
   was sampled in φ2 of the cycle before"). So a line must be asserted by φ2 of the
   second-to-last cycle to be serviced after this instruction. For a 2-cycle instruction
   the poll cycle is cycle 1 (the opcode fetch). `isPollCycle` below computes this.
4. **I mask.** IRQ is selected at the poll only if the I flag *as seen at the poll* is 0.
   CLI, SEI and PLP change I in their last cycle, i.e. *after* the poll, so the poll sees
   the old value: an IRQ is still taken right after SEI if I was 0, and is taken only after
   the instruction *following* CLI/PLP. RTI pulls P in cycle 5 of 6 (its second-to-last),
   so its poll already sees the restored I (no delay). `pollIFlag` encodes this.
5. **Branches.** Interrupts are polled at the end of cycle 1 (before the operand fetch)
   for every branch, and again at the end of cycle 3 (before the PCH fix-up) only for a
   taken branch that crosses a page. A taken branch *without* page cross (3 cycles) is
   therefore polled only at the end of cycle 1, not at its second-to-last cycle: an
   interrupt arriving in its cycle 2 is delayed by one instruction. `branchPollCycle`.
6. **Priority at the boundary.** RESET > NMI > IRQ. Interrupt sequences themselves never
   poll, so the first instruction of a handler always executes before another interrupt
   (an NMI arriving late in a BRK/IRQ sequence is serviced after that instruction).
7. **Hijacking.** During a BRK or IRQ sequence, the vector is chosen in cycle 5 (the P
   push) from the NMI detector output, i.e. from lines sampled up to φ2 of cycle 4. If an
   NMI is pending then, the sequence fetches $FFFA instead of $FFFE and the NMI is
   consumed; the pushed P keeps the B bit of the original sequence (set for BRK, clear for
   IRQ), and the BRK still consumes its 7 cycles and pushed `PC+2`. An NMI asserted in
   cycles 5–7 is not lost: it stays pending and is taken after the handler's first
   instruction. An NMI sequence is never hijacked by IRQ.
8. **RESET.** Runs the same 7-cycle sequence with the three stack writes turned into
   reads (SP still decremented by 3), sets I, and fetches $FFFC.
9. **B bit.** Set only in the pushed copy, and only for BRK (and PHP, outside this module);
   IRQ and NMI push B = 0. `IntKind.pushB`.

## Known gaps

* RESET is taken at the next instruction boundary, not mid-instruction (the real CPU
  aborts the current instruction). Programs cannot observe the difference in practice.
* The "NMI edge lost if a hijacking NMI is asserted for only part of cycle 4/5" sub-cycle
  glitches are not modelled (we sample once per cycle).
* An NMI edge occurring during cycles 1–4 of an NMI sequence itself is consumed by that
  sequence's vector fetch (`vectorFetch` clears `nmiPending`).
* IRQ asserted then deasserted *during* an IRQ sequence still vectors through $FFFE
  (correct per NESdev), and an IRQ sequence starting from a since-deasserted line is
  likewise not cancelled.
-/

namespace Nes.Cpu

/-- Interrupt input lines this cycle; `true` = asserted (pin pulled low). -/
structure IntLines where
  nmi : Bool
  irq : Bool
  reset : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Kind of interrupt sequence to run at an instruction boundary (or `none` = fetch the next
opcode). `brk` is the software interrupt; it shares the IRQ vector but pushes B = 1. -/
inductive IntKind where
  | none | nmi | irq | brk | reset
  deriving Repr, DecidableEq, Inhabited

namespace IntKind

/-- NMI vector. -/
@[inline] def vecNmi : UInt16 := 0xFFFA
/-- RESET vector. -/
@[inline] def vecReset : UInt16 := 0xFFFC
/-- IRQ/BRK vector. -/
@[inline] def vecIrq : UInt16 := 0xFFFE

/-- Default vector (low byte address) of each sequence, before any hijack. -/
@[inline] def vector : IntKind → UInt16
  | .nmi => vecNmi
  | .reset => vecReset
  | .irq | .brk | .none => vecIrq

/-- B bit of the pushed status byte: set only for BRK. -/
@[inline] def pushB : IntKind → Bool
  | .brk => true
  | _ => false

/-- RESET turns the three stack pushes into reads (SP still decremented by 3). -/
@[inline] def suppressWrites : IntKind → Bool
  | .reset => true
  | _ => false

/-- Whether the sequence's vector can be hijacked by a pending NMI (BRK and IRQ only). -/
@[inline] def hijackable : IntKind → Bool
  | .irq | .brk => true
  | _ => false

end IntKind

/-- Interrupt detector state, carried by the CPU between cycles. -/
structure IntState where
  /-- NMI line level sampled in the previous cycle (edge detection). -/
  nmiPrev : Bool
  /-- NMI edge detector output: an edge was seen and the NMI is not serviced yet. -/
  nmiPending : Bool
  /-- IRQ level detector output: the IRQ line level sampled this cycle. -/
  irqPending : Bool
  /-- RESET line was asserted; taken at the next boundary. -/
  resetPending : Bool
  /-- NMI detector output latched at the last polling point. -/
  pollNmi : Bool
  /-- IRQ detector output, masked by the I flag seen at the poll, latched at the last poll. -/
  pollIrq : Bool
  deriving Repr, DecidableEq, Inhabited

namespace IntState

/-- All detectors idle. (Power-up itself is driven by the caller running a RESET sequence;
set `resetPending := true` to request it through `atBoundary`.) -/
def init : IntState :=
  { nmiPrev := false, nmiPending := false, irqPending := false, resetPending := false,
    pollNmi := false, pollIrq := false }

/-- Per-cycle update. Call once per CPU cycle, *after* that cycle's bus operation, with the
lines as they stand in that cycle's φ2.
* NMI: `nmiPending` is set on a not-asserted → asserted edge and held until `vectorFetch`.
* IRQ: `irqPending` is the line level this cycle.
* RESET: latched into `resetPending`.
* If `isPollCycle` (the instruction's polling cycle, see `isPollCycle`/`branchPollCycle`;
  always `false` inside interrupt sequences) the outputs are latched into `pollNmi`/`pollIrq`,
  IRQ masked by `iFlag` = the I flag the poll sees (`pollIFlag`). -/
@[inline] def sampleCycle (st : IntState) (lines : IntLines) (iFlag : Bool)
    (isPollCycle : Bool) : IntState :=
  let nmiPending := st.nmiPending || (!st.nmiPrev && lines.nmi)
  let irqPending := lines.irq
  { nmiPrev := lines.nmi, nmiPending, irqPending,
    resetPending := st.resetPending || lines.reset,
    pollNmi := if isPollCycle then nmiPending else st.pollNmi,
    pollIrq := if isPollCycle then irqPending && !iFlag else st.pollIrq }

/-- Decision at an instruction boundary (after the last cycle of an instruction, instead of
fetching the next opcode). Priority RESET > NMI > IRQ. Pure: follow with `ack` when the
returned kind is not `none`. -/
@[inline] def atBoundary (st : IntState) : IntKind :=
  if st.resetPending then .reset
  else if st.pollNmi then .nmi
  else if st.pollIrq then .irq
  else .none

/-- Acknowledge the start of an interrupt sequence: clear the poll latches (and the RESET
request), so the handler's first instruction always runs before the next poll. The NMI edge
latch `nmiPending` is cleared later, by `vectorFetch`. -/
@[inline] def ack (st : IntState) : IntState :=
  { st with pollNmi := false, pollIrq := false, resetPending := false }

/-- Vector selection, called in **cycle 5** of the 7-cycle sequence (the P push), *before*
that cycle's `sampleCycle` — so it sees NMI edges sampled up to cycle 4. Returns the address
of the vector's low byte (fetched in cycle 6; high byte at `+1` in cycle 7) and the new state.
BRK/IRQ with an NMI pending are hijacked to $FFFA; NMI (own or hijacking) clears
`nmiPending`. The pushed B bit is unaffected by a hijack (use `kind.pushB`). -/
@[inline] def vectorFetch (st : IntState) (kind : IntKind) : UInt16 × IntState :=
  if kind == .nmi || (kind.hijackable && st.nmiPending) then
    (IntKind.vecNmi, { st with nmiPending := false })
  else (kind.vector, st)

end IntState

/-- The I flag value that the poll of instruction `op` sees: CLI, SEI and PLP change I only
after their poll, so it sees `iBefore`; every other instruction (notably RTI, which restores
P before its poll) is polled with `iAfter` = the I flag after the instruction. -/
@[inline] def pollIFlag (op : Instr) (iBefore iAfter : Bool) : Bool :=
  match op with
  | .CLI | .SEI | .PLP => iBefore
  | _ => iAfter

/-- Is 1-based `cycle` the polling cycle of a non-branch instruction of `total` cycles? It is
the second-to-last cycle (cycle 1 for a 2-cycle instruction). -/
@[inline] def isPollCycle (cycle total : UInt8) : Bool := cycle + 1 == total

/-- Polling cycles of a branch: cycle 1 always (before the operand fetch), plus cycle 3 for a
taken branch crossing a page (before the PCH fix-up). A taken branch without page cross is
not polled in its second-to-last cycle (NESdev "CPU interrupts", branch quirk). -/
@[inline] def branchPollCycle (cycle : UInt8) (takenCross : Bool) : Bool :=
  cycle == 1 || (takenCross && cycle == 3)

/-! ## Sanity checks -/

section Examples
open IntState

private def L (nmi irq : Bool) : IntLines := { nmi := nmi, irq := irq, reset := false }

-- An NMI edge is latched only on a not-asserted → asserted transition.
example : (sampleCycle init (L true false) false false).nmiPending = true := by decide
example : (sampleCycle { init with nmiPrev := true } (L true false) false false).nmiPending
    = false := by decide
example : (sampleCycle init (L false false) false false).nmiPending = false := by decide
-- Once latched, the NMI edge persists after the line is released.
example : (sampleCycle (sampleCycle init (L true false) false false) (L false false) false
    false).nmiPending = true := by decide

-- IRQ with I = 1 is never selected; with I = 0 it is.
example (st : IntState) (irq : Bool) :
    (sampleCycle st { nmi := false, irq := irq, reset := false } true true).pollIrq = false := by
  cases st; cases irq <;> rfl
example : atBoundary (sampleCycle init (L false true) false true) = .irq := by decide
-- NMI beats IRQ; latching happens only at the poll cycle.
example : atBoundary (sampleCycle init (L true true) false true) = .nmi := by decide
example : atBoundary (sampleCycle init (L true true) false false) = .none := by decide

-- Hijack: a BRK or IRQ sequence with an NMI pending fetches $FFFA and consumes the NMI.
example : vectorFetch { init with nmiPending := true } .brk
    = (0xFFFA, init) := by decide
example : vectorFetch { init with nmiPending := true } .irq
    = (0xFFFA, init) := by decide
example : (vectorFetch init .brk).1 = 0xFFFE := by decide
example : (vectorFetch init .reset).1 = 0xFFFC := by decide
example : (vectorFetch { init with nmiPending := true } .reset).1 = 0xFFFC := by decide

-- CLI/SEI/PLP delay; RTI does not delay.
example : pollIFlag .CLI true false = true := by decide
example : pollIFlag .RTI true false = false := by decide

-- Taken branch without page cross: only cycle 1 polls.
example : branchPollCycle 2 false = false := by decide
example : branchPollCycle 3 true = true := by decide

end Examples

end Nes.Cpu
