import Nes.Cpu.Core
import Nes.Cpu.Proofs.Refinement

/-!
# `Nes.Cpu.Proofs.Interrupts` — T-CPU-7: interrupt semantics

## Spec

Decision layer (pure `IntState` logic, `Nes.Cpu.Interrupts`):
* `T_CPU_7_irq_masked`: from a state with a clear IRQ poll latch, any sequence of
  `sampleCycle` steps whose polls see I = 1 (`sampleMasked`) never selects IRQ at a boundary.
  `pollIFlag_true`: when I is set before and after an instruction its poll sees I = 1.
* `T_CPU_7_hijack_decision`: `vectorFetch` of a BRK/IRQ sequence with an NMI pending returns
  `$FFFA` and clears `nmiPending`; `vectorFetch_no_hijack`, `vectorFetch_nmi`.
* `T_CPU_7_nmi_latch`: an NMI edge sets `nmiPending`, which survives any number of
  `sampleCycle` steps; the next poll latches it into `pollNmi`, and `atBoundary` then returns
  `.nmi` (or `.reset`, which has priority).

Core layer (cycle-by-cycle over `Core.runCycles`, lines held constant):
* `T_CPU_7_entry`: from a boundary at which an NMI or IRQ sequence was requested, exactly 7
  cycles (no boundary in cycles 1–6) push `PCH`, `PCL`, `P|$20` at `$0100+SP, SP-1, SP-2`
  (`entryMem`), leave `SP - 3`, I = 1 and `PC = mem16[v]` (read after the pushes) with
  `v = entryVector k ints lines` (`$FFFA` for NMI; `$FFFE` for IRQ unless hijacked).
  `T_CPU_7_entry_irq`: an IRQ with no NMI pending / no NMI edge loads `$FFFE`.
* `T_CPU_7_brk`: the same for an executed `BRK` (opcode `$00`): pushes `PC + 2` and `P|$30`.
* `T_CPU_7_B_only_pushed`: the register P keeps its bit 4 through an entry (only I changes);
  the pushed copy has B = 1 for BRK and B = register bit 4 (= 0 in every reachable state,
  since PLP/RTI clear it) for NMI/IRQ.
* `T_CPU_7_hijack`: a BRK with an NMI already pending (or an NMI edge in its first cycle)
  takes 7 cycles, pushes `PC + 2` and `P|$30` (B = 1) and ends at `PC = mem16[$FFFA]`.
* `T_CPU_7_irq_masked_core`: one `Core.complete` step that keeps I = 1 (before and after the
  instruction) keeps the IRQ poll latch clear and never starts an IRQ sequence; iterated over
  `Core.runCycles` by `T_CPU_7_irq_masked_run`.
* `T_CPU_7_boundary_bound`: every instruction of the micro-machine (non-halted) reaches the
  next boundary in at most 7 cycles (from T-REF-1 + a 256-opcode table fact), and the
  interrupt sequence takes exactly 7 (`entry_micro`).

NMI latency (`maxInstrCycles + 7`) is delivered as these two halves; the composition over
`Core` (relating `Core.runCycles` to `MicroState.runInstr` and tracking the poll cycle) is not
done here.
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs
open Nes Nes.Cpu IntState MicroState Refinement

/-! ## Decision layer -/

/-- The I flag seen at a poll is set whenever I is set both before and after the instruction. -/
theorem pollIFlag_true (op : Instr) : pollIFlag op true true = true := by
  cases op <;> rfl

/-- With the I flag seen at the poll set, `sampleCycle` never sets the IRQ poll latch. -/
theorem sampleCycle_pollIrq (st : IntState) (l : IntLines) (p : Bool) :
    (st.sampleCycle l true p).pollIrq = (!p && st.pollIrq) := by
  cases p <;> simp [sampleCycle]

/-- Run `sampleCycle` over a sequence of `(lines, poll)` with the I flag seen at the poll set. -/
def sampleMasked (st : IntState) : List (IntLines × Bool) → IntState
  | [] => st
  | (l, p) :: xs => sampleMasked (st.sampleCycle l true p) xs

theorem sampleMasked_pollIrq (st : IntState) (xs : List (IntLines × Bool))
    (h : st.pollIrq = false) : (sampleMasked st xs).pollIrq = false := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => obtain ⟨l, p⟩ := x; exact ih _ (by simp [sampleCycle_pollIrq, h])

theorem atBoundary_ne_irq (st : IntState) (h : st.pollIrq = false) : st.atBoundary ≠ .irq := by
  simp only [IntState.atBoundary, h]; split <;> (try split) <;> simp

/-- **T-CPU-7 (IRQ masked, decision layer).** Starting from a state whose IRQ poll latch is
clear (any state just after `ack`, or after a poll that saw I = 1), any sequence of cycles whose
polls see I = 1 never selects IRQ at a boundary, whatever the lines do. -/
theorem T_CPU_7_irq_masked (st : IntState) (xs : List (IntLines × Bool))
    (h : st.pollIrq = false) : (sampleMasked st xs).atBoundary ≠ .irq :=
  atBoundary_ne_irq _ (sampleMasked_pollIrq st xs h)

theorem ack_pollIrq (st : IntState) : st.ack.pollIrq = false := rfl

theorem vectorFetch_pollIrq (st : IntState) (k : IntKind) :
    (st.vectorFetch k).2.pollIrq = st.pollIrq := by
  simp only [vectorFetch]; split <;> rfl

/-! ## Hijack (decision layer) -/

/-- **T-CPU-7 (hijack, decision layer).** A BRK or IRQ sequence whose vector is chosen while an
NMI is pending fetches the NMI vector `$FFFA` and consumes the NMI. -/
theorem T_CPU_7_hijack_decision (st : IntState) (k : IntKind) (hk : k = .brk ∨ k = .irq)
    (h : st.nmiPending = true) :
    st.vectorFetch k = (IntKind.vecNmi, { st with nmiPending := false }) := by
  rcases hk with rfl | rfl <;> simp [vectorFetch, h, IntKind.hijackable]

/-- Without a pending NMI, `vectorFetch` returns the sequence's own vector and changes nothing. -/
theorem vectorFetch_no_hijack (st : IntState) (k : IntKind) (hk : k ≠ .nmi)
    (h : st.nmiPending = false) : st.vectorFetch k = (k.vector, st) := by
  cases k <;> simp_all [vectorFetch, IntKind.hijackable]

/-- An NMI sequence always fetches `$FFFA` and consumes the edge latch. -/
theorem vectorFetch_nmi (st : IntState) :
    st.vectorFetch .nmi = (IntKind.vecNmi, { st with nmiPending := false }) := by
  simp [vectorFetch]

/-! ## NMI latency (decision layer) -/

/-- An NMI edge sets `nmiPending`. -/
theorem sampleCycle_edge (st : IntState) (l : IntLines) (i p : Bool)
    (h : st.nmiPrev = false) (hl : l.nmi = true) : (st.sampleCycle l i p).nmiPending = true := by
  simp [sampleCycle, h, hl]

/-- `nmiPending` persists across `sampleCycle` (only `vectorFetch` clears it). -/
theorem sampleCycle_nmiPending (st : IntState) (l : IntLines) (i p : Bool)
    (h : st.nmiPending = true) : (st.sampleCycle l i p).nmiPending = true := by
  simp [sampleCycle, h]

/-- At a poll cycle the pending NMI is latched into `pollNmi`. -/
theorem sampleCycle_poll_nmi (st : IntState) (l : IntLines) (i : Bool)
    (h : (st.sampleCycle l i true).nmiPending = true) :
    (st.sampleCycle l i true).pollNmi = true := by
  simpa [sampleCycle] using h

/-- A latched NMI poll is taken at the boundary unless a RESET is pending. -/
theorem atBoundary_nmi (st : IntState) (h : st.pollNmi = true) :
    st.atBoundary = .nmi ∨ st.atBoundary = .reset := by
  simp only [IntState.atBoundary, h]; split <;> simp

/-! ## Core layer: interrupt entry -/

/-- Memory after the three pushes of an interrupt entry. -/
def entryMem (s : State) (m : Mem) (pb : UInt8) : Mem :=
  ((m.write (0x100 ||| s.sp.toUInt16) (UInt16.hi s.pc)).write
    (0x100 ||| (s.sp - 1).toUInt16) (UInt16.lo s.pc)).write
    (0x100 ||| (s.sp - 2).toUInt16) pb

theorem sub_two : ∀ x : UInt8, x - 1 - 1 = x - 2 := by decide
theorem sub_three : ∀ x : UInt8, x - 2 - 1 = x - 3 := by decide

/-- Registers after an interrupt entry from `s` that loads `pc`: I set, `SP - 3`. -/
def entryCpu (s : State) (pc : UInt16) : State :=
  { s.setI true with sp := s.sp - 3, pc := pc }

/-- The interrupt-entry program of the micro-machine (`intPending` at a boundary, writes not
suppressed) takes exactly 7 cycles, pushes `PCH, PCL, P|$20`, sets I, `SP - 3`, and loads `PC`
from `ms.vec`. -/
theorem entry_micro (ms : MicroState) (m : Mem) (f : Nat) (hpos : ms.pos = 0)
    (hint : ms.intPending = true) (hsw : ms.suppressWrites = false) :
    let s := ms.cpu
    let m' := entryMem s m (s.p ||| 0x20)
    let r := runInstr (f + 7) ms m
    r.2.2 = 7 ∧ r.2.1 = m' ∧ r.1.pos = 0 ∧
      r.1.cpu = entryCpu s (UInt16.ofLoHi (m'.read ms.vec) (m'.read (ms.vec + 1))) := by
  obtain ⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩ := ms
  simp only at hpos hint hsw; subst hpos hint hsw
  simp [runInstr, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_00,
    skips, stackAddr, pushOp, entryMem, -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu,
    State.setI, State.setBit]

@[simp] theorem boundary_cpu (c : Core) : c.boundary.ms.cpu = c.ms.cpu := by
  simp only [Core.boundary]; split <;> (try split) <;> rfl
@[simp] theorem boundary_pos (c : Core) : c.boundary.ms.pos = c.ms.pos := by
  simp only [Core.boundary]; split <;> (try split) <;> rfl

@[simp] theorem sc_nmiPrev (st : IntState) (l : IntLines) (i p : Bool) :
    (st.sampleCycle l i p).nmiPrev = l.nmi := rfl
@[simp] theorem sc_nmiPending (st : IntState) (l : IntLines) (i p : Bool) :
    (st.sampleCycle l i p).nmiPending = (st.nmiPending || (!st.nmiPrev && l.nmi)) := rfl

@[simp] theorem vf_fst (st : IntState) (k : IntKind) : (st.vectorFetch k).1 =
    if k == .nmi || (k.hijackable && st.nmiPending) then IntKind.vecNmi else k.vector := by
  simp only [IntState.vectorFetch]; split <;> simp_all

/-- The vector a BRK/IRQ/NMI sequence started with lines held at `lines` fetches: `$FFFA` for
NMI, or for BRK/IRQ when an NMI is pending by cycle 4 (latched before, or an edge in cycle 1). -/
def entryVector (k : IntKind) (st : IntState) (lines : IntLines) : UInt16 :=
  if k == .nmi || (k.hijackable && (st.nmiPending || (!st.nmiPrev && lines.nmi))) then
    IntKind.vecNmi else k.vector

/-- **T-CPU-7 (entry, NMI/IRQ).** From a boundary at which `Core.boundary` requested an NMI or
IRQ sequence, with lines held at `lines`: no boundary in cycles 1–6; after cycle 7 the stack
holds `PCH, PCL, P|$20` (B as in the register, bit 5 set), `SP - 3`, I = 1 and
`PC = mem16[entryVector k …]`. -/
theorem T_CPU_7_entry (c : Core) (lines : IntLines) (m : Mem) (k : IntKind)
    (hk : k = .nmi ∨ k = .irq)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = true) (hsw : c.ms.suppressWrites = false)
    (hkind : c.kind = k) :
    let s := c.ms.cpu
    let m' := entryMem s m (s.p ||| 0x20)
    let v := entryVector k c.ints lines
    let r := Core.runCycles 7 c lines m
    (∀ j, 1 ≤ j → j < 7 → (Core.runCycles j c lines m).1.ms.pos ≠ 0) ∧
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read v) (m'.read (v + 1))) := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hsw hkind; subst hpos hint hsw hkind
  refine ⟨?_, ?_⟩
  · intro j h1 h2
    obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
      omega
    all_goals rcases hk with rfl | rfl <;>
      simp [Core.runCycles, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
        complete, MicroState.exec, advance, ctl_uops_00, skips, IntKind.isSeq, pushOp]

  rcases hk with rfl | rfl <;>
  simp [Core.runCycles, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
    complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
    -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
    vf_fst, IntKind.vecNmi, entryVector, sc_nmiPending, sc_nmiPrev, IntKind.hijackable]


/-- **T-CPU-7 (entry, BRK).** Executing opcode `$00` from a boundary: 7 cycles, pushes
`PC + 2` and `P|$30` (B = 1), `SP - 3`, I = 1, `PC = mem16[entryVector .brk …]` (`$FFFE`, or
`$FFFA` when hijacked). -/
theorem T_CPU_7_brk (c : Core) (lines : IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) :
    let s := c.ms.cpu
    let m' := entryMem { s with pc := s.pc + 2 } m (s.p ||| 0x30)
    let v := entryVector .brk c.ints lines
    let r := Core.runCycles 7 c lines m
    (∀ j, 1 ≤ j → j < 7 → (Core.runCycles j c lines m).1.ms.pos ≠ 0) ∧
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read v) (m'.read (v + 1))) := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hh hop; subst hpos hint
  refine ⟨?_, ?_⟩
  · intro j h1 h2
    obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
      omega
    all_goals simp [Core.runCycles, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp,
      curOp, complete, MicroState.exec, advance, ctl_uops_00, skips, IntKind.isSeq, hh, hop,
      pushOp]
  simp [Core.runCycles, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
    complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
    -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
    vf_fst, IntKind.vecNmi, entryVector, sc_nmiPending, sc_nmiPrev, IntKind.hijackable,
    hh, hop, UInt16.add_assoc]

/-- An IRQ sequence with no NMI pending and no NMI edge in its first cycle loads `$FFFE`. -/
theorem T_CPU_7_entry_irq (st : IntState) (lines : IntLines) (h : st.nmiPending = false)
    (hl : st.nmiPrev = true ∨ lines.nmi = false) : entryVector .irq st lines = IntKind.vecIrq := by
  rcases hl with hl | hl <;> simp [entryVector, h, hl, IntKind.hijackable, IntKind.vector]

theorem entryVector_nmi (st : IntState) (lines : IntLines) :
    entryVector .nmi st lines = IntKind.vecNmi := by simp [entryVector]

/-! ## B bit -/

theorem or_I_bitB : ∀ x : UInt8, (x ||| Flags.maskI) &&& 0x10 = x &&& 0x10 := by decide
theorem or20_bitB : ∀ x : UInt8, (x ||| 0x20) &&& 0x10 = x &&& 0x10 := by decide
theorem or30_bitB : ∀ x : UInt8, (x ||| 0x30) &&& 0x10 = 0x10 := by decide
theorem or_I_i : ∀ x : UInt8, ((x ||| Flags.maskI) &&& Flags.maskI != 0) = true := by decide

/-- **T-CPU-7 (B bit).** An interrupt entry leaves bit 4 (B) of the register P unchanged and
sets I; the pushed copy has B = 1 for BRK (`P|$30`) and B = the register's bit 4 for NMI/IRQ
(`P|$20`), i.e. B = 0 whenever the register's B is clear. -/
theorem T_CPU_7_B_only_pushed (s : State) (pc : UInt16) :
    (entryCpu s pc).p &&& 0x10 = s.p &&& 0x10 ∧ (entryCpu s pc).i = true ∧
    (s.p ||| 0x30) &&& 0x10 = 0x10 ∧ (s.p ||| 0x20) &&& 0x10 = s.p &&& 0x10 := by
  refine ⟨?_, ?_, or30_bitB _, or20_bitB _⟩
  · simp only [entryCpu, State.setI, State.setBit, ite_true]; exact or_I_bitB _
  · simp only [entryCpu, State.setI, State.setBit, State.i, State.getBit, ite_true]
    exact or_I_i _

/-! ## Hijack (core layer) -/

/-- **T-CPU-7 (hijack, core layer).** A BRK with an NMI pending (latched before it, or an NMI
edge in its first cycle) still takes 7 cycles and pushes `PC + 2` and `P|$30` (B = 1), but ends
at `PC = mem16[$FFFA]`. -/
theorem T_CPU_7_hijack (c : Core) (lines : IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0)
    (hn : c.ints.nmiPending = true ∨ (c.ints.nmiPrev = false ∧ lines.nmi = true)) :
    let s := c.ms.cpu
    let m' := entryMem { s with pc := s.pc + 2 } m (s.p ||| 0x30)
    let r := Core.runCycles 7 c lines m
    (∀ j, 1 ≤ j → j < 7 → (Core.runCycles j c lines m).1.ms.pos ≠ 0) ∧
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read 0xFFFA) (m'.read 0xFFFB)) := by
  have hv : entryVector .brk c.ints lines = IntKind.vecNmi := by
    rcases hn with hn | ⟨h1, h2⟩
    · simp [entryVector, IntKind.hijackable, hn]
    · simp [entryVector, IntKind.hijackable, h1, h2]
  have := T_CPU_7_brk c lines m hpos hint hh hop
  simp only [hv] at this
  exact this

/-! ## NMI latency (decision layer) -/

/-- Run `sampleCycle` over a sequence of `(lines, iFlag, poll)`. -/
def sampleAll (st : IntState) : List (IntLines × Bool × Bool) → IntState
  | [] => st
  | (l, i, p) :: xs => sampleAll (st.sampleCycle l i p) xs

theorem sampleAll_nmiPending (st : IntState) (xs : List (IntLines × Bool × Bool))
    (h : st.nmiPending = true) : (sampleAll st xs).nmiPending = true := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => obtain ⟨l, i, p⟩ := x; exact ih _ (sampleCycle_nmiPending _ _ _ _ h)

/-- **T-CPU-7 (NMI latency, decision layer).** An NMI edge sampled in some cycle sets
`nmiPending`; it survives any further cycles (only `vectorFetch` clears it), so the next poll
cycle latches `pollNmi`, and the following boundary selects `.nmi` (or `.reset`). -/
theorem T_CPU_7_nmi_latch (st : IntState) (l : IntLines) (i p : Bool)
    (xs : List (IntLines × Bool × Bool)) (l' : IntLines) (i' : Bool)
    (h : st.nmiPrev = false) (hl : l.nmi = true) :
    let st' := (sampleAll (st.sampleCycle l i p) xs).sampleCycle l' i' true
    st'.pollNmi = true ∧ (st'.atBoundary = .nmi ∨ st'.atBoundary = .reset) := by
  have h1 := sampleAll_nmiPending _ xs (sampleCycle_edge st l i p h hl)
  have h2 := sampleCycle_poll_nmi _ l' i' (sampleCycle_nmiPending _ l' i' true h1)
  exact ⟨h2, atBoundary_nmi _ h2⟩

/-! ## Instruction length bound (micro layer) -/

theorem runInstr_pos (f : Nat) (ms : MicroState) (m : Mem) :
    (runInstr f ms m).1.pos ≠ 0 → (runInstr f ms m).2.2 = f := by
  induction f generalizing ms m with
  | zero => intro _; rfl
  | succ f ih =>
    rw [runInstr_succ]
    split
    · rename_i h; intro h'; simp_all
    · intro h'; simp only [bump] at h' ⊢; rw [ih _ _ h']

/-- Every opcode outside the RMW class takes at most 7 cycles (penalties included); RMW
opcodes take at most 8 (the illegal `(ind,X)`/`(ind),Y` RMWs). -/
theorem cycles_table : ∀ i : Fin 256,
    (decodeFin i).cycles.toNat + (if (decodeFin i).mode == .rel then 2
      else if (decodeFin i).pageCross then 1 else 0) ≤
      (if classify (decodeFin i) == .rmw then 8 else 7) := by
  decide +kernel

theorem step_cycles_le (s : State) (m : Mem) :
    (step s m).2.2 ≤ (if classify (decode (m.read s.pc)) == .rmw then 8 else 7) := by
  have ht := cycles_table ⟨(m.read s.pc).toNat, (m.read s.pc).toNat_lt⟩
  rw [← decode_eq_decodeFin] at ht
  unfold step
  split
  · split <;> simp
  · simp only [extraCycles]
    revert ht
    generalize decode (m.read s.pc) = e
    intro ht
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega

theorem modePrefix_size (mode : AddrMode) : (modePrefix mode).size ≤ 4 := by
  cases mode <;> decide

/-- RMW instructions end at a boundary (their suffix always runs to the end). -/
theorem rmw_boundary (s : State) (m : Mem) (h : s.halted = false)
    (hc : classify (decode (m.read s.pc)) = .rmw) :
    ((MicroState.ofState s).runInstr maxCycles m).1.pos = 0 := by
  obtain ⟨base, data, heq, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  rw [heq]
  have hk4 := prefixCycles_le (decode (m.read s.pc)).mode (decode (m.read s.pc)).pageCross
    (if resolvesAddr (decode (m.read s.pc)).mode then
      prefixAddr s m (decode (m.read s.pc)).mode else (0, false)).2
  have hsz := modePrefix_size (decode (m.read s.pc)).mode
  revert hk4
  generalize prefixCycles _ _ _ = k
  intro hk4
  rw [show 7 - k = (4 - k) + 1 + 1 + 1 by omega,
    rmw_suffix _ _ _ (modePrefix (decode (m.read s.pc)).mode)]
  · rfl
  · show uops (m.read s.pc) = _
    rw [uops_split _ (by rw [hc]; rfl), hc]; rfl
  · simp; omega
  · exact hsz

/-- **T-CPU-7 (instruction length).** From any non-halted boundary, the micro-machine reaches
the next boundary within 8 cycles (7 for every non-RMW opcode); `maxCycles = 8` suffices. -/
theorem T_CPU_7_boundary_bound (s : State) (m : Mem) (h : s.halted = false) :
    let r := (MicroState.ofState s).runInstr maxCycles m
    r.1.pos = 0 ∧ r.2.2 ≤ 8 := by
  have hs := T_REF_1 s m h
  have hc := step_cycles_le s m
  simp only [microStep] at hs
  rw [← hs] at hc
  have hn : ((MicroState.ofState s).runInstr maxCycles m).2.2 ≤
      (if classify (decode (m.read s.pc)) == .rmw then 8 else 7) := hc
  refine ⟨?_, by split at hn <;> omega⟩
  by_cases hr : classify (decode (m.read s.pc)) = .rmw
  · exact rmw_boundary s m h hr
  · refine Classical.byContradiction fun hp => ?_
    have := runInstr_pos _ _ _ hp
    simp only [hr, beq_iff_eq, ite_false, maxCycles] at hn this
    omega

/-! ## IRQ masked (core layer) -/

theorem boundary_masked (c : Core) (hp : c.ints.pollIrq = false) (hk : c.kind ≠ .irq) :
    c.boundary.ints.pollIrq = false ∧ c.boundary.kind ≠ .irq ∧
      c.boundary.iBefore = c.iBefore := by
  have hb := atBoundary_ne_irq _ hp
  simp only [Core.boundary]
  split <;> (try split) <;> simp_all [IntState.ack]

/-- **T-CPU-7 (IRQ masked, core layer, one cycle).** If the IRQ poll latch is clear, I is set
at the start of the instruction (`iBefore`, or the current I at an opcode fetch) and stays set
after this cycle's micro-op, and no IRQ sequence is running, then after the cycle (any lines,
any byte read) the latch is still clear, I is still set and no IRQ sequence has been started. -/
theorem T_CPU_7_irq_masked_core (c : Core) (lines : IntLines) (v : UInt8)
    (hp : c.ints.pollIrq = false) (hI0 : c.ms.cpu.i = true) (hIb : c.iBefore = true)
    (hI1 : (c.ms.complete v).cpu.i = true) (hk : c.kind ≠ .irq) :
    let c' := c.complete lines v
    c'.ints.pollIrq = false ∧ c'.ms.cpu.i = true ∧ c'.iBefore = true ∧ c'.kind ≠ .irq := by
  intro c'
  have key : ∀ (c0 : Core) (b : Bool), c0.ints.pollIrq = false → c0.kind ≠ .irq →
      c0.iBefore = true → c0.ms.cpu.i = true →
      let c1 := if b then c0.boundary else c0
      c1.ints.pollIrq = false ∧ c1.ms.cpu.i = true ∧ c1.iBefore = true ∧ c1.kind ≠ .irq := by
    intro c0 b h1 h2 h3 h4
    have := boundary_masked c0 h1 h2
    cases b <;> simp_all
  simp only [c', Core.complete]
  apply key
  all_goals (try split) <;> (try split) <;> simp_all [IntState.sampleCycle, pollIFlag_true,
    vectorFetch_pollIrq]
  all_goals split <;> simp

theorem complete_cpu (c : Core) (lines : IntLines) (v : UInt8) :
    (c.complete lines v).ms.cpu = (c.ms.complete v).cpu := by
  simp only [Core.complete]
  split <;> (try split) <;> simp <;> split <;> simp

theorem cycle_complete (c : Core) (lines : IntLines) (m : Mem) :
    ∃ v, (c.cycle lines m).1 = c.complete lines v := by
  simp only [Core.cycle]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **T-CPU-7 (IRQ masked, core layer).** Run `n` cycles from a core whose IRQ poll latch is
clear, with I set at the start and after every cycle (no CLI/PLP/RTI clearing it), and no IRQ
sequence running: the IRQ poll latch stays clear and no IRQ sequence is ever started, whatever
the (constant) lines and memory. -/
theorem T_CPU_7_irq_masked_run (n : Nat) (c : Core) (lines : IntLines) (m : Mem)
    (hp : c.ints.pollIrq = false) (hIb : c.iBefore = true) (hk : c.kind ≠ .irq)
    (hI : ∀ j ≤ n, (Core.runCycles j c lines m).1.ms.cpu.i = true) :
    (Core.runCycles n c lines m).1.ints.pollIrq = false ∧
      (Core.runCycles n c lines m).1.kind ≠ .irq := by
  induction n generalizing c m with
  | zero => exact ⟨hp, hk⟩
  | succ n ih =>
    have hI0 := hI 0 (by omega)
    have hI1 := hI 1 (by omega)
    simp only [Core.runCycles] at hI0 hI1
    obtain ⟨v, hv⟩ := cycle_complete c lines m
    rw [hv, complete_cpu] at hI1
    have h := T_CPU_7_irq_masked_core c lines v hp hI0 hIb hI1 hk
    simp only at h
    obtain ⟨h1, -, h3, h4⟩ := h
    show (Core.runCycles n (c.cycle lines m).1 lines (c.cycle lines m).2).1.ints.pollIrq = false ∧
      (Core.runCycles n (c.cycle lines m).1 lines (c.cycle lines m).2).1.kind ≠ .irq
    apply ih
    · rw [hv]; exact h1
    · rw [hv]; exact h3
    · rw [hv]; exact h4
    · intro j hj; exact hI (j + 1) (by omega)

end Nes.Cpu.Proofs
