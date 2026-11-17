import Nes.Cpu.Proofs.Interrupts

/-!
# `Nes.Cpu.Proofs.InterruptsHijack` — T-CPU-7: mid-BRK NMI hijack, IRQ masking from the opcode

## Spec

* `runSched n ls c m`: `n` cycles of `Core.cycle` where cycle `k` (0-based) sees lines `ls k`.
  `runSched_const`: constant schedule = `Core.runCycles`; `runSched_add`: split at `a + b`.
* `T_CPU_7_hijack_mid`: BRK fetched at a boundary, NMI line inactive before it and asserted from
  1-based cycle `j ∈ {2,3,4}` on (`hjNmiFrom j irq`, IRQ line arbitrary): cycles 1–6 stay inside
  the sequence; after 7 cycles the stack holds `PC + 2`, `P|$30` (B = 1, bit 5), `SP - 3`,
  I = 1, `PC = mem16[$FFFA]`, `nmiPending = false` (consumed), and `hjQuiet` holds after every
  later cycle `7 + n` (no NMI sequence is ever requested while the line stays asserted).
* `T_CPU_7_hijack_late`: the edge in cycle `j ≥ 5` is too late: the BRK fetches `$FFFE`, and for
  `j ≤ 7` the NMI is still pending after the 7 cycles (no NMI sequence requested yet).
* `hj_quiet_run`: with the NMI line held asserted, an NMI-quiet core (edge latch clear, line
  already high, no NMI poll latched, no NMI sequence) stays quiet for any number of cycles.
* `T_CPU_7_irq_masked_opcode`: from an opcode-fetch boundary with I = 1 and the IRQ poll latch
  clear, if the opcode is not `$58` (CLI), `$28` (PLP) or `$40` (RTI), then under any line
  schedule every cycle of the instruction, up to the one reaching the next boundary, keeps
  I = 1 and the IRQ poll latch clear and requests no IRQ sequence. Derived from the micro-op
  semantics (`hj_exec_i`) and a 256-opcode table (`hj_pullP_table`: only RTI pulls P via
  `pullPInc`; `hj_clr_table`: only those three bytes decode to CLI/PLP/RTI).
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs
open Nes Nes.Cpu IntState MicroState Refinement

/-- Run `n` cycles against flat memory with a per-cycle line schedule: cycle `k` (0-based, i.e.
1-based cycle `k + 1`) sees `ls k`. -/
def runSched : Nat → (Nat → IntLines) → Core → Mem → Core × Mem
  | 0, _, c, m => (c, m)
  | n + 1, ls, c, m =>
    let r := c.cycle (ls 0) m
    runSched n (fun k => ls (k + 1)) r.1 r.2

theorem runSched_const (n : Nat) (l : IntLines) (c : Core) (m : Mem) :
    runSched n (fun _ => l) c m = Core.runCycles n c l m := by
  induction n generalizing c m with
  | zero => rfl
  | succ n ih => simp only [runSched, Core.runCycles]; exact ih _ _

theorem runSched_add (a b : Nat) (ls : Nat → IntLines) (c : Core) (m : Mem) :
    runSched (a + b) ls c m =
      runSched b (fun k => ls (a + k)) (runSched a ls c m).1 (runSched a ls c m).2 := by
  induction a generalizing ls c m with
  | zero => simp [runSched]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runSched]
    rw [ih]
    congr 1 <;> (funext k; congr 1; omega)

@[local simp] theorem hj_boundary_nmiPending (c : Core) :
    c.boundary.ints.nmiPending = c.ints.nmiPending := by
  simp only [Core.boundary]; split <;> (try split) <;> rfl
@[local simp] theorem hj_boundary_nmiPrev (c : Core) : c.boundary.ints.nmiPrev = c.ints.nmiPrev := by
  simp only [Core.boundary]; split <;> (try split) <;> rfl
@[local simp] theorem hj_vf_nmiPending (st : IntState) (k : IntKind) : (st.vectorFetch k).2.nmiPending =
    (st.nmiPending && !(k == .nmi || k.hijackable)) := by
  obtain ⟨a, b, c, d, e, f⟩ := st
  cases k <;> cases b <;> rfl
@[local simp] theorem hj_vf_nmiPrev (st : IntState) (k : IntKind) :
    (st.vectorFetch k).2.nmiPrev = st.nmiPrev := by
  simp only [IntState.vectorFetch]; split <;> rfl

/-- NMI line asserted from 1-based cycle `j` on. -/
def hjNmiFrom (j : Nat) (irq : Nat → Bool) : Nat → IntLines :=
  fun k => { nmi := decide (j ≤ k + 1), irq := irq k, reset := false }

@[local simp] theorem hj_sc_pollNmi (st : IntState) (l : IntLines) (i : Bool) :
    (st.sampleCycle l i false).pollNmi = st.pollNmi := rfl
@[local simp] theorem hj_vf_pollNmi (st : IntState) (k : IntKind) :
    (st.vectorFetch k).2.pollNmi = st.pollNmi := by
  simp only [IntState.vectorFetch]; split <;> rfl

theorem hj_boundary_kind (c : Core) (h : c.ints.pollNmi = false) (hk : c.kind ≠ .nmi) :
    c.boundary.kind ≠ .nmi := by
  simp only [Core.boundary, IntState.atBoundary, h]
  repeat' split
  all_goals simp_all [IntKind.isSeq]

theorem hj_boundary_pollNmi (c : Core) (h : c.ints.pollNmi = false) :
    c.boundary.ints.pollNmi = false := by
  simp only [Core.boundary]
  repeat' split
  all_goals simp_all [IntState.ack]

/-- BRK cycles 1–6 never reach a boundary, whatever the lines. -/
theorem hj_brk_inside (c : Core) (ls : Nat → IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) :
    ∀ k, 1 ≤ k → k < 7 → (runSched k ls c m).1.ms.pos ≠ 0 := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hh hop; subst hpos hint
  intro k h1 h2
  obtain rfl | rfl | rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    omega
  all_goals simp [runSched, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp,
      curOp, complete, MicroState.exec, advance, ctl_uops_00, skips, IntKind.isSeq, hh, hop,
      pushOp]

/-- The common 7-cycle BRK run under an NMI schedule starting at cycle `j`. -/
theorem hj_brk_from (c : Core) (irq : Nat → Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) (hpend : c.ints.nmiPending = false)
    (hprev : c.ints.nmiPrev = false) (hpoll : c.ints.pollNmi = false) (hj : 2 ≤ j) :
    let s := c.ms.cpu
    let m' := entryMem { s with pc := s.pc + 2 } m (s.p ||| 0x30)
    let v : UInt16 := if j ≤ 4 then 0xFFFA else 0xFFFE
    let r := runSched 7 (hjNmiFrom j irq) c m
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read v) (m'.read (v + 1))) ∧
      r.1.ints.nmiPending = decide (5 ≤ j ∧ j ≤ 7) ∧ r.1.ints.nmiPrev = decide (j ≤ 7) ∧
      r.1.ints.pollNmi = false ∧ r.1.kind ≠ .nmi := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hh hop hpend hprev hpoll; subst hpos hint
  have h1 : decide (j ≤ 0 + 1) = false := by simp; omega
  by_cases h4 : j ≤ 4
  · have : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases this with rfl | rfl | rfl <;>
    simp [runSched, hjNmiFrom, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
      complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
      -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
      vf_fst, IntKind.vecNmi, sc_nmiPending, sc_nmiPrev, IntKind.hijackable,
      hh, hop, UInt16.add_assoc, hpend, hprev, hpoll, hj_boundary_kind, hj_boundary_pollNmi]
  · have e1 : decide (j ≤ 1 + 1) = false := by simp; omega
    have e2 : decide (j ≤ 2 + 1) = false := by simp; omega
    have e3 : decide (j ≤ 3 + 1) = false := by simp; omega
    have e4 : (5 ≤ j) := by omega
    simp [runSched, hjNmiFrom, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
      complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
      -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
      vf_fst, IntKind.vecNmi, sc_nmiPending, sc_nmiPrev, IntKind.hijackable, IntKind.vector,
      IntKind.vecIrq, hh, hop, UInt16.add_assoc, hpend, hprev, hpoll, hj_boundary_kind, hj_boundary_pollNmi, h1, e1, e2, e3, h4, e4]
    by_cases a5 : j ≤ 5 <;> by_cases a6 : j ≤ 6 <;> by_cases a7 : j ≤ 7 <;> simp [a5, a6, a7] <;>
      omega

/-- NMI-quiet invariant: the edge latch is clear, the line was asserted last cycle (no new
edge while it stays asserted), no NMI poll latched and no NMI sequence requested. -/
def hjQuiet (c : Core) : Prop :=
  c.ints.nmiPending = false ∧ c.ints.nmiPrev = true ∧ c.ints.pollNmi = false ∧ c.kind ≠ .nmi

theorem hj_boundary_quiet (c : Core) (h : hjQuiet c) : hjQuiet c.boundary := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, ?_, hj_boundary_kind c h3 h4⟩
  simp only [Core.boundary]
  repeat' split
  all_goals simp_all [IntState.ack]

theorem hj_complete_quiet (c : Core) (lines : IntLines) (v : UInt8) (hl : lines.nmi = true)
    (h : hjQuiet c) : hjQuiet (c.complete lines v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ c0 : Core, hjQuiet c0 → ∀ b : Bool, hjQuiet (if b then c0.boundary else c0) := by
    intro c0 hq b; cases b
    · exact hq
    · exact hj_boundary_quiet c0 hq
  simp only [Core.complete]
  apply key
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (try split) <;> simp_all [IntState.sampleCycle]
  all_goals (repeat' split) <;> simp_all

theorem hj_cycle_complete (c : Core) (lines : IntLines) (m : Mem) :
    ∃ v, (c.cycle lines m).1 = c.complete lines v := by
  simp only [Core.cycle]; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- While the NMI line stays asserted (no new edge), a quiet core stays quiet: no NMI sequence
is ever requested, for any number of cycles and any instructions. -/
theorem hj_quiet_run (n : Nat) (ls : Nat → IntLines) (c : Core) (m : Mem)
    (hl : ∀ k, (ls k).nmi = true) (h : hjQuiet c) : hjQuiet (runSched n ls c m).1 := by
  induction n generalizing ls c m with
  | zero => exact h
  | succ n ih =>
    simp only [runSched]
    apply ih _ _ _ (fun k => hl (k + 1))
    obtain ⟨v, hv⟩ := hj_cycle_complete c (ls 0) m
    rw [hv]; exact hj_complete_quiet c _ v (hl 0) h

/-- **T-CPU-7 (hijack mid-BRK, core layer).** A BRK fetched at a boundary with the NMI line
inactive before it and asserted from cycle `j ∈ {2,3,4}` on (the edge is sampled in cycle `j`):
cycles 1–6 stay inside the sequence; after 7 cycles the stack holds `PC + 2` and `P|$30`
(B = 1, bit 5 set), `SP - 3`, I = 1, `PC = mem16[$FFFA]`, the NMI is consumed
(`nmiPending = false`), and — since the line stays asserted (no new edge) — no NMI sequence is
requested at any later cycle (`kind ≠ .nmi` after `7 + n` cycles, for every `n`). -/
theorem T_CPU_7_hijack_mid (c : Core) (irq : Nat → Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) (hpend : c.ints.nmiPending = false)
    (hprev : c.ints.nmiPrev = false) (hpoll : c.ints.pollNmi = false) (hj : 2 ≤ j ∧ j ≤ 4) :
    let s := c.ms.cpu
    let m' := entryMem { s with pc := s.pc + 2 } m (s.p ||| 0x30)
    let ls := hjNmiFrom j irq
    let r := runSched 7 ls c m
    (∀ k, 1 ≤ k → k < 7 → (runSched k ls c m).1.ms.pos ≠ 0) ∧
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read 0xFFFA) (m'.read 0xFFFB)) ∧
      r.1.ints.nmiPending = false ∧
      ∀ n, hjQuiet (runSched (7 + n) ls c m).1 := by
  dsimp only
  have hb := hj_brk_from c irq m j hpos hint hh hop hpend hprev hpoll hj.1
  dsimp only at hb
  have e4 : (if j ≤ 4 then (0xFFFA : UInt16) else 0xFFFE) = 0xFFFA := by simp [hj.2]
  have e5 : decide (5 ≤ j ∧ j ≤ 7) = false := by simp; omega
  have e6 : decide (j ≤ 7) = true := by simp; omega
  rw [e4, e5, e6] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hb
  refine ⟨hj_brk_inside c _ m hpos hint hh hop, h1, h2, h3, h4, fun n => ?_⟩
  rw [runSched_add]
  apply hj_quiet_run
  · intro k; simp only [hjNmiFrom]; simp; omega
  · exact ⟨h4, h5, h6, h7⟩

/-- **T-CPU-7 (NMI too late to hijack).** The same BRK with the NMI edge in cycle `j ≥ 5`
(after the vector was chosen in cycle 5): it fetches `$FFFE`, and for `j ≤ 7` the NMI is still
pending after the 7 cycles (it is taken after the handler's first instruction). -/
theorem T_CPU_7_hijack_late (c : Core) (irq : Nat → Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) (hpend : c.ints.nmiPending = false)
    (hprev : c.ints.nmiPrev = false) (hpoll : c.ints.pollNmi = false) (hj : 5 ≤ j) :
    let s := c.ms.cpu
    let m' := entryMem { s with pc := s.pc + 2 } m (s.p ||| 0x30)
    let r := runSched 7 (hjNmiFrom j irq) c m
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read 0xFFFE) (m'.read 0xFFFF)) ∧
      r.1.ints.nmiPending = decide (j ≤ 7) ∧ r.1.kind ≠ .nmi := by
  dsimp only
  have hb := hj_brk_from c irq m j hpos hint hh hop hpend hprev hpoll (by omega)
  dsimp only at hb
  have e4 : (if j ≤ 4 then (0xFFFA : UInt16) else 0xFFFE) = 0xFFFE := by simp; omega
  have e5 : decide (5 ≤ j ∧ j ≤ 7) = decide (j ≤ 7) := by simp [hj]
  rw [e4, e5] at hb
  obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := hb
  exact ⟨h1, h2, h3, h4, h7⟩

/-! ## IRQ masked, derived from the opcode -/

/-! I-flag preservation (decided over the 256 status bytes; no `bv_decide`). -/

theorem hj_i_eq (s : State) : s.i = (s.p &&& 4 != 0) := rfl

theorem hj_setBit_i (s : State) (m : UInt8) (b : Bool)
    (hm : m = 1 ∨ m = 2 ∨ m = 8 ∨ m = 0x40 ∨ m = 0x80) : (s.setBit m b).i = s.i := by
  rw [hj_i_eq, hj_i_eq]
  simp only [State.setBit]
  generalize s.p = p
  revert p
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

@[local simp] theorem hj_setC_i (s : State) (b : Bool) : (s.setC b).i = s.i :=
  hj_setBit_i s _ b (by simp [Flags.maskC])
@[local simp] theorem hj_setZ_i (s : State) (b : Bool) : (s.setZ b).i = s.i :=
  hj_setBit_i s _ b (by simp [Flags.maskZ])
@[local simp] theorem hj_setD_i (s : State) (b : Bool) : (s.setD b).i = s.i :=
  hj_setBit_i s _ b (by simp [Flags.maskD])
@[local simp] theorem hj_setV_i (s : State) (b : Bool) : (s.setV b).i = s.i :=
  hj_setBit_i s _ b (by simp [Flags.maskV])
@[local simp] theorem hj_setN_i (s : State) (b : Bool) : (s.setN b).i = s.i :=
  hj_setBit_i s _ b (by simp [Flags.maskN])

theorem hj_and80 : ∀ r : UInt8, r &&& 0x80 = 0 ∨ r &&& 0x80 = 0x80 := by decide

@[local simp] theorem hj_setZN_i (s : State) (r : UInt8) : (s.setZN r).i = s.i := by
  rw [hj_i_eq, hj_i_eq]
  simp only [State.setZN]
  generalize s.p = p
  rcases hj_and80 r with h | h <;> rw [h] <;> split <;> revert p <;> decide

@[local simp] theorem hj_setI_i (s : State) (b : Bool) : (s.setI b).i = b := by
  rw [hj_i_eq]
  simp only [State.setI, State.setBit, Flags.maskI]
  generalize s.p = p
  revert p
  cases b <;> decide

@[local simp] theorem hj_i_mk (a x y sp : UInt8) (pc : UInt16) (p : UInt8) (h : Bool) :
    (State.mk a x y sp pc p h).i = (p &&& Flags.maskI != 0) := rfl
@[local simp] theorem hj_i_p (s : State) : (s.p &&& Flags.maskI != 0) = s.i := rfl
@[local simp] theorem hj_ldA_i (s : State) (r : UInt8) : (s.ldA r).i = s.i := by
  simp [State.ldA]
@[local simp] theorem hj_arith_i (s : State) (r : Alu.Res) : (s.arith r).i = s.i := by
  simp [State.arith]
@[local simp] theorem hj_compare_i (s : State) (r : Alu.RC) : (s.compare r).i = s.i := by
  simp [State.compare]

theorem hj_execRead_i (e : Entry) (s : State) (v : UInt8) : (execRead e s v).i = s.i := by
  unfold execRead; split <;> simp

theorem hj_rmwState_i (i : Instr) (s : State) (v : UInt8) : (rmwState i s v).i = s.i := by
  unfold rmwState; split <;> simp

theorem hj_execImp_i (i : Instr) (s : State) (hs : s.i = true) (hc : i ≠ .CLI) :
    (execImp i s).i = true := by
  unfold execImp; split <;> simp_all

/-- Micro-ops that preserve (or set) I for every instruction other than CLI/PLP/RTI. -/
theorem hj_exec_i (ms : MicroState) (u : MicroOp) (v : UInt8) (hu : u ≠ .pullPInc)
    (hs : ms.cpu.i = true) (hc : (decode ms.op).instr ≠ .CLI)
    (hp : (decode ms.op).instr ≠ .PLP) : (ms.exec u v).cpu.i = true := by
  cases u <;> simp only [MicroState.exec] <;> (try split) <;>
    simp_all [hj_execRead_i, hj_rmwState_i, hj_execImp_i]

theorem hj_exec_op (ms : MicroState) (u : MicroOp) (v : UInt8) : (ms.exec u v).op = ms.op := by
  cases u <;> simp only [MicroState.exec] <;> (try split) <;> rfl

/-- `pullPInc` (the RTI P pull) occurs in no other instruction's micro-program. -/
theorem hj_pullP_table : ∀ i : Fin 256,
    ((decodeFin i).instr == .RTI || !(program (decodeFin i)).contains .pullPInc) = true := by
  decide +kernel

theorem hj_curOp_ne_pullP (ms : MicroState) (h : (decode ms.op).instr ≠ .RTI) :
    ms.curOp ≠ .pullPInc := by
  have ht := hj_pullP_table ⟨ms.op.toNat, ms.op.toNat_lt⟩
  rw [← decode_eq_decodeFin] at ht
  have ht' : (program (decode ms.op)).contains .pullPInc = false := by
    revert ht; cases (program (decode ms.op)).contains .pullPInc <;> simp [h]
  clear ht
  intro hc
  rw [MicroState.curOp, uops_eq] at hc
  have hg : ∀ (a : Array MicroOp) (i : Nat) (d : MicroOp),
      a.getD i d = if h : i < a.size then a[i] else d := fun _ _ _ => rfl
  rw [hg] at hc
  split at hc
  · have := Array.contains_eq_true_of_mem (hc ▸ Array.getElem_mem ‹_›)
    rw [ht'] at this; exact absurd this (by decide)
  · exact absurd hc (by decide)

/-- Only `$58`, `$28`, `$40` decode to CLI, PLP, RTI. -/
theorem hj_clr_table : ∀ i : Fin 256,
    (!((decodeFin i).instr == .CLI || (decodeFin i).instr == .PLP ||
        (decodeFin i).instr == .RTI) ||
      (i.val == 0x58 || i.val == 0x28 || i.val == 0x40)) = true := by
  decide +kernel

theorem hj_not_clr (op : UInt8) (h : op ≠ 0x58 ∧ op ≠ 0x28 ∧ op ≠ 0x40) :
    (decode op).instr ≠ .CLI ∧ (decode op).instr ≠ .PLP ∧ (decode op).instr ≠ .RTI := by
  have ht := hj_clr_table ⟨op.toNat, op.toNat_lt⟩
  rw [← decode_eq_decodeFin] at ht
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : (op.toNat == 0x58) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h1 (UInt8.toNat_inj.mp e)
  have e2 : (op.toNat == 0x28) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h2 (UInt8.toNat_inj.mp e)
  have e3 : (op.toNat == 0x40) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h3 (UInt8.toNat_inj.mp e)
  simp only [e1, e2, e3, Bool.or_false] at ht
  revert ht
  generalize (decode op).instr = i
  cases i <;> simp

theorem hj_micro_op (ms : MicroState) (v : UInt8) (h : ms.pos ≠ 0) :
    (ms.complete v).op = ms.op := by
  simp only [MicroState.complete, beq_iff_eq, h, ite_false, MicroState.advance]
  exact hj_exec_op _ _ _

theorem hj_micro_i (ms : MicroState) (v : UInt8) (h : ms.pos ≠ 0) (hs : ms.cpu.i = true)
    (hn : (decode ms.op).instr ≠ .CLI ∧ (decode ms.op).instr ≠ .PLP ∧
      (decode ms.op).instr ≠ .RTI) : (ms.complete v).cpu.i = true := by
  simp only [MicroState.complete, beq_iff_eq, h, ite_false, MicroState.advance]
  exact hj_exec_i _ _ _ (hj_curOp_ne_pullP _ hn.2.2) hs hn.1 hn.2.1

@[local simp] theorem hj_boundary_op (c : Core) : c.boundary.ms.op = c.ms.op := by
  simp only [Core.boundary]; split <;> (try split) <;> rfl

theorem hj_complete_op (c : Core) (l : IntLines) (v : UInt8) :
    (c.complete l v).ms.op = (c.ms.complete v).op := by
  simp only [Core.complete]
  split <;> (try split) <;> simp <;> split <;> simp

/-- IRQ-masked invariant inside an instruction with opcode `op`. -/
def hjMasked (op : UInt8) (c : Core) : Prop :=
  c.ms.op = op ∧ c.ms.cpu.i = true ∧ c.iBefore = true ∧ c.ints.pollIrq = false ∧ c.kind ≠ .irq

/-- The opcode-fetch cycle ignores the stale `iBefore`/`kind`. -/
theorem hj_fetch_eq (c : Core) (l : IntLines) (v : UInt8) (hpos : c.ms.pos = 0)
    (hint : c.ms.intPending = false) :
    c.complete l v = ({ c with iBefore := true, kind := .none } : Core).complete l v := by
  obtain ⟨ms, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint
  simp [Core.complete, hpos, hint]

theorem hj_fetch_masked (c : Core) (l : IntLines) (m : Mem) (hpos : c.ms.pos = 0)
    (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false) (hI : c.ms.cpu.i = true)
    (hp : c.ints.pollIrq = false) :
    hjMasked (m.read c.ms.cpu.pc) (c.cycle l m).1 := by
  have hb : (c.cycle l m).1 = c.complete l (m.read c.ms.cpu.pc) := by
    simp [Core.cycle, Core.busOp, MicroState.busOp, hpos, hint, hh]
  rw [hb]
  have hI1 : (c.ms.complete (m.read c.ms.cpu.pc)).cpu.i = true := by
    simpa [MicroState.complete, hpos, hint, hh] using hI
  have hop1 : (c.ms.complete (m.read c.ms.cpu.pc)).op = m.read c.ms.cpu.pc := by
    simp [MicroState.complete, hpos, hint, hh]
  have h := T_CPU_7_irq_masked_core { c with iBefore := true, kind := .none } l
    (m.read c.ms.cpu.pc) hp hI rfl hI1 (by simp)
  simp only at h
  rw [hj_fetch_eq c l _ hpos hint]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, h2, h3, h1, h4⟩
  rw [hj_complete_op, hop1]

theorem hj_step_masked (op : UInt8) (c : Core) (l : IntLines) (m : Mem)
    (hn : (decode op).instr ≠ .CLI ∧ (decode op).instr ≠ .PLP ∧ (decode op).instr ≠ .RTI)
    (h : hjMasked op c) (hpos : c.ms.pos ≠ 0) : hjMasked op (c.cycle l m).1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  obtain ⟨v, hv⟩ := hj_cycle_complete c l m
  rw [hv]
  have hI1 := hj_micro_i c.ms v hpos h1 (h0 ▸ hn)
  have h := T_CPU_7_irq_masked_core c l v h3 h1 h2 hI1 h4
  simp only at h
  obtain ⟨g1, g2, g3, g4⟩ := h
  exact ⟨by rw [hj_complete_op, hj_micro_op _ _ hpos, h0], g2, g3, g1, g4⟩

/-- **T-CPU-7 (IRQ masked, derived from the opcode).** From a boundary that fetches an opcode
(no interrupt sequence pending, not halted) with I = 1 and the IRQ poll latch clear, if the
opcode is not CLI (`$58`), PLP (`$28`) or RTI (`$40`), then for *any* line schedule (IRQ, NMI
and RESET arbitrary) every cycle of the instruction — up to and including the cycle that reaches
the next boundary — keeps I = 1 and the IRQ poll latch clear, and no IRQ sequence is requested
(`kind ≠ .irq`). SEI keeps I = 1; BRK sets it; nothing else touches it. -/
theorem T_CPU_7_irq_masked_opcode (c : Core) (ls : Nat → IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hI : c.ms.cpu.i = true) (hp : c.ints.pollIrq = false)
    (hop : m.read c.ms.cpu.pc ≠ 0x58 ∧ m.read c.ms.cpu.pc ≠ 0x28 ∧ m.read c.ms.cpu.pc ≠ 0x40)
    (n : Nat) (hn : 1 ≤ n) (hin : ∀ k, 1 ≤ k → k < n → (runSched k ls c m).1.ms.pos ≠ 0) :
    (runSched n ls c m).1.ints.pollIrq = false ∧ (runSched n ls c m).1.kind ≠ .irq ∧
      (runSched n ls c m).1.ms.cpu.i = true := by
  have hcl := hj_not_clr _ hop
  suffices H : ∀ n, 1 ≤ n → (∀ k, 1 ≤ k → k < n → (runSched k ls c m).1.ms.pos ≠ 0) →
      hjMasked (m.read c.ms.cpu.pc) (runSched n ls c m).1 by
    obtain ⟨-, h1, -, h3, h4⟩ := H n hn hin
    exact ⟨h3, h4, h1⟩
  intro n hn hin
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos'
    · exact hj_fetch_masked c (ls 0) m hpos hint hh hI hp
    · have hm := ih hpos' (fun k h1 h2 => hin k h1 (by omega))
      rw [runSched_add]
      exact hj_step_masked _ _ _ _ hcl hm (hin n hpos' (by omega))

end Nes.Cpu.Proofs
