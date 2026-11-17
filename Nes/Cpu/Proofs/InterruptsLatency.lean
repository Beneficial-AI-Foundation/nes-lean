import Nes.Cpu.Proofs.Interrupts

/-!
# `Nes.Cpu.Proofs.InterruptsLatency` — T-CPU-7: NMI latency end to end over `Core`

## Spec

* `T_CPU_7_nmi_taken`: from a core at an instruction boundary that fetches an ordinary opcode
  (not BRK, not JAM; not halted), with an NMI edge latched or arriving in the fetch cycle, no
  RESET, lines constant: after the instruction (`2 ≤ k ≤ maxCycles = 8` cycles) the core is at
  the next boundary with the NMI sequence requested (`kind = nmi`, `intPending`, vector
  `$FFFA`, pushes not suppressed).
* `T_CPU_7_nmi_latency`: under the same hypotheses (BRK allowed: it is hijacked), within
  `n ≤ maxCycles + 7 = 15` cycles the core is at a boundary with I set and `PC = mem16[$FFFA]`.

The bound is measured from the start of the instruction during whose first cycle the edge is
sampled (or with the edge already latched). An edge arriving later inside an instruction adds
that instruction's remaining cycles (it may be polled only by the next instruction: after the
poll of a non-branch instruction, or in cycles 2–3 of a non-crossing taken branch); that
composition is not proved here.

## Method

The core follows `MicroState.complete` exactly while an ordinary instruction runs
(`lat_core_mid`: `kind = none`, no vector override, `boundary` only at `pos = 0`). Positions
are tracked in an abstract model (`latAdv`/`latCnt`/`latJ`: position, `crossed`, branch
condition, cycles so far) related to the micro-machine by `lat_micro_step`; four facts over
all 256 opcodes (`decide +kernel`) give: the model's invariant is inductive, the position
strictly increases, every program has at most 7 micro-ops, and for every non-branch opcode
the cycle before the last one is `isPollCycle` (branches always poll in cycle 1). `LatInv`
carries this plus "NMI pending, no RESET, the poll latched NMI if it already happened" through
`Core.runCycles` (`lat_mid_step`, `lat_run`).
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs
open Nes Nes.Cpu IntState MicroState Refinement

/-! ## Abstract position model -/

/-- `MicroState.skips` as a function of the decoded entry, `crossed` and the branch condition. -/
def latSkip (e : Entry) (cr cond : Bool) : MicroOp → Bool
  | .indexFixup => e.pageCross && !cr
  | .branchTaken => !cond
  | .branchFixup => !(cond && cr)
  | _ => false

/-- Micro-ops that (may) change `crossed`. -/
def latSets : MicroOp → Bool
  | .fetchHiX | .fetchHiY | .ptrHiY | .branchFetch => true
  | _ => false

/-- Micro-ops of a branch program (plus the `getD` default), which leave `P` unchanged. -/
def latBrOp : MicroOp → Bool
  | .branchFetch | .branchTaken | .branchFixup | .jamHalt => true
  | _ => false

/-- `MicroState.advance`'s new position (as `Nat`, `0` = end). -/
def latAdv (prog : MicroProgram) (e : Entry) (p : Nat) (cr cond : Bool) : Nat :=
  let n := prog.size
  let i := if p < n && latSkip e cr cond (prog.getD p .jamHalt) then p + 1 else p
  let i := if i < n && latSkip e cr cond (prog.getD i .jamHalt) then i + 1 else i
  if i < n then i + 1 else 0

/-- Cycles completed when the next micro-op is `prog[p-1]`: the opcode fetch plus the
non-skipped micro-ops before it. -/
def latCnt (prog : MicroProgram) (e : Entry) (p : Nat) (cr cond : Bool) : Nat :=
  1 + ((prog.toList.take (p - 1)).filter (fun u => !latSkip e cr cond u)).length

/-- Reachable abstract positions: in range, not on a skipped micro-op, `crossed` only after a
setter. -/
def latJ (prog : MicroProgram) (e : Entry) (p : Nat) (cr cond : Bool) : Bool :=
  1 ≤ p && p ≤ prog.size && !latSkip e cr cond (prog.getD (p - 1) .jamHalt) &&
    (!cr || (prog.toList.take (p - 1)).any latSets)

/-! ## Table facts (all 256 opcodes) -/

theorem lat_init_table : ∀ i : Fin 256, ∀ cond : Bool,
    latJ (program (decodeFin i)) (decodeFin i) 1 false cond = true ∧
      (program (decodeFin i)).size ≤ 7 := by
  decide +kernel

theorem lat_step_table : ∀ i : Fin 256, ∀ p : Fin 9, ∀ cr b cond cond' : Bool,
    let e := decodeFin i
    let prog := program e
    latJ prog e p cr cond = true → (e.instr.isBranch = true → cond' = cond) →
    let cr' := if latSets (prog.getD (p - 1) .jamHalt) then b else cr
    let p' := latAdv prog e p cr' cond'
    p' ≠ 0 → latJ prog e p' cr' cond' = true ∧
      latCnt prog e p' cr' cond' = latCnt prog e p cr cond + 1 ∧ p.val < p' := by
  decide +kernel

theorem lat_poll_table : ∀ i : Fin 256, ∀ p : Fin 9, ∀ cr b cond cond' : Bool,
    let e := decodeFin i
    let prog := program e
    latJ prog e p cr cond = true → e.instr.isBranch = false →
    let cr' := if latSets (prog.getD (p - 1) .jamHalt) then b else cr
    latAdv prog e p cr' cond' = 0 →
    isPollCycle (latCnt prog e p cr cond).toUInt8
      (e.cycles + (if e.pageCross && cr then 1 else 0)) = true := by
  decide +kernel

theorem lat_prog_table : ∀ i : Fin 256,
    (classify (decodeFin i) ≠ .jam → (program (decodeFin i)).all (· != .jamHalt) = true) ∧
    ((decodeFin i).instr.isBranch = true → (program (decodeFin i)).all latBrOp = true) := by
  decide +kernel

/-! ## Micro layer: one cycle in the abstract model -/

theorem lat_skips (ms : MicroState) (u : MicroOp) :
    ms.skips u = latSkip (decode ms.op) ms.crossed (branchCond ms.cpu (decode ms.op).instr) u := by
  cases u <;> rfl

theorem lat_ite_toUInt8 (c : Prop) [Decidable c] (k : Nat) :
    (if c then k.toUInt8 else 0) = (if c then k else 0).toUInt8 := by
  split <;> rfl

theorem lat_advance_pos (ms : MicroState) :
    ms.advance.pos = (latAdv (uops ms.op) (decode ms.op) ms.pos.toNat ms.crossed
      (branchCond ms.cpu (decode ms.op).instr)).toUInt8 := by
  unfold MicroState.advance latAdv
  simp only [lat_skips]
  exact lat_ite_toUInt8 _ _

theorem lat_advance (ms : MicroState) : ms.advance = { ms with pos := ms.advance.pos } := by
  unfold MicroState.advance
  generalize uops ms.op = prog
  simp

theorem lat_exec_crossed (ms : MicroState) (u : MicroOp) (v : UInt8) (h : latSets u = false) :
    (ms.exec u v).crossed = ms.crossed := by
  cases u <;> simp_all [latSets, MicroState.exec] <;> split <;> rfl

theorem lat_execRead_halted (e : Entry) (s : State) (v : UInt8) :
    (execRead e s v).halted = s.halted := by
  unfold execRead
  split <;> simp [State.ldA, State.setZN, State.arith, State.compare, State.setC, State.setV,
    State.setZ, State.setN, State.setBit]

theorem lat_execImp_halted (i : Instr) (s : State) :
    (execImp i s).halted = s.halted := by
  unfold execImp
  split <;> simp [State.ldA, State.setZN, State.arith, State.compare, State.setC, State.setV,
    State.setZ, State.setN, State.setBit, State.setI, State.setD]

theorem lat_rmwState_halted (i : Instr) (s : State) (v : UInt8) :
    (rmwState i s v).halted = s.halted := by
  unfold rmwState
  split <;> simp [State.ldA, State.setZN, State.arith, State.compare, State.setC, State.setV,
    State.setZ, State.setN, State.setBit]

theorem lat_exec_halted (ms : MicroState) (u : MicroOp) (v : UInt8) (h : u ≠ .jamHalt) :
    (ms.exec u v).cpu.halted = ms.cpu.halted := by
  cases u <;> simp_all [MicroState.exec, lat_execRead_halted, lat_execImp_halted,
    lat_rmwState_halted] <;> (try split) <;>
    simp_all [State.ldA, State.setZN, State.setI, State.setBit]

theorem lat_exec_p (ms : MicroState) (u : MicroOp) (v : UInt8) (h : latBrOp u = true) :
    (ms.exec u v).cpu.p = ms.cpu.p := by
  cases u <;> simp_all [latBrOp, MicroState.exec]

theorem lat_branchCond (s t : State) (i : Instr) (h : s.p = t.p) :
    branchCond s i = branchCond t i := by
  cases i <;> simp [branchCond, State.n, State.v, State.c, State.z, State.getBit, h]

theorem lat_complete_mid (ms : MicroState) (v : UInt8) (h : ms.pos ≠ 0) :
    ms.complete v = (ms.exec ms.curOp v).advance := by
  simp [MicroState.complete, h]

/-! ## Table facts at a concrete opcode -/

theorem lat_size (op : UInt8) : (uops op).size ≤ 7 := by
  rw [uops_eq]; exact (lat_init_table ⟨op.toNat, op.toNat_lt⟩ false).2

theorem lat_init (op : UInt8) (cond : Bool) : latJ (uops op) (decode op) 1 false cond = true := by
  rw [uops_eq]; exact (lat_init_table ⟨op.toNat, op.toNat_lt⟩ cond).1

theorem lat_nojam (op : UInt8) (h : classify (decode op) ≠ .jam) :
    (uops op).all (· != .jamHalt) = true := by
  rw [uops_eq]; exact (lat_prog_table ⟨op.toNat, op.toNat_lt⟩).1 h

theorem lat_brops (op : UInt8) (h : (decode op).instr.isBranch = true) :
    (uops op).all latBrOp = true := by
  rw [uops_eq]; exact (lat_prog_table ⟨op.toNat, op.toNat_lt⟩).2 h

theorem lat_step (op : UInt8) (p : Nat) (hp : p < 9) (cr b cond cond' : Bool)
    (hJ : latJ (uops op) (decode op) p cr cond = true)
    (hb : (decode op).instr.isBranch = true → cond' = cond)
    (hz : latAdv (uops op) (decode op) p
      (if latSets ((uops op).getD (p - 1) .jamHalt) then b else cr) cond' ≠ 0) :
    let cr' := if latSets ((uops op).getD (p - 1) .jamHalt) then b else cr
    let p' := latAdv (uops op) (decode op) p cr' cond'
    latJ (uops op) (decode op) p' cr' cond' = true ∧
      latCnt (uops op) (decode op) p' cr' cond' = latCnt (uops op) (decode op) p cr cond + 1 ∧
      p < p' := by
  simp only [uops_eq] at *
  exact lat_step_table ⟨op.toNat, op.toNat_lt⟩ ⟨p, hp⟩ cr b cond cond' hJ hb hz

theorem lat_poll (op : UInt8) (p : Nat) (hp : p < 9) (cr b cond cond' : Bool)
    (hJ : latJ (uops op) (decode op) p cr cond = true)
    (hb : (decode op).instr.isBranch = false)
    (hz : latAdv (uops op) (decode op) p
      (if latSets ((uops op).getD (p - 1) .jamHalt) then b else cr) cond' = 0) :
    isPollCycle (latCnt (uops op) (decode op) p cr cond).toUInt8
      ((decode op).cycles + (if (decode op).pageCross && cr then 1 else 0)) = true := by
  simp only [uops_eq] at *
  exact lat_poll_table ⟨op.toNat, op.toNat_lt⟩ ⟨p, hp⟩ cr b cond cond' hJ hb hz

theorem lat_J_le (prog : MicroProgram) (e : Entry) (p : Nat) (cr cond : Bool)
    (h : latJ prog e p cr cond = true) : 1 ≤ p ∧ p ≤ prog.size := by
  simp only [latJ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem lat_getD_mem {α} (a : Array α) (i : Nat) (d : α) (P : α → Bool) (h : a.all P = true)
    (hd : P d = true) : P (a.getD i d) = true := by
  rw [Array.all_eq_true] at h
  simp only [Array.getD_eq_getD_getElem?]
  by_cases hi : i < a.size
  · simp [hi, h i hi]
  · simp [hi, hd]

/-! ## Core layer -/

theorem lat_core_mid (c : Core) (lines : IntLines) (v : UInt8) (hp : c.ms.pos ≠ 0)
    (hk : c.kind = .none) :
    c.complete lines v =
      let ms' := c.ms.complete v
      let c' : Core := ⟨ms',
        c.ints.sampleCycle lines (pollIFlag (decode ms'.op).instr c.iBefore ms'.cpu.i)
          (Core.pollAt ms' (c.cyc + 1)), c.cyc + 1, .none, c.iBefore⟩
      if ms'.pos = 0 then c'.boundary else c' := by
  have hb : (c.ms.pos == 0) = false := by simpa using hp
  simp [Core.complete, hb, hk, IntKind.isSeq]

theorem lat_boundary_nmi (c : Core) (hr : c.ints.resetPending = false)
    (hn : c.ints.pollNmi = true) (hh : c.ms.cpu.halted = false) :
    c.boundary = ⟨c.ms.requestInterrupt 0xFFFA false, c.ints.ack, c.cyc, .nmi, c.iBefore⟩ := by
  simp [Core.boundary, IntState.atBoundary, hr, hn, hh, IntKind.isSeq, IntKind.vector,
    IntKind.vecNmi, IntKind.suppressWrites]

theorem lat_getD_in {α} (a : Array α) (i : Nat) (d : α) (P : α → Bool) (h : a.all P = true)
    (hi : i < a.size) : P (a.getD i d) = true := by
  rw [Array.all_eq_true] at h
  simp only [Array.getD_eq_getD_getElem?]
  simp [hi, h i hi]

/-- One mid-instruction cycle of the micro-machine, in the abstract model. -/
theorem lat_micro_step (ms : MicroState) (v : UInt8) (hp : ms.pos ≠ 0)
    (hnj : classify (decode ms.op) ≠ .jam)
    (hJ : latJ (uops ms.op) (decode ms.op) ms.pos.toNat ms.crossed
      (branchCond ms.cpu (decode ms.op).instr) = true) :
    let ms' := ms.complete v
    ms'.op = ms.op ∧ ms'.cpu.halted = ms.cpu.halted ∧
    ((decode ms.op).instr.isBranch = true →
      branchCond ms'.cpu (decode ms.op).instr = branchCond ms.cpu (decode ms.op).instr) ∧
    (if latSets ((uops ms.op).getD (ms.pos.toNat - 1) .jamHalt) then ms'.crossed
      else ms.crossed) = ms'.crossed ∧
    ms'.pos = (latAdv (uops ms.op) (decode ms.op) ms.pos.toNat ms'.crossed
      (branchCond ms'.cpu (decode ms.op).instr)).toUInt8 := by
  have hr := lat_J_le _ _ _ _ _ hJ
  have hi : ms.pos.toNat - 1 < (uops ms.op).size := by omega
  have hu : ms.curOp = (uops ms.op).getD (ms.pos.toNat - 1) .jamHalt := rfl
  rw [lat_complete_mid _ _ hp]
  generalize hU : ms.curOp = u
  rw [hU] at hu
  have hop : (ms.exec u v).op = ms.op := exec_op _ _ _
  have hpos : (ms.exec u v).pos = ms.pos := exec_pos _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lat_advance]; exact hop
  · rw [lat_advance]; dsimp only
    refine lat_exec_halted ms u v ?_
    have := lat_getD_in _ _ MicroOp.jamHalt _ (lat_nojam _ hnj) hi
    rw [← hu] at this
    simpa using this
  · intro hb
    rw [lat_advance]; dsimp only
    refine lat_branchCond _ _ _ (lat_exec_p ms u v ?_)
    have := lat_getD_in _ _ MicroOp.jamHalt _ (lat_brops _ hb) hi
    rw [← hu] at this
    exact this
  · rw [← hu, lat_advance]
    cases hs : latSets u
    · simp [lat_exec_crossed _ _ _ hs]
    · simp
  · rw [lat_advance_pos, hop, hpos, lat_advance]

/-- Invariant of a core in the middle of an ordinary (non-JAM) instruction, with an NMI edge
latched and no RESET pending. -/
structure LatInv (c : Core) : Prop where
  kind : c.kind = .none
  halted : c.ms.cpu.halted = false
  nojam : classify (decode c.ms.op) ≠ .jam
  j : latJ (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) = true
  cnt : c.cyc = (latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr)).toUInt8
  le : latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) ≤ c.ms.pos.toNat
  pend : c.ints.nmiPending = true
  rst : c.ints.resetPending = false
  poll : Core.pollAt c.ms c.cyc = true → c.ints.pollNmi = true
  br : (decode c.ms.op).instr.isBranch = true → c.ints.pollNmi = true

theorem lat_toUInt8_succ (n : Nat) : (n + 1).toUInt8 = n.toUInt8 + 1 := by
  apply UInt8.toNat_inj.mp; simp [UInt8.toNat_add]

theorem lat_toNat_toUInt8 (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp; omega

/-- One cycle of a core satisfying `LatInv`: either the instruction goes on (invariant kept,
position advanced), or it ends and the core is at a boundary with the NMI sequence requested. -/
theorem lat_mid_step (c : Core) (lines : IntLines) (v : UInt8) (hr : lines.reset = false)
    (h : LatInv c) :
    (LatInv (c.complete lines v) ∧ c.ms.pos.toNat < (c.complete lines v).ms.pos.toNat ∧
      (c.complete lines v).cyc.toNat = c.cyc.toNat + 1) ∨
    ((c.complete lines v).ms.pos = 0 ∧ (c.complete lines v).ms.intPending = true ∧
      (c.complete lines v).ms.suppressWrites = false ∧ (c.complete lines v).kind = .nmi ∧
      c.cyc.toNat + 1 ≤ 8) := by
  obtain ⟨hk, hh, hnj, hJ, hcnt, hle, hpend, hrst, hpoll, hbr⟩ := h
  have hr1 := lat_J_le _ _ _ _ _ hJ
  have hsz := lat_size c.ms.op
  have hp0 : c.ms.pos ≠ 0 := by
    intro h0; rw [h0] at hr1; simp at hr1
  have hcyc : c.cyc.toNat = latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
      (branchCond c.ms.cpu (decode c.ms.op).instr) := by
    rw [hcnt, lat_toNat_toUInt8]; omega
  obtain ⟨hop, hhalt, hcond, hcr, hpos'⟩ := lat_micro_step c.ms v hp0 hnj hJ
  rw [lat_core_mid c lines v hp0 hk]
  generalize hM : c.ms.complete v = ms' at hop hhalt hcond hcr hpos'
  have key := lat_step c.ms.op c.ms.pos.toNat (by omega) c.ms.crossed ms'.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) (branchCond ms'.cpu (decode c.ms.op).instr)
    hJ hcond
  rw [hcr] at key
  by_cases hz : latAdv (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat ms'.crossed
      (branchCond ms'.cpu (decode c.ms.op).instr) = 0
  · -- last cycle
    have hpz : ms'.pos = 0 := by rw [hpos', hz]; rfl
    have hpn : c.ints.pollNmi = true := by
      cases hb : (decode c.ms.op).instr.isBranch
      · apply hpoll
        have hp := lat_poll c.ms.op c.ms.pos.toNat (by omega) c.ms.crossed ms'.crossed
          (branchCond c.ms.cpu (decode c.ms.op).instr) (branchCond ms'.cpu (decode c.ms.op).instr)
          hJ hb (by rw [hcr]; exact hz)
        simp only [Core.pollAt, hb, Bool.false_eq_true, ite_false]
        rw [hcnt]; exact hp
      · exact hbr hb
    right
    simp only [hpz, ite_true]
    rw [lat_boundary_nmi _ (by simp [IntState.sampleCycle, hrst, hr])
      (by simp [IntState.sampleCycle, hpn, hpend]) (by simpa [hhalt] using hh)]
    refine ⟨by simp [MicroState.requestInterrupt, hpz], rfl, rfl, rfl, ?_⟩
    rw [hcyc]; omega
  · -- the instruction goes on
    obtain ⟨hJ', hcnt', hlt⟩ := key hz
    have hr2 := lat_J_le _ _ _ _ _ hJ'
    have hpn : ms'.pos.toNat = latAdv (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat ms'.crossed
        (branchCond ms'.cpu (decode c.ms.op).instr) := by
      rw [hpos', lat_toNat_toUInt8]; omega
    have hpnz : ms'.pos ≠ 0 := by
      intro h0; rw [h0] at hpn; simp at hpn; omega
    left
    simp only [hpnz, ite_false]
    refine ⟨⟨rfl, by simpa [hhalt] using hh, by rw [hop]; exact hnj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_, ?_⟩
    · rw [hop, hpn]; exact hJ'
    · rw [hop, hpn, hcnt', lat_toUInt8_succ, hcnt]
    · rw [hop, hpn, hcnt']; omega
    · simp [IntState.sampleCycle, hpend]
    · simp [IntState.sampleCycle, hrst, hr]
    · intro hp; simp [IntState.sampleCycle, hp, hpend]
    · intro hb; rw [hop] at hb
      simp only [IntState.sampleCycle, hbr hb]; split <;> simp [hpend]
    · omega
    · show (c.cyc + 1).toNat = _
      rw [UInt8.toNat_add]; simp only [UInt8.reduceToNat]; omega

/-- The machine after the opcode-fetch cycle of an ordinary instruction (`MicroState.complete`
at a boundary with no pending interrupt). -/
def latFetched (ms : MicroState) (v : UInt8) : MicroState :=
  { ms with op := v, pos := 1, inInt := false, suppressWrites := false, vec := 0xFFFE,
            crossed := false, cpu := { ms.cpu with pc := ms.cpu.pc + 1 } }

/-- The opcode-fetch cycle of an ordinary instruction (not BRK, not JAM) with an NMI edge
latched (or arriving in this cycle) establishes `LatInv`, with `cyc = 1`. -/
theorem lat_fetch (c : Core) (lines : IntLines) (v : UInt8) (hpos : c.ms.pos = 0)
    (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false) (hv : v ≠ 0)
    (hjam : classify (decode v) ≠ .jam) (hrst : c.ints.resetPending = false)
    (hr : lines.reset = false)
    (hn : c.ints.nmiPending = true ∨ (c.ints.nmiPrev = false ∧ lines.nmi = true)) :
    LatInv (c.complete lines v) ∧ (c.complete lines v).cyc = 1 := by
  have hpd : (c.ints.nmiPending || (!c.ints.nmiPrev && lines.nmi)) = true := by
    rcases hn with h | ⟨h1, h2⟩ <;> simp [*]
  have hv' : (v == 0) = false := by simpa using hv
  have heq : c.complete lines v =
      let ms1 := latFetched c.ms v
      ⟨ms1, c.ints.sampleCycle lines (pollIFlag (decode v).instr c.ms.cpu.i ms1.cpu.i)
        (Core.pollAt ms1 1), 1, .none, c.ms.cpu.i⟩ := by
    simp [Core.complete, hpos, hint, hh, MicroState.complete, hv', IntKind.isSeq, latFetched]
  rw [heq]
  refine ⟨⟨rfl, hh, hjam, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · exact lat_init v _
  · simp [latCnt, latFetched]
  · simp [latCnt, latFetched]
  · simpa [IntState.sampleCycle] using hpd
  · simp [IntState.sampleCycle, hrst, hr]
  · intro hp; simp only [IntState.sampleCycle, hp, ite_true]; exact hpd
  · intro hb
    simp only [latFetched] at hb
    have hp : Core.pollAt (latFetched c.ms v) 1 = true := by
      simp [Core.pollAt, hb, branchPollCycle, latFetched]
    simp only [IntState.sampleCycle, hp, ite_true]; exact hpd

theorem lat_runCycles_succ (n : Nat) (c : Core) (lines : IntLines) (m : Mem) :
    Core.runCycles (n + 1) c lines m =
      Core.runCycles n (c.cycle lines m).1 lines (c.cycle lines m).2 := rfl

theorem lat_runCycles_add (a b : Nat) (c : Core) (lines : IntLines) (m : Mem) :
    Core.runCycles (a + b) c lines m =
      Core.runCycles b (Core.runCycles a c lines m).1 lines (Core.runCycles a c lines m).2 := by
  induction a generalizing c m with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, lat_runCycles_succ, ih, lat_runCycles_succ]

/-- From a core satisfying `LatInv`, the instruction ends within the remaining cycles (total
at most 8) at a boundary with the NMI sequence requested. -/
theorem lat_run (k : Nat) : ∀ (c : Core) (lines : IntLines) (m : Mem), lines.reset = false →
    LatInv c → 8 ≤ k + c.ms.pos.toNat →
    ∃ n, 1 ≤ n ∧ c.cyc.toNat + n ≤ 8 ∧
      (Core.runCycles n c lines m).1.ms.pos = 0 ∧
      (Core.runCycles n c lines m).1.ms.intPending = true ∧
      (Core.runCycles n c lines m).1.ms.suppressWrites = false ∧
      (Core.runCycles n c lines m).1.kind = .nmi := by
  induction k with
  | zero =>
    intro c lines m _ h hk
    have := lat_J_le _ _ _ _ _ h.j; have := lat_size c.ms.op; omega
  | succ k ih =>
    intro c lines m hr h hk
    obtain ⟨v, hv⟩ := cycle_complete c lines m
    rcases lat_mid_step c lines v hr h with ⟨h', hlt, hcy⟩ | ⟨h1, h2, h3, h4, h5⟩
    · obtain ⟨n, hn1, hn2, hn3⟩ := ih (c.complete lines v) lines (c.cycle lines m).2 hr h'
        (by omega)
      refine ⟨n + 1, by omega, by omega, ?_⟩
      rw [lat_runCycles_succ, hv]; exact hn3
    · refine ⟨1, Nat.le_refl _, h5, ?_⟩
      rw [lat_runCycles_succ, hv]; exact ⟨h1, h2, h3, h4⟩

theorem lat_cycle_fetch (c : Core) (lines : IntLines) (m : Mem) (hpos : c.ms.pos = 0)
    (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false) :
    c.cycle lines m = (c.complete lines (m.read c.ms.cpu.pc), m) := by
  simp [Core.cycle, Core.busOp, MicroState.busOp, hpos, hint, hh]

/-! ## T-CPU-7: NMI latency over `Core` -/

/-- **T-CPU-7 (NMI taken after the current instruction).** From an instruction boundary of the
core where the next opcode is fetched (no sequence requested, not halted), executing an
ordinary instruction (not BRK = `$00`, not JAM), with an NMI edge already latched or arriving in
the opcode-fetch cycle, no RESET, and lines held constant: the instruction polls (every
instruction has a poll cycle before its last cycle; branches poll in cycle 1), so after its
`k ∈ [2, 8]` cycles the core is at the next boundary with the NMI sequence requested
(`kind = nmi`, vector `$FFFA`, pushes not suppressed). -/
theorem T_CPU_7_nmi_taken (c : Core) (lines : IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hbrk : m.read c.ms.cpu.pc ≠ 0) (hjam : classify (decode (m.read c.ms.cpu.pc)) ≠ .jam)
    (hrst : c.ints.resetPending = false) (hr : lines.reset = false)
    (hn : c.ints.nmiPending = true ∨ (c.ints.nmiPrev = false ∧ lines.nmi = true)) :
    ∃ k, 2 ≤ k ∧ k ≤ maxCycles ∧
      (Core.runCycles k c lines m).1.ms.pos = 0 ∧
      (Core.runCycles k c lines m).1.ms.intPending = true ∧
      (Core.runCycles k c lines m).1.ms.suppressWrites = false ∧
      (Core.runCycles k c lines m).1.kind = .nmi := by
  obtain ⟨hI, hc1⟩ := lat_fetch c lines _ hpos hint hh hbrk hjam hrst hr hn
  obtain ⟨n, hn1, hn2, hres⟩ := lat_run 8 _ lines m hr hI (by omega)
  rw [hc1] at hn2
  simp only [UInt8.reduceToNat] at hn2
  refine ⟨n + 1, by omega, by simp only [maxCycles]; omega, ?_⟩
  rw [lat_runCycles_succ, lat_cycle_fetch c lines m hpos hint hh]
  exact hres

/-- **T-CPU-7 (NMI latency, end to end over `Core`).** From an instruction boundary of the
core (next opcode fetched, not halted, not a JAM opcode), with an NMI edge already latched or
arriving in the first cycle, no RESET pending or asserted, and the lines held constant: within
`n ≤ maxCycles + 7 = 15` cycles the core is at a boundary with I set and
`PC = mem16[$FFFA]` (read from the memory as it stands, after the entry's pushes). Ordinary
instructions: the NMI is taken after the instruction (`T_CPU_7_nmi_taken`) and entered in 7
cycles (`T_CPU_7_entry`); BRK is hijacked (`T_CPU_7_hijack`, 7 cycles). -/
theorem T_CPU_7_nmi_latency (c : Core) (lines : IntLines) (m : Mem)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hjam : classify (decode (m.read c.ms.cpu.pc)) ≠ .jam)
    (hrst : c.ints.resetPending = false) (hr : lines.reset = false)
    (hn : c.ints.nmiPending = true ∨ (c.ints.nmiPrev = false ∧ lines.nmi = true)) :
    ∃ n, 7 ≤ n ∧ n ≤ maxCycles + 7 ∧
      (Core.runCycles n c lines m).1.ms.pos = 0 ∧
      (Core.runCycles n c lines m).1.ms.cpu.i = true ∧
      (Core.runCycles n c lines m).1.ms.cpu.pc =
        UInt16.ofLoHi ((Core.runCycles n c lines m).2.read 0xFFFA)
          ((Core.runCycles n c lines m).2.read 0xFFFB) := by
  by_cases hb : m.read c.ms.cpu.pc = 0
  · have := T_CPU_7_hijack c lines m hpos hint hh hb hn
    simp only at this
    obtain ⟨-, hm, hp, hcpu⟩ := this
    refine ⟨7, Nat.le_refl _, by simp only [maxCycles]; omega, hp, ?_, ?_⟩
    · rw [hcpu]; exact (T_CPU_7_B_only_pushed _ _).2.1
    · rw [hcpu, hm]; rfl
  · obtain ⟨k, -, hk8, h1, h2, h3, h4⟩ :=
      T_CPU_7_nmi_taken c lines m hpos hint hh hb hjam hrst hr hn
    have := T_CPU_7_entry (Core.runCycles k c lines m).1 lines (Core.runCycles k c lines m).2
      .nmi (Or.inl rfl) h1 h2 h3 h4
    simp only [entryVector_nmi] at this
    obtain ⟨-, hm, hp, hcpu⟩ := this
    refine ⟨k + 7, by omega, by omega, ?_⟩
    rw [lat_runCycles_add]
    refine ⟨hp, ?_, ?_⟩
    · rw [hcpu]; exact (T_CPU_7_B_only_pushed _ _).2.1
    · rw [hcpu, hm]; rfl

end Nes.Cpu.Proofs
