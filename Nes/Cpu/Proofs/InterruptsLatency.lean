import Nes.Cpu.Proofs.Interrupts
import Nes.Cpu.Proofs.InterruptsHijack

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


Edge arriving mid-instruction (the plan's literal "`maxInstrCycles + 7` from the edge" is false:
an edge after the poll — e.g. in cycle 2 of a non-crossing taken branch — waits for the next
instruction; the honest bound is "rest of the current instruction + `maxCycles + 7`"):
* `T_CPU_7_nmi_latency_mid`: from a core in the middle of an ordinary instruction (`LatMid`,
  `cyc` cycles done), lines constant, NMI edge latched or sampled in the next cycle: within
  `n ≤ (maxCycles - cyc) + maxCycles + 7` cycles, boundary with I set and `PC = mem16[$FFFA]`.
* `T_CPU_7_nmi_latency_edge`: from an opcode-fetch boundary (NMI line low, detectors idle) with
  the NMI line asserted from the instruction's 1-based cycle `j` on (`hjNmiFrom j`, IRQ
  constant), the edge inside the instruction: `d` cycles after the edge,
  `d ≤ (maxCycles - (j - 1)) + maxCycles + 7` (≤ 22 for `j ≥ 2`), boundary with I set and
  `PC = mem16[$FFFA]`. Covers BRK (edge in cycles 2–4: hijacked; 5–7: taken after the
  handler's first instruction).
* `T_CPU_7_nmi_latency_edge_irq`: the same inside an IRQ sequence (edge in its cycle
  `j ∈ [1, 7]`): `d ≤ (7 - (j - 1)) + maxCycles + 7`; cycles 1–4 hijack it.
Side condition everywhere: no JAM opcode is fetched at the boundary where the next instruction
starts. NMI sequences are excluded (an edge in their cycles 1–4 is consumed, a documented gap).

## Method

The core follows `MicroState.complete` exactly while an ordinary instruction runs
(`lat_core_mid`: `kind = none`, no vector override, `boundary` only at `pos = 0`). Positions
are tracked in an abstract model (`latAdv`/`latCnt`/`latJ`: position, `crossed`, branch
condition, cycles so far) related to the micro-machine by `lat_micro_step`; four facts over
all 256 opcodes (`decide +kernel`) give: the model's invariant is inductive, the position
strictly increases, every program has at most 7 micro-ops, and for every non-branch opcode
the cycle before the last one is `isPollCycle` (branches always poll in cycle 1). `LatInv`
carries this plus "NMI pending, no RESET, the poll latched NMI if it already happened" through
`Core.runCycles` (`lat_mid_step`, `lat_run`). For an edge mid-instruction, `LatMid` drops the
NMI fields: the instruction ends (`lat_run2`) at a boundary (`LatEnd`) with the NMI pending,
whence `lat_dispatch`: an NMI sequence requested there is entered (7 cycles), an IRQ sequence is
hijacked (7 cycles), otherwise the next instruction polls it (`T_CPU_7_nmi_latency`, ≤ 15).
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

theorem lat_exec_intPending (ms : MicroState) (u : MicroOp) (v : UInt8) :
    (ms.exec u v).intPending = ms.intPending := by
  cases u <;> simp only [MicroState.exec] <;> split <;> rfl

theorem lat_complete_intPending (ms : MicroState) (v : UInt8) (hp : ms.pos ≠ 0) :
    (ms.complete v).intPending = ms.intPending := by
  rw [lat_complete_mid _ _ hp]
  unfold MicroState.advance
  generalize uops (ms.exec ms.curOp v).op = prog
  simp only [lat_exec_intPending]

/-- At a boundary with a sequence requested, it is an NMI or IRQ sequence with pushes. -/
def LatSeq (c : Core) : Prop :=
  c.ms.intPending = true → c.ms.suppressWrites = false ∧ (c.kind = .nmi ∨ c.kind = .irq)

/-- The core at the boundary ending an instruction. -/
structure LatEnd (c : Core) : Prop where
  pos : c.ms.pos = 0
  halted : c.ms.cpu.halted = false
  rst : c.ints.resetPending = false
  seq : LatSeq c

theorem lat_boundary_end (c0 : Core) (h0 : c0.ms.intPending = false)
    (hr : c0.ints.resetPending = false) (hh : c0.ms.cpu.halted = false) (hp : c0.ms.pos = 0) :
    LatEnd c0.boundary ∧ c0.boundary.ints.nmiPending = c0.ints.nmiPending ∧
      c0.boundary.ints.nmiPrev = c0.ints.nmiPrev := by
  unfold Core.boundary IntState.atBoundary
  simp only [hr, hh]
  cases hn : c0.ints.pollNmi <;> cases hi : c0.ints.pollIrq <;>
    simp [LatSeq, IntKind.isSeq, MicroState.requestInterrupt, IntKind.suppressWrites,
      IntState.ack, h0, hh, hr, hp] <;>
    constructor <;> simp [LatSeq, h0, hh, hp, hr]

/-- Invariant of a core in the middle of an ordinary (non-JAM) instruction, with no assumption
on the NMI detector (`LatInv` without `pend`/`poll`/`br`). -/
structure LatMid (c : Core) : Prop where
  kind : c.kind = .none
  halted : c.ms.cpu.halted = false
  nojam : classify (decode c.ms.op) ≠ .jam
  j : latJ (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) = true
  cnt : c.cyc = (latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr)).toUInt8
  le : latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) ≤ c.ms.pos.toNat
  rst : c.ints.resetPending = false
  ip : c.ms.intPending = false

/-- One cycle of a core satisfying `LatMid`: the NMI edge detector is updated as usual, and
either the instruction goes on (invariant kept, position advanced) or it ends at a boundary
(`LatEnd`: no RESET, and any requested sequence is an NMI or IRQ one, with pushes). -/
theorem lat_mid_step2 (c : Core) (lines : IntLines) (v : UInt8) (hr : lines.reset = false)
    (h : LatMid c) :
    (c.complete lines v).ints.nmiPending = (c.ints.nmiPending || (!c.ints.nmiPrev && lines.nmi)) ∧
    (c.complete lines v).ints.nmiPrev = lines.nmi ∧
    ((LatMid (c.complete lines v) ∧ c.ms.pos.toNat < (c.complete lines v).ms.pos.toNat ∧
      (c.complete lines v).cyc.toNat = c.cyc.toNat + 1) ∨
    (LatEnd (c.complete lines v) ∧ c.cyc.toNat + 1 ≤ 8)) := by
  obtain ⟨hk, hh, hnj, hJ, hcnt, hle, hrst, hip⟩ := h
  have hr1 := lat_J_le _ _ _ _ _ hJ
  have hsz := lat_size c.ms.op
  have hp0 : c.ms.pos ≠ 0 := by
    intro h0; rw [h0] at hr1; simp at hr1
  have hcyc : c.cyc.toNat = latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
      (branchCond c.ms.cpu (decode c.ms.op).instr) := by
    rw [hcnt, lat_toNat_toUInt8]; omega
  have hip' : (c.ms.complete v).intPending = false := by
    rw [lat_complete_intPending _ _ hp0, hip]
  obtain ⟨hop, hhalt, hcond, hcr, hpos'⟩ := lat_micro_step c.ms v hp0 hnj hJ
  rw [lat_core_mid c lines v hp0 hk]
  generalize hM : c.ms.complete v = ms' at hop hhalt hcond hcr hpos' hip'
  have key := lat_step c.ms.op c.ms.pos.toNat (by omega) c.ms.crossed ms'.crossed
    (branchCond c.ms.cpu (decode c.ms.op).instr) (branchCond ms'.cpu (decode c.ms.op).instr)
    hJ hcond
  rw [hcr] at key
  by_cases hz : latAdv (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat ms'.crossed
      (branchCond ms'.cpu (decode c.ms.op).instr) = 0
  · -- last cycle
    have hpz : ms'.pos = 0 := by rw [hpos', hz]; rfl
    simp only [hpz, ite_true]
    obtain ⟨hE, hn1, hn2⟩ := lat_boundary_end
      ⟨ms', c.ints.sampleCycle lines (pollIFlag (decode ms'.op).instr c.iBefore ms'.cpu.i)
        (Core.pollAt ms' (c.cyc + 1)), c.cyc + 1, .none, c.iBefore⟩ hip'
      (by simp [IntState.sampleCycle, hrst, hr]) (by simpa [hhalt] using hh) hpz
    refine ⟨by rw [hn1]; rfl, by rw [hn2]; rfl, Or.inr ⟨hE, ?_⟩⟩
    have hcl : latCnt (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat c.ms.crossed
        (branchCond c.ms.cpu (decode c.ms.op).instr) ≤ 7 := by omega
    rw [hcyc]; omega
  · -- the instruction goes on
    obtain ⟨hJ', hcnt', hlt⟩ := key hz
    have hr2 := lat_J_le _ _ _ _ _ hJ'
    have hpn : ms'.pos.toNat = latAdv (uops c.ms.op) (decode c.ms.op) c.ms.pos.toNat ms'.crossed
        (branchCond ms'.cpu (decode c.ms.op).instr) := by
      rw [hpos', lat_toNat_toUInt8]; omega
    have hpnz : ms'.pos ≠ 0 := by
      intro h0; rw [h0] at hpn; simp at hpn; omega
    simp only [hpnz, ite_false]
    refine ⟨rfl, rfl, Or.inl ⟨⟨rfl, by simpa [hhalt] using hh, by rw [hop]; exact hnj, ?_, ?_, ?_,
      ?_, hip'⟩, ?_, ?_⟩⟩
    · rw [hop, hpn]; exact hJ'
    · rw [hop, hpn, hcnt', lat_toUInt8_succ, hcnt]
    · rw [hop, hpn, hcnt']; omega
    · simp [IntState.sampleCycle, hrst, hr]
    · omega
    · show (c.cyc + 1).toNat = _
      rw [UInt8.toNat_add]; simp only [UInt8.reduceToNat]; omega

/-- From a core satisfying `LatMid` whose NMI detector holds an edge (latched, or sampled in the
next cycle), the instruction ends within its remaining cycles (`cyc + n ≤ 8`) at a boundary
(`LatEnd`) with the NMI still pending. -/
theorem lat_run2 (k : Nat) : ∀ (c : Core) (lines : IntLines) (m : Mem), lines.reset = false →
    LatMid c → 8 ≤ k + c.ms.pos.toNat →
    (c.ints.nmiPending || (!c.ints.nmiPrev && lines.nmi)) = true →
    ∃ n, 1 ≤ n ∧ c.cyc.toNat + n ≤ 8 ∧ LatEnd (Core.runCycles n c lines m).1 ∧
      (Core.runCycles n c lines m).1.ints.nmiPending = true := by
  induction k with
  | zero =>
    intro c lines m _ h hk
    have := lat_J_le _ _ _ _ _ h.j; have := lat_size c.ms.op; omega
  | succ k ih =>
    intro c lines m hr h hk hn
    obtain ⟨v, hv⟩ := cycle_complete c lines m
    obtain ⟨hp1, -, hs⟩ := lat_mid_step2 c lines v hr h
    rcases hs with ⟨h', hlt, hcy⟩ | ⟨hE, h5⟩
    · obtain ⟨n, hn1, hn2, hn3⟩ := ih (c.complete lines v) lines (c.cycle lines m).2 hr h'
        (by omega) (by rw [hp1, hn]; rfl)
      refine ⟨n + 1, by omega, by omega, ?_⟩
      rw [lat_runCycles_succ, hv]; exact hn3
    · refine ⟨1, Nat.le_refl _, h5, ?_⟩
      rw [lat_runCycles_succ, hv]; exact ⟨hE, by show (c.complete lines v).ints.nmiPending = true; rw [hp1, hn]⟩

/-- From an instruction-ending boundary (`LatEnd`) with an NMI pending, no RESET, lines held
constant, and (if an opcode is fetched next) a non-JAM opcode: within `7 ≤ n ≤ 15` cycles the
core is at a boundary with I set and `PC = mem16[$FFFA]`. An NMI sequence requested here is
entered in 7 cycles; an IRQ sequence is hijacked (the NMI is pending at its cycle 5), 7 cycles;
otherwise the next instruction polls the pending NMI (`T_CPU_7_nmi_latency`). -/
theorem lat_dispatch (E : Core) (lines : IntLines) (m : Mem) (hE : LatEnd E)
    (hr : lines.reset = false) (hnp : E.ints.nmiPending = true)
    (hjam : E.ms.intPending = false → classify (decode (m.read E.ms.cpu.pc)) ≠ .jam) :
    ∃ n, 7 ≤ n ∧ n ≤ maxCycles + 7 ∧
      (Core.runCycles n E lines m).1.ms.pos = 0 ∧
      (Core.runCycles n E lines m).1.ms.cpu.i = true ∧
      (Core.runCycles n E lines m).1.ms.cpu.pc =
        UInt16.ofLoHi ((Core.runCycles n E lines m).2.read 0xFFFA)
          ((Core.runCycles n E lines m).2.read 0xFFFB) := by
  obtain ⟨hpos, hh, hrst, hseq⟩ := hE
  cases hint : E.ms.intPending
  · exact T_CPU_7_nmi_latency E lines m hpos hint hh (hjam hint) hrst hr (Or.inl hnp)
  · obtain ⟨hsw, hk⟩ := hseq hint
    have := T_CPU_7_entry E lines m E.kind hk hpos hint hsw rfl
    have hv : entryVector E.kind E.ints lines = IntKind.vecNmi := by
      rcases hk with hk | hk <;> rw [hk]
      · exact entryVector_nmi _ _
      · simp [entryVector, IntKind.hijackable, hnp]
    simp only [hv] at this
    obtain ⟨-, hm, hp, hcpu⟩ := this
    refine ⟨7, Nat.le_refl _, by simp only [maxCycles]; omega, hp, ?_, ?_⟩
    · rw [hcpu]; exact (T_CPU_7_B_only_pushed _ _).2.1
    · rw [hcpu, hm]; rfl

/-- **T-CPU-7 (NMI latency, edge mid-instruction, invariant form).** From a core in the middle
of an ordinary (non-JAM) instruction (`LatMid`: `cyc` cycles done, `1 ≤ cyc`), no RESET, lines
held constant, with an NMI edge latched or sampled in the next cycle: within
`n ≤ (8 - cyc) + 15` cycles (the rest of the instruction, then at most `maxCycles + 7`) the core
is at a boundary with I set and `PC = mem16[$FFFA]`, provided the opcode fetched at the
instruction's end (if any) is not JAM. -/
theorem T_CPU_7_nmi_latency_mid (c : Core) (lines : IntLines) (m : Mem) (h : LatMid c)
    (hr : lines.reset = false)
    (hn : c.ints.nmiPending = true ∨ (c.ints.nmiPrev = false ∧ lines.nmi = true))
    (hjam : ∀ n, n ≤ 8 → (Core.runCycles n c lines m).1.ms.pos = 0 →
      (Core.runCycles n c lines m).1.ms.intPending = false →
      classify (decode ((Core.runCycles n c lines m).2.read
        (Core.runCycles n c lines m).1.ms.cpu.pc)) ≠ .jam) :
    ∃ n, n ≤ (maxCycles - c.cyc.toNat) + maxCycles + 7 ∧
      (Core.runCycles n c lines m).1.ms.pos = 0 ∧
      (Core.runCycles n c lines m).1.ms.cpu.i = true ∧
      (Core.runCycles n c lines m).1.ms.cpu.pc =
        UInt16.ofLoHi ((Core.runCycles n c lines m).2.read 0xFFFA)
          ((Core.runCycles n c lines m).2.read 0xFFFB) := by
  have hpd : (c.ints.nmiPending || (!c.ints.nmiPrev && lines.nmi)) = true := by
    rcases hn with h | ⟨h1, h2⟩ <;> simp [*]
  obtain ⟨k, hk1, hk8, hE, hnp⟩ := lat_run2 8 c lines m hr h (by omega) hpd
  obtain ⟨n, -, hn15, hres⟩ := lat_dispatch _ lines (Core.runCycles k c lines m).2 hE hr hnp
    (hjam k (by omega) hE.pos)
  refine ⟨k + n, by simp only [maxCycles] at hn15 ⊢; omega, ?_⟩
  rw [lat_runCycles_add]; exact hres

theorem lat_vf_rst (st : IntState) (k : IntKind) :
    (st.vectorFetch k).2.resetPending = st.resetPending := by
  simp only [IntState.vectorFetch]; split <;> rfl

/-- A BRK run for 7 cycles (any NMI schedule, no RESET, poll latches clear) ends at a boundary
with no sequence requested, no RESET pending, not halted. -/
theorem lat_brk_end (c : Core) (irq : Nat → Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc = 0) (hpoll : c.ints.pollNmi = false)
    (hpirq : c.ints.pollIrq = false) (hrst : c.ints.resetPending = false) :
    let r := runSched 7 (hjNmiFrom j irq) c m
    r.1.ms.intPending = false ∧ r.1.ints.resetPending = false ∧ r.1.ms.cpu.halted = false := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hh hop hpoll hpirq hrst; subst hpos hint
  simp [runSched, hjNmiFrom, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
    complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, IntKind.isSeq,
    hh, hop, hpoll, hpirq, hrst, Core.boundary, IntState.atBoundary,
    IntState.sampleCycle, lat_vf_rst, hj_vf_pollNmi, vectorFetch_pollIrq, State.setI, State.setBit]

/-- An IRQ sequence under the schedule `hjNmiFrom j` (edge in its cycle `j ≥ 1`): after 7 cycles
the pushes are done, `PC = mem16[$FFFA]` if `j ≤ 4` (hijack) else `mem16[$FFFE]`, the NMI is
still pending iff `5 ≤ j ≤ 7`, and no sequence or RESET is requested. -/
theorem lat_irq_from (c : Core) (irq : Nat → Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = true) (hsw : c.ms.suppressWrites = false)
    (hkind : c.kind = .irq) (hpend : c.ints.nmiPending = false)
    (hprev : c.ints.nmiPrev = false) (hpoll : c.ints.pollNmi = false)
    (hpirq : c.ints.pollIrq = false) (hrst : c.ints.resetPending = false) (hj : 1 ≤ j) :
    let s := c.ms.cpu
    let m' := entryMem s m (s.p ||| 0x20)
    let v : UInt16 := if j ≤ 4 then 0xFFFA else 0xFFFE
    let r := runSched 7 (hjNmiFrom j irq) c m
    r.2 = m' ∧ r.1.ms.pos = 0 ∧
      r.1.ms.cpu = entryCpu s (UInt16.ofLoHi (m'.read v) (m'.read (v + 1))) ∧
      r.1.ints.nmiPending = decide (5 ≤ j ∧ j ≤ 7) ∧
      r.1.ms.intPending = false ∧ r.1.ints.resetPending = false := by
  obtain ⟨⟨s, op, pos, addr, base, data, crossed, ip, inInt, sw, vec⟩, ints, cyc, kind, ib⟩ := c
  simp only at hpos hint hsw hkind hpend hprev hpoll hpirq hrst; subst hpos hint hsw hkind
  by_cases h4 : j ≤ 4
  · have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
    simp [runSched, hjNmiFrom, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
      complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
      -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
      vf_fst, IntKind.vecNmi, sc_nmiPending, sc_nmiPrev, IntKind.hijackable,
      UInt16.add_assoc, hpend, hprev, hpoll, hpirq, hrst, Core.boundary, IntState.atBoundary,
      IntState.sampleCycle, IntState.vectorFetch]
  · have e1 : decide (j ≤ 0 + 1) = false := by simp; omega
    have e2 : decide (j ≤ 1 + 1) = false := by simp; omega
    have e3 : decide (j ≤ 2 + 1) = false := by simp; omega
    have e4' : decide (j ≤ 3 + 1) = false := by simp; omega
    have e4 : (5 ≤ j) := by omega
    simp [runSched, hjNmiFrom, Core.cycle, Core.busOp, Core.complete, Core.pollAt, busOp, curOp,
      complete, MicroState.exec, advance, ctl_uops_00, skips, stackAddr, pushOp, entryMem,
      -UInt8.toUInt16_sub, sub_two, sub_three, entryCpu, State.setI, State.setBit, IntKind.isSeq,
      vf_fst, IntKind.vecNmi, sc_nmiPending, sc_nmiPrev, IntKind.hijackable, IntKind.vector,
      IntKind.vecIrq, UInt16.add_assoc, hpend, hprev, hpoll, hpirq, hrst, e1, e2, e3, e4', h4, e4,
      Core.boundary, IntState.atBoundary, IntState.sampleCycle, IntState.vectorFetch]
    by_cases a5 : j ≤ 5 <;> by_cases a6 : j ≤ 6 <;> by_cases a7 : j ≤ 7 <;> simp [a5, a6, a7] <;>
      omega

/-- The opcode-fetch cycle of an ordinary instruction (not BRK, not JAM) establishes `LatMid`
with `cyc = 1`, whatever the NMI line does. -/
theorem lat_fetch2 (c : Core) (lines : IntLines) (v : UInt8) (hpos : c.ms.pos = 0)
    (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false) (hv : v ≠ 0)
    (hjam : classify (decode v) ≠ .jam) (hrst : c.ints.resetPending = false)
    (hr : lines.reset = false) :
    LatMid (c.complete lines v) ∧ (c.complete lines v).cyc = 1 ∧
      (c.complete lines v).ints.nmiPrev = lines.nmi := by
  have hv' : (v == 0) = false := by simpa using hv
  have heq : c.complete lines v =
      let ms1 := latFetched c.ms v
      ⟨ms1, c.ints.sampleCycle lines (pollIFlag (decode v).instr c.ms.cpu.i ms1.cpu.i)
        (Core.pollAt ms1 1), 1, .none, c.ms.cpu.i⟩ := by
    simp [Core.complete, hpos, hint, hh, MicroState.complete, hv', IntKind.isSeq, latFetched]
  rw [heq]
  refine ⟨⟨rfl, hh, hjam, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · exact lat_init v _
  · simp [latCnt, latFetched]
  · simp [latCnt, latFetched]
  · simp [IntState.sampleCycle, hrst, hr]
  · simpa [latFetched] using hint

theorem lat_mid_cyc (c : Core) (h : LatMid c) : c.cyc.toNat ≤ 7 := by
  have h1 := lat_J_le _ _ _ _ _ h.j
  have h2 := lat_size c.ms.op
  have h3 := h.le
  rw [h.cnt, lat_toNat_toUInt8] <;> omega

/-- The lines after the edge. -/
abbrev latHigh (irq : Bool) : IntLines := { nmi := true, irq := irq, reset := false }

theorem lat_after_edge (j a : Nat) (irq : Bool) (h : j ≤ a + 1) :
    (fun k => hjNmiFrom j (fun _ => irq) (a + k)) = fun _ => latHigh irq := by
  funext k; simp only [hjNmiFrom, latHigh]; congr 1; simp; omega

theorem lat_sched_after (j a d : Nat) (irq : Bool) (c : Core) (m : Mem) (h : j ≤ a + 1) :
    runSched (a + d) (hjNmiFrom j fun _ => irq) c m =
      Core.runCycles d (runSched a (hjNmiFrom j fun _ => irq) c m).1 (latHigh irq)
        (runSched a (hjNmiFrom j fun _ => irq) c m).2 := by
  rw [runSched_add, lat_after_edge j a irq h, runSched_const]

/-- Before the edge (cycles `1 … j-1`), an ordinary instruction keeps `LatMid`, counts its
cycles, and the NMI line was sampled low. -/
theorem lat_prefix (c : Core) (irq : Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hop : m.read c.ms.cpu.pc ≠ 0) (hjam : classify (decode (m.read c.ms.cpu.pc)) ≠ .jam)
    (hrst : c.ints.resetPending = false)
    (hin : ∀ k, 1 ≤ k → k < j → (runSched k (hjNmiFrom j fun _ => irq) c m).1.ms.pos ≠ 0) :
    ∀ k, 1 ≤ k → k < j → LatMid (runSched k (hjNmiFrom j fun _ => irq) c m).1 ∧
      (runSched k (hjNmiFrom j fun _ => irq) c m).1.cyc.toNat = k ∧
      (runSched k (hjNmiFrom j fun _ => irq) c m).1.ints.nmiPrev = false := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [runSched]
      rw [lat_cycle_fetch c _ m hpos hint hh]
      obtain ⟨h1, h2, h3⟩ := lat_fetch2 c (hjNmiFrom j (fun _ => irq) 0) _ hpos hint hh hop hjam hrst rfl
      refine ⟨h1, by rw [h2]; rfl, by rw [h3]; simp [hjNmiFrom]; omega⟩
    · obtain ⟨hM, hc, -⟩ := ih hk0 (by omega)
      have hne := hin (k + 1) (by omega) hk
      rw [runSched_add] at hne ⊢
      simp only [runSched, Nat.add_zero] at hne ⊢
      generalize runSched k (hjNmiFrom j fun _ => irq) c m = r at hM hc hne ⊢
      obtain ⟨v, hv⟩ := cycle_complete r.1 (hjNmiFrom j (fun _ => irq) k) r.2
      rw [hv] at hne ⊢
      obtain ⟨-, hpr, hs⟩ := lat_mid_step2 r.1 (hjNmiFrom j (fun _ => irq) k) v rfl hM
      rcases hs with ⟨h', -, hcy⟩ | ⟨hE, -⟩
      · exact ⟨h', by rw [hcy, hc], by rw [hpr]; simp [hjNmiFrom]; omega⟩
      · exact absurd hE.pos hne

theorem lat_entryCpu_halted (s : State) (pc : UInt16) : (entryCpu s pc).halted = s.halted := by
  simp [entryCpu, State.setI, State.setBit]

/-- **T-CPU-7 (NMI latency, edge mid-instruction).** From an instruction boundary that fetches
an opcode (no sequence requested, not halted, no RESET, detectors idle for NMI: line low, no
edge latched, no NMI/IRQ poll latched), with lines `hjNmiFrom j (fun _ => irq)`: the NMI line low before the
instruction's 1-based cycle `j` and asserted (held) from cycle `j` on, IRQ constant, no RESET.
If the edge falls inside the instruction (cycles `1 … j-1` do not end it) and no JAM opcode is
fetched in the window, then `d` cycles after the edge, with
`d ≤ (maxCycles - (j - 1)) + maxCycles + 7` (rest of the instruction + 15; ≤ 22 for `j ≥ 2`),
the core is at a boundary with I set and `PC = mem16[$FFFA]`. Ordinary instructions: the
current instruction ends (`T_CPU_7_nmi_latency_mid`); if its poll already happened, the next
instruction polls the NMI (or an IRQ sequence requested at the boundary is hijacked). BRK: an
edge in cycles 2–4 hijacks it (`T_CPU_7_hijack_mid`, 7 cycles); in cycles 5–7 the handler's
first instruction runs and then the NMI is taken. -/
theorem T_CPU_7_nmi_latency_edge (c : Core) (irq : Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = false) (hh : c.ms.cpu.halted = false)
    (hrst : c.ints.resetPending = false) (hprev : c.ints.nmiPrev = false)
    (hpend : c.ints.nmiPending = false) (hpoll : c.ints.pollNmi = false)
    (hpirq : c.ints.pollIrq = false) (hj : 1 ≤ j)
    (hin : ∀ k, 1 ≤ k → k < j → (runSched k (hjNmiFrom j fun _ => irq) c m).1.ms.pos ≠ 0)
    (hjam : ∀ n, n ≤ 2 * maxCycles + 7 →
      (runSched n (hjNmiFrom j fun _ => irq) c m).1.ms.pos = 0 →
      (runSched n (hjNmiFrom j fun _ => irq) c m).1.ms.intPending = false →
      classify (decode ((runSched n (hjNmiFrom j fun _ => irq) c m).2.read
        (runSched n (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.pc)) ≠ .jam) :
    ∃ d, d ≤ (maxCycles - (j - 1)) + maxCycles + 7 ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.pos = 0 ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.i = true ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.pc =
        UInt16.ofLoHi ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).2.read 0xFFFA)
          ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).2.read 0xFFFB) := by
  have hjam0 := hjam 0 (by omega) hpos hint
  simp only [runSched] at hjam0
  rcases Nat.eq_or_lt_of_le hj with rfl | hj2
  · -- edge in the opcode-fetch cycle
    obtain ⟨n, -, hn, hres⟩ := T_CPU_7_nmi_latency c (latHigh irq) m hpos hint hh hjam0 hrst rfl
      (Or.inr ⟨hprev, rfl⟩)
    refine ⟨n, by simp only [maxCycles] at hn ⊢; omega, ?_⟩
    rw [lat_sched_after 1 0 n irq c m (by omega)]
    exact hres
  by_cases hop : m.read c.ms.cpu.pc = 0
  · -- BRK
    have hb := hj_brk_from c (fun _ => irq) m j hpos hint hh hop hpend hprev hpoll (by omega)
    dsimp only at hb
    obtain ⟨hb1, hb2, hb3, hb4, -, -, -⟩ := hb
    have hj7 : j ≤ 7 := by
      refine Classical.byContradiction fun h => ?_
      exact hin 7 (by omega) (by omega) hb2
    by_cases hj4 : j ≤ 4
    · obtain ⟨-, hm, hp, hcpu, -⟩ := T_CPU_7_hijack_mid c (fun _ => irq) m j hpos hint hh hop hpend
        hprev hpoll ⟨by omega, hj4⟩
      refine ⟨8 - j, by simp only [maxCycles]; omega, ?_⟩
      rw [show j - 1 + (8 - j) = 7 by omega]
      refine ⟨hp, ?_, ?_⟩
      · rw [hcpu]; exact (T_CPU_7_B_only_pushed _ _).2.1
      · rw [hcpu, hm]; rfl
    · have he := lat_brk_end c (fun _ => irq) m j hpos hint hh hop hpoll hpirq hrst
      dsimp only at he
      obtain ⟨he1, he2, he3⟩ := he
      have hnp : (runSched 7 (hjNmiFrom j fun _ => irq) c m).1.ints.nmiPending = true := by
        rw [hb4]; simp; omega
      have hE : LatEnd (runSched 7 (hjNmiFrom j fun _ => irq) c m).1 :=
        ⟨hb2, he3, he2, fun h => by rw [he1] at h; cases h⟩
      obtain ⟨n, -, hn, hres⟩ := lat_dispatch _ (latHigh irq) _ hE rfl hnp
        (hjam 7 (by simp only [maxCycles]; omega) hb2)
      refine ⟨8 - j + n, by simp only [maxCycles] at hn ⊢; omega, ?_⟩
      rw [show j - 1 + (8 - j + n) = 7 + n by omega, lat_sched_after j 7 n irq c m (by omega)]
      exact hres
  · -- ordinary instruction: run up to the edge, then `T_CPU_7_nmi_latency_mid`
    obtain ⟨hM, hc, hpr⟩ := lat_prefix c irq m j hpos hint hh hop hjam0 hrst hin (j - 1)
      (by omega) (by omega)
    have h7 := lat_mid_cyc _ hM
    obtain ⟨n, hn, hres⟩ := T_CPU_7_nmi_latency_mid _ (latHigh irq) _ hM rfl
      (Or.inr ⟨hpr, rfl⟩) (by
        intro n hn8
        rw [← lat_sched_after j (j - 1) n irq c m (by omega)]
        exact hjam _ (by simp only [maxCycles]; omega))
    refine ⟨n, by rw [hc] at hn; exact hn, ?_⟩
    rw [lat_sched_after j (j - 1) n irq c m (by omega)]
    exact hres

/-- **T-CPU-7 (NMI latency, edge inside an IRQ sequence).** From a boundary at which an IRQ
sequence was requested (pushes on, no RESET, not halted, NMI line low with no edge latched,
poll latches clear as after `ack`), with the NMI line asserted (held) from the sequence's
1-based cycle `j ∈ [1, 7]` on and IRQ constant: an edge in cycles 1–4 hijacks the sequence
(`PC = mem16[$FFFA]` after its 7 cycles); in cycles 5–7 the sequence loads `$FFFE`, the
handler's first instruction runs and then the NMI is taken. Either way, `d` cycles after the
edge, `d ≤ (7 - (j - 1)) + maxCycles + 7`, the core is at a boundary with I set and
`PC = mem16[$FFFA]` (provided no JAM opcode is fetched at the end of the sequence). -/
theorem T_CPU_7_nmi_latency_edge_irq (c : Core) (irq : Bool) (m : Mem) (j : Nat)
    (hpos : c.ms.pos = 0) (hint : c.ms.intPending = true) (hsw : c.ms.suppressWrites = false)
    (hkind : c.kind = .irq) (hh : c.ms.cpu.halted = false)
    (hrst : c.ints.resetPending = false) (hprev : c.ints.nmiPrev = false)
    (hpend : c.ints.nmiPending = false) (hpoll : c.ints.pollNmi = false)
    (hpirq : c.ints.pollIrq = false) (hj : 1 ≤ j) (hj7 : j ≤ 7)
    (hjam : (runSched 7 (hjNmiFrom j fun _ => irq) c m).1.ms.intPending = false →
      classify (decode ((runSched 7 (hjNmiFrom j fun _ => irq) c m).2.read
        (runSched 7 (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.pc)) ≠ .jam) :
    ∃ d, d ≤ (7 - (j - 1)) + maxCycles + 7 ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.pos = 0 ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.i = true ∧
      (runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).1.ms.cpu.pc =
        UInt16.ofLoHi ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).2.read 0xFFFA)
          ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) c m).2.read 0xFFFB) := by
  have hb := lat_irq_from c (fun _ => irq) m j hpos hint hsw hkind hpend hprev hpoll hpirq hrst hj
  dsimp only at hb
  obtain ⟨hm, hp, hcpu, hnp, hip, hr7⟩ := hb
  by_cases hj4 : j ≤ 4
  · simp only [hj4, ite_true] at hcpu
    refine ⟨8 - j, by simp only [maxCycles]; omega, ?_⟩
    rw [show j - 1 + (8 - j) = 7 by omega]
    refine ⟨hp, ?_, ?_⟩
    · rw [hcpu]; exact (T_CPU_7_B_only_pushed _ _).2.1
    · rw [hcpu, hm]; rfl
  · have hnp' : (runSched 7 (hjNmiFrom j fun _ => irq) c m).1.ints.nmiPending = true := by
      rw [hnp]; simp; omega
    have hE : LatEnd (runSched 7 (hjNmiFrom j fun _ => irq) c m).1 :=
      ⟨hp, by rw [hcpu, lat_entryCpu_halted]; exact hh, hr7, fun h => by rw [hip] at h; cases h⟩
    obtain ⟨n, -, hn, hres⟩ := lat_dispatch _ (latHigh irq) _ hE rfl hnp' (hjam)
    refine ⟨8 - j + n, by simp only [maxCycles] at hn ⊢; omega, ?_⟩
    rw [show j - 1 + (8 - j + n) = 7 + n by omega, lat_sched_after j 7 n irq c m (by omega)]
    exact hres

end Nes.Cpu.Proofs
