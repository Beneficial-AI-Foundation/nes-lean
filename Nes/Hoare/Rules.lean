import Nes.Hoare.Logic

/-!
# `Nes.Hoare.Rules` — the proof rules of the 6502 Hoare logic

Every rule is a theorem about the semantic `Triple` / `CTriple` / `TripleM` of
`Nes.Hoare.Logic` (shallow embedding), so the logic is sound by construction.

## Spec

* **Structural.** `Reach.seq`, `Reach.conseq`, `Reach.of_imp` (zero steps), `Reach.step_then`
  / `Reach.then_step` (one instruction before / after). `Triple.seq` composes
  `{P} e ⟶ mid {R}` and `{R} mid ⟶ x {Q}`; `Triple.conseq` (strengthen pre, weaken post),
  `Triple.pre`, `Triple.post`; `Triple.skip` (`{P} e ⟶ e {Q}` when `P → Q`, zero steps);
  `Triple.cases` (split the precondition on any `C`); `Triple.exists_pre` (ghost variables:
  a triple for every `v` gives one for `∃ v, P v`); `Triple.false_pre`.
  `CTriple.seq` adds cycle counts; `CTriple.conseq`, `CTriple.skip`. `TripleM.seq`,
  `TripleM.conseq`, `TripleM.mono` (enlarge the footprint), `TripleM.skip`.
* **Frame.** `TripleM.frame`: if `{P} e ⟶ x {Q}` modifies only `F` and the memory assertion `R`
  is independent of `F` (`Indep R F`), then `{P ∧ R} e ⟶ x {Q ∧ R}` (still modifying only
  `F`). `Triple.frame` is the same conclusion as a plain triple.
* **Branch.** `IsBranch op instr` lists the eight conditional-branch opcodes (`BPL $10` …
  `BEQ $F0`). `step_branch`: on a running CPU with a branch opcode at `pc`, `step` leaves
  memory unchanged and moves `pc` to `branchTarget (pc+2) off` if `branchCond s instr`, else to
  `pc + 2` (nothing else changes); cycles `branchCycles` = 2 / 3 / 4.
  `Triple.branch`: for a pc-free precondition `P` with the branch at `b`, a triple from the
  taken target (under `P ∧ cond`) and one from `b + 2` (under `P ∧ ¬cond`) to the same exit
  give `{P} b ⟶ x {Q}`.
* **Loop.** `Triple.loop` (general, well-founded fuel): if from the loop head `h` every
  `I`-state with measure `μ = k` reaches either the head again with `I` and `μ < k`, or the
  exit `x` with `Q`, then `{I} h ⟶ x {Q}`. `Triple.loop_branch` specialises it to the usual
  bottom-tested 6502 loop `h: body; Bcc h`: a body triple `{I ∧ μ = k} h ⟶ b {R k}` ending at a
  backward branch at `b`, the taken side re-establishing `I` with smaller `μ`, the fall-through
  side giving `Q` at `b + 2`.
* **Calls.** `Triple.call` (JSR/RTS): `JSR t` at `c` (`$20`, operand `read16 (c+1) = t`, with
  `c + 2` not one of the two stacked cells since `Isa` reads the target high byte *after* the
  pushes), a callee run from `t` to an `RTS` at `r` that leaves SP as JSR left it and the two
  return-address bytes intact gives `{P} c ⟶ c+3 {Q}`; the RTS step is discharged with
  `T_CPU_6_jsr_rts`. `Triple.call_frame` is the modular form: the callee has *one* proved spec
  `∀ sp, {Pc ∧ SP = sp} t ⟶ r {Qc ∧ SP = sp}` modifying only `F`, the two stacked return-address
  cells lie outside `F`, and the caller learns `Qc` plus agreement of memory outside `F`.
-/

namespace Nes.Hoare

open Nes Nes.Cpu Nes.Cpu.Proofs

/-! ## Reach -/

theorem Reach.of_imp {P Q : Assn} (h : ∀ s m, P s m → Q s m) : Reach P Q :=
  fun s m hP => ⟨0, h s m hP⟩

theorem Reach.conseq {P P' Q Q' : Assn} (h : Reach P Q) (hP : ∀ s m, P' s m → P s m)
    (hQ : ∀ s m, Q s m → Q' s m) : Reach P' Q' := fun s m hP' =>
  let ⟨n, hn⟩ := h s m (hP s m hP'); ⟨n, hQ _ _ hn⟩

theorem Reach.seq {P R Q : Assn} (h₁ : Reach P R) (h₂ : Reach R Q) : Reach P Q := by
  intro s m hP
  obtain ⟨n₁, h1⟩ := h₁ s m hP
  obtain ⟨n₂, h2⟩ := h₂ _ _ h1
  exact ⟨n₁ + n₂, by rw [steps_add]; exact h2⟩

/-- One instruction first. -/
theorem Reach.step_then {P R Q : Assn} (h₁ : ∀ s m, P s m → R (step s m).1 (step s m).2.1)
    (h₂ : Reach R Q) : Reach P Q := by
  intro s m hP
  obtain ⟨n, h⟩ := h₂ _ _ (h₁ s m hP)
  exact ⟨n + 1, by rw [steps_succ]; exact h⟩

/-- One instruction last. -/
theorem Reach.then_step {P R Q : Assn} (h₁ : Reach P R)
    (h₂ : ∀ s m, R s m → Q (step s m).1 (step s m).2.1) : Reach P Q :=
  h₁.seq (fun s m hR => ⟨1, by rw [steps_one]; exact h₂ s m hR⟩)

/-! ## Structural rules for `Triple` -/

theorem Triple.seq {P R Q : Assn} {e mid x : UInt16} (h₁ : Triple P e mid R)
    (h₂ : Triple R mid x Q) : Triple P e x Q :=
  Reach.seq h₁ (h₂.conseq (fun _ _ ⟨h1, h2⟩ => ⟨h2, h1⟩) (fun _ _ h => h))

theorem Triple.conseq {P P' Q Q' : Assn} {e x : UInt16} (h : Triple P e x Q)
    (hP : ∀ s m, P' s m → P s m) (hQ : ∀ s m, Q s m → Q' s m) : Triple P' e x Q' :=
  Reach.conseq h (fun s m ⟨h1, h2⟩ => ⟨hP s m h1, h2⟩) (fun s m ⟨h1, h2⟩ => ⟨h1, hQ s m h2⟩)

theorem Triple.pre {P P' Q : Assn} {e x : UInt16} (h : Triple P e x Q)
    (hP : ∀ s m, P' s m → P s m) : Triple P' e x Q := h.conseq hP (fun _ _ h => h)

theorem Triple.post {P Q Q' : Assn} {e x : UInt16} (h : Triple P e x Q)
    (hQ : ∀ s m, Q s m → Q' s m) : Triple P e x Q' := h.conseq (fun _ _ h => h) hQ

theorem Triple.skip {P Q : Assn} {e : UInt16} (h : ∀ s m, P s m → Q s m) : Triple P e e Q :=
  Reach.of_imp fun s m ⟨hP, hpc⟩ => ⟨hpc, h s m hP⟩

theorem Triple.cases {P Q : Assn} {e x : UInt16} (C : Assn)
    (h₁ : Triple (fun s m => P s m ∧ C s m) e x Q) (h₂ : Triple (fun s m => P s m ∧ ¬ C s m) e x Q) :
    Triple P e x Q := fun s m ⟨hP, hpc⟩ => by
  by_cases hc : C s m
  · exact h₁ s m ⟨⟨hP, hc⟩, hpc⟩
  · exact h₂ s m ⟨⟨hP, hc⟩, hpc⟩

theorem Triple.exists_pre {α : Sort _} {P : α → Assn} {Q : Assn} {e x : UInt16}
    (h : ∀ v, Triple (P v) e x Q) : Triple (fun s m => ∃ v, P v s m) e x Q :=
  fun s m ⟨⟨v, hv⟩, hpc⟩ => h v s m ⟨hv, hpc⟩

theorem Triple.false_pre {Q : Assn} {e x : UInt16} : Triple (fun _ _ => False) e x Q :=
  fun _ _ ⟨h, _⟩ => h.elim

/-! ## Structural rules for `CTriple` (cycle counts) -/

theorem CTriple.seq {P R Q : Assn} {e mid x : UInt16} {c₁ c₂ : Nat} (h₁ : CTriple P e mid R c₁)
    (h₂ : CTriple R mid x Q c₂) : CTriple P e x Q (c₁ + c₂) := by
  intro s m hP hpc
  obtain ⟨n₁, p1, r1, c1⟩ := h₁ s m hP hpc
  obtain ⟨n₂, p2, r2, c2⟩ := h₂ _ _ r1 p1
  exact ⟨n₁ + n₂, by rw [steps_add]; exact ⟨p2, r2, by rw [c1, c2]⟩⟩

theorem CTriple.conseq {P P' Q Q' : Assn} {e x : UInt16} {c : Nat} (h : CTriple P e x Q c)
    (hP : ∀ s m, P' s m → P s m) (hQ : ∀ s m, Q s m → Q' s m) : CTriple P' e x Q' c :=
  fun s m hP' hpc => let ⟨n, h1, h2, h3⟩ := h s m (hP s m hP') hpc; ⟨n, h1, hQ _ _ h2, h3⟩

theorem CTriple.skip {P Q : Assn} {e : UInt16} (h : ∀ s m, P s m → Q s m) : CTriple P e e Q 0 :=
  fun s m hP hpc => ⟨0, hpc, h s m hP, rfl⟩

/-! ## Structural rules and the frame rule for `TripleM` -/

theorem TripleM.seq {P R Q : Assn} {e mid x : UInt16} {F : Region} (h₁ : TripleM P e mid R F)
    (h₂ : TripleM R mid x Q F) : TripleM P e x Q F := by
  intro s m hP hpc
  obtain ⟨n₁, p1, r1, a1⟩ := h₁ s m hP hpc
  obtain ⟨n₂, p2, r2, a2⟩ := h₂ _ _ r1 p1
  exact ⟨n₁ + n₂, by rw [steps_add]; exact ⟨p2, r2, a1.trans a2⟩⟩

theorem TripleM.conseq {P P' Q Q' : Assn} {e x : UInt16} {F : Region} (h : TripleM P e x Q F)
    (hP : ∀ s m, P' s m → P s m) (hQ : ∀ s m, Q s m → Q' s m) : TripleM P' e x Q' F :=
  fun s m hP' hpc => let ⟨n, h1, h2, h3⟩ := h s m (hP s m hP') hpc; ⟨n, h1, hQ _ _ h2, h3⟩

theorem TripleM.mono {P Q : Assn} {e x : UInt16} {F G : Region} (h : TripleM P e x Q F)
    (hFG : Region.Sub F G) : TripleM P e x Q G :=
  fun s m hP hpc => let ⟨n, h1, h2, h3⟩ := h s m hP hpc; ⟨n, h1, h2, h3.mono hFG⟩

theorem TripleM.skip {P Q : Assn} {e : UInt16} {F : Region} (h : ∀ s m, P s m → Q s m) :
    TripleM P e e Q F := fun s m hP hpc => ⟨0, hpc, h s m hP, Agree.refl F m⟩

/-- **Frame rule.** A memory assertion independent of the footprint survives the run. -/
theorem TripleM.frame {P Q : Assn} {R : Mem → Prop} {e x : UInt16} {F : Region}
    (h : TripleM P e x Q F) (hR : Indep R F) :
    TripleM (fun s m => P s m ∧ R m) e x (fun s m => Q s m ∧ R m) F := by
  intro s m ⟨hP, hRm⟩ hpc
  obtain ⟨n, h1, h2, h3⟩ := h s m hP hpc
  exact ⟨n, h1, ⟨h2, hR _ _ h3 hRm⟩, h3⟩

theorem Triple.frame {P Q : Assn} {R : Mem → Prop} {e x : UInt16} {F : Region}
    (h : TripleM P e x Q F) (hR : Indep R F) :
    Triple (fun s m => P s m ∧ R m) e x (fun s m => Q s m ∧ R m) :=
  (h.frame hR).toTriple

/-! ## Branches -/

/-- The eight conditional-branch opcodes and their instruction. -/
inductive IsBranch : UInt8 → Instr → Prop
  | bpl : IsBranch 0x10 .BPL
  | bmi : IsBranch 0x30 .BMI
  | bvc : IsBranch 0x50 .BVC
  | bvs : IsBranch 0x70 .BVS
  | bcc : IsBranch 0x90 .BCC
  | bcs : IsBranch 0xB0 .BCS
  | bne : IsBranch 0xD0 .BNE
  | beq : IsBranch 0xF0 .BEQ

/-- Cycles of a branch at `pc` with offset `off`: 2 not taken, 3 taken, 4 taken to another page. -/
def branchCycles (taken : Bool) (pc : UInt16) (off : UInt8) : Nat :=
  if taken then
    (if UInt16.hi (branchTarget (pc + 2) off) != UInt16.hi (pc + 2) then 4 else 3)
  else 2

theorem exec_branch {op : UInt8} {instr : Instr} (hb : IsBranch op instr) (s : State) (m : Mem)
    (ea : UInt16) (cr : Bool) :
    exec (decode op) s m ea cr =
      (if branchCond s instr then { s with pc := ea } else { s with pc := s.pc + 2 }, m) := by
  cases hb <;> rfl

theorem extraCycles_branch {op : UInt8} {instr : Instr} (hb : IsBranch op instr) (s : State)
    (cr : Bool) :
    (decode op).cycles.toNat + extraCycles (decode op) s cr =
      if branchCond s instr then (if cr then 4 else 3) else 2 := by
  cases hb <;>
  · simp only [dec_10, dec_30, dec_50, dec_70, dec_90, dec_B0, dec_D0, dec_F0, extraCycles]
    cases branchCond s _ <;> cases cr <;> rfl

theorem step_branch {op : UInt8} {instr : Instr} (hb : IsBranch op instr) (s : State) (m : Mem)
    (hh : s.halted = false) (h : m.read s.pc = op) :
    step s m =
      (if branchCond s instr then { s with pc := branchTarget (s.pc + 2) (m.read (s.pc + 1)) }
        else { s with pc := s.pc + 2 }, m,
       branchCycles (branchCond s instr) s.pc (m.read (s.pc + 1))) := by
  have hmode : (decode op).mode = .rel := by cases hb <;> rfl
  simp only [step, hh, h, Bool.false_eq_true, ite_false, exec_branch hb, extraCycles_branch hb,
    hmode, branchCycles]
  rfl

/-- **Branch rule.** Two-way case split at a conditional branch at `b`. -/
theorem Triple.branch {P Q : Assn} {b x : UInt16} {op off : UInt8} {instr : Instr}
    (hb : IsBranch op instr) (hpf : PcFree P)
    (hcode : ∀ s m, P s m → s.pc = b → s.halted = false ∧ m.read b = op ∧ m.read (b + 1) = off)
    (htaken : Triple (fun s m => P s m ∧ branchCond s instr = true) (branchTarget (b + 2) off) x Q)
    (hnot : Triple (fun s m => P s m ∧ branchCond s instr = false) (b + 2) x Q) :
    Triple P b x Q := by
  intro s m ⟨hP, hpc⟩
  obtain ⟨hh, hop, hoff⟩ := hcode s m hP hpc
  have e := step_branch hb s m hh (hpc ▸ hop)
  rw [hpc, hoff] at e
  cases hc : branchCond s instr
  · obtain ⟨n, hn⟩ := hnot _ m ⟨⟨hpf s m (b + 2) hP, hc⟩, rfl⟩
    exact ⟨n + 1, by rw [steps_succ, e, hc]; exact hn⟩
  · obtain ⟨n, hn⟩ := htaken _ m ⟨⟨hpf s m (branchTarget (b + 2) off) hP, hc⟩, rfl⟩
    exact ⟨n + 1, by rw [steps_succ, e, hc]; exact hn⟩

/-! ## Loops -/

/-- **Loop rule** (well-founded fuel `μ`). -/
theorem Triple.loop {I Q : Assn} {h x : UInt16} (μ : State → Mem → Nat)
    (body : ∀ k, Reach (fun s m => I s m ∧ s.pc = h ∧ μ s m = k)
      (fun s m => (I s m ∧ s.pc = h ∧ μ s m < k) ∨ (s.pc = x ∧ Q s m))) :
    Triple I h x Q := by
  suffices H : ∀ k s m, μ s m = k → I s m → s.pc = h →
      ∃ n, (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1 from
    fun s m ⟨hI, hpc⟩ => H _ s m rfl hI hpc
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro s m hk hI hpc
    obtain ⟨n₁, hn₁⟩ := body k s m ⟨hI, hpc, hk⟩
    rcases hn₁ with ⟨hI', hpc', hlt⟩ | hdone
    · obtain ⟨n₂, hn₂⟩ := ih _ hlt _ _ rfl hI' hpc'
      exact ⟨n₁ + n₂, by rw [steps_add]; exact hn₂⟩
    · exact ⟨n₁, hdone⟩

/-- **Bottom-tested loop** `h: body; B?? h` with the backward branch at `b`. -/
theorem Triple.loop_branch {I Q : Assn} {R : Nat → Assn} {h b : UInt16} {op off : UInt8}
    {instr : Instr} (μ : State → Mem → Nat) (hb : IsBranch op instr)
    (htgt : branchTarget (b + 2) off = h)
    (body : ∀ k, Triple (fun s m => I s m ∧ μ s m = k) h b (R k))
    (hcode : ∀ k s m, R k s m → s.halted = false ∧ m.read b = op ∧ m.read (b + 1) = off)
    (hback : ∀ k s m, R k s m → branchCond s instr = true →
      I { s with pc := h } m ∧ μ { s with pc := h } m < k)
    (hexit : ∀ k s m, R k s m → branchCond s instr = false → Q { s with pc := b + 2 } m) :
    Triple I h (b + 2) Q := by
  apply Triple.loop μ
  intro k
  refine Reach.seq (R := fun s m => s.pc = b ∧ R k s m)
    (Reach.conseq (body k) (fun s m ⟨hI, hpc, hk⟩ => ⟨⟨hI, hk⟩, hpc⟩) (fun _ _ h => h)) ?_
  refine Reach.step_then (R := fun s m => (I s m ∧ s.pc = h ∧ μ s m < k) ∨ (s.pc = b + 2 ∧ Q s m))
    ?_ (Reach.of_imp fun _ _ h => h)
  intro s m ⟨hpc, hR⟩
  obtain ⟨hh, hop, hoff⟩ := hcode k s m hR
  rw [step_branch hb s m hh (hpc ▸ hop), hpc, hoff, htgt]
  cases hc : branchCond s instr
  · exact Or.inr ⟨rfl, hexit k s m hR hc⟩
  · exact Or.inl ⟨(hback k s m hR hc).1, rfl, (hback k s m hR hc).2⟩

/-! ## Subroutine calls -/

/-- **JSR/RTS rule.** The callee obligation is stated for the concrete state JSR produces
(ghost `s0`, `m0` = the caller's state); use `Triple.call_frame` for a modular callee spec. -/
theorem Triple.call {P Q : Assn} {c t r : UInt16}
    (hjsr : ∀ s m, P s m → s.pc = c → s.halted = false ∧ m.read c = 0x20 ∧
      m.read16 (c + 1) = t ∧ c + 2 ≠ stackAddr s.sp ∧ c + 2 ≠ stackAddr (s.sp - 1))
    (hbody : ∀ s0 m0, P s0 m0 → s0.pc = c →
      Triple (fun s m => s = { s0 with sp := s0.sp - 1 - 1, pc := t } ∧ m = jsrMem s0 m0) t r
        (fun s m => s.halted = false ∧ m.read r = 0x60 ∧ s.sp = s0.sp - 1 - 1 ∧
          m.read (stackAddr s0.sp) = UInt16.hi (c + 2) ∧
          m.read (stackAddr (s0.sp - 1)) = UInt16.lo (c + 2) ∧
          Q { s with pc := c + 3, sp := s0.sp } m)) :
    Triple P c (c + 3) Q := by
  intro s0 m0 ⟨hP, hpc⟩
  obtain ⟨hh, hj, ht, ha1, ha2⟩ := hjsr s0 m0 hP hpc
  have hj' : m0.read s0.pc = 0x20 := hpc ▸ hj
  have ej := step_jsr s0 m0 hh hj'
  -- JSR lands on `t`
  have htgt : UInt16.ofLoHi (m0.read (s0.pc + 1)) ((jsrMem s0 m0).read (s0.pc + 2)) = t := by
    rw [← ht, hpc]
    simp only [jsrMem, read_write, Ne.symm ha1, Ne.symm ha2, ↓reduceIte, Mem.read16,
      UInt16.add_assoc]
    rfl
  rw [htgt] at ej
  obtain ⟨n, hpcr, hhr, hrts, hsp, hhi, hlo, hQ⟩ :=
    hbody s0 m0 hP hpc _ (jsrMem s0 m0) ⟨⟨rfl, rfl⟩, rfl⟩
  have hj1 : (jsrMem s0 m0).read (stackAddr s0.sp) = UInt16.hi (c + 2) := by
    simp only [jsrMem, read_write, Ne.symm (stackAddr_sub_one_ne s0.sp), ↓reduceIte, hpc]
  have hj2 : (jsrMem s0 m0).read (stackAddr (s0.sp - 1)) = UInt16.lo (c + 2) := by
    simp only [jsrMem, read_write, ↓reduceIte, hpc]
  refine ⟨1 + n + 1, ?_⟩
  rw [steps_add, steps_one, steps_add 1, steps_one, ej]
  dsimp only
  generalize steps n { s0 with sp := s0.sp - 1 - 1, pc := t } (jsrMem s0 m0) = r₂ at *
  obtain ⟨s₂, m₂, k⟩ := r₂
  dsimp only at hpcr hhr hrts hsp hhi hlo hQ ⊢
  have hr : m₂.read s₂.pc = 0x60 := hpcr ▸ hrts
  -- the RTS step, via T-CPU-6
  obtain ⟨hpc', hsp'⟩ := T_CPU_6_jsr_rts s0 m0 hh hj' s₂ m₂ hhr hr
    (by rw [ej]; exact hsp) (by rw [ej]; exact hhi.trans hj1.symm)
    (by rw [ej]; exact hlo.trans hj2.symm)
  rw [step_rts s₂ m₂ hhr hr] at hpc' hsp' ⊢
  dsimp only at hpc' hsp' ⊢
  rw [hpc', hsp', hpc]
  exact ⟨rfl, hQ⟩

/-- **Modular JSR/RTS rule with framing.** The callee has one spec, SP-balanced and modifying
only `F`; the two stacked return-address cells lie outside `F`. -/
theorem Triple.call_frame {P Q Pc Qc : Assn} {c t r : UInt16} {F : Region}
    (hjsr : ∀ s m, P s m → s.pc = c → s.halted = false ∧ m.read c = 0x20 ∧
      m.read16 (c + 1) = t ∧ c + 2 ≠ stackAddr s.sp ∧ c + 2 ≠ stackAddr (s.sp - 1))
    (hcallee : ∀ sp : UInt8,
      TripleM (fun s m => Pc s m ∧ s.sp = sp) t r (fun s m => Qc s m ∧ s.sp = sp) F)
    (hpre : ∀ s m, P s m → s.pc = c → Pc { s with sp := s.sp - 1 - 1, pc := t } (jsrMem s m))
    (hF : ∀ s m, P s m → ¬ F (stackAddr s.sp) ∧ ¬ F (stackAddr (s.sp - 1)))
    (hret : ∀ s m, Qc s m → s.halted = false ∧ m.read r = 0x60)
    (hpost : ∀ s0 m0 s m, P s0 m0 → s0.pc = c → Qc s m → s.sp = s0.sp - 1 - 1 →
      Agree F (jsrMem s0 m0) m → Q { s with pc := c + 3, sp := s0.sp } m) :
    Triple P c (c + 3) Q := by
  apply Triple.call hjsr
  intro s0 m0 hP hpc s m ⟨⟨hs, hm⟩, hpct⟩
  subst hs hm
  obtain ⟨n, h1, ⟨hQc, hsp⟩, hag⟩ := hcallee (s0.sp - 1 - 1) _ _ ⟨hpre s0 m0 hP hpc, rfl⟩ hpct
  obtain ⟨hF1, hF2⟩ := hF s0 m0 hP
  obtain ⟨hh, hr⟩ := hret _ _ hQc
  refine ⟨n, h1, hh, hr, hsp, ?_, ?_, hpost s0 m0 _ _ hP hpc hQc hsp hag⟩
  · rw [hag _ hF1]
    simp only [jsrMem, read_write, Ne.symm (stackAddr_sub_one_ne s0.sp), ↓reduceIte, hpc]
  · rw [hag _ hF2]
    simp only [jsrMem, read_write, ↓reduceIte, hpc]

end Nes.Hoare
