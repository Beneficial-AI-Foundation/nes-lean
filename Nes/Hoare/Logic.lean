import Nes.Cpu.Isa
import Nes.Cpu.Proofs.Stack

/-!
# `Nes.Hoare.Logic` — a Hoare logic over `Cpu.Isa`

A shallow embedding: assertions are Lean predicates on the CPU state and memory, programs are
the bytes in memory, and a triple is *defined* as a statement about `Cpu.step`. "Soundness"
therefore means: every rule (here and in `Nes.Hoare.Rules`) is a theorem about that semantic
definition, so a proved triple is a fact about the instruction-level spec that the emulator is
tested and proved against — nothing is axiomatised.

## Spec

* `Assn := State → Mem → Prop`. Code is just memory: `codeAt m base bytes` says the bytes are
  stored from `base` on (addresses wrap modulo 2^16).
* `steps n s m` runs `n` instructions with `Cpu.step`, returning the final state, memory and
  the total cycle count (`steps_add`: running `a + b` = running `a` then `b`, cycles add).
  `steps_eq_repeat` shows the state/memory part is literally `n`-fold iteration of `step`.
* `Reach P Q`: from every `P`-state, some finite number of steps reaches a `Q`-state. This is
  the primitive (total-correctness, existential fuel) notion.
* `Triple P entry exit Q` (`{P} entry ⟶ exit {Q}`): from every `P`-state at `pc = entry`, some
  number of steps reaches `pc = exit` with `Q`. Total correctness; the fuel is existential, so
  no step bound has to be stated. Intermediate visits to `exit` are allowed (the triple only
  claims *some* later visit), which is what makes sequencing compositional.
* `CTriple P entry exit Q c`: as `Triple`, and the run takes exactly `c` cycles.
* Separation: a `Region` is a set of addresses; `region lo len` is the `len` addresses from
  `lo` (wrapping). `Agree F m m'` says `m'` equals `m` outside `F`; `Indep R F` says the
  memory assertion `R` only reads cells outside `F` (it is invariant under `Agree F`).
  `TripleM P entry exit Q F` is a triple whose run additionally *modifies only* `F`: the final
  memory agrees with the initial one outside `F`. This is a semantic footprint (what the
  final memory looks like), not a syntactic analysis of the code; cells written and then
  restored are allowed. `TripleM.frame` (in `Rules`) is the frame rule.
* `PcFree P`: `P` does not look at `pc` (needed by the branch rules: a branch changes only `pc`).
* Single-instruction rules (weakest-precondition form): `Triple.of_step` / `CTriple.of_step` /
  `TripleM.of_step` reduce a one-instruction triple to a statement about `step s m`;
  `Triple.wp_step` is the WP triple `{(step s m) satisfies pc = exit ∧ Q} entry ⟶ exit {Q}`.
  `Triple.of_steps n` does the same for a fixed number of instructions (straight-line code).
-/

namespace Nes.Hoare

open Nes Nes.Cpu Nes.Cpu.Proofs

/-- Assertions over CPU state and memory. -/
abbrev Assn := State → Mem → Prop

/-! ## Running instructions -/

/-- Run `n` instructions; return the final state, memory and total cycles. -/
def steps : Nat → State → Mem → State × Mem × Nat
  | 0, s, m => (s, m, 0)
  | n + 1, s, m =>
    let r := step s m
    let r' := steps n r.1 r.2.1
    (r'.1, r'.2.1, r.2.2 + r'.2.2)

@[simp] theorem steps_zero (s : State) (m : Mem) : steps 0 s m = (s, m, 0) := rfl

theorem steps_succ (n : Nat) (s : State) (m : Mem) :
    steps (n + 1) s m =
      ((steps n (step s m).1 (step s m).2.1).1, (steps n (step s m).1 (step s m).2.1).2.1,
        (step s m).2.2 + (steps n (step s m).1 (step s m).2.1).2.2) := rfl

theorem steps_one (s : State) (m : Mem) : steps 1 s m = step s m := by
  simp [steps_succ]

theorem steps_add (a b : Nat) (s : State) (m : Mem) :
    steps (a + b) s m =
      ((steps b (steps a s m).1 (steps a s m).2.1).1,
        (steps b (steps a s m).1 (steps a s m).2.1).2.1,
        (steps a s m).2.2 + (steps b (steps a s m).1 (steps a s m).2.1).2.2) := by
  induction a generalizing s m with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_right_comm, steps_succ, ih, steps_succ]
    simp only [Nat.add_assoc]

/-- The state/memory part of `steps` is `n`-fold iteration of `step`. -/
theorem steps_eq_repeat (n : Nat) (s : State) (m : Mem) :
    ((steps n s m).1, (steps n s m).2.1) =
      Nat.repeat (fun r : State × Mem => ((step r.1 r.2).1, (step r.1 r.2).2.1)) n (s, m) := by
  induction n generalizing s m with
  | zero => rfl
  | succ n ih =>
    rw [steps_succ]
    simp only
    rw [ih]
    -- `Nat.repeat f (n+1) x = f (Nat.repeat f n x)`: iterate on the other side
    clear ih
    induction n generalizing s m with
    | zero => rfl
    | succ n ih2 => simp only [Nat.repeat] at ih2 ⊢; rw [ih2]

/-! ## Code in memory -/

/-- `bytes` are stored at `base, base+1, …` (wrapping modulo 2^16). -/
def codeAt (m : Mem) (base : UInt16) : List UInt8 → Prop
  | [] => True
  | b :: bs => m.read base = b ∧ codeAt m (base + 1) bs

@[simp] theorem codeAt_nil (m : Mem) (base : UInt16) : codeAt m base [] = True := rfl

@[simp] theorem codeAt_cons (m : Mem) (base : UInt16) (b : UInt8) (bs : List UInt8) :
    codeAt m base (b :: bs) = (m.read base = b ∧ codeAt m (base + 1) bs) := rfl

/-! ## Separation: regions, agreement, independence -/

/-- A set of addresses. -/
abbrev Region := UInt16 → Prop

/-- The `len` addresses `lo, lo+1, …, lo+len-1` (wrapping). -/
def region (lo : UInt16) (len : Nat) : Region := fun a => (a - lo).toNat < len

/-- The stack page `$0100–$01FF`. -/
def stackPage : Region := region 0x100 256

/-- Union of regions. -/
def Region.union (A B : Region) : Region := fun a => A a ∨ B a

/-- `A ⊆ B`. -/
def Region.Sub (A B : Region) : Prop := ∀ a, A a → B a

/-- Disjoint regions. -/
def Region.Disjoint (A B : Region) : Prop := ∀ a, A a → B a → False

/-- `m'` agrees with `m` outside `F` (everything not in `F` is unchanged). -/
def Agree (F : Region) (m m' : Mem) : Prop := ∀ a, ¬ F a → m'.read a = m.read a

/-- The memory assertion `R` reads only cells outside `F`. -/
def Indep (R : Mem → Prop) (F : Region) : Prop := ∀ m m', Agree F m m' → R m → R m'

/-- The assertion does not depend on `pc`. -/
def PcFree (P : Assn) : Prop := ∀ s m (pc : UInt16), P s m → P { s with pc := pc } m

theorem Agree.refl (F : Region) (m : Mem) : Agree F m m := fun _ _ => rfl

theorem Agree.trans {F : Region} {m₁ m₂ m₃ : Mem} (h₁ : Agree F m₁ m₂) (h₂ : Agree F m₂ m₃) :
    Agree F m₁ m₃ := fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem Agree.mono {F G : Region} {m m' : Mem} (hFG : Region.Sub F G) (h : Agree F m m') :
    Agree G m m' := fun a ha => h a (fun hf => ha (hFG a hf))

theorem Agree.union_left {F G : Region} {m m' : Mem} (h : Agree F m m') :
    Agree (F.union G) m m' := h.mono (fun _ h => Or.inl h)

theorem Agree.union_right {F G : Region} {m m' : Mem} (h : Agree G m m') :
    Agree (F.union G) m m' := h.mono (fun _ h => Or.inr h)

/-- Read-after-write on `Mem`. -/
theorem read_write (m : Mem) (a b : UInt16) (v : UInt8) :
    (m.write a v).read b = if a = b then v else m.read b := by
  simp only [Mem.read, Mem.write, Vector.getElem_set, UInt16.toNat_inj]

/-- A write inside the footprint keeps agreement. -/
theorem Agree.write {F : Region} {m m' : Mem} {a : UInt16} (v : UInt8) (ha : F a)
    (h : Agree F m m') : Agree F m (m'.write a v) := by
  intro b hb
  rw [read_write]
  have : a ≠ b := fun e => hb (e ▸ ha)
  simp only [this, ↓reduceIte]
  exact h b hb

theorem Agree.write_self {F : Region} {m : Mem} {a : UInt16} (v : UInt8) (ha : F a) :
    Agree F m (m.write a v) := (Agree.refl F m).write v ha

/-- `codeAt` is independent of any footprint disjoint from the code. -/
theorem codeAt_indep (base : UInt16) (bytes : List UInt8) (F : Region)
    (h : ∀ i, i < bytes.length → ¬ F (base + UInt16.ofNat i)) :
    Indep (fun m => codeAt m base bytes) F := by
  intro m m' hag hc
  induction bytes generalizing base with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨h0, hrest⟩ := hc
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp)
      rw [show base + UInt16.ofNat 0 = base from by simp] at this
      rw [hag base this, h0]
    · apply ih (base + 1) _ hrest
      intro i hi
      have := h (i + 1) (by simp; omega)
      rwa [show base + UInt16.ofNat (i + 1) = base + 1 + UInt16.ofNat i from by
        rw [_root_.UInt16.ofNat_add, _root_.UInt16.add_assoc, _root_.UInt16.add_comm (UInt16.ofNat i)]
        rfl] at this

/-! ## Reachability and triples -/

/-- From every `P`-state, finitely many instructions reach a `Q`-state. -/
def Reach (P Q : Assn) : Prop :=
  ∀ s m, P s m → ∃ n, Q (steps n s m).1 (steps n s m).2.1

/-- `{P} entry ⟶ exit {Q}`: total correctness, existential fuel. -/
def Triple (P : Assn) (entry exit : UInt16) (Q : Assn) : Prop :=
  Reach (fun s m => P s m ∧ s.pc = entry) (fun s m => s.pc = exit ∧ Q s m)

/-- `Triple` that also fixes the cycle count of the run to exactly `c`. -/
def CTriple (P : Assn) (entry exit : UInt16) (Q : Assn) (c : Nat) : Prop :=
  ∀ s m, P s m → s.pc = entry →
    ∃ n, (steps n s m).1.pc = exit ∧ Q (steps n s m).1 (steps n s m).2.1 ∧ (steps n s m).2.2 = c

/-- `Triple` whose run modifies only the region `F` (final memory agrees with the initial one
outside `F`). -/
def TripleM (P : Assn) (entry exit : UInt16) (Q : Assn) (F : Region) : Prop :=
  ∀ s m, P s m → s.pc = entry →
    ∃ n, (steps n s m).1.pc = exit ∧ Q (steps n s m).1 (steps n s m).2.1 ∧
      Agree F m (steps n s m).2.1

/-! ## Soundness, unfolded -/

/-- What a triple means operationally: an actual `Cpu.step` run (by `steps_eq_repeat`, the
`n`-fold iterate of `step`) from the precondition to the exit with the postcondition. -/
theorem Triple.sound {P Q : Assn} {e x : UInt16} (h : Triple P e x Q) {s : State} {m : Mem}
    (hP : P s m) (hpc : s.pc = e) :
    ∃ n, (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1 :=
  h s m ⟨hP, hpc⟩

theorem Triple.intro {P Q : Assn} {e x : UInt16}
    (h : ∀ s m, P s m → s.pc = e → ∃ n, (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1) :
    Triple P e x Q := fun s m ⟨hP, hpc⟩ => h s m hP hpc

theorem CTriple.toTriple {P Q : Assn} {e x : UInt16} {c : Nat} (h : CTriple P e x Q c) :
    Triple P e x Q := fun s m ⟨hP, hpc⟩ =>
  let ⟨n, h1, h2, _⟩ := h s m hP hpc; ⟨n, h1, h2⟩

theorem TripleM.toTriple {P Q : Assn} {e x : UInt16} {F : Region} (h : TripleM P e x Q F) :
    Triple P e x Q := fun s m ⟨hP, hpc⟩ =>
  let ⟨n, h1, h2, _⟩ := h s m hP hpc; ⟨n, h1, h2⟩

/-- A `Triple` that remembers the initial memory `m0` as a ghost and proves agreement outside
`F` is the same thing as a `TripleM`. -/
theorem TripleM.iff_ghost {P Q : Assn} {e x : UInt16} {F : Region} :
    TripleM P e x Q F ↔
      ∀ m0, Triple (fun s m => P s m ∧ m = m0) e x (fun s m => Q s m ∧ Agree F m0 m) := by
  constructor
  · intro h m0 s m ⟨⟨hP, hm⟩, hpc⟩
    subst hm
    obtain ⟨n, h1, h2, h3⟩ := h s m hP hpc
    exact ⟨n, h1, h2, h3⟩
  · intro h s m hP hpc
    obtain ⟨n, h1, h2, h3⟩ := h m s m ⟨⟨hP, rfl⟩, hpc⟩
    exact ⟨n, h1, h2, h3⟩

/-! ## Single-instruction rules -/

theorem Triple.of_steps {P Q : Assn} {e x : UInt16} (n : Nat)
    (h : ∀ s m, P s m → s.pc = e → (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1) :
    Triple P e x Q := fun s m ⟨hP, hpc⟩ => ⟨n, h s m hP hpc⟩

theorem Triple.of_step {P Q : Assn} {e x : UInt16}
    (h : ∀ s m, P s m → s.pc = e → (step s m).1.pc = x ∧ Q (step s m).1 (step s m).2.1) :
    Triple P e x Q := Triple.of_steps 1 (by simpa only [steps_one] using h)

/-- Weakest-precondition triple of one instruction. -/
theorem Triple.wp_step (e x : UInt16) (Q : Assn) :
    Triple (fun s m => (step s m).1.pc = x ∧ Q (step s m).1 (step s m).2.1) e x Q :=
  Triple.of_step fun _ _ h _ => h

theorem CTriple.of_steps {P Q : Assn} {e x : UInt16} {c : Nat} (n : Nat)
    (h : ∀ s m, P s m → s.pc = e →
      (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1 ∧ (steps n s m).2.2 = c) :
    CTriple P e x Q c := fun s m hP hpc => ⟨n, h s m hP hpc⟩

theorem CTriple.of_step {P Q : Assn} {e x : UInt16} {c : Nat}
    (h : ∀ s m, P s m → s.pc = e →
      (step s m).1.pc = x ∧ Q (step s m).1 (step s m).2.1 ∧ (step s m).2.2 = c) :
    CTriple P e x Q c := CTriple.of_steps 1 (by simpa only [steps_one] using h)

theorem TripleM.of_steps {P Q : Assn} {e x : UInt16} {F : Region} (n : Nat)
    (h : ∀ s m, P s m → s.pc = e →
      (steps n s m).1.pc = x ∧ Q (steps n s m).1 (steps n s m).2.1 ∧ Agree F m (steps n s m).2.1) :
    TripleM P e x Q F := fun s m hP hpc => ⟨n, h s m hP hpc⟩

theorem TripleM.of_step {P Q : Assn} {e x : UInt16} {F : Region}
    (h : ∀ s m, P s m → s.pc = e →
      (step s m).1.pc = x ∧ Q (step s m).1 (step s m).2.1 ∧ Agree F m (step s m).2.1) :
    TripleM P e x Q F := TripleM.of_steps 1 (by simpa only [steps_one] using h)

/-! ## Decoded opcodes

`dec_NN : decode 0xNN = …` for all 256 opcodes (each by `decide`, generated from the table in
`Nes.Cpu.Decode`). `simp` indexes them by the literal, so `hoare_step` passes all of them and
only the one matching the opcode byte fires. -/

theorem dec_00 : decode 0x00 = ⟨.BRK, .imp, 7, false, true⟩ := by decide
theorem dec_01 : decode 0x01 = ⟨.ORA, .indx, 6, false, true⟩ := by decide
theorem dec_02 : decode 0x02 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_03 : decode 0x03 = ⟨.SLO, .indx, 8, false, false⟩ := by decide
theorem dec_04 : decode 0x04 = ⟨.NOP, .zp, 3, false, false⟩ := by decide
theorem dec_05 : decode 0x05 = ⟨.ORA, .zp, 3, false, true⟩ := by decide
theorem dec_06 : decode 0x06 = ⟨.ASL, .zp, 5, false, true⟩ := by decide
theorem dec_07 : decode 0x07 = ⟨.SLO, .zp, 5, false, false⟩ := by decide
theorem dec_08 : decode 0x08 = ⟨.PHP, .imp, 3, false, true⟩ := by decide
theorem dec_09 : decode 0x09 = ⟨.ORA, .imm, 2, false, true⟩ := by decide
theorem dec_0A : decode 0x0A = ⟨.ASL, .acc, 2, false, true⟩ := by decide
theorem dec_0B : decode 0x0B = ⟨.ANC, .imm, 2, false, false⟩ := by decide
theorem dec_0C : decode 0x0C = ⟨.NOP, .abs, 4, false, false⟩ := by decide
theorem dec_0D : decode 0x0D = ⟨.ORA, .abs, 4, false, true⟩ := by decide
theorem dec_0E : decode 0x0E = ⟨.ASL, .abs, 6, false, true⟩ := by decide
theorem dec_0F : decode 0x0F = ⟨.SLO, .abs, 6, false, false⟩ := by decide
theorem dec_10 : decode 0x10 = ⟨.BPL, .rel, 2, false, true⟩ := by decide
theorem dec_11 : decode 0x11 = ⟨.ORA, .indy, 5, true, true⟩ := by decide
theorem dec_12 : decode 0x12 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_13 : decode 0x13 = ⟨.SLO, .indy, 8, false, false⟩ := by decide
theorem dec_14 : decode 0x14 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_15 : decode 0x15 = ⟨.ORA, .zpx, 4, false, true⟩ := by decide
theorem dec_16 : decode 0x16 = ⟨.ASL, .zpx, 6, false, true⟩ := by decide
theorem dec_17 : decode 0x17 = ⟨.SLO, .zpx, 6, false, false⟩ := by decide
theorem dec_18 : decode 0x18 = ⟨.CLC, .imp, 2, false, true⟩ := by decide
theorem dec_19 : decode 0x19 = ⟨.ORA, .absy, 4, true, true⟩ := by decide
theorem dec_1A : decode 0x1A = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_1B : decode 0x1B = ⟨.SLO, .absy, 7, false, false⟩ := by decide
theorem dec_1C : decode 0x1C = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_1D : decode 0x1D = ⟨.ORA, .absx, 4, true, true⟩ := by decide
theorem dec_1E : decode 0x1E = ⟨.ASL, .absx, 7, false, true⟩ := by decide
theorem dec_1F : decode 0x1F = ⟨.SLO, .absx, 7, false, false⟩ := by decide
theorem dec_20 : decode 0x20 = ⟨.JSR, .abs, 6, false, true⟩ := by decide
theorem dec_21 : decode 0x21 = ⟨.AND, .indx, 6, false, true⟩ := by decide
theorem dec_22 : decode 0x22 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_23 : decode 0x23 = ⟨.RLA, .indx, 8, false, false⟩ := by decide
theorem dec_24 : decode 0x24 = ⟨.BIT, .zp, 3, false, true⟩ := by decide
theorem dec_25 : decode 0x25 = ⟨.AND, .zp, 3, false, true⟩ := by decide
theorem dec_26 : decode 0x26 = ⟨.ROL, .zp, 5, false, true⟩ := by decide
theorem dec_27 : decode 0x27 = ⟨.RLA, .zp, 5, false, false⟩ := by decide
theorem dec_28 : decode 0x28 = ⟨.PLP, .imp, 4, false, true⟩ := by decide
theorem dec_29 : decode 0x29 = ⟨.AND, .imm, 2, false, true⟩ := by decide
theorem dec_2A : decode 0x2A = ⟨.ROL, .acc, 2, false, true⟩ := by decide
theorem dec_2B : decode 0x2B = ⟨.ANC, .imm, 2, false, false⟩ := by decide
theorem dec_2C : decode 0x2C = ⟨.BIT, .abs, 4, false, true⟩ := by decide
theorem dec_2D : decode 0x2D = ⟨.AND, .abs, 4, false, true⟩ := by decide
theorem dec_2E : decode 0x2E = ⟨.ROL, .abs, 6, false, true⟩ := by decide
theorem dec_2F : decode 0x2F = ⟨.RLA, .abs, 6, false, false⟩ := by decide
theorem dec_30 : decode 0x30 = ⟨.BMI, .rel, 2, false, true⟩ := by decide
theorem dec_31 : decode 0x31 = ⟨.AND, .indy, 5, true, true⟩ := by decide
theorem dec_32 : decode 0x32 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_33 : decode 0x33 = ⟨.RLA, .indy, 8, false, false⟩ := by decide
theorem dec_34 : decode 0x34 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_35 : decode 0x35 = ⟨.AND, .zpx, 4, false, true⟩ := by decide
theorem dec_36 : decode 0x36 = ⟨.ROL, .zpx, 6, false, true⟩ := by decide
theorem dec_37 : decode 0x37 = ⟨.RLA, .zpx, 6, false, false⟩ := by decide
theorem dec_38 : decode 0x38 = ⟨.SEC, .imp, 2, false, true⟩ := by decide
theorem dec_39 : decode 0x39 = ⟨.AND, .absy, 4, true, true⟩ := by decide
theorem dec_3A : decode 0x3A = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_3B : decode 0x3B = ⟨.RLA, .absy, 7, false, false⟩ := by decide
theorem dec_3C : decode 0x3C = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_3D : decode 0x3D = ⟨.AND, .absx, 4, true, true⟩ := by decide
theorem dec_3E : decode 0x3E = ⟨.ROL, .absx, 7, false, true⟩ := by decide
theorem dec_3F : decode 0x3F = ⟨.RLA, .absx, 7, false, false⟩ := by decide
theorem dec_40 : decode 0x40 = ⟨.RTI, .imp, 6, false, true⟩ := by decide
theorem dec_41 : decode 0x41 = ⟨.EOR, .indx, 6, false, true⟩ := by decide
theorem dec_42 : decode 0x42 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_43 : decode 0x43 = ⟨.SRE, .indx, 8, false, false⟩ := by decide
theorem dec_44 : decode 0x44 = ⟨.NOP, .zp, 3, false, false⟩ := by decide
theorem dec_45 : decode 0x45 = ⟨.EOR, .zp, 3, false, true⟩ := by decide
theorem dec_46 : decode 0x46 = ⟨.LSR, .zp, 5, false, true⟩ := by decide
theorem dec_47 : decode 0x47 = ⟨.SRE, .zp, 5, false, false⟩ := by decide
theorem dec_48 : decode 0x48 = ⟨.PHA, .imp, 3, false, true⟩ := by decide
theorem dec_49 : decode 0x49 = ⟨.EOR, .imm, 2, false, true⟩ := by decide
theorem dec_4A : decode 0x4A = ⟨.LSR, .acc, 2, false, true⟩ := by decide
theorem dec_4B : decode 0x4B = ⟨.ALR, .imm, 2, false, false⟩ := by decide
theorem dec_4C : decode 0x4C = ⟨.JMP, .abs, 3, false, true⟩ := by decide
theorem dec_4D : decode 0x4D = ⟨.EOR, .abs, 4, false, true⟩ := by decide
theorem dec_4E : decode 0x4E = ⟨.LSR, .abs, 6, false, true⟩ := by decide
theorem dec_4F : decode 0x4F = ⟨.SRE, .abs, 6, false, false⟩ := by decide
theorem dec_50 : decode 0x50 = ⟨.BVC, .rel, 2, false, true⟩ := by decide
theorem dec_51 : decode 0x51 = ⟨.EOR, .indy, 5, true, true⟩ := by decide
theorem dec_52 : decode 0x52 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_53 : decode 0x53 = ⟨.SRE, .indy, 8, false, false⟩ := by decide
theorem dec_54 : decode 0x54 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_55 : decode 0x55 = ⟨.EOR, .zpx, 4, false, true⟩ := by decide
theorem dec_56 : decode 0x56 = ⟨.LSR, .zpx, 6, false, true⟩ := by decide
theorem dec_57 : decode 0x57 = ⟨.SRE, .zpx, 6, false, false⟩ := by decide
theorem dec_58 : decode 0x58 = ⟨.CLI, .imp, 2, false, true⟩ := by decide
theorem dec_59 : decode 0x59 = ⟨.EOR, .absy, 4, true, true⟩ := by decide
theorem dec_5A : decode 0x5A = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_5B : decode 0x5B = ⟨.SRE, .absy, 7, false, false⟩ := by decide
theorem dec_5C : decode 0x5C = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_5D : decode 0x5D = ⟨.EOR, .absx, 4, true, true⟩ := by decide
theorem dec_5E : decode 0x5E = ⟨.LSR, .absx, 7, false, true⟩ := by decide
theorem dec_5F : decode 0x5F = ⟨.SRE, .absx, 7, false, false⟩ := by decide
theorem dec_60 : decode 0x60 = ⟨.RTS, .imp, 6, false, true⟩ := by decide
theorem dec_61 : decode 0x61 = ⟨.ADC, .indx, 6, false, true⟩ := by decide
theorem dec_62 : decode 0x62 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_63 : decode 0x63 = ⟨.RRA, .indx, 8, false, false⟩ := by decide
theorem dec_64 : decode 0x64 = ⟨.NOP, .zp, 3, false, false⟩ := by decide
theorem dec_65 : decode 0x65 = ⟨.ADC, .zp, 3, false, true⟩ := by decide
theorem dec_66 : decode 0x66 = ⟨.ROR, .zp, 5, false, true⟩ := by decide
theorem dec_67 : decode 0x67 = ⟨.RRA, .zp, 5, false, false⟩ := by decide
theorem dec_68 : decode 0x68 = ⟨.PLA, .imp, 4, false, true⟩ := by decide
theorem dec_69 : decode 0x69 = ⟨.ADC, .imm, 2, false, true⟩ := by decide
theorem dec_6A : decode 0x6A = ⟨.ROR, .acc, 2, false, true⟩ := by decide
theorem dec_6B : decode 0x6B = ⟨.ARR, .imm, 2, false, false⟩ := by decide
theorem dec_6C : decode 0x6C = ⟨.JMP, .ind, 5, false, true⟩ := by decide
theorem dec_6D : decode 0x6D = ⟨.ADC, .abs, 4, false, true⟩ := by decide
theorem dec_6E : decode 0x6E = ⟨.ROR, .abs, 6, false, true⟩ := by decide
theorem dec_6F : decode 0x6F = ⟨.RRA, .abs, 6, false, false⟩ := by decide
theorem dec_70 : decode 0x70 = ⟨.BVS, .rel, 2, false, true⟩ := by decide
theorem dec_71 : decode 0x71 = ⟨.ADC, .indy, 5, true, true⟩ := by decide
theorem dec_72 : decode 0x72 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_73 : decode 0x73 = ⟨.RRA, .indy, 8, false, false⟩ := by decide
theorem dec_74 : decode 0x74 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_75 : decode 0x75 = ⟨.ADC, .zpx, 4, false, true⟩ := by decide
theorem dec_76 : decode 0x76 = ⟨.ROR, .zpx, 6, false, true⟩ := by decide
theorem dec_77 : decode 0x77 = ⟨.RRA, .zpx, 6, false, false⟩ := by decide
theorem dec_78 : decode 0x78 = ⟨.SEI, .imp, 2, false, true⟩ := by decide
theorem dec_79 : decode 0x79 = ⟨.ADC, .absy, 4, true, true⟩ := by decide
theorem dec_7A : decode 0x7A = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_7B : decode 0x7B = ⟨.RRA, .absy, 7, false, false⟩ := by decide
theorem dec_7C : decode 0x7C = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_7D : decode 0x7D = ⟨.ADC, .absx, 4, true, true⟩ := by decide
theorem dec_7E : decode 0x7E = ⟨.ROR, .absx, 7, false, true⟩ := by decide
theorem dec_7F : decode 0x7F = ⟨.RRA, .absx, 7, false, false⟩ := by decide
theorem dec_80 : decode 0x80 = ⟨.NOP, .imm, 2, false, false⟩ := by decide
theorem dec_81 : decode 0x81 = ⟨.STA, .indx, 6, false, true⟩ := by decide
theorem dec_82 : decode 0x82 = ⟨.NOP, .imm, 2, false, false⟩ := by decide
theorem dec_83 : decode 0x83 = ⟨.SAX, .indx, 6, false, false⟩ := by decide
theorem dec_84 : decode 0x84 = ⟨.STY, .zp, 3, false, true⟩ := by decide
theorem dec_85 : decode 0x85 = ⟨.STA, .zp, 3, false, true⟩ := by decide
theorem dec_86 : decode 0x86 = ⟨.STX, .zp, 3, false, true⟩ := by decide
theorem dec_87 : decode 0x87 = ⟨.SAX, .zp, 3, false, false⟩ := by decide
theorem dec_88 : decode 0x88 = ⟨.DEY, .imp, 2, false, true⟩ := by decide
theorem dec_89 : decode 0x89 = ⟨.NOP, .imm, 2, false, false⟩ := by decide
theorem dec_8A : decode 0x8A = ⟨.TXA, .imp, 2, false, true⟩ := by decide
theorem dec_8B : decode 0x8B = ⟨.XAA, .imm, 2, false, false⟩ := by decide
theorem dec_8C : decode 0x8C = ⟨.STY, .abs, 4, false, true⟩ := by decide
theorem dec_8D : decode 0x8D = ⟨.STA, .abs, 4, false, true⟩ := by decide
theorem dec_8E : decode 0x8E = ⟨.STX, .abs, 4, false, true⟩ := by decide
theorem dec_8F : decode 0x8F = ⟨.SAX, .abs, 4, false, false⟩ := by decide
theorem dec_90 : decode 0x90 = ⟨.BCC, .rel, 2, false, true⟩ := by decide
theorem dec_91 : decode 0x91 = ⟨.STA, .indy, 6, false, true⟩ := by decide
theorem dec_92 : decode 0x92 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_93 : decode 0x93 = ⟨.AHX, .indy, 6, false, false⟩ := by decide
theorem dec_94 : decode 0x94 = ⟨.STY, .zpx, 4, false, true⟩ := by decide
theorem dec_95 : decode 0x95 = ⟨.STA, .zpx, 4, false, true⟩ := by decide
theorem dec_96 : decode 0x96 = ⟨.STX, .zpy, 4, false, true⟩ := by decide
theorem dec_97 : decode 0x97 = ⟨.SAX, .zpy, 4, false, false⟩ := by decide
theorem dec_98 : decode 0x98 = ⟨.TYA, .imp, 2, false, true⟩ := by decide
theorem dec_99 : decode 0x99 = ⟨.STA, .absy, 5, false, true⟩ := by decide
theorem dec_9A : decode 0x9A = ⟨.TXS, .imp, 2, false, true⟩ := by decide
theorem dec_9B : decode 0x9B = ⟨.TAS, .absy, 5, false, false⟩ := by decide
theorem dec_9C : decode 0x9C = ⟨.SHY, .absx, 5, false, false⟩ := by decide
theorem dec_9D : decode 0x9D = ⟨.STA, .absx, 5, false, true⟩ := by decide
theorem dec_9E : decode 0x9E = ⟨.SHX, .absy, 5, false, false⟩ := by decide
theorem dec_9F : decode 0x9F = ⟨.AHX, .absy, 5, false, false⟩ := by decide
theorem dec_A0 : decode 0xA0 = ⟨.LDY, .imm, 2, false, true⟩ := by decide
theorem dec_A1 : decode 0xA1 = ⟨.LDA, .indx, 6, false, true⟩ := by decide
theorem dec_A2 : decode 0xA2 = ⟨.LDX, .imm, 2, false, true⟩ := by decide
theorem dec_A3 : decode 0xA3 = ⟨.LAX, .indx, 6, false, false⟩ := by decide
theorem dec_A4 : decode 0xA4 = ⟨.LDY, .zp, 3, false, true⟩ := by decide
theorem dec_A5 : decode 0xA5 = ⟨.LDA, .zp, 3, false, true⟩ := by decide
theorem dec_A6 : decode 0xA6 = ⟨.LDX, .zp, 3, false, true⟩ := by decide
theorem dec_A7 : decode 0xA7 = ⟨.LAX, .zp, 3, false, false⟩ := by decide
theorem dec_A8 : decode 0xA8 = ⟨.TAY, .imp, 2, false, true⟩ := by decide
theorem dec_A9 : decode 0xA9 = ⟨.LDA, .imm, 2, false, true⟩ := by decide
theorem dec_AA : decode 0xAA = ⟨.TAX, .imp, 2, false, true⟩ := by decide
theorem dec_AB : decode 0xAB = ⟨.LAX, .imm, 2, false, false⟩ := by decide
theorem dec_AC : decode 0xAC = ⟨.LDY, .abs, 4, false, true⟩ := by decide
theorem dec_AD : decode 0xAD = ⟨.LDA, .abs, 4, false, true⟩ := by decide
theorem dec_AE : decode 0xAE = ⟨.LDX, .abs, 4, false, true⟩ := by decide
theorem dec_AF : decode 0xAF = ⟨.LAX, .abs, 4, false, false⟩ := by decide
theorem dec_B0 : decode 0xB0 = ⟨.BCS, .rel, 2, false, true⟩ := by decide
theorem dec_B1 : decode 0xB1 = ⟨.LDA, .indy, 5, true, true⟩ := by decide
theorem dec_B2 : decode 0xB2 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_B3 : decode 0xB3 = ⟨.LAX, .indy, 5, true, false⟩ := by decide
theorem dec_B4 : decode 0xB4 = ⟨.LDY, .zpx, 4, false, true⟩ := by decide
theorem dec_B5 : decode 0xB5 = ⟨.LDA, .zpx, 4, false, true⟩ := by decide
theorem dec_B6 : decode 0xB6 = ⟨.LDX, .zpy, 4, false, true⟩ := by decide
theorem dec_B7 : decode 0xB7 = ⟨.LAX, .zpy, 4, false, false⟩ := by decide
theorem dec_B8 : decode 0xB8 = ⟨.CLV, .imp, 2, false, true⟩ := by decide
theorem dec_B9 : decode 0xB9 = ⟨.LDA, .absy, 4, true, true⟩ := by decide
theorem dec_BA : decode 0xBA = ⟨.TSX, .imp, 2, false, true⟩ := by decide
theorem dec_BB : decode 0xBB = ⟨.LAS, .absy, 4, true, false⟩ := by decide
theorem dec_BC : decode 0xBC = ⟨.LDY, .absx, 4, true, true⟩ := by decide
theorem dec_BD : decode 0xBD = ⟨.LDA, .absx, 4, true, true⟩ := by decide
theorem dec_BE : decode 0xBE = ⟨.LDX, .absy, 4, true, true⟩ := by decide
theorem dec_BF : decode 0xBF = ⟨.LAX, .absy, 4, true, false⟩ := by decide
theorem dec_C0 : decode 0xC0 = ⟨.CPY, .imm, 2, false, true⟩ := by decide
theorem dec_C1 : decode 0xC1 = ⟨.CMP, .indx, 6, false, true⟩ := by decide
theorem dec_C2 : decode 0xC2 = ⟨.NOP, .imm, 2, false, false⟩ := by decide
theorem dec_C3 : decode 0xC3 = ⟨.DCP, .indx, 8, false, false⟩ := by decide
theorem dec_C4 : decode 0xC4 = ⟨.CPY, .zp, 3, false, true⟩ := by decide
theorem dec_C5 : decode 0xC5 = ⟨.CMP, .zp, 3, false, true⟩ := by decide
theorem dec_C6 : decode 0xC6 = ⟨.DEC, .zp, 5, false, true⟩ := by decide
theorem dec_C7 : decode 0xC7 = ⟨.DCP, .zp, 5, false, false⟩ := by decide
theorem dec_C8 : decode 0xC8 = ⟨.INY, .imp, 2, false, true⟩ := by decide
theorem dec_C9 : decode 0xC9 = ⟨.CMP, .imm, 2, false, true⟩ := by decide
theorem dec_CA : decode 0xCA = ⟨.DEX, .imp, 2, false, true⟩ := by decide
theorem dec_CB : decode 0xCB = ⟨.SBX, .imm, 2, false, false⟩ := by decide
theorem dec_CC : decode 0xCC = ⟨.CPY, .abs, 4, false, true⟩ := by decide
theorem dec_CD : decode 0xCD = ⟨.CMP, .abs, 4, false, true⟩ := by decide
theorem dec_CE : decode 0xCE = ⟨.DEC, .abs, 6, false, true⟩ := by decide
theorem dec_CF : decode 0xCF = ⟨.DCP, .abs, 6, false, false⟩ := by decide
theorem dec_D0 : decode 0xD0 = ⟨.BNE, .rel, 2, false, true⟩ := by decide
theorem dec_D1 : decode 0xD1 = ⟨.CMP, .indy, 5, true, true⟩ := by decide
theorem dec_D2 : decode 0xD2 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_D3 : decode 0xD3 = ⟨.DCP, .indy, 8, false, false⟩ := by decide
theorem dec_D4 : decode 0xD4 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_D5 : decode 0xD5 = ⟨.CMP, .zpx, 4, false, true⟩ := by decide
theorem dec_D6 : decode 0xD6 = ⟨.DEC, .zpx, 6, false, true⟩ := by decide
theorem dec_D7 : decode 0xD7 = ⟨.DCP, .zpx, 6, false, false⟩ := by decide
theorem dec_D8 : decode 0xD8 = ⟨.CLD, .imp, 2, false, true⟩ := by decide
theorem dec_D9 : decode 0xD9 = ⟨.CMP, .absy, 4, true, true⟩ := by decide
theorem dec_DA : decode 0xDA = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_DB : decode 0xDB = ⟨.DCP, .absy, 7, false, false⟩ := by decide
theorem dec_DC : decode 0xDC = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_DD : decode 0xDD = ⟨.CMP, .absx, 4, true, true⟩ := by decide
theorem dec_DE : decode 0xDE = ⟨.DEC, .absx, 7, false, true⟩ := by decide
theorem dec_DF : decode 0xDF = ⟨.DCP, .absx, 7, false, false⟩ := by decide
theorem dec_E0 : decode 0xE0 = ⟨.CPX, .imm, 2, false, true⟩ := by decide
theorem dec_E1 : decode 0xE1 = ⟨.SBC, .indx, 6, false, true⟩ := by decide
theorem dec_E2 : decode 0xE2 = ⟨.NOP, .imm, 2, false, false⟩ := by decide
theorem dec_E3 : decode 0xE3 = ⟨.ISC, .indx, 8, false, false⟩ := by decide
theorem dec_E4 : decode 0xE4 = ⟨.CPX, .zp, 3, false, true⟩ := by decide
theorem dec_E5 : decode 0xE5 = ⟨.SBC, .zp, 3, false, true⟩ := by decide
theorem dec_E6 : decode 0xE6 = ⟨.INC, .zp, 5, false, true⟩ := by decide
theorem dec_E7 : decode 0xE7 = ⟨.ISC, .zp, 5, false, false⟩ := by decide
theorem dec_E8 : decode 0xE8 = ⟨.INX, .imp, 2, false, true⟩ := by decide
theorem dec_E9 : decode 0xE9 = ⟨.SBC, .imm, 2, false, true⟩ := by decide
theorem dec_EA : decode 0xEA = ⟨.NOP, .imp, 2, false, true⟩ := by decide
theorem dec_EB : decode 0xEB = ⟨.SBC, .imm, 2, false, false⟩ := by decide
theorem dec_EC : decode 0xEC = ⟨.CPX, .abs, 4, false, true⟩ := by decide
theorem dec_ED : decode 0xED = ⟨.SBC, .abs, 4, false, true⟩ := by decide
theorem dec_EE : decode 0xEE = ⟨.INC, .abs, 6, false, true⟩ := by decide
theorem dec_EF : decode 0xEF = ⟨.ISC, .abs, 6, false, false⟩ := by decide
theorem dec_F0 : decode 0xF0 = ⟨.BEQ, .rel, 2, false, true⟩ := by decide
theorem dec_F1 : decode 0xF1 = ⟨.SBC, .indy, 5, true, true⟩ := by decide
theorem dec_F2 : decode 0xF2 = ⟨.JAM, .imp, 3, false, false⟩ := by decide
theorem dec_F3 : decode 0xF3 = ⟨.ISC, .indy, 8, false, false⟩ := by decide
theorem dec_F4 : decode 0xF4 = ⟨.NOP, .zpx, 4, false, false⟩ := by decide
theorem dec_F5 : decode 0xF5 = ⟨.SBC, .zpx, 4, false, true⟩ := by decide
theorem dec_F6 : decode 0xF6 = ⟨.INC, .zpx, 6, false, true⟩ := by decide
theorem dec_F7 : decode 0xF7 = ⟨.ISC, .zpx, 6, false, false⟩ := by decide
theorem dec_F8 : decode 0xF8 = ⟨.SED, .imp, 2, false, true⟩ := by decide
theorem dec_F9 : decode 0xF9 = ⟨.SBC, .absy, 4, true, true⟩ := by decide
theorem dec_FA : decode 0xFA = ⟨.NOP, .imp, 2, false, false⟩ := by decide
theorem dec_FB : decode 0xFB = ⟨.ISC, .absy, 7, false, false⟩ := by decide
theorem dec_FC : decode 0xFC = ⟨.NOP, .absx, 4, true, false⟩ := by decide
theorem dec_FD : decode 0xFD = ⟨.SBC, .absx, 4, true, true⟩ := by decide
theorem dec_FE : decode 0xFE = ⟨.INC, .absx, 7, false, true⟩ := by decide
theorem dec_FF : decode 0xFF = ⟨.ISC, .absx, 7, false, false⟩ := by decide

end Nes.Hoare
