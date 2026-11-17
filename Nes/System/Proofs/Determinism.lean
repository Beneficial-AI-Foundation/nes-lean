import Nes.System.SaveState

/-!
# T-REF-4 — determinism and replay (PLAN §6.1)

The machine is a pure function: `runFrames k input n` and `runScript obs n script` are Lean
functions, so equal inputs give equal results (`T_REF_4_replay`, by `rfl`). The useful
statement is *prefix stability*: the first `k` frames depend only on the first `k` entries of
the input script.

* `T_REF_4_prefix`: `(∀ i < k, s₁ i = s₂ i) → runFrames k s₁ n = runFrames k s₂ n`;
* `T_REF_4_split`: `runFrames (k + m) s n` is `m` more frames run from `runFrames k s n` (the
  state after the first `k` frames of a longer run is `runFrames k s n`, which by
  `T_REF_4_prefix` depends on `s` below `k` only);
* `T_REF_4_script_prefix`: for scripts as lists, `take k s₁ = take k s₂` implies the first `k`
  recorded observations agree (`runScript`, e.g. the frame hashes of `runScriptHashes`), and
  `T_REF_4_script_state`: the state after the first `k` frames agrees;
* `runScript_eq_runFrames`: `runScript` is `runFrames` with `input i = script[i]`.

TAS-replay reproducibility is the corollary: replaying a recorded script prefix reproduces the
recorded frame hashes.
-/

namespace Nes.System.Proofs.Determinism

open Nes.System

theorem runFrames_go_congr (s₁ s₂ : Nat → UInt8 × UInt8) :
    ∀ (k i : Nat) (n : Nes), (∀ j, i ≤ j → j < i + k → s₁ j = s₂ j) →
      Nes.runFrames.go s₁ i k n = Nes.runFrames.go s₂ i k n
  | 0, _, _, _ => rfl
  | k + 1, i, n, h => by
    simp only [Nes.runFrames.go]
    rw [h i (Nat.le_refl _) (by omega)]
    exact runFrames_go_congr s₁ s₂ k (i + 1) _ (fun j h1 h2 => h j (by omega) (by omega))

/-- T-REF-4: the first `k` frames depend only on the first `k` script entries. -/
theorem T_REF_4_prefix {k : Nat} {s₁ s₂ : Nat → UInt8 × UInt8} (n : Nes)
    (h : ∀ i < k, s₁ i = s₂ i) : n.runFrames k s₁ = n.runFrames k s₂ := by
  unfold Nes.runFrames
  exact runFrames_go_congr s₁ s₂ k 0 n (fun j _ hj => h j (by omega))

theorem runFrames_go_add (s : Nat → UInt8 × UInt8) :
    ∀ (k m i : Nat) (n : Nes),
      Nes.runFrames.go s i (k + m) n = Nes.runFrames.go s (i + k) m (Nes.runFrames.go s i k n)
  | 0, m, i, n => by simp [Nes.runFrames.go]
  | k + 1, m, i, n => by
    rw [show k + 1 + m = (k + m) + 1 by omega]
    simp only [Nes.runFrames.go]
    rw [runFrames_go_add s k m (i + 1), show i + 1 + k = i + (k + 1) by omega]

/-- T-REF-4: a `k + m`-frame run is the `k`-frame run followed by `m` frames (inputs from `k`
on). -/
theorem T_REF_4_split (s : Nat → UInt8 × UInt8) (k m : Nat) (n : Nes) :
    n.runFrames (k + m) s = Nes.runFrames.go s k m (n.runFrames k s) := by
  unfold Nes.runFrames
  rw [runFrames_go_add s k m 0 n, Nat.zero_add]

/-- T-REF-4 (list scripts): the first `k` observations depend only on the first `k` entries. -/
theorem T_REF_4_script_prefix {α : Type} (obs : Nes → α) :
    ∀ (k : Nat) (n : Nes) (s₁ s₂ : List (UInt8 × UInt8)), s₁.take k = s₂.take k →
      ((Nes.runScript obs n s₁).2).take k = ((Nes.runScript obs n s₂).2).take k
  | 0, _, _, _, _ => by simp
  | _ + 1, _, [], [], _ => rfl
  | _ + 1, _, [], _ :: _, h => by simp at h
  | _ + 1, _, _ :: _, [], h => by simp at h
  | k + 1, n, (b1, b2) :: t₁, a₂ :: t₂, h => by
    simp only [List.take_succ_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Nes.runScript, List.take_succ_cons]
    rw [T_REF_4_script_prefix obs k _ t₁ t₂ h]

/-- A script run in two pieces: the run of `s ++ t` is `t` run from the end of `s`, with the
observations concatenated. -/
theorem runScript_append {α : Type} (obs : Nes → α) :
    ∀ (n : Nes) (s t : List (UInt8 × UInt8)),
      Nes.runScript obs n (s ++ t) =
        ((Nes.runScript obs (Nes.runScript obs n s).1 t).1,
          (Nes.runScript obs n s).2 ++ (Nes.runScript obs (Nes.runScript obs n s).1 t).2)
  | _, [], _ => rfl
  | n, (b1, b2) :: s, t => by
    simp only [List.cons_append, Nes.runScript, runScript_append obs _ s t]

/-- T-REF-4 (list scripts): the state after the first `k` frames (`runScript_append` with
`s = take k s ++ drop k s`) depends only on the first `k` entries. -/
theorem T_REF_4_script_state {α : Type} (obs : Nes → α) (k : Nat) (n : Nes)
    (s₁ s₂ : List (UInt8 × UInt8)) (h : s₁.take k = s₂.take k) :
    (Nes.runScript obs n (s₁.take k)).1 = (Nes.runScript obs n (s₂.take k)).1 := by
  rw [h]

/-- Frame-hash replay: equal script prefixes give equal frame-hash prefixes. -/
theorem T_REF_4_hashes (k : Nat) (n : Nes) (s₁ s₂ : List (UInt8 × UInt8))
    (h : s₁.take k = s₂.take k) :
    ((Nes.runScriptHashes n s₁).2).take k = ((Nes.runScriptHashes n s₂).2).take k :=
  T_REF_4_script_prefix _ k n s₁ s₂ h

/-- Replay: the run is a function of `(machine, script)`. -/
theorem T_REF_4_replay {α : Type} (obs : Nes → α) (n : Nes) (s : List (UInt8 × UInt8)) :
    Nes.runScript obs n s = Nes.runScript obs n s := rfl

theorem runScript_eq_go {α : Type} (obs : Nes → α) (input : Nat → UInt8 × UInt8) :
    ∀ (s : List (UInt8 × UInt8)) (i : Nat) (n : Nes),
      (∀ j < s.length, input (i + j) = s.getD j (0, 0)) →
      Nes.runFrames.go input i s.length n = (Nes.runScript obs n s).1
  | [], _, _, _ => rfl
  | (b1, b2) :: t, i, n, h => by
    have h0 : input i = (b1, b2) := by simpa using h 0 (by simp)
    simp only [List.length_cons, Nes.runFrames.go, h0, Nes.runScript]
    apply runScript_eq_go obs input t (i + 1)
    intro j hj
    have := h (j + 1) (by simp; omega)
    rw [show i + (j + 1) = i + 1 + j by omega] at this
    simpa using this

/-- `runScript` is `runFrames` with `input i = script[i]`. -/
theorem runScript_eq_runFrames {α : Type} (obs : Nes → α) (n : Nes)
    (s : List (UInt8 × UInt8)) :
    (Nes.runScript obs n s).1 = n.runFrames s.length (fun i => s.getD i (0, 0)) := by
  unfold Nes.runFrames
  exact (runScript_eq_go obs _ s 0 n (fun j _ => by simp)).symm

end Nes.System.Proofs.Determinism
