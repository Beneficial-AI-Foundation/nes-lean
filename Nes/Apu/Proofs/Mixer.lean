import Nes.Apu.Mixer

/-!
# `Nes.Apu.Proofs.Mixer` — T-APU-2 (mixer bounds, monotonicity, table accuracy)

## Spec

`mix p1 p2 t n d = pulseOut (p1 + p2) + tndOut t n d` is the NESdev nonlinear mixer as exact
`Rat` fractions of naturals (see `Nes.Apu.Mixer`). In-range means `p1 p2 t n ≤ 15`, `d ≤ 127`.

* **T-APU-2 (bounds).** In range, `0 ≤ mix p1 p2 t n d ≤ 1` (`T_APU_2_bounds`); the exact maximum
  `mix 15 15 15 15 127 = 591703959257554691 / 591704343376070600 < 1` (`T_APU_2_max`).
* **T-APU-2 (monotone).** `mix` is monotone in each argument separately, for *all* naturals
  (`T_APU_2_mono_p1`, `_p2`, `_t`, `_n`, `_d`).
* **Tables.** `pulseTable` / `tndTable` are exactly the `UInt16` images of `pulseLevels` /
  `tndLevels` (`pulseTable_levels`, `tndTable_levels`). Every `pulseLevels[i]` is
  `round(65535 · pulseOut i)` (round half up, `T_APU_2_pulseTable`) and lies within ½ LSB of it
  (`T_APU_2_pulseTable_err`); every `tndLevels[k]` is `round(65535 · tndApprox k)` — the NESdev
  lookup approximation (`T_APU_2_tndTable`). For all 32768 in-range `(t, n, d)`,
  `|tndLevels[3t+2n+d] / 65535 − tndOut t n d| ≤ 13/1000` (`T_APU_2_tndTable_err`): the runtime
  tnd path is accurate to 1.3 % of full scale (≈ 850 LSB), dominated by the approximation itself
  (worst case `t = n = 0`, `d = 118`), not by rounding.

Method: every spec value is `frac a b = (a : Rat) / b` with naturals. Order between fractions is
reduced to `Nat` cross-multiplication (`frac_le`), sums to one fraction (`frac_add`). Monotonicity
uses `a·x / (b + c·x)` increasing in `x` (`frac_mono`). Table facts are decided by kernel
evaluation of `Nat`-only checkers (GMP-backed), never of `Rat` arithmetic over the 32768 cases.
-/

namespace Nes.Apu.Proofs

open Nes.Apu

/-! ### `frac` algebra -/

theorem frac_le {A B C D : Nat} (hB : 0 < B) (hD : 0 < D) (h : A * D ≤ C * B) :
    frac A B ≤ frac C D := by
  unfold frac
  have hB' : (0 : Rat) < B := Rat.natCast_pos.mpr hB
  have hD' : (0 : Rat) < D := Rat.natCast_pos.mpr hD
  rw [← Rat.not_lt]
  intro hlt
  rw [Rat.div_lt_iff hD'] at hlt
  have e : (A : Rat) / B * D = ((A * D : Nat) : Rat) / B := by
    rw [Rat.natCast_mul, Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm (B : Rat)⁻¹,
      ← Rat.mul_assoc]
  rw [e, Rat.lt_div_iff hB', ← Rat.natCast_mul, Rat.natCast_lt_natCast] at hlt
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h)

theorem frac_add {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) :
    frac a b + frac c d = frac (a * d + c * b) (b * d) := by
  unfold frac
  have := Rat.divInt_add_divInt (a : Int) (c : Int) (d₁ := (b : Int)) (d₂ := (d : Int))
    (by omega) (by omega)
  simp only [Rat.divInt_eq_div, Rat.intCast_natCast, Rat.intCast_add, Rat.intCast_mul] at this
  rw [this, Rat.natCast_add, Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_mul]

theorem frac_zero_le {a b : Nat} (hb : 0 < b) : (0 : Rat) ≤ frac a b := by
  have : (0 : Rat) = frac 0 1 := by decide +kernel
  rw [this]
  exact frac_le (by decide) hb (by simp)

/-- `a·x / (b + c·x)` is increasing in `x`. -/
theorem frac_mono {a b c x y : Nat} (hb : 0 < b) (hxy : x ≤ y) :
    frac (a * x) (b + c * x) ≤ frac (a * y) (b + c * y) := by
  apply frac_le (by omega) (by omega)
  have h1 : a * x * b ≤ a * y * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxy)
  have h2 : a * x * (c * y) = a * y * (c * x) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [Nat.mul_add, Nat.mul_add, h2]
  omega

theorem add_le_add' {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

/-! ### Monotonicity -/

theorem pulseOut_mono {x y : Nat} (h : x ≤ y) : pulseOut x ≤ pulseOut y :=
  frac_mono (by decide) h

theorem tndDen_pos : 0 < 100 * tndDen := by decide

theorem tndOut_mono {t n d t' n' d' : Nat} (h : tndNum t n d ≤ tndNum t' n' d') :
    tndOut t n d ≤ tndOut t' n' d' :=
  frac_mono tndDen_pos h

theorem T_APU_2_mono_p1 {p1 p1' : Nat} (p2 t n d : Nat) (h : p1 ≤ p1') :
    mix p1 p2 t n d ≤ mix p1' p2 t n d :=
  Rat.add_le_add_right.mpr (pulseOut_mono (by omega))

theorem T_APU_2_mono_p2 {p2 p2' : Nat} (p1 t n d : Nat) (h : p2 ≤ p2') :
    mix p1 p2 t n d ≤ mix p1 p2' t n d :=
  Rat.add_le_add_right.mpr (pulseOut_mono (by omega))

theorem T_APU_2_mono_t {t t' : Nat} (p1 p2 n d : Nat) (h : t ≤ t') :
    mix p1 p2 t n d ≤ mix p1 p2 t' n d :=
  Rat.add_le_add_left.mpr (tndOut_mono (by unfold tndNum; omega))

theorem T_APU_2_mono_n {n n' : Nat} (p1 p2 t d : Nat) (h : n ≤ n') :
    mix p1 p2 t n d ≤ mix p1 p2 t n' d :=
  Rat.add_le_add_left.mpr (tndOut_mono (by unfold tndNum; omega))

theorem T_APU_2_mono_d {d d' : Nat} (p1 p2 t n : Nat) (h : d ≤ d') :
    mix p1 p2 t n d ≤ mix p1 p2 t n d' :=
  Rat.add_le_add_left.mpr (tndOut_mono (by unfold tndNum; omega))

/-! ### Bounds -/

theorem T_APU_2_max : mix 15 15 15 15 127 = 591703959257554691 / 591704343376070600 ∧
    mix 15 15 15 15 127 ≤ 1 := by
  constructor <;> decide +kernel

theorem T_APU_2_bounds {p1 p2 t n d : Nat} (h1 : p1 ≤ 15) (h2 : p2 ≤ 15) (ht : t ≤ 15)
    (hn : n ≤ 15) (hd : d ≤ 127) : 0 ≤ mix p1 p2 t n d ∧ mix p1 p2 t n d ≤ 1 := by
  constructor
  · have : (0 : Rat) = 0 + 0 := (Rat.add_zero 0).symm
    rw [this]
    exact add_le_add' (frac_zero_le (by omega)) (frac_zero_le (by unfold tndDen; omega))
  · refine Rat.le_trans ?_ T_APU_2_max.2
    exact add_le_add' (pulseOut_mono (by omega)) (tndOut_mono (by unfold tndNum; omega))

/-! ### Tables -/

theorem pulseTable_levels : pulseTable.toList.map UInt16.toNat = pulseLevels := by decide +kernel

theorem tndTable_levels : tndTable.toList.map UInt16.toNat = tndLevels := by decide +kernel

theorem pulseLevels_length : pulseLevels.length = 31 := by decide +kernel

theorem tndLevels_length : tndLevels.length = 203 := by decide +kernel

/-- Round half up: `⌊a / b + 1/2⌋`. -/
def roundFrac (a b : Nat) : Nat := (2 * a + b) / (2 * b)

theorem T_APU_2_pulseTable :
    ∀ i < 31, pulseLevels.getD i 0 = roundFrac (65535 * (9588 * i)) (812800 + 10000 * i) := by
  decide +kernel

theorem T_APU_2_tndTable :
    ∀ k < 203, tndLevels.getD k 0 = roundFrac (65535 * (16367 * k)) (2432900 + 10000 * k) := by
  decide +kernel

/-- `Nat` form of `frac A B ≤ frac e M + frac c d ∧ frac e M ≤ frac A B + frac c d`. -/
def closeN (e M A B c d : Nat) : Bool :=
  A * (M * d) ≤ (e * d + c * M) * B && e * (B * d) ≤ (A * d + c * B) * M

theorem close_of {e M A B c d : Nat} (hM : 0 < M) (hB : 0 < B) (hd : 0 < d)
    (h : closeN e M A B c d = true) :
    frac A B ≤ frac e M + frac c d ∧ frac e M ≤ frac A B + frac c d := by
  simp only [closeN, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [frac_add hM hd, frac_add hB hd]
  exact ⟨frac_le hB (Nat.mul_pos hM hd) h.1, frac_le hM (Nat.mul_pos hB hd) h.2⟩

theorem T_APU_2_pulseTable_err : ∀ i < 31,
    pulseOut i ≤ frac (pulseLevels.getD i 0) 65535 + frac 1 131070 ∧
      frac (pulseLevels.getD i 0) 65535 ≤ pulseOut i + frac 1 131070 := by
  have hc : ∀ i < 31,
      closeN (pulseLevels.getD i 0) 65535 (9588 * i) (812800 + 10000 * i) 1 131070 = true := by
    decide +kernel
  intro i hi
  exact close_of (by decide) (by omega) (by decide) (hc i hi)

/-- Checker for one `(t, n)` row of the tnd table: `l` is `tndLevels.drop (3t + 2n)`. -/
def tndRow (t n : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | d, e :: es =>
    if d < 128 then
      closeN e 65535 (15979 * tndNum t n d) (100 * tndDen + 10000 * tndNum t n d) 13 1000 &&
        tndRow t n (d + 1) es
    else true

def tndAll : Bool :=
  (List.range 16).all fun t => (List.range 16).all fun n => tndRow t n 0 (tndLevels.drop (3 * t + 2 * n))

theorem tndAll_ok : tndAll = true := by decide +kernel

theorem tndRow_spec (t n : Nat) : ∀ (l : List Nat) (d0 j : Nat), tndRow t n d0 l = true →
    j < l.length → d0 + j < 128 →
    closeN (l.getD j 0) 65535 (15979 * tndNum t n (d0 + j))
      (100 * tndDen + 10000 * tndNum t n (d0 + j)) 13 1000 = true
  | [], _, _, _, hj, _ => absurd hj (by simp)
  | e :: es, d0, j, h, hj, hd => by
    have hd0 : d0 < 128 := by omega
    simp only [tndRow, hd0, ↓reduceIte, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := tndRow_spec t n es (d0 + 1) j h.2 (by simp at hj; omega) (by omega)
      simp only [List.getD_cons_succ]
      rwa [show d0 + (j + 1) = d0 + 1 + j by omega]

theorem T_APU_2_tndTable_err {t n d : Nat} (ht : t < 16) (hn : n < 16) (hd : d < 128) :
    tndOut t n d ≤ frac (tndLevels.getD (3 * t + 2 * n + d) 0) 65535 + frac 13 1000 ∧
      frac (tndLevels.getD (3 * t + 2 * n + d) 0) 65535 ≤ tndOut t n d + frac 13 1000 := by
  have hall := tndAll_ok
  simp only [tndAll, List.all_eq_true, List.mem_range] at hall
  have hrow := hall t ht n hn
  have hc := tndRow_spec t n _ 0 d hrow (by simp [tndLevels_length]; omega) (by omega)
  simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_drop] at hc
  exact close_of (by decide) (by unfold tndDen; omega) (by decide) hc

end Nes.Apu.Proofs
