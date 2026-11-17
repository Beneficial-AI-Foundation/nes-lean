import Nes.Ppu.Sprites

/-!
# `Nes.Ppu.Proofs.Sprites` — T-PPU-3 (sprite evaluation)

## Spec

`evalLine s` runs evaluation dots 1–256 of a line: dot `d` sets `dot := d` and calls
`Sprites.evalDot` (what `Nes.Ppu.Step.render` does on a visible line with rendering enabled,
after `advance` has moved `dot` to `d`). With `L = s.scanline`, `h = 16` in 8×16 mode else 8, and
`(sel, ovf) = evalSpec s.oam L h` (first ≤ 8 in-range sprites in OAM order; the hardware's
diagonal-walk overflow predicate, both declarative in `Nes.Ppu.Sprites`):

* **T-PPU-3 (`T_PPU_3_eval`).** From any state at dot 0 with a 32-byte secondary OAM and any
  OAM: `|sel| ≤ 8`; `secOam[4k + b] = oam[4·sel[k] + b]` for `k < |sel|`, `b < 4`;
  `evalSec = 4·|sel|`, so the dot-257 sprite count `evalSec >>> 2 = |sel|`;
  `spr0Next = (0 ∈ sel)`; `status = if ovf then status₀ ||| $20 else status₀`, hence the
  overflow flag (bit 5) is `old ∨ ovf`; OAM, line and `ctrl` are untouched.
* **Clear phase (`clear_phase`).** Dots 1–64 change only `dot` and secondary OAM, which ends
  all `$FF`.

Method. The per-dot machine is related (`Rel`) to an abstract machine `Ev` with `Nat`
counters `n m sec`, flags `spr0 ovf` and secondary OAM as a function; one latch dot (odd) plus
one act dot (even) is one abstract step `pstep` (`latch_dot`, `latch_first`, `act_dot`, via the
`packEval` unpacking lemmas `pack_*`). On the abstract side, with `hb n` = the in-range indices
below `n`, the invariant is `Inv1` (copy phase: `sec = 4·|hb n| + m`, `|hb n| < 8`, the first
`|hb n|` slots hold `hb n`, the `m` bytes of the sprite being copied follow, `spr0` ↔
`0 ∈ hb n ∨ (n = 0 ∧ m ≠ 0)`) or `Inv2` (overflow phase after the 8th hit `k`: `sec = 32`,
`m = (n − k − 1) mod 4`, no earlier diagonal byte in range — or the flag set with
`overflowSpec`). `Inv` is preserved by each step (`inv1_step`, `inv2_step`), the measure
`(64 − n) + (32 − sec)` (≤ 96, the number of latch/act pairs in dots 65–256) drops on every
non-final step, and at `n ≥ 64` the invariant gives `evalSpec` (`post_of`, `run_post`). No
dot-by-dot unfolding with a symbolic OAM is ever performed.
-/

namespace Nes.Ppu.Proofs.SpriteEval

open Nes.Ppu Nes.Ppu.Sprites

/-! ### Byte-array, packing and integer helpers -/

theorem getByte_set (a : ByteArray) (i j : Nat) (v : UInt8) :
    getByte (a.set! i v) j = if i = j ∧ i < a.size then v else getByte a j := by
  rcases a with ⟨bs⟩
  unfold getByte
  simp only [ByteArray.set!, ByteArray.size, ByteArray.getElem_eq_getElem_data, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]
  by_cases hj : j < bs.size
  · simp only [hj, dite_true, Array.getElem_setIfInBounds hj]
    by_cases hij : i = j
    · subst hij; simp [hj]
    · simp [hij, Nat.not_le.mpr hj]
  · have : ¬ (i = j ∧ i < bs.size) := fun ⟨h1, h2⟩ => hj (h1 ▸ h2)
    simp [hj, this]

theorem set_getByte_self (a : ByteArray) (i : Nat) : a.set! i (getByte a i) = a := by
  rcases a with ⟨bs⟩
  simp only [ByteArray.set!, getByte, ByteArray.size, Array.set!_eq_setIfInBounds]
  congr 1
  apply Array.ext
  · simp
  · intro j h1 h2
    rw [Array.getElem_setIfInBounds h2]
    split
    · rename_i hij; subst hij; simp [ByteArray.getElem_eq_getElem_data, h2]
    · rfl


theorem pack_n (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    (packEval n m sec latch st spr0 i b).toUInt8 = n := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_m (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 8).toUInt8 = m := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_sec (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 16).toUInt8 = sec := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_latch (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 24).toUInt8 = latch := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_st (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 32).toUInt8 = st := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_b (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 48).toUInt8 = b := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_i8 (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 40).toUInt8 = i &&& 0x1F := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_s8 (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    ((packEval n m sec latch st spr0 i b) >>> 56).toUInt8 = if spr0 then 1 else 0 := by
  unfold packEval; apply UInt8.eq_of_toBitVec_eq
  cases spr0 <;> simp <;> ext j hj <;> rcases j with _|_|_|_|_|_|_|_|j <;> first | omega | simp
theorem pack_i (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    (((packEval n m sec latch st spr0 i b) >>> 40) &&& 0x1F).toNat = (i &&& 0x1F).toNat := by
  have h := congrArg UInt8.toNat (pack_i8 n m sec latch st spr0 i b)
  generalize (packEval n m sec latch st spr0 i b) >>> 40 = x at h ⊢
  rw [UInt8.toNat_and] at h
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_and, UInt8.toNat_and] at h ⊢
  have e1 : ∀ y : Nat, y &&& 31 = y % 32 := fun y => Nat.and_two_pow_sub_one_eq_mod y 5
  simp only [show UInt64.toNat 31 = 31 from rfl, show UInt8.toNat 31 = 31 from rfl, e1] at h ⊢
  omega
theorem pack_spr0 (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    (((packEval n m sec latch st spr0 i b) >>> 56) &&& 1 != 0) = spr0 := by
  have h := congrArg UInt8.toNat (pack_s8 n m sec latch st spr0 i b)
  generalize (packEval n m sec latch st spr0 i b) >>> 56 = x at h ⊢
  have e : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1
  simp only [UInt64.toNat_toUInt8] at h
  cases spr0 <;> simp at h
  · rw [bne_eq_false_iff_eq]
    apply UInt64.toNat_inj.mp; rw [e]; simp; omega
  · simp only [bne_iff_ne, ne_eq]
    intro hx; have := congrArg UInt64.toNat hx; rw [e] at this; simp at this; omega

theorem evalDot_pack (t : State) (hd : (t.dot == 0 || t.dot > 256) = false)
    {n m sec latch st : UInt8} {spr0 : Bool} {i b : UInt8}
    (h : evalStep t = packEval n m sec latch st spr0 i b) :
    evalDot t =
      { t with secOam := t.secOam.set! (i &&& 0x1F).toNat b, evalN := n, evalM := m,
               evalSec := sec, evalLatch := latch, status := st, spr0Next := spr0 } := by
  unfold evalDot
  simp only [hd, Bool.false_eq_true, ite_false, h, pack_n, pack_m, pack_sec, pack_latch, pack_st, pack_b,
    pack_i, pack_spr0]

theorem dot_ok (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 256) : (k.toUInt16 == 0 || k.toUInt16 > 256) = false := by
  have : k.toUInt16.toNat = k := by simp; omega
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, ne_eq]
  constructor
  · intro h; rw [h] at this; simp at this; omega
  · show ¬ (256 : UInt16) < k.toUInt16
    rw [UInt16.lt_iff_toNat_lt, this]; simp; omega
theorem u8_succ (x : UInt8) (h : x.toNat < 255) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt8.toNat_add]; simp; omega
theorem u8_and1F (x : UInt8) (h : x.toNat < 32) : (x &&& 0x1F).toNat = x.toNat := by
  rw [UInt8.toNat_and]; exact (Nat.and_two_pow_sub_one_eq_mod _ 5).trans (Nat.mod_eq_of_lt h)
theorem u8_succ3 (x : UInt8) (h : x.toNat < 4) : ((x + 1) &&& 3).toNat = (x.toNat + 1) % 4 := by
  rw [UInt8.toNat_and, u8_succ x (by omega)]; exact Nat.and_two_pow_sub_one_eq_mod _ 2
theorem u8_beq0 (x : UInt8) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x.toNat = 0
  · simp [h]; exact UInt8.toNat_inj.mp h
  · simp [h]; intro hx; apply h; rw [hx]; rfl
theorem u8_beq4 (x : UInt8) (hx : x.toNat < 4) : (x + 1 == 4) = decide (x.toNat + 1 = 4) := by
  have := u8_succ x (by omega)
  by_cases h : x.toNat + 1 = 4
  · simp [h]; apply UInt8.toNat_inj.mp; rw [this, h]; rfl
  · simp [h]; intro hx; apply h; rw [← this, hx]; rfl
theorem u8_ge64 (x : UInt8) : (x ≥ 64) ↔ 64 ≤ x.toNat := by
  rw [ge_iff_le, UInt8.le_iff_toNat_le]; rfl
theorem u8_lt32 (x : UInt8) : (x < 32) ↔ x.toNat < 32 := by
  rw [UInt8.lt_iff_toNat_lt]; rfl
theorem u16 (k : Nat) (hk : k < 65536) : k.toUInt16.toNat = k := by simp; omega
theorem dot_and1 (k : Nat) : (k.toUInt16 &&& 1).toNat = k % 2 := by rw [UInt16.toNat_and]; simp
theorem clear_idx (k : Nat) (h1 : 2 ≤ k) (h2 : k ≤ 64) :
    ((k.toUInt16 / 2 - 1).toUInt8 &&& 0x1F).toNat = k / 2 - 1 := by
  have hk := u16 k (by omega)
  have hd : (k.toUInt16 / 2).toNat = k / 2 := by rw [UInt16.toNat_div, hk]; rfl
  have hs : (k.toUInt16 / 2 - 1).toNat = k / 2 - 1 := by
    rw [UInt16.toNat_sub_of_le, hd]; rfl
    rw [UInt16.le_iff_toNat_le, hd]; simp; omega
  rw [UInt8.toNat_and, UInt16.toNat_toUInt8, hs, Nat.mod_eq_of_lt (by omega)]
  exact (Nat.and_two_pow_sub_one_eq_mod _ 5).trans (Nat.mod_eq_of_lt (by omega))

/-! ### The abstract evaluation machine -/

structure Ev where
  n : Nat
  m : Nat
  sec : Nat
  spr0 : Bool
  ovf : Bool
  mem : Nat → UInt8

def pstep (B : Nat → UInt8) (hit : UInt8 → Bool) (e : Ev) : Ev :=
  if 64 ≤ e.n then e else
  let b := B (4 * e.n + e.m)
  if e.sec < 32 then
    let mem := fun j => if j = e.sec then b else e.mem j
    if e.m = 0 ∧ hit b = false then { e with n := e.n + 1, mem }
    else
      let spr0 := e.spr0 || (e.m == 0 && e.n == 0)
      if e.m + 1 = 4 then { e with n := e.n + 1, m := 0, sec := e.sec + 1, spr0, mem }
      else { e with m := e.m + 1, sec := e.sec + 1, spr0, mem }
  else if hit b then { e with n := 64, ovf := true }
  else { e with n := e.n + 1, m := (e.m + 1) % 4 }

def iter (f : Ev → Ev) : Nat → Ev → Ev
  | 0, e => e
  | k + 1, e => iter f k (f e)

def mu (e : Ev) : Nat := (64 - e.n) + (32 - e.sec)

theorem iter_succ (f : Ev → Ev) (k : Nat) (e : Ev) : iter f k (f e) = iter f (k + 1) e := rfl

theorem pstep_done {B hit} {e : Ev} (h : 64 ≤ e.n) : pstep B hit e = e := by
  simp [pstep, h]

theorem iter_done {B hit} {e : Ev} (h : 64 ≤ e.n) : ∀ k, iter (pstep B hit) k e = e
  | 0 => rfl
  | k + 1 => by simp only [iter, pstep_done h]; exact iter_done h k

theorem pstep_mu {B hit} {e : Ev} (hn : e.n < 64) (hs : e.sec ≤ 32) :
    mu (pstep B hit e) < mu e := by
  unfold pstep mu
  simp only [Nat.not_le.mpr hn, ite_false]
  repeat' split
  all_goals simp only
  all_goals omega

section
variable (oam : ByteArray) (L h : Nat)

def hitY (n : Nat) : Bool := inRangeSpec (getByte oam (4 * n)) L h

def hb (n : Nat) : List Nat := (List.range n).filter (hitY oam L h)

def MemOK (mem : Nat → UInt8) (sel : List Nat) : Prop :=
  ∀ k (hk : k < sel.length), ∀ b < 4, mem (4 * k + b) = getByte oam (4 * sel[k] + b)

def Inv1 (e : Ev) : Prop :=
  e.n ≤ 64 ∧ e.m < 4 ∧ (hb oam L h e.n).length < 8 ∧ e.sec = 4 * (hb oam L h e.n).length + e.m ∧
  (e.m ≠ 0 → e.n < 64 ∧ hitY oam L h e.n = true) ∧ e.ovf = false ∧
  (e.spr0 = true ↔ (0 ∈ hb oam L h e.n ∨ (e.n = 0 ∧ e.m ≠ 0))) ∧ MemOK oam e.mem (hb oam L h e.n) ∧
  ∀ b < e.m, e.mem (4 * (hb oam L h e.n).length + b) = getByte oam (4 * e.n + b)

def Inv2 (e : Ev) : Prop := ∃ k, (hb oam L h 64)[7]? = some k ∧ e.sec = 32 ∧ e.m < 4 ∧ e.n ≤ 64 ∧
  (e.spr0 = true ↔ 0 ∈ (hb oam L h 64).take 8) ∧ MemOK oam e.mem ((hb oam L h 64).take 8) ∧
  ((e.ovf = false ∧ k + 1 ≤ e.n ∧ e.m = (e.n - (k + 1)) % 4 ∧
      ∀ j < e.n - (k + 1), inRangeSpec (getByte oam (4 * (k + 1 + j) + j % 4)) L h = false) ∨
    (e.ovf = true ∧ e.n = 64 ∧ overflowSpec oam L h k = true))

def Inv (e : Ev) : Prop := Inv1 oam L h e ∨ Inv2 oam L h e

def Post (e : Ev) : Prop :=
  e.sec = 4 * (evalSpec oam L h).1.length ∧ (e.spr0 = true ↔ 0 ∈ (evalSpec oam L h).1) ∧
  e.ovf = (evalSpec oam L h).2 ∧ MemOK oam e.mem (evalSpec oam L h).1

abbrev step : Ev → Ev := pstep (getByte oam) (fun b => inRangeSpec b L h)

theorem hb_succ (n : Nat) :
    hb oam L h (n + 1) = hb oam L h n ++ (if hitY oam L h n then [n] else []) := by
  unfold hb; rw [List.range_succ, List.filter_append]
  by_cases hy : hitY oam L h n = true <;> simp [hy]

theorem hb_append (n : Nat) : ∀ k, ∃ r, hb oam L h (n + k) = hb oam L h n ++ r
  | 0 => ⟨[], by simp⟩
  | k + 1 => by
    obtain ⟨r, hr⟩ := hb_append n k
    exact ⟨r ++ (if hitY oam L h (n + k) then [n + k] else []), by
      rw [← Nat.add_assoc, hb_succ, hr, List.append_assoc]⟩

theorem evalSpec_eq : evalSpec oam L h = ((hb oam L h 64).take 8,
    match (hb oam L h 64)[7]? with
    | none => false
    | some k => overflowSpec oam L h k) := rfl

theorem memOK_upd {mem : Nat → UInt8} {sel : List Nat} {sec : Nat} {v : UInt8}
    (hm : MemOK oam mem sel) (hs : 4 * sel.length ≤ sec) :
    MemOK oam (fun j => if j = sec then v else mem j) sel := by
  intro k hk b hb
  have : 4 * k + b ≠ sec := by omega
  simp only [this, ite_false]; exact hm k hk b hb


theorem inv1_step {e : Ev} (hi : Inv1 oam L h e) (hn : e.n < 64) :
    Inv1 oam L h (step oam L h e) ∨ Inv2 oam L h (step oam L h e) := by
  obtain ⟨_, hm4, hlen, hsec, hmne, hovf, hspr, hmem, hpart⟩ := hi
  have hs32 : e.sec < 32 := by omega
  unfold step pstep
  simp only [Nat.not_le.mpr hn, hs32, ite_false, ite_true]
  generalize hl : (hb oam L h e.n).length = len at *
  by_cases hc : e.m = 0 ∧ inRangeSpec (getByte oam (4 * e.n + e.m)) L h = false
  · -- a miss on the Y byte: next sprite, nothing kept
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    obtain ⟨hm0, hmiss⟩ := hc
    have hy : hitY oam L h e.n = false := by simpa [hitY, hm0] using hmiss
    have hb1 : hb oam L h (e.n + 1) = hb oam L h e.n := by simp [hb_succ, hy]
    left
    dsimp only [Inv1]
    refine ⟨by omega, hm4, ?_, ?_, ?_, hovf, ?_, ?_, ?_⟩
    · rw [hb1, hl]; omega
    · rw [hb1, hl]; omega
    · intro h'; exact absurd hm0 h'
    · rw [hb1, hspr]; simp [hm0]
    · rw [hb1]; exact memOK_upd oam hmem (by omega)
    · intro b hb'; omega
  · have hy : hitY oam L h e.n = true := by
      by_cases hm0 : e.m = 0
      · have : inRangeSpec (getByte oam (4 * e.n + e.m)) L h = true := by
          cases hr : inRangeSpec (getByte oam (4 * e.n + e.m)) L h
          · exact absurd ⟨hm0, hr⟩ hc
          · rfl
        simpa [hitY, hm0] using this
      · exact (hmne hm0).2
    have hb1 : hb oam L h (e.n + 1) = hb oam L h e.n ++ [e.n] := by simp [hb_succ, hy]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    by_cases h3 : e.m + 1 = 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
      have hl1 : (hb oam L h (e.n + 1)).length = len + 1 := by simp [hb1, hl]
      have hmemN : MemOK oam (fun j => if j = e.sec then getByte oam (4 * e.n + e.m) else e.mem j)
          (hb oam L h (e.n + 1)) := by
        rw [hb1]
        intro k hk b hb'
        by_cases hkl : k < len
        · have hkl' : k < (hb oam L h e.n).length := by omega
          rw [List.getElem_append_left hkl']
          have : 4 * k + b ≠ e.sec := by omega
          simp only [this, ite_false]; exact hmem k hkl' b hb'
        · have hk' : k = len := by simp [hl] at hk; omega
          rw [List.getElem_append_right (by omega)]
          simp only [hl, show k - len = 0 by omega, List.getElem_cons_zero]
          by_cases hb3 : b = 3
          · have : 4 * k + b = e.sec := by omega
            simp only [this, ite_true]; congr 2; omega
          · have : 4 * k + b ≠ e.sec := by omega
            simp only [this, ite_false]; rw [hk']; exact hpart b (by omega)
      have hsp : ((e.spr0 || (e.m == 0 && e.n == 0)) = true) ↔ 0 ∈ hb oam L h (e.n + 1) := by
        rw [hb1]; simp only [Bool.or_eq_true, hspr, List.mem_append, List.mem_singleton]
        have : e.m ≠ 0 := by omega
        simp only [this, ne_eq, not_false_eq_true, and_true, Bool.and_eq_true, beq_iff_eq, false_and, or_false]
        exact or_congr Iff.rfl ⟨Eq.symm, Eq.symm⟩
      by_cases h8 : len + 1 < 8
      · left
        dsimp only [Inv1]
        refine ⟨?_, ?_, ?_, ?_, ?_, hovf, ?_, hmemN, ?_⟩
        · omega
        · omega
        · omega
        · omega
        · intro h'; exact absurd rfl h'
        · simp only [Nat.add_eq_zero_iff, and_false, ne_eq, not_true_eq_false, and_false, or_false]
          exact hsp
        · intro b hb'; omega
      · right
        dsimp only [Inv2]
        obtain ⟨r, hr⟩ := hb_append oam L h (e.n + 1) (64 - (e.n + 1))
        rw [show e.n + 1 + (64 - (e.n + 1)) = 64 by omega] at hr
        have htake : (hb oam L h 64).take 8 = hb oam L h (e.n + 1) := by
          rw [hr, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        refine ⟨e.n, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨hovf, ?_, ?_, ?_⟩⟩
        · rw [hr, List.getElem?_append_left (by omega), hb1, List.getElem?_append_right (by omega)]
          simp [hl, show 7 - len = 0 by omega]
        · omega
        · omega
        · omega
        · rw [htake]; exact hsp
        · rw [htake]; exact hmemN
        · omega
        · simp
        · intro j hj; simp at hj
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
      left
      dsimp only [Inv1]
      simp only [hl]
      refine ⟨by omega, by omega, by omega, by omega, fun _ => ⟨hn, hy⟩, hovf, ?_, memOK_upd oam hmem (by omega), ?_⟩
      · simp only [Bool.or_eq_true, hspr, Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro ((h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h1, by omega⟩
          · exact Or.inr ⟨h2, by omega⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · exact Or.inl (Or.inl h1)
          · by_cases hm0 : e.m = 0
            · exact Or.inr ⟨hm0, h1⟩
            · exact Or.inl (Or.inr ⟨h1, hm0⟩)
      · intro b hb'
        by_cases hbm : b = e.m
        · rw [hbm]; simp only [show 4 * len + e.m = e.sec by omega, ite_true]
        · have : 4 * len + b ≠ e.sec := by omega
          simp only [this, ite_false]; exact hpart b (by omega)

theorem inv2_step {e : Ev} (hi : Inv2 oam L h e) (hn : e.n < 64) : Inv2 oam L h (step oam L h e) := by
  obtain ⟨k, hk, hsec, hm4, hn64, hspr, hmem, hph⟩ := hi
  rcases hph with ⟨hovf, hkn, hm, hall⟩ | ⟨_, hn', _⟩
  · unfold step pstep
    simp only [Nat.not_le.mpr hn, hsec, Nat.lt_irrefl, ite_false]
    by_cases hit : inRangeSpec (getByte oam (4 * e.n + e.m)) L h = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hit)]
      refine ⟨k, hk, rfl, hm4, Nat.le_refl _, hspr, hmem, Or.inr ⟨rfl, rfl, ?_⟩⟩
      unfold overflowSpec
      rw [List.any_eq_true]
      refine ⟨e.n - (k + 1), List.mem_range.mpr (by omega), ?_⟩
      rw [← hit, hm]; congr 2; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hit)]
      refine ⟨k, hk, rfl, by dsimp only; omega, by dsimp only; omega, hspr, hmem, Or.inl ⟨hovf, ?_, ?_, ?_⟩⟩
      · dsimp only; omega
      · dsimp only; rw [hm, show e.n + 1 - (k + 1) = e.n - (k + 1) + 1 by omega, Nat.add_mod]
        simp
      · dsimp only
        intro j hj
        by_cases hj' : j < e.n - (k + 1)
        · exact hall j hj'
        · have hj2 : j = e.n - (k + 1) := by omega
          simp only [Bool.not_eq_true] at hit
          rw [← hit, hm, hj2]; congr 2; omega
  · omega

theorem inv_step {e : Ev} (hi : Inv oam L h e) : Inv oam L h (step oam L h e) := by
  by_cases hn : 64 ≤ e.n
  · rw [step, pstep_done hn]; exact hi
  · rcases hi with hi | hi
    · exact inv1_step oam L h hi (by omega)
    · exact Or.inr (inv2_step oam L h hi (by omega))

theorem inv_bounds {e : Ev} (hi : Inv oam L h e) : e.n ≤ 64 ∧ e.m < 4 ∧ e.sec ≤ 32 := by
  rcases hi with ⟨h1, h2, h3, h4, -⟩ | ⟨k, -, h1, h2, h3, -⟩ <;> omega

theorem post_of {e : Ev} (hi : Inv oam L h e) (hn : 64 ≤ e.n) : Post oam L h e := by
  unfold Post
  rw [evalSpec_eq]
  rcases hi with ⟨hn64, hm4, hlen, hsec, hmne, hovf, hspr, hmem, -⟩ |
      ⟨k, hk, hsec, hm4, hn64, hspr, hmem, hph⟩
  · have hn' : e.n = 64 := by omega
    have hm0 : e.m = 0 := by
      by_cases hm : e.m = 0
      · exact hm
      · exact absurd (hmne hm).1 (by omega)
    rw [hn'] at hlen hsec hspr hmem
    have h7 : (hb oam L h 64)[7]? = none := List.getElem?_eq_none (by omega)
    rw [h7]; dsimp only
    rw [List.take_of_length_le (by omega)]
    refine ⟨by omega, ?_, hovf, hmem⟩
    rw [hspr]; simp [hm0]
  · have hl : 8 ≤ (hb oam L h 64).length := by
      obtain ⟨h7, -⟩ := List.getElem?_eq_some_iff.mp hk
      omega
    rw [hk]; dsimp only
    refine ⟨by simp; omega, hspr, ?_, hmem⟩
    rcases hph with ⟨hovf, hkn, -, hall⟩ | ⟨hovf, -, hspec⟩
    · rw [hovf]
      unfold overflowSpec
      symm
      rw [List.any_eq_false]
      intro j hj
      have hj' : j < 64 - (k + 1) := List.mem_range.mp hj
      have := hall j (by omega)
      simp [this]
    · rw [hovf, hspec]

theorem run_post : ∀ K (e : Ev), Inv oam L h e → mu e ≤ K → Post oam L h (iter (step oam L h) K e)
  | 0, e, hi, hmu => by
    have := inv_bounds oam L h hi
    show Post oam L h e
    exact post_of oam L h hi (by unfold mu at hmu; omega)
  | K + 1, e, hi, hmu => by
    by_cases hn : 64 ≤ e.n
    · rw [iter_done hn _]; exact post_of oam L h hi hn
    · have hb := inv_bounds oam L h hi
      have : mu (step oam L h e) < mu e := pstep_mu (B := getByte oam) (hit := fun b => inRangeSpec b L h) (Nat.lt_of_not_le hn) hb.2.2
      exact run_post K _ (inv_step oam L h hi) (by omega)

theorem iter_inv : ∀ K (e : Ev), Inv oam L h e → Inv oam L h (iter (step oam L h) K e)
  | 0, _, hi => hi
  | K + 1, _, hi => iter_inv K _ (inv_step oam L h hi)

/-- The abstract machine started from the dot-65 reset state. -/
def e0 (mem : Nat → UInt8) : Ev := ⟨0, 0, 0, false, false, mem⟩

theorem inv_e0 : Inv oam L h (e0 fun _ => 0xFF) := by
  left
  refine ⟨by decide, by decide, by simp [hb, e0], by simp [hb, e0], fun h' => absurd rfl h', rfl, ?_, ?_, ?_⟩
  · simp [e0, hb]
  · intro k hk; simp [hb, e0] at hk
  · intro b hb'; simp [e0] at hb'

theorem e0_post : Post oam L h (iter (step oam L h) 96 (e0 fun _ => 0xFF)) :=
  run_post oam L h 96 _ (inv_e0 oam L h) (by simp [mu, e0])

end


/-! ### Simulation: `evalDot` refines the abstract machine -/

/-- Sprite height in rows. -/
def hgt (s : State) : Nat := if s.sprTall then 16 else 8

theorem inRange_spec (b : UInt8) (L : UInt16) (s : State) :
    inRange b L (height s) = inRangeSpec b L.toNat (hgt s) := by
  have e1 : (b.toUInt16 ≤ L) ↔ b.toNat ≤ L.toNat := by rw [UInt16.le_iff_toNat_le]; simp
  unfold inRange inRangeSpec height hgt
  by_cases hle : b.toNat ≤ L.toNat
  · have e2 : (L - b.toUInt16).toNat = L.toNat - b.toNat := by
      rw [UInt16.toNat_sub_of_le _ _ (e1.mpr hle)]; simp
    cases s.sprTall <;> simp [e1, hle, UInt16.lt_iff_toNat_lt, e2] <;> omega
  · cases s.sprTall <;> simp [e1, hle]

/-- The machine state `t` is related to the abstract state `e`, with the read-only inputs
(OAM, line, `ctrl`) those of the start state `s0`. -/
def Rel (s0 t : State) (e : Ev) : Prop :=
  t.oam = s0.oam ∧ t.scanline = s0.scanline ∧ t.ctrl = s0.ctrl ∧ t.evalN.toNat = e.n ∧
  t.evalM.toNat = e.m ∧ t.evalSec.toNat = e.sec ∧ t.spr0Next = e.spr0 ∧
  t.status = (if e.ovf then s0.status ||| 0x20 else s0.status) ∧ t.secOam.size = 32 ∧
  ∀ j < 32, getByte t.secOam j = e.mem j

theorem rel_of_pack (s0 t : State) (k : Nat) (e' : Ev) {n m sec latch st : UInt8} {spr0 : Bool}
    {i b : UInt8} (hk1 : 1 ≤ k) (hk2 : k ≤ 256)
    (hst : evalStep { t with dot := k.toUInt16 } = packEval n m sec latch st spr0 i b)
    (R0 : t.oam = s0.oam ∧ t.scanline = s0.scanline ∧ t.ctrl = s0.ctrl ∧ t.secOam.size = 32)
    (hn : n.toNat = e'.n) (hm : m.toNat = e'.m) (hs : sec.toNat = e'.sec) (hsp : spr0 = e'.spr0)
    (hstat : st = if e'.ovf then s0.status ||| 0x20 else s0.status)
    (hmem : ∀ j < 32, getByte (t.secOam.set! (i &&& 0x1F).toNat b) j = e'.mem j) :
    Rel s0 (evalDot { t with dot := k.toUInt16 }) e' := by
  rw [evalDot_pack _ (dot_ok k hk1 hk2) hst]
  exact ⟨R0.1, R0.2.1, R0.2.2.1, hn, hm, hs, hsp, hstat, by simp [R0.2.2.2], hmem⟩

theorem dot_le64 (k : Nat) (hk : k < 65536) : (k.toUInt16 ≤ 64) ↔ k ≤ 64 := by
  rw [UInt16.le_iff_toNat_le, u16 k hk]; rfl

theorem dot_odd (k : Nat) : (k.toUInt16 &&& 1 == 1) = decide (k % 2 = 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← dot_and1]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UInt16.toNat_inj.mp h

theorem dot_even (k : Nat) : (k.toUInt16 &&& 1 == 0) = decide (k % 2 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← dot_and1]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UInt16.toNat_inj.mp h

theorem dot_eq65 (k : Nat) (hk : k < 65536) : (k.toUInt16 == 65) = decide (k = 65) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg UInt16.toNat h; rw [u16 k hk] at this; exact this
  · intro h; subst h; rfl

/-- Clear-phase dot `k` (1–64): even dots write `$FF` to `secOam[k/2 - 1]`, nothing else moves. -/
theorem clear_dot (t : State) (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 64) :
    evalDot { t with dot := k.toUInt16 } =
      { t with dot := k.toUInt16,
               secOam := if k % 2 = 0 then t.secOam.set! (k / 2 - 1) 0xFF else t.secOam } := by
  by_cases hk : k % 2 = 0
  · have hst : evalStep { t with dot := k.toUInt16 } = packEval t.evalN t.evalM t.evalSec t.evalLatch
        t.status t.spr0Next (k.toUInt16 / 2 - 1).toUInt8 0xFF := by
      unfold evalStep
      simp only [(dot_le64 k (by omega)).mpr h2, ite_true, dot_even, hk, decide_true]
    rw [evalDot_pack _ (dot_ok k h1 (by omega)) hst, clear_idx k (by omega) h2]
    simp only [hk, ite_true]
  · have hst : evalStep { t with dot := k.toUInt16 } = packEval t.evalN t.evalM t.evalSec t.evalLatch
        t.status t.spr0Next 0 (getByte t.secOam 0) := by
      unfold evalStep
      simp only [(dot_le64 k (by omega)).mpr h2, ite_true, dot_even, hk, decide_false]
      rfl
    rw [evalDot_pack _ (dot_ok k h1 (by omega)) hst]
    simp only [hk, ite_false, show ((0 : UInt8) &&& 0x1F).toNat = 0 from rfl, set_getByte_self]

/-- Latch dot `k` (odd, 67–255): `evalLatch := oam[4·evalN + evalM]`, nothing else moves. -/
theorem latch_dot (t : State) (k : Nat) (h1 : 67 ≤ k) (h2 : k ≤ 255) (hk : k % 2 = 1) :
    evalDot { t with dot := k.toUInt16 } =
      { t with dot := k.toUInt16, evalLatch := getByte t.oam (4 * t.evalN.toNat + t.evalM.toNat) } := by
  have hst : evalStep { t with dot := k.toUInt16 } = packEval t.evalN t.evalM t.evalSec
      (getByte t.oam (4 * t.evalN.toNat + t.evalM.toNat)) t.status t.spr0Next 0 (getByte t.secOam 0) := by
    unfold evalStep
    have : ¬ k ≤ 64 := by omega
    simp only [dot_le64 k (by omega), this, ite_false, dot_odd, hk, decide_true, ite_true,
      dot_eq65 k (by omega), show ¬ k = 65 by omega, decide_false, Bool.false_eq_true]
  rw [evalDot_pack _ (dot_ok k (by omega) (by omega)) hst]
  simp only [show ((0 : UInt8) &&& 0x1F).toNat = 0 from rfl, set_getByte_self]

/-- Dot 65: reset `evalN evalM evalSec spr0Next` and latch `oam[0]`. -/
theorem latch_first (t : State) :
    evalDot { t with dot := (65 : Nat).toUInt16 } =
      { t with dot := (65 : Nat).toUInt16, evalN := 0, evalM := 0, evalSec := 0, spr0Next := false,
               evalLatch := getByte t.oam 0 } := by
  have hst : evalStep { t with dot := (65 : Nat).toUInt16 } = packEval 0 0 0
      (getByte t.oam 0) t.status false 0 (getByte t.secOam 0) := by
    unfold evalStep
    simp only [dot_le64 65 (by omega), dot_odd, dot_eq65 65 (by omega)]
    rfl
  rw [evalDot_pack _ (dot_ok 65 (by omega) (by omega)) hst]
  simp only [show ((0 : UInt8) &&& 0x1F).toNat = 0 from rfl, set_getByte_self]

theorem u8_or20_idem : ∀ x : UInt8, (x ||| 0x20) ||| 0x20 = x ||| 0x20 := by decide

/-- Act dot `k` (even, 66–256): the abstract step `pstep` on the latched byte. -/
theorem act_dot (s0 t : State) (e : Ev) (k : Nat) (h1 : 66 ≤ k) (h2 : k ≤ 256) (hk : k % 2 = 0)
    (R : Rel s0 t e) (hb : e.n ≤ 64 ∧ e.m < 4 ∧ e.sec ≤ 32)
    (hlatch : t.evalLatch = getByte s0.oam (4 * e.n + e.m)) :
    Rel s0 (evalDot { t with dot := k.toUInt16 }) (step s0.oam s0.scanline.toNat (hgt s0) e) := by
  obtain ⟨ho, hsc, hc, hN, hM, hS, hSp, hSt, hsz, hmem⟩ := R
  have hst0 : evalStep { t with dot := k.toUInt16 } = evalAct { t with dot := k.toUInt16 } := by
    unfold evalStep
    have : ¬ k ≤ 64 := by omega
    simp only [dot_le64 k (by omega), this, ite_false, dot_odd, show ¬ k % 2 = 1 by omega,
      decide_false, Bool.false_eq_true]
  have hhit : inRange t.evalLatch t.scanline (height t) =
      inRangeSpec (getByte s0.oam (4 * e.n + e.m)) s0.scanline.toNat (hgt s0) := by
    rw [hlatch, hsc, ← inRange_spec]
    unfold height State.sprTall; rw [hc]
  replace hhit : inRange t.evalLatch t.scanline (height { t with dot := k.toUInt16 }) =
      inRangeSpec (getByte s0.oam (4 * e.n + e.m)) s0.scanline.toNat (hgt s0) := hhit
  have R0 : t.oam = s0.oam ∧ t.scanline = s0.scanline ∧ t.ctrl = s0.ctrl ∧ t.secOam.size = 32 :=
    ⟨ho, hsc, hc, hsz⟩
  have hmem0 : ∀ j < 32, getByte (t.secOam.set! ((0 : UInt8) &&& 0x1F).toNat (getByte t.secOam 0)) j
      = e.mem j := by
    simp only [show ((0 : UInt8) &&& 0x1F).toNat = 0 from rfl, set_getByte_self]; exact hmem
  have hsec_upd : e.sec < 32 → ∀ j < 32, getByte (t.secOam.set! (t.evalSec &&& 0x1F).toNat t.evalLatch) j
      = (fun j => if j = e.sec then getByte s0.oam (4 * e.n + e.m) else e.mem j) j := by
    intro hs j hj
    rw [getByte_set, u8_and1F _ (by omega), hS, hsz, hlatch]
    by_cases hje : j = e.sec
    · subst hje; simp [hs]
    · simp only [show ¬ (e.sec = j ∧ e.sec < 32) from fun h => hje h.1.symm, ite_false, hje]
      exact hmem j hj
  unfold step pstep
  by_cases hn : 64 ≤ e.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    refine rel_of_pack s0 t k e (latch := t.evalLatch) (by omega) h2 ?_ R0 hN hM hS hSp hSt hmem0
    rw [hst0]; unfold evalAct
    simp only [(u8_ge64 _).mpr (hN ▸ hn), ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
    have hn' : ¬ (t.evalN ≥ 64) := by rw [u8_ge64, hN]; exact hn
    have hN1 : (t.evalN + 1).toNat = e.n + 1 := by rw [u8_succ _ (by omega), hN]
    by_cases hs : e.sec < 32
    · simp only [hs, ite_true]
      have hs' : t.evalSec < 32 := by rw [u8_lt32, hS]; exact hs
      have hS1 : (t.evalSec + 1).toNat = e.sec + 1 := by rw [u8_succ _ (by omega), hS]
      by_cases hc1 : e.m = 0 ∧ inRangeSpec (getByte s0.oam (4 * e.n + e.m)) s0.scanline.toNat (hgt s0) = false
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc1)]
        refine rel_of_pack s0 t k _ (latch := t.evalLatch) (by omega) h2 ?_ R0 hN1 hM hS hSp hSt (hsec_upd hs)
        rw [hst0]; unfold evalAct
        have : (t.evalM == 0 && !inRange t.evalLatch t.scanline (height { t with dot := k.toUInt16 })) = true := by
          rw [u8_beq0, hM, hhit, hc1.2, hc1.1]; rfl
        simp only [hn', ite_false, hs', ite_true, this]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc1)]
        have hcb : (t.evalM == 0 && !inRange t.evalLatch t.scanline (height { t with dot := k.toUInt16 })) = false := by
          rw [u8_beq0, hM, hhit]
          cases h' : inRangeSpec (getByte s0.oam (4 * e.n + e.m)) s0.scanline.toNat (hgt s0)
          · have : e.m ≠ 0 := fun h0 => hc1 ⟨h0, h'⟩
            simp [this]
          · simp
        have hsp : (t.spr0Next || (t.evalM == 0 && t.evalN == 0)) =
            (e.spr0 || (e.m == 0 && e.n == 0)) := by
          rw [u8_beq0, u8_beq0, hM, hN, hSp]; rfl
        by_cases h3 : e.m + 1 = 4
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
          refine rel_of_pack s0 t k _ (latch := t.evalLatch) (m := 0) (by omega) h2 ?_ R0 hN1 rfl hS1 hsp hSt (hsec_upd hs)
          rw [hst0]; unfold evalAct
          have : (t.evalM + 1 == 4) = true := by rw [u8_beq4 _ (by omega), hM, h3]; rfl
          simp only [hn', ite_false, hs', ite_true, hcb, this, Bool.false_eq_true]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
          have hM1 : (t.evalM + 1).toNat = e.m + 1 := by rw [u8_succ _ (by omega), hM]
          refine rel_of_pack s0 t k _ (latch := t.evalLatch) (by omega) h2 ?_ R0 hN hM1 hS1 hsp hSt (hsec_upd hs)
          rw [hst0]; unfold evalAct
          have : (t.evalM + 1 == 4) = false := by rw [u8_beq4 _ (by omega), hM]; simp [h3]
          simp only [hn', ite_false, hs', ite_true, hcb, this, Bool.false_eq_true]
    · simp only [hs, ite_false]
      have hs' : ¬ t.evalSec < 32 := by rw [u8_lt32, hS]; exact hs
      by_cases hh : inRangeSpec (getByte s0.oam (4 * e.n + e.m)) s0.scanline.toNat (hgt s0) = false
      · simp only [hh, Bool.false_eq_true, ite_false]
        refine rel_of_pack s0 t k _ (latch := t.evalLatch) (m := (t.evalM + 1) &&& 3) (by omega) h2 ?_ R0 hN1
          (by rw [u8_succ3 _ (by omega), hM]) hS hSp hSt hmem0
        rw [hst0]; unfold evalAct
        simp only [hn', ite_false, hs', hhit, hh, Bool.false_eq_true]
      · simp only [Bool.not_eq_false] at hh
        simp only [hh, ite_true]
        refine rel_of_pack s0 t k _ (latch := t.evalLatch) (n := 64) (st := t.status ||| 0x20) (by omega) h2 ?_ R0 rfl hM hS hSp ?_ hmem0
        · rw [hst0]; unfold evalAct
          simp only [hn', ite_false, hs', hhit, hh, ite_true]
        · rw [hSt]; cases e.ovf
          · rfl
          · exact u8_or20_idem _

/-! ### Running the dots -/

/-- `evalFrom d k s` runs evaluation dots `d + 1, …, d + k` (each `evalDot` on the state with
`dot` set to that dot, as `Nes.Ppu.Step` does after `advance`). -/
def evalFrom : Nat → Nat → State → State
  | _, 0, s => s
  | d, k + 1, s => evalFrom (d + 1) k (evalDot { s with dot := (d + 1).toUInt16 })

theorem evalFrom_add (d a b : Nat) (s : State) :
    evalFrom d (a + b) s = evalFrom (d + a) b (evalFrom d a s) := by
  induction a generalizing d s with
  | zero => simp [evalFrom]
  | succ a ih =>
    rw [Nat.add_right_comm, evalFrom, ih, evalFrom, Nat.add_assoc, Nat.add_comm 1 a]

theorem foldl_evalFrom (d k : Nat) (s : State) :
    (List.range' d k).foldl (fun t i => evalDot { t with dot := (i + 1).toUInt16 }) s =
      evalFrom d k s := by
  induction k generalizing d s with
  | zero => rfl
  | succ k ih => exact ih (d + 1) _

/-- Clear phase (dots 1–64): only `dot` and secondary OAM change, and secondary OAM is all `$FF`. -/
theorem clear_phase (s : State) (hdot : s.dot = 0) (hsz : s.secOam.size = 32) :
    ∀ k ≤ 64, ∃ X : ByteArray, evalFrom 0 k s = { s with dot := k.toUInt16, secOam := X } ∧
      X.size = 32 ∧ ∀ j < k / 2, getByte X j = 0xFF
  | 0, _ => ⟨s.secOam, by rw [evalFrom]; cases s; simp_all, hsz, fun j hj => by omega⟩
  | k + 1, hk => by
    obtain ⟨X, hX, hXs, hXc⟩ := clear_phase s hdot hsz k (by omega)
    refine ⟨if (k + 1) % 2 = 0 then X.set! ((k + 1) / 2 - 1) 0xFF else X, ?_, ?_, ?_⟩
    · rw [evalFrom_add, hX]
      show evalDot { { s with dot := k.toUInt16, secOam := X } with dot := (0 + k + 1).toUInt16 } = _
      rw [show 0 + k + 1 = k + 1 by omega, clear_dot _ (k + 1) (by omega) hk]
    · split <;> simp [hXs]
    · intro j hj
      split
      · rw [getByte_set]
        by_cases hj' : j < k / 2
        · split
          · rfl
          · exact hXc j hj'
        · have : (k + 1) / 2 - 1 = j ∧ (k + 1) / 2 - 1 < X.size := by omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
      · exact hXc j (by omega)

/-- Dots `k + 1` (latch) and `k + 2` (act) refine one abstract step. -/
theorem pair_dots (s0 t : State) (e : Ev) (k : Nat) (h1 : 66 ≤ k) (h2 : k + 2 ≤ 256)
    (hk : k % 2 = 0) (R : Rel s0 t e) (hb : e.n ≤ 64 ∧ e.m < 4 ∧ e.sec ≤ 32) :
    Rel s0 (evalFrom k 2 t) (step s0.oam s0.scanline.toNat (hgt s0) e) := by
  show Rel s0 (evalDot { evalDot { t with dot := (k + 1).toUInt16 } with dot := (k + 1 + 1).toUInt16 }) _
  rw [latch_dot t (k + 1) (by omega) (by omega) (by omega)]
  obtain ⟨ho, hsc, hc, hN, hM, hS, hSp, hSt, hsz, hmem⟩ := R
  exact act_dot s0 _ e (k + 1 + 1) (by omega) (by omega) (by omega)
    ⟨ho, hsc, hc, hN, hM, hS, hSp, hSt, hsz, hmem⟩ hb (by simp only [ho, hN, hM])

theorem pairs (s0 : State) : ∀ q (t : State) (e : Ev), 2 * q ≤ 190 → Rel s0 t e →
    Inv s0.oam s0.scanline.toNat (hgt s0) e →
    Rel s0 (evalFrom (256 - 2 * q) (2 * q) t) (iter (step s0.oam s0.scanline.toNat (hgt s0)) q e)
  | 0, _, _, _, R, _ => R
  | q + 1, t, e, hq, R, hi => by
    rw [show 2 * (q + 1) = 2 + 2 * q by omega, evalFrom_add,
      show 256 - (2 + 2 * q) + 2 = 256 - 2 * q by omega]
    exact pairs s0 q _ _ (by omega)
      (pair_dots s0 t e _ (by omega) (by omega) (by omega) R (inv_bounds _ _ _ hi))
      (inv_step _ _ _ hi)

/-- The whole of evaluation (dots 1–256) as `Nes.Ppu.Step` runs it on a visible line: each dot
sets `dot` and calls `evalDot`. -/
def evalLine (s : State) : State :=
  (List.range 256).foldl (fun t i => evalDot { t with dot := (i + 1).toUInt16 }) s

theorem evalLine_rel (s : State) (hdot : s.dot = 0) (hsz : s.secOam.size = 32) :
    Rel s (evalLine s) (iter (step s.oam s.scanline.toNat (hgt s)) 96 (e0 fun _ => 0xFF)) := by
  unfold evalLine
  rw [List.range_eq_range', foldl_evalFrom]
  have h256 : evalFrom 0 256 s = evalFrom 0 (64 + (2 + 2 * 95)) s := rfl
  rw [h256, evalFrom_add, evalFrom_add]
  obtain ⟨X, hX, hXs, hXc⟩ := clear_phase s hdot hsz 64 (Nat.le_refl _)
  rw [hX]
  -- dots 65–66: reset, latch `oam[0]`, first act
  have R65 : Rel s { { s with dot := (64 : Nat).toUInt16, secOam := X } with
      dot := (65 : Nat).toUInt16, evalN := 0, evalM := 0, evalSec := 0, spr0Next := false,
      evalLatch := getByte s.oam 0 } (e0 fun _ => 0xFF) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [e0], hXs, fun j hj => hXc j (by omega)⟩
  have R66 : Rel s (evalFrom 64 2 { s with dot := (64 : Nat).toUInt16, secOam := X })
      (step s.oam s.scanline.toNat (hgt s) (e0 fun _ => 0xFF)) := by
    show Rel s (evalDot { evalDot { { s with dot := (64 : Nat).toUInt16, secOam := X } with
      dot := (65 : Nat).toUInt16 } with dot := (66 : Nat).toUInt16 }) _
    rw [latch_first]
    exact act_dot s _ _ 66 (by omega) (by omega) (by omega) R65 ⟨by decide, by decide, by decide⟩ rfl
  have h := pairs s 95 _ _ (by omega) R66 (inv_step _ _ _ (inv_e0 _ _ _))
  rw [show 256 - 2 * 95 = 64 + 2 from rfl, iter_succ] at h
  rw [Nat.zero_add]
  exact h


theorem u8_shr2 : ∀ x : UInt8, (x >>> 2).toNat = x.toNat / 4 := by decide
theorem u8_or20_bit : ∀ x : UInt8, ((x ||| 0x20) &&& 0x20 != 0) = true := by decide

end Nes.Ppu.Proofs.SpriteEval

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.Sprites Nes.Ppu.Proofs.SpriteEval

/-- **T-PPU-3 (sprite evaluation).** Running evaluation dots 1–256 (`evalLine`) from dot 0 of a
line `L = s.scanline`, with any OAM: secondary OAM starts with the four OAM bytes of each sprite
of `(evalSpec oam L h).1` — the first ≤ 8 in-range sprites in OAM order — `evalSec`, the sprite
count latched at dot 257 (`evalSec >>> 2`) and `spr0Next` agree with it, and the sprite-overflow
flag (status bit 5) is set exactly when the declarative buggy-walk predicate
`(evalSpec oam L h).2` holds (never cleared). -/
theorem T_PPU_3_eval (s : State) (hdot : s.dot = 0) (hsz : s.secOam.size = 32) :
    let spec := evalSpec s.oam s.scanline.toNat (if s.sprTall then 16 else 8)
    let r := evalLine s
    spec.1.length ≤ 8 ∧
    (∀ k (hk : k < spec.1.length), ∀ b < 4,
      getByte r.secOam (4 * k + b) = getByte s.oam (4 * spec.1[k] + b)) ∧
    r.evalSec.toNat = 4 * spec.1.length ∧ (r.evalSec >>> 2).toNat = spec.1.length ∧
    r.spr0Next = decide (0 ∈ spec.1) ∧
    r.status = (if spec.2 then s.status ||| 0x20 else s.status) ∧
    r.sprOverflow = (s.sprOverflow || spec.2) ∧
    r.oam = s.oam ∧ r.scanline = s.scanline ∧ r.ctrl = s.ctrl := by
  intro spec r
  have R := evalLine_rel s hdot hsz
  have P := e0_post s.oam s.scanline.toNat (hgt s)
  generalize iter (step s.oam s.scanline.toNat (hgt s)) 96 (e0 fun _ => 0xFF) = e at R P
  obtain ⟨ho, hsc, hc, hN, hM, hS, hSp, hSt, hsz', hmem⟩ := R
  obtain ⟨psec, pspr, povf, pmem⟩ := P
  have hlen : spec.1.length ≤ 8 := by
    show ((hb s.oam s.scanline.toNat _ 64).take 8).length ≤ 8
    exact List.length_take_le _ _
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ho, hsc, hc⟩
  · intro k hk b hb
    rw [hmem _ (by omega)]
    exact pmem k hk b hb
  · rw [hS, psec]; rfl
  · rw [u8_shr2, hS, psec]; show 4 * spec.1.length / 4 = _; omega
  · rw [hSp]
    cases h : e.spr0
    · symm; simp only [decide_eq_false_iff_not]; intro h0; exact absurd (pspr.mpr h0) (by simp [h])
    · symm; simp only [decide_eq_true_eq]; exact pspr.mp h
  · rw [hSt, povf]; rfl
  · unfold State.sprOverflow
    rw [hSt, povf]
    show _ = (_ || (evalSpec s.oam s.scanline.toNat (hgt s)).2)
    cases (evalSpec s.oam s.scanline.toNat (hgt s)).2
    · simp
    · simp only [ite_true, u8_or20_bit, Bool.or_true]

end Nes.Ppu.Proofs
