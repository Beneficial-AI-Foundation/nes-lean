import Nes.Bus.Map

/-!
# `Nes.Bus.Proofs.Mirroring` — T-BUS-1 (mirroring laws) and fast-path agreement

## Spec

Throughout `a k : UInt16`; `n mod m` is on `a.toNat`.

**CPU decode, closed forms.** `decode a` is `ram (a mod $800)` on `$0000–$1FFF`
(`decode_ram`), `ppuReg (a mod 8)` on `$2000–$3FFF` (`decode_ppuReg`), `apuIo (a − $4000)` on
`$4000–$4017` (`decode_apuIo`) and `cart a` on `$4018–$FFFF` (`decode_cart`).

**T-BUS-1 (CPU).**
* `T_BUS_1_ram`: `a < $1800 → decode (a + $800) = decode a`.
* `T_BUS_1_ppuReg`: `k < $2000 → decode ($2000 + k) = decode ($2000 + k mod 8)`.

**T-BUS-1 (PPU).**
* `T_BUS_1_ppu_wrap`: the PPU bus is 14 bits, `ppuDecode (a + $4000) = ppuDecode a`.
* `T_BUS_1_palette`: on `$3F00–$3FFF`, `ppuDecode a = palette (palSpec a)` where
  `palSpec a = a mod 32 − 16` if `a mod 4 = 0 ∧ a mod 32 ≥ 16`, else `a mod 32`
  (`ppuDecode_palette`); hence `$3F10/14/18/1C` alias `$3F00/04/08/0C`
  (`T_BUS_1_palette_aliases`, and generally `T_BUS_1_palette`), and the 32-byte palette
  repeats through `$3FFF` (`T_BUS_1_palette_period`).
* `T_BUS_1_nametable_fold`: `$3000–$3EFF` decodes as `$2000–$2EFF`; every nametable target
  lies in `$2000–$2FFF` and keeps `a mod $1000` (`ppuDecode_nametable`).
* `T_BUS_1_nametable` (all five modes `m`): `ntCanonical m` is idempotent, lands in
  `$2000–$2FFF` (`ntCanonical_range`), and `ciramIndex m (ntCanonical m a) = ciramIndex m a`
  (CIRAM factors through the canonical address). Per mode the CIRAM cell is
  `page · $400 + a mod $400` with page `table / 2` (horizontal), `table mod 2` (vertical),
  `0` (singleLow), `1` (singleHigh), where `table = (a / $400) mod 4`
  (`T_BUS_1_ciram_horizontal` … `T_BUS_1_ciram_singleHigh`). `fourScreenIndex a = a mod $1000`.

**Fast-path agreement.** The four range predicates partition `UInt16`
(`fast_partition`, `fast_disjoint`); under each, `decode` returns the constructor built from
the raw offset (`decode_of_isRam`, `decode_of_isPpuReg`, `decode_of_isApuIo`,
`decode_of_isCart`), and the raw offsets are the spec indices
(`ramOffset_toNat`, `ppuRegOffset_toNat`, `apuIoOffset_toNat`).

Method: everything is moved to `toNat` (mask-with-`2^k−1` = `mod 2^k`, shift = division) and
closed by `omega`; table numbers (four values) are case-split and closed by `decide`.
No `bv_decide`, so only the standard axioms.
-/

namespace Nes.Bus.Proofs

open Nes Nes.Bus

/-! ### `toNat` bridging -/

private theorem and_mask (a : UInt16) (k : Nat) (m : UInt16) (hm : m.toNat = 2 ^ k - 1) :
    (a &&& m).toNat = a.toNat % 2 ^ k := by
  rw [UInt16.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

@[simp] private theorem nat_and_2047 (n : Nat) : n &&& 2047 = n % 2048 :=
  Nat.and_two_pow_sub_one_eq_mod n 11
@[simp] private theorem nat_and_7 (n : Nat) : n &&& 7 = n % 8 :=
  Nat.and_two_pow_sub_one_eq_mod n 3
@[simp] private theorem nat_and_16383 (n : Nat) : n &&& 16383 = n % 16384 :=
  Nat.and_two_pow_sub_one_eq_mod n 14
@[simp] private theorem nat_and_31 (n : Nat) : n &&& 31 = n % 32 :=
  Nat.and_two_pow_sub_one_eq_mod n 5
@[simp] private theorem nat_and_1023 (n : Nat) : n &&& 1023 = n % 1024 :=
  Nat.and_two_pow_sub_one_eq_mod n 10
@[simp] private theorem nat_and_4095 (n : Nat) : n &&& 4095 = n % 4096 :=
  Nat.and_two_pow_sub_one_eq_mod n 12
@[simp] private theorem nat_and_3 (n : Nat) : n &&& 3 = n % 4 :=
  Nat.and_two_pow_sub_one_eq_mod n 2

@[simp] theorem toNat_and_7FF (a : UInt16) : (a &&& 0x7FF).toNat = a.toNat % 2048 :=
  and_mask a 11 _ rfl
@[simp] theorem toNat_and_7 (a : UInt16) : (a &&& 0x7).toNat = a.toNat % 8 :=
  and_mask a 3 _ rfl
@[simp] theorem toNat_and_3FFF (a : UInt16) : (a &&& 0x3FFF).toNat = a.toNat % 16384 :=
  and_mask a 14 _ rfl
@[simp] theorem toNat_and_1F (a : UInt16) : (a &&& 0x1F).toNat = a.toNat % 32 :=
  and_mask a 5 _ rfl
@[simp] theorem toNat_and_3FF (a : UInt16) : (a &&& 0x3FF).toNat = a.toNat % 1024 :=
  and_mask a 10 _ rfl
@[simp] theorem toNat_and_FFF (a : UInt16) : (a &&& 0xFFF).toNat = a.toNat % 4096 :=
  and_mask a 12 _ rfl
@[simp] theorem toNat_and_3 (a : UInt16) : (a &&& 0x3).toNat = a.toNat % 4 :=
  and_mask a 2 _ rfl

theorem ramOffset_toNat (a : UInt16) : (ramOffset a).toNat = a.toNat % 2048 := by
  simp [ramOffset]
theorem ppuRegOffset_toNat (a : UInt16) : (ppuRegOffset a).toNat = a.toNat % 8 := by
  simp [ppuRegOffset]
theorem apuIoOffset_toNat (a : UInt16) (h : 0x4000 ≤ a) :
    (apuIoOffset a).toNat = a.toNat - 0x4000 := by
  simp [apuIoOffset, UInt16.toNat_sub_of_le _ _ h]

theorem ntOffset_toNat (a : UInt16) : (ntOffset a).toNat = a.toNat % 1024 := by
  simp [ntOffset]
theorem ntTable_toNat (a : UInt16) : (ntTable a).toNat = a.toNat / 1024 % 4 := by
  simp [ntTable, UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-! ### CPU decode: closed forms -/

theorem decode_ram (a : UInt16) (h : a < 0x2000) :
    decode a = .ram ⟨a.toNat % 2048, Nat.mod_lt _ (by decide)⟩ := by
  simp [decode, h, ramIndex, ramOffset]

theorem decode_ppuReg (a : UInt16) (h1 : 0x2000 ≤ a) (h2 : a < 0x4000) :
    decode a = .ppuReg ⟨a.toNat % 8, Nat.mod_lt _ (by decide)⟩ := by
  have : ¬ a < 0x2000 := by
    rw [UInt16.lt_iff_toNat_lt]; rw [UInt16.le_iff_toNat_le] at h1; simp at h1 ⊢; omega
  simp [decode, this, h2, ppuRegIndex, ppuRegOffset]

theorem decode_apuIo (a : UInt16) (h1 : 0x4000 ≤ a) (h2 : a < 0x4018) :
    decode a = .apuIo ⟨a.toNat - 0x4000, by
      rw [UInt16.lt_iff_toNat_lt] at h2; simp at h2; omega⟩ := by
  have n1 : ¬ a < 0x2000 := by
    rw [UInt16.lt_iff_toNat_lt]; rw [UInt16.le_iff_toNat_le] at h1; simp at h1 ⊢; omega
  have n2 : ¬ a < 0x4000 := by
    rw [UInt16.lt_iff_toNat_lt]; rw [UInt16.le_iff_toNat_le] at h1; simp at h1 ⊢; omega
  simp [decode, n1, n2, h2, apuIoOffset_toNat a h1]

theorem decode_cart (a : UInt16) (h : 0x4018 ≤ a) : decode a = .cart a := by
  rw [UInt16.le_iff_toNat_le] at h
  have n1 : ¬ a < 0x2000 := by rw [UInt16.lt_iff_toNat_lt]; simp at h ⊢; omega
  have n2 : ¬ a < 0x4000 := by rw [UInt16.lt_iff_toNat_lt]; simp at h ⊢; omega
  have n3 : ¬ a < 0x4018 := by rw [UInt16.lt_iff_toNat_lt]; simp at h ⊢; omega
  simp [decode, n1, n2, n3]

/-! ### T-BUS-1 (CPU) -/

theorem T_BUS_1_ram (a : UInt16) (h : a < 0x1800) : decode (a + 0x800) = decode a := by
  rw [UInt16.lt_iff_toNat_lt] at h; simp at h
  have e : (a + 0x800).toNat = a.toNat + 0x800 := by
    rw [UInt16.toNat_add]; simp; omega
  rw [decode_ram _ (by rw [UInt16.lt_iff_toNat_lt, e]; simp; omega),
    decode_ram _ (by rw [UInt16.lt_iff_toNat_lt]; simp; omega)]
  apply congrArg Target.ram; apply Fin.ext; show (a + 0x800).toNat % 2048 = a.toNat % 2048; rw [e]; omega

theorem T_BUS_1_ppuReg (k : UInt16) (h : k < 0x2000) :
    decode (0x2000 + k) = decode (0x2000 + k % 8) := by
  rw [UInt16.lt_iff_toNat_lt] at h; simp at h
  have e1 : (0x2000 + k).toNat = 0x2000 + k.toNat := by rw [UInt16.toNat_add]; simp; omega
  have e2 : (0x2000 + k % 8).toNat = 0x2000 + k.toNat % 8 := by
    rw [UInt16.toNat_add, UInt16.toNat_mod]; simp; omega
  rw [decode_ppuReg _ (by rw [UInt16.le_iff_toNat_le, e1]; simp)
      (by rw [UInt16.lt_iff_toNat_lt, e1]; simp; omega),
    decode_ppuReg _ (by rw [UInt16.le_iff_toNat_le, e2]; simp)
      (by rw [UInt16.lt_iff_toNat_lt, e2]; simp; omega)]
  simp only [e1, e2, Target.ppuReg.injEq, Fin.mk.injEq]; omega

/-! ### Fast-path agreement -/

theorem fast_partition (a : UInt16) : isRam a || isPpuReg a || isApuIo a || isCart a := by
  simp only [isRam, isPpuReg, isApuIo, isCart, UInt16.lt_iff_toNat_lt, UInt16.le_iff_toNat_le]
  simp; omega

theorem fast_disjoint (a : UInt16) :
    (isRam a && isPpuReg a) = false ∧ (isRam a && isApuIo a) = false ∧
    (isRam a && isCart a) = false ∧ (isPpuReg a && isApuIo a) = false ∧
    (isPpuReg a && isCart a) = false ∧ (isApuIo a && isCart a) = false := by
  simp only [isRam, isPpuReg, isApuIo, isCart, UInt16.lt_iff_toNat_lt, UInt16.le_iff_toNat_le]
  simp; omega

theorem decode_of_isRam (a : UInt16) (h : isRam a) : decode a = .ram (ramIndex a) := by
  simp only [isRam, decide_eq_true_eq] at h; simp [decode, h]

theorem decode_of_isPpuReg (a : UInt16) (h : isPpuReg a) :
    decode a = .ppuReg (ppuRegIndex a) := by
  simp only [isPpuReg, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [decode_ppuReg a h.1 h.2]; simp [ppuRegIndex, ppuRegOffset]

theorem decode_of_isApuIo (a : UInt16) (h : isApuIo a) :
    ∃ r : Fin 24, decode a = .apuIo r ∧ r.val = (apuIoOffset a).toNat := by
  simp only [isApuIo, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨_, decode_apuIo a h.1 h.2, (apuIoOffset_toNat a h.1).symm⟩

theorem decode_of_isCart (a : UInt16) (h : isCart a) : decode a = .cart a := by
  simp only [isCart, decide_eq_true_eq] at h; exact decode_cart a h

/-! ### PPU decode -/

theorem T_BUS_1_ppu_wrap (a : UInt16) : ppuDecode (a + 0x4000) = ppuDecode a := by
  have : (a + 0x4000) &&& 0x3FFF = a &&& 0x3FFF := by
    apply UInt16.toNat_inj.mp; simp [UInt16.toNat_add]
  simp only [ppuDecode, this]

/-- Palette cell of a palette-range address, as a `Nat` spec. -/
def palSpec (n : Nat) : Nat := if n % 4 = 0 ∧ 16 ≤ n % 32 then n % 32 - 16 else n % 32

theorem palSpec_lt (n : Nat) : palSpec n < 32 := by unfold palSpec; split <;> omega

theorem ppuDecode_palette (a : UInt16) (h1 : 0x3F00 ≤ a) (h2 : a < 0x4000) :
    ppuDecode a = .palette ⟨palSpec a.toNat, palSpec_lt _⟩ := by
  rw [UInt16.le_iff_toNat_le] at h1; rw [UInt16.lt_iff_toNat_lt] at h2; simp at h1 h2
  have e : a &&& 0x3FFF = a := by apply UInt16.toNat_inj.mp; simp; omega
  have n1 : ¬ a < 0x2000 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  have n2 : ¬ a < 0x3F00 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  simp only [ppuDecode, e, n1, n2, ↓reduceIte, PpuTarget.palette.injEq]
  apply Fin.ext
  simp only [paletteIndex, palSpec]
  have i1 : (a &&& 0x1F &&& 0x3).toNat = a.toNat % 4 := by simp
  by_cases c : a.toNat % 4 = 0 ∧ 16 ≤ a.toNat % 32
  · have hc : ((a &&& 0x1F &&& 0x3 == 0) && (0x10 ≤ a &&& 0x1F)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← UInt16.toNat_inj,
        UInt16.le_iff_toNat_le, i1]; simp; omega
    simp only [hc, c, ↓reduceDIte, ↓reduceIte, and_self]
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]; simp
  · have hc : ¬ ((a &&& 0x1F &&& 0x3 == 0) && (0x10 ≤ a &&& 0x1F)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← UInt16.toNat_inj,
        UInt16.le_iff_toNat_le, i1]; simp; omega
    simp only [hc, c, ↓reduceIte]; simp

/-- T-BUS-1 (palette): in `$3F00–$3FFF`, the sprite-backdrop entries alias the background
ones: `a mod 4 = 0`, `a mod 32 < 16` ⇒ `a + $10` decodes as `a`. -/
theorem T_BUS_1_palette (a : UInt16) (h1 : 0x3F00 ≤ a) (h2 : a < 0x3FF0)
    (h4 : a.toNat % 4 = 0) (h16 : a.toNat % 32 < 16) :
    ppuDecode (a + 0x10) = ppuDecode a := by
  rw [UInt16.le_iff_toNat_le] at h1; rw [UInt16.lt_iff_toNat_lt] at h2; simp at h1 h2
  have e : (a + 0x10).toNat = a.toNat + 0x10 := by rw [UInt16.toNat_add]; simp; omega
  rw [ppuDecode_palette _ (by rw [UInt16.le_iff_toNat_le, e]; simp; omega)
      (by rw [UInt16.lt_iff_toNat_lt, e]; simp; omega),
    ppuDecode_palette _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)
      (by rw [UInt16.lt_iff_toNat_lt]; simp; omega)]
  simp only [e, PpuTarget.palette.injEq, Fin.mk.injEq, palSpec]
  split <;> split <;> omega

theorem T_BUS_1_palette_aliases :
    ppuDecode 0x3F10 = ppuDecode 0x3F00 ∧ ppuDecode 0x3F14 = ppuDecode 0x3F04 ∧
    ppuDecode 0x3F18 = ppuDecode 0x3F08 ∧ ppuDecode 0x3F1C = ppuDecode 0x3F0C := by
  decide

theorem T_BUS_1_palette_period (a : UInt16) (h1 : 0x3F00 ≤ a) (h2 : a < 0x3FE0) :
    ppuDecode (a + 0x20) = ppuDecode a := by
  rw [UInt16.le_iff_toNat_le] at h1; rw [UInt16.lt_iff_toNat_lt] at h2; simp at h1 h2
  have e : (a + 0x20).toNat = a.toNat + 0x20 := by rw [UInt16.toNat_add]; simp; omega
  rw [ppuDecode_palette _ (by rw [UInt16.le_iff_toNat_le, e]; simp; omega)
      (by rw [UInt16.lt_iff_toNat_lt, e]; simp; omega),
    ppuDecode_palette _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)
      (by rw [UInt16.lt_iff_toNat_lt]; simp; omega)]
  simp only [e, PpuTarget.palette.injEq, Fin.mk.injEq, palSpec]
  split <;> split <;> omega

theorem ppuDecode_nametable (a : UInt16) (h1 : 0x2000 ≤ a) (h2 : a < 0x3F00) :
    ∃ b, ppuDecode a = .nametable b ∧ 0x2000 ≤ b ∧ b < 0x3000 ∧
      b.toNat % 0x1000 = a.toNat % 0x1000 := by
  rw [UInt16.le_iff_toNat_le] at h1; rw [UInt16.lt_iff_toNat_lt] at h2; simp at h1 h2
  have e : a &&& 0x3FFF = a := by apply UInt16.toNat_inj.mp; simp; omega
  have n1 : ¬ a < 0x2000 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  have p2 : a < 0x3F00 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  simp only [ppuDecode, e, n1, p2, ↓reduceIte, PpuTarget.nametable.injEq,
    exists_eq_left']
  by_cases c : (0x3000 : UInt16) ≤ a
  · have c' := c; rw [UInt16.le_iff_toNat_le] at c'; simp at c'
    have es : (a - 0x1000).toNat = a.toNat - 0x1000 := by
      rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]; simp
    simp only [c, ↓reduceIte, UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt, es]
    simp; omega
  · have c' := c; rw [UInt16.le_iff_toNat_le] at c'; simp at c'
    simp only [c, ↓reduceIte]
    simp only [UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt]; simp; omega

theorem T_BUS_1_nametable_fold (a : UInt16) (h1 : 0x3000 ≤ a) (h2 : a < 0x3F00) :
    ppuDecode a = ppuDecode (a - 0x1000) := by
  rw [UInt16.le_iff_toNat_le] at h1; rw [UInt16.lt_iff_toNat_lt] at h2; simp at h1 h2
  have es : (a - 0x1000).toNat = a.toNat - 0x1000 := by
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]; simp
  have e : a &&& 0x3FFF = a := by apply UInt16.toNat_inj.mp; simp; omega
  have e' : (a - 0x1000) &&& 0x3FFF = a - 0x1000 := by
    apply UInt16.toNat_inj.mp; simp only [toNat_and_3FFF, es]; omega
  have n1 : ¬ a < 0x2000 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  have p2 : a < 0x3F00 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  have c : (0x3000 : UInt16) ≤ a := by rw [UInt16.le_iff_toNat_le]; simp; omega
  have n1' : ¬ a - 0x1000 < 0x2000 := by rw [UInt16.lt_iff_toNat_lt, es]; simp; omega
  have p2' : a - 0x1000 < 0x3F00 := by rw [UInt16.lt_iff_toNat_lt, es]; simp; omega
  have c' : ¬ (0x3000 : UInt16) ≤ a - 0x1000 := by rw [UInt16.le_iff_toNat_le, es]; simp; omega
  simp only [ppuDecode, e, e', n1, p2, c, n1', p2', c', ↓reduceIte]

/-! ### Nametable mirroring -/

private theorem four_cases (t : UInt16) (h : t.toNat < 4) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  have : t.toNat = 0 ∨ t.toNat = 1 ∨ t.toNat = 2 ∨ t.toNat = 3 := by omega
  rcases this with h | h | h | h <;> simp [← UInt16.toNat_inj, h]

private theorem ntTable_lt (a : UInt16) : (ntTable a).toNat < 4 := by
  rw [ntTable_toNat]; omega

private theorem canonTable_lt (m : Mirroring) (a : UInt16) :
    (canonTable m (ntTable a)).toNat < 4 := by
  rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] <;> cases m <;> decide

theorem ntCanonical_toNat (m : Mirroring) (a : UInt16) :
    (ntCanonical m a).toNat = 0x2000 + (canonTable m (ntTable a)).toNat * 0x400 + a.toNat % 1024 := by
  have := canonTable_lt m a
  simp only [ntCanonical, UInt16.toNat_add, UInt16.toNat_mul, ntOffset_toNat]
  simp; omega

theorem ntCanonical_range (m : Mirroring) (a : UInt16) :
    0x2000 ≤ ntCanonical m a ∧ ntCanonical m a < 0x3000 := by
  have := canonTable_lt m a
  rw [UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt, ntCanonical_toNat]; simp; omega

private theorem ntTable_ntCanonical (m : Mirroring) (a : UInt16) :
    ntTable (ntCanonical m a) = canonTable m (ntTable a) := by
  have := canonTable_lt m a
  apply UInt16.toNat_inj.mp; rw [ntTable_toNat, ntCanonical_toNat]; omega

private theorem ntOffset_ntCanonical (m : Mirroring) (a : UInt16) :
    ntOffset (ntCanonical m a) = ntOffset a := by
  have := canonTable_lt m a
  apply UInt16.toNat_inj.mp; rw [ntOffset_toNat, ntOffset_toNat, ntCanonical_toNat]; omega

/-- T-BUS-1 (nametables): canonicalisation is idempotent. -/
theorem T_BUS_1_nametable_idem (m : Mirroring) (a : UInt16) :
    ntCanonical m (ntCanonical m a) = ntCanonical m a := by
  have h : canonTable m (canonTable m (ntTable a)) = canonTable m (ntTable a) := by
    rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] <;> cases m <;> decide
  calc ntCanonical m (ntCanonical m a)
      = 0x2000 + canonTable m (ntTable (ntCanonical m a)) * 0x400 + ntOffset (ntCanonical m a) :=
        rfl
    _ = ntCanonical m a := by rw [ntTable_ntCanonical, ntOffset_ntCanonical, h]; rfl

/-- T-BUS-1 (nametables): the CIRAM cell depends only on the canonical address. -/
theorem T_BUS_1_nametable (m : Mirroring) (a : UInt16) :
    ciramIndex m (ntCanonical m a) = ciramIndex m a := by
  have h : ciramPage m (canonTable m (ntTable a)) = ciramPage m (ntTable a) := by
    rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] <;> cases m <;> decide
  simp only [ciramIndex, ciramOffset, ntTable_ntCanonical, ntOffset_ntCanonical, h]

private theorem ciramIndex_val (m : Mirroring) (a : UInt16) :
    (ciramIndex m a).val = (ciramPage m (ntTable a)).toNat * 0x400 + a.toNat % 1024 := by
  have := (ciramIndex m a).isLt
  simp only [ciramIndex, ciramOffset] at this ⊢
  have hp : (ciramPage m (ntTable a)).toNat ≤ 3 := by
    rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] <;> cases m <;> decide
  simp only [UInt16.toNat_add, UInt16.toNat_mul, ntOffset_toNat]; simp; omega

theorem T_BUS_1_ciram_horizontal (a : UInt16) :
    (ciramIndex .horizontal a).val = (a.toNat / 1024 % 4 / 2) * 0x400 + a.toNat % 1024 := by
  rw [ciramIndex_val]
  have := ntTable_toNat a
  rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] at this ⊢ <;>
    simp [ciramPage] at this ⊢ <;> omega

theorem T_BUS_1_ciram_vertical (a : UInt16) :
    (ciramIndex .vertical a).val = (a.toNat / 1024 % 2) * 0x400 + a.toNat % 1024 := by
  rw [ciramIndex_val]
  have := ntTable_toNat a
  rcases four_cases _ (ntTable_lt a) with h | h | h | h <;> rw [h] at this ⊢ <;>
    simp [ciramPage] at this ⊢ <;> omega

theorem T_BUS_1_ciram_singleLow (a : UInt16) :
    (ciramIndex .singleLow a).val = a.toNat % 1024 := by
  rw [ciramIndex_val]; simp [ciramPage]

theorem T_BUS_1_ciram_singleHigh (a : UInt16) :
    (ciramIndex .singleHigh a).val = 0x400 + a.toNat % 1024 := by
  rw [ciramIndex_val]; simp [ciramPage]

theorem fourScreenIndex_val (a : UInt16) : (fourScreenIndex a).val = a.toNat % 4096 := by
  simp [fourScreenIndex]

end Nes.Bus.Proofs
