import Std.Tactic.BVDecide

/-!
# `Nes.Prelude.Bits` — `UInt8`/`UInt16` ↔ `BitVec`/`Nat` bridging

Registers are `UInt8`/`UInt16`. Proofs go through `toBitVec` (closed by `bv_decide`) for
bit-level facts and through `toNat` (closed by `omega`) for arithmetic facts. This file
collects the small helpers and bridging lemmas the rest of the development needs.

## Spec

* `UInt8.toNat_lt_256`, `UInt16.toNat_lt_65536`: every byte is `< 256`, every word `< 65536`.
* `UInt16.lo x` / `UInt16.hi x` are the low and high bytes of the 16-bit word `x`;
  `UInt16.ofLoHi lo hi` assembles a little-endian word from its two bytes.
* `ofLoHi_lo_hi`: splitting a word into bytes and reassembling it is the identity.
* `lo_ofLoHi`, `hi_ofLoHi`: assembling then splitting recovers each byte.
* `ofLoHi_eq_add`: `ofLoHi lo hi = lo + hi * 256` as 16-bit arithmetic.
* `toNat_ofLoHi`: numerically, `ofLoHi lo hi` is `lo + 256 * hi`.
* `toNat_lo`, `toNat_hi`: numerically, `lo x = x mod 256` and `hi x = x / 256`.
* `Bits.smoke_bv_decide`: the 6502 overflow-flag formula
  `(a ^ r) & (m ^ r) & 0x80 ≠ 0` (with `r = a + m`) holds exactly when `a` and `m` have the
  same sign bit and `r`'s sign bit differs from it (signed overflow). Closed by `bv_decide`.
* `Bits.smoke_omega`: an 8-bit add carries out (`a.toNat + m.toNat ≥ 256`) exactly when the
  wrapped sum is smaller than `a`. Closed by `omega` on `toNat`.
-/

namespace Nes

/-- Low byte of a 16-bit word. -/
@[inline] def UInt16.lo (x : UInt16) : UInt8 := x.toUInt8

/-- High byte of a 16-bit word. -/
@[inline] def UInt16.hi (x : UInt16) : UInt8 := (x >>> 8).toUInt8

/-- Little-endian assembly of a 16-bit word from its low and high bytes. -/
@[inline] def UInt16.ofLoHi (lo hi : UInt8) : UInt16 := lo.toUInt16 ||| (hi.toUInt16 <<< 8)

theorem UInt8.toNat_lt_256 (x : UInt8) : x.toNat < 256 := x.toNat_lt

theorem UInt16.toNat_lt_65536 (x : UInt16) : x.toNat < 65536 := x.toNat_lt

theorem UInt16.ofLoHi_lo_hi (x : UInt16) : UInt16.ofLoHi (UInt16.lo x) (UInt16.hi x) = x := by
  apply _root_.UInt16.eq_of_toBitVec_eq
  simp [UInt16.ofLoHi, UInt16.lo, UInt16.hi]
  bv_decide

theorem UInt16.lo_ofLoHi (l h : UInt8) : UInt16.lo (UInt16.ofLoHi l h) = l := by
  apply _root_.UInt8.eq_of_toBitVec_eq
  simp only [UInt16.ofLoHi, UInt16.lo, _root_.UInt8.toBitVec_toUInt16,
    _root_.UInt16.toBitVec_toUInt8, _root_.UInt16.toBitVec_or, _root_.UInt16.toBitVec_shiftLeft]
  bv_decide

theorem UInt16.hi_ofLoHi (l h : UInt8) : UInt16.hi (UInt16.ofLoHi l h) = h := by
  apply _root_.UInt8.eq_of_toBitVec_eq
  simp only [UInt16.ofLoHi, UInt16.hi, _root_.UInt8.toBitVec_toUInt16,
    _root_.UInt16.toBitVec_toUInt8, _root_.UInt16.toBitVec_or, _root_.UInt16.toBitVec_shiftLeft,
    _root_.UInt16.toBitVec_shiftRight]
  bv_decide

theorem UInt16.ofLoHi_eq_add (l h : UInt8) :
    UInt16.ofLoHi l h = l.toUInt16 + h.toUInt16 * 256 := by
  apply _root_.UInt16.eq_of_toBitVec_eq
  simp [UInt16.ofLoHi]
  bv_decide

theorem UInt16.toNat_ofLoHi (l h : UInt8) :
    (UInt16.ofLoHi l h).toNat = l.toNat + 256 * h.toNat := by
  rw [UInt16.ofLoHi_eq_add]
  simp [_root_.UInt16.toNat_add, _root_.UInt16.toNat_mul]
  have := l.toNat_lt; have := h.toNat_lt
  omega

theorem UInt16.toNat_lo (x : UInt16) : (UInt16.lo x).toNat = x.toNat % 256 := by
  simp [UInt16.lo]

theorem UInt16.toNat_hi (x : UInt16) : (UInt16.hi x).toNat = x.toNat / 256 := by
  simp [UInt16.hi]
  have := x.toNat_lt
  omega

namespace Bits

/-- Smoke test for `bv_decide`: the 6502 ADC overflow-flag formula is signed overflow. -/
theorem smoke_bv_decide (a m : UInt8) :
    ((a ^^^ (a + m)) &&& (m ^^^ (a + m)) &&& 0x80 ≠ 0) ↔
      (a.toBitVec.msb = m.toBitVec.msb ∧ (a + m).toBitVec.msb ≠ a.toBitVec.msb) := by
  bv_decide

/-- Smoke test for `omega`: an 8-bit add carries out iff the wrapped sum is below `a`. -/
theorem smoke_omega (a m : UInt8) : 256 ≤ a.toNat + m.toNat ↔ (a + m).toNat < a.toNat := by
  rw [_root_.UInt8.toNat_add]
  have := a.toNat_lt; have := m.toNat_lt
  omega

end Bits

end Nes
