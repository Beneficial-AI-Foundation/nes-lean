import Nes.Ppu.Registers

/-!
# `Nes.Ppu.Proofs.Loopy` — T-PPU-2 (loopy algebra), T-REF-2 (loopy fields)

## Spec

Throughout, `v t : UInt16` are loopy words, `toFields` is their field view (coarse X bits 0–4,
coarse Y 5–9, nametable 10–11, fine Y 12–14), and `Nat.repeat f n` is `f` applied `n` times.

* **T-PPU-2 (incX).** Thirty-two coarse-X increments flip bit 10 (horizontal nametable) and
  change nothing else: `Nat.repeat incX 32 v = v ^^^ 0x0400`; in particular coarse X returns
  to where it started (0 if it started at 0) (`T_PPU_2_incX_32`).
* **T-PPU-2 (incY).** From fine Y = 7, coarse Y = 29: fine Y and coarse Y become 0 and bit 11
  (vertical nametable) flips, all else unchanged: `incY v = (v &&& ~~~0x73E0) ^^^ 0x0800`
  (`T_PPU_2_incY_29`). From fine Y = 7, coarse Y = 31: both become 0 and bit 11 is *not*
  flipped: `incY v = v &&& ~~~0x73E0` (`T_PPU_2_incY_31`).
* **T-PPU-2 (copyX/copyY).** `copyX v t` agrees with `t` on `maskX = 0x041F` (coarse X, bit 10)
  and with `v` elsewhere (`T_PPU_2_copyX`); `copyY v t` likewise with `maskY = 0x7BE0` (coarse
  Y, fine Y, bit 11) (`T_PPU_2_copyY`).
* **T-PPU-2 ($2005 pair).** From `w = false`, writing `d₁` then `d₂` to `$2005`: `w` is `true`
  after the first write and `false` after the second; `t`'s coarse X is `d₁ >> 3`, fine X
  `x = d₁ & 7`, coarse Y is `d₂ >> 3`, fine Y is `d₂ & 7`, the nametable bits and `v` are
  unchanged (`T_PPU_2_2005_pair`).
* **T-PPU-2 ($2006 pair).** From `w = false`, writing `d₁` then `d₂` to `$2006`: `w` is `true`
  then `false`; `t = ((d₁ & 0x3F) << 8) | d₂` (bit 14 cleared), `v = t`, `x` unchanged
  (`T_PPU_2_2006_pair`).
* **T-REF-2 (loopy).** The bit-twiddled word operations equal the field-level spec through
  `toFields`: `toFields (incX v) = (toFields v).incX`, likewise `incY`, and
  `toFields (copyX v t) = Fields.copyX (toFields v) (toFields t)`, likewise `copyY`
  (`T_REF_2_loopy`). Also `Fields.toWord` is a left inverse of `toFields` on 15-bit words
  (`toWord_toFields`), so the field view loses nothing.

Method: unfold to `UInt16.toBitVec` and close by `bv_decide` (no case enumeration).
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.Loopy

set_option linter.unusedSimpArgs false

theorem Fields.ext_iff' {a b : Fields} :
    a = b ↔ a.coarseX = b.coarseX ∧ a.coarseY = b.coarseY ∧ a.nt = b.nt ∧ a.fineY = b.fineY := by
  cases a; cases b; simp

/-- Unfold loopy words to `BitVec 16` and bit-blast. -/
local macro "loopy_bv" : tactic =>
  `(tactic| (
    simp only [incX, incY, copyX, copyY, maskX, maskY, coarseX, coarseY, fineY, nt,
      Fields.incX, Fields.incY, Fields.copyX, Fields.copyY, toFields, Fields.toWord,
      Fields.ext_iff', apply_ite UInt16.toBitVec, apply_ite Fields.coarseX,
      apply_ite Fields.coarseY, apply_ite Fields.nt, apply_ite Fields.fineY,
      beq_iff_eq, bne_iff_ne, ne_eq, ← UInt16.toBitVec_inj, UInt16.toBitVec_and,
      UInt16.toBitVec_or, UInt16.toBitVec_xor, UInt16.toBitVec_add, UInt16.toBitVec_not,
      UInt16.toBitVec_shiftLeft, UInt16.toBitVec_shiftRight, UInt8.toBitVec_toUInt16,
      UInt8.toBitVec_and, UInt8.toBitVec_shiftRight, Nat.repeat] at *
    bv_decide))

/-! ### T-PPU-2 -/

theorem T_PPU_2_incX_32 (v : UInt16) : Nat.repeat incX 32 v = v ^^^ 0x0400 := by loopy_bv

theorem T_PPU_2_incY_29 (v : UInt16) (hf : fineY v = 7) (hc : coarseY v = 29) :
    incY v = (v &&& ~~~0x73E0) ^^^ 0x0800 := by loopy_bv

theorem T_PPU_2_incY_31 (v : UInt16) (hf : fineY v = 7) (hc : coarseY v = 31) :
    incY v = v &&& ~~~0x73E0 := by loopy_bv

theorem T_PPU_2_copyX (v t : UInt16) :
    copyX v t &&& maskX = t &&& maskX ∧ copyX v t &&& ~~~maskX = v &&& ~~~maskX := by
  constructor <;> loopy_bv

theorem T_PPU_2_copyY (v t : UInt16) :
    copyY v t &&& maskY = t &&& maskY ∧ copyY v t &&& ~~~maskY = v &&& ~~~maskY := by
  constructor <;> loopy_bv

theorem T_PPU_2_2005_pair (s : State) (d₁ d₂ : UInt8) (hw : s.w = false) :
    let s₁ := s.writeScroll d₁
    let s₂ := s₁.writeScroll d₂
    s₁.w = true ∧ s₂.w = false ∧ s₂.x = d₁ &&& 7 ∧ s₂.v = s.v ∧
    coarseX s₂.t = (d₁ >>> 3).toUInt16 ∧ coarseY s₂.t = (d₂ >>> 3).toUInt16 ∧
    fineY s₂.t = (d₂ &&& 7).toUInt16 ∧ nt s₂.t = nt s.t := by
  simp only [State.writeScroll, hw, Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> loopy_bv

theorem T_PPU_2_2006_pair (s : State) (d₁ d₂ : UInt8) (hw : s.w = false) :
    let s₁ := s.writeAddr d₁
    let s₂ := s₁.writeAddr d₂
    s₁.w = true ∧ s₂.w = false ∧ s₂.t = ((d₁ &&& 0x3F).toUInt16 <<< 8) ||| d₂.toUInt16 ∧
    s₂.v = s₂.t ∧ s₂.x = s.x := by
  simp only [State.writeAddr, hw, Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true, true_and, and_true]
  loopy_bv

/-! ### T-REF-2 (loopy) -/

theorem T_REF_2_incX (v : UInt16) : toFields (incX v) = (toFields v).incX := by loopy_bv
theorem T_REF_2_incY (v : UInt16) : toFields (incY v) = (toFields v).incY := by loopy_bv
theorem T_REF_2_copyX (v t : UInt16) :
    toFields (copyX v t) = Fields.copyX (toFields v) (toFields t) := by loopy_bv
theorem T_REF_2_copyY (v t : UInt16) :
    toFields (copyY v t) = Fields.copyY (toFields v) (toFields t) := by loopy_bv

theorem T_REF_2_loopy (v t : UInt16) :
    toFields (incX v) = (toFields v).incX ∧ toFields (incY v) = (toFields v).incY ∧
    toFields (copyX v t) = Fields.copyX (toFields v) (toFields t) ∧
    toFields (copyY v t) = Fields.copyY (toFields v) (toFields t) :=
  ⟨T_REF_2_incX v, T_REF_2_incY v, T_REF_2_copyX v t, T_REF_2_copyY v t⟩

theorem toWord_toFields (v : UInt16) (h : v < 0x8000) : (toFields v).toWord = v := by
  simp only [UInt16.lt_iff_toBitVec_lt] at h
  loopy_bv

end Nes.Ppu.Proofs
