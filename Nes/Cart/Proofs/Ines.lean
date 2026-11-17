import Nes.Cart.Ines
import Std.Tactic.BVDecide

/-!
# T-CART-1 — iNES header round trip

## Spec

* `decode_encode`: decoding the bytes `Header.toBytes h` produces (bytes 4–15) gives back
  `h`, for every well-formed `h`.
* `parse_serialize` (T-CART-1): `Header.WF h → parse (serialize h) = some h`. `WF` says each
  field fits its bit field, NES 2.0-only fields are zero in an iNES 1.0 header, and the
  mirroring is `horizontal`, `vertical` or `fourScreen`.
* `parse_of_short`: input shorter than 16 bytes is rejected.
* `parse_of_bad_magic` (T-CART-1): if the first four bytes are not `"NES"` `$1A`, `parse`
  returns `none`.
* `serialize_size`: the encoding is 16 bytes.
-/

namespace Nes.Cart

theorem decode_encode (h : Header) (wf : h.WF) :
    decode h.prgBanks.toUInt8 h.chrBanks.toUInt8 h.byte6 h.byte7
      (((h.mapper >>> 8) &&& 0xF).toUInt8 ||| (h.submapper <<< 4))
      (((h.prgBanks >>> 8) &&& 0xF).toUInt8 ||| (((h.chrBanks >>> 8) &&& 0xF).toUInt8 <<< 4))
      (h.prgRamShift ||| (h.prgNvramShift <<< 4)) (h.chrRamShift ||| (h.chrNvramShift <<< 4))
      h.timing h.systemType h.miscRoms h.expansion = h := by
  obtain ⟨prg, chr, mapper, sub, mir, bat, tr, ct, n2, prs, pns, crs, cns, tim, sys, misc,
    exp⟩ := h
  obtain ⟨hmir, hct, hprg, hchr, hmap, hsub, hprs, hpns, hcrs, hcns, htim, hsys, hmisc,
    hexp⟩ := wf
  simp only at *
  rcases hmir with rfl | rfl | rfl <;> cases bat <;> cases tr <;> cases n2 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true] at * <;>
    simp only [decode, Header.byte6, Header.byte7, ite_true, ite_false, reduceCtorEq,
      Bool.false_eq_true] <;>
    (repeat' split) <;>
    simp only [Header.mk.injEq, reduceCtorEq, true_and, and_false, false_and,
      bne] at * <;>
    bv_decide

theorem parse_serialize (h : Header) (wf : h.WF) : parse (serialize h) = some h := by
  have hs : 16 ≤ (serialize h).size := Nat.le_refl _
  rw [parse, dite_eq_left hs]
  show (if magicOk 0x4E 0x45 0x53 0x1A then some (decode h.prgBanks.toUInt8 h.chrBanks.toUInt8
      h.byte6 h.byte7 (((h.mapper >>> 8) &&& 0xF).toUInt8 ||| (h.submapper <<< 4))
      (((h.prgBanks >>> 8) &&& 0xF).toUInt8 ||| (((h.chrBanks >>> 8) &&& 0xF).toUInt8 <<< 4))
      (h.prgRamShift ||| (h.prgNvramShift <<< 4)) (h.chrRamShift ||| (h.chrNvramShift <<< 4))
      h.timing h.systemType h.miscRoms h.expansion) else none) = some h
  rw [decode_encode h wf]; rfl

theorem serialize_size (h : Header) : (serialize h).size = 16 := rfl

theorem parse_of_short (b : ByteArray) (hb : b.size < 16) : parse b = none := by
  simp [parse, Nat.not_le.mpr hb]

theorem parse_of_bad_magic (b : ByteArray) (hb : 4 ≤ b.size)
    (bad : ¬ (b[0] = 0x4E ∧ b[1] = 0x45 ∧ b[2] = 0x53 ∧ b[3] = 0x1A)) : parse b = none := by
  unfold parse
  split
  · rw [ite_eq_right]
    simp only [magicOk, Bool.and_eq_true, beq_iff_eq]
    intro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    exact bad ⟨h0, h1, h2, h3⟩
  · rfl

end Nes.Cart
