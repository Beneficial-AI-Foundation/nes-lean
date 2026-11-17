import Nes.Cpu.Alu

/-!
# `Nes.Cpu.Proofs.Alu` — T-CPU-1 (flag arithmetic), T-CPU-2 (shift/rotate algebra), T-REF-2 (ALU)

## Spec

Throughout, `a m reg v : UInt8`, `c : Bool`, `f : Flags`, and `sval` is the two's-complement
value of a byte (`Alu.spec.sval`).

* **T-CPU-1 (ADC).** With `s = a + m + c` (naturals): `spec.adc` returns `s mod 256`, carry
  `↔ s ≥ 256`, overflow `↔ sval a + sval m + c ∉ [−128,127]`, and the Z/N it induces through
  `spec.nz` are `Z ↔ r = 0`, `N ↔ r ≥ 128` (`T_CPU_1_adc`).
* **T-CPU-1 (SBC).** SBC is ADC of the one's complement, `sbc a m c = adc a (~~~m) c`, for the
  borrow-arithmetic spec (a real proof) and for the fast layer (by definition)
  (`T_CPU_1_sbc_eq_adc_compl`).
* **T-CPU-1 (CMP/CPX/CPY).** `spec.cmp reg m` has the result and carry of `spec.sbc reg m true`
  (subtraction with no borrow); carry `↔ m ≤ reg`, `Z ↔ reg = m`, `N` = bit 7 of `reg − m`
  (`T_CPU_1_cmp`).
* **T-CPU-2.** `ror ∘ rol = id` and `rol ∘ ror = id` on `(value, carry)`, in both layers
  (`T_CPU_2_ror_rol`, `T_CPU_2_rol_ror`). ASL is `×2 mod 256` with carry = old bit 7
  (`T_CPU_2_asl`); LSR is `/2` with carry = old bit 0 (`T_CPU_2_lsr`).
* **T-REF-2 (ALU).** Every `fast` op equals its `spec`: `adc`, `sbc`, `cmp`, `asl/lsr/rol/ror`,
  `bit`, `inc/dec` (`T_REF_2_adc` … `T_REF_2_incdec`), and the raw-byte Z/N update agrees with
  the flag-record one: `Flags.ofByte (fast.nz p r) = spec.nz (Flags.ofByte p) r`
  (`T_REF_2_nz`).

Method: single-byte facts close by `decide` (256–512 kernel cases); the two-operand facts are
bridged to `toNat` and closed by `omega`, with the purely bitwise steps (carry bit of a 16-bit
sum, the ADC overflow formula, the `nz` byte update) closed by `bv_decide`.
-/

namespace Nes.Cpu.Proofs

open Nes.Cpu Nes.Cpu.Alu

/-! ### Bit-level helpers (`bv_decide`) -/

/-- Bit 8 of a 9-bit value is set iff it is at least 256. -/
theorem carry16 (x : UInt16) (h : x < 512) : (x &&& 0x100 != 0) = decide (256 ≤ x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  bv_decide

/-- The ADC overflow bit trick is "same-sign operands, different-sign result". -/
theorem ovf8 (a m k : UInt8) (hk : k ≤ 1) :
    ((a ^^^ (a + m + k)) &&& (m ^^^ (a + m + k)) &&& 0x80 != 0) =
      decide ((a < 128 ∧ m < 128 ∧ 128 ≤ a + m + k) ∨ (128 ≤ a ∧ 128 ≤ m ∧ a + m + k < 128)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  bv_decide

/-- The ADC overflow bit trick equals the spec's signed-range test. -/
theorem ovf_spec (a m : UInt8) (c : Bool) :
    ((a ^^^ (a + m + fast.cin c)) &&& (m ^^^ (a + m + fast.cin c)) &&& 0x80 != 0) =
      spec.sOut (spec.sval a + spec.sval m + c.toNat) := by
  have ha := a.toNat_lt; have hm := m.toNat_lt
  rw [ovf8 _ _ _ (by cases c <;> decide)]
  simp only [spec.sOut, spec.sval, _root_.UInt8.lt_iff_toNat_lt, _root_.UInt8.le_iff_toNat_le,
    _root_.UInt8.toNat_add]
  cases c <;> simp only [fast.cin, Bool.toNat_false, Bool.toNat_true, ite_false, ite_true,
    Bool.false_eq_true] <;> split <;> split <;> rw [decide_eq_decide] <;>
    simp only [UInt8.reduceToNat] <;> omega

/-! ### T-REF-2: `fast = spec` -/

theorem T_REF_2_adc (a m : UInt8) (c : Bool) : fast.adc a m c = spec.adc a m c := by
  have ha := a.toNat_lt; have hm := m.toNat_lt
  have hs : (a.toUInt16 + m.toUInt16 + (fast.cin c).toUInt16).toNat =
      a.toNat + m.toNat + c.toNat := by
    cases c <;> simp [fast.cin, _root_.UInt16.toNat_add, _root_.UInt8.toNat_toUInt16] <;> omega
  have hr : (a.toUInt16 + m.toUInt16 + (fast.cin c).toUInt16).toUInt8 = a + m + fast.cin c := by
    apply _root_.UInt8.toNat_inj.mp
    rw [_root_.UInt16.toNat_toUInt8, hs]
    cases c <;> simp [fast.cin, _root_.UInt8.toNat_add] <;> omega
  simp only [fast.adc, spec.adc, Res.mk.injEq, hr]
  refine ⟨?_, ?_, ?_⟩
  · apply _root_.UInt8.toNat_inj.mp
    cases c <;> simp [fast.cin, _root_.UInt8.toNat_add] <;> omega
  · rw [carry16 _ (by rw [_root_.UInt16.lt_iff_toNat_lt, hs]; cases c <;> simp <;> omega)]
    simp only [decide_eq_decide, _root_.UInt16.le_iff_toNat_le, hs]; rfl
  · exact ovf_spec a m c

/-! ### T-CPU-1: flag arithmetic -/

/-- ADC: unsigned result/carry, signed overflow, and the Z/N it induces. -/
theorem T_CPU_1_adc (a m : UInt8) (c : Bool) (f : Flags) :
    (spec.adc a m c).r.toNat = (a.toNat + m.toNat + c.toNat) % 256 ∧
    ((spec.adc a m c).c = true ↔ 256 ≤ a.toNat + m.toNat + c.toNat) ∧
    ((spec.adc a m c).v = true ↔
      ¬(-128 ≤ spec.sval a + spec.sval m + c.toNat ∧
        spec.sval a + spec.sval m + c.toNat ≤ 127)) ∧
    ((spec.nz f (spec.adc a m c).r).z = true ↔ (spec.adc a m c).r = 0) ∧
    ((spec.nz f (spec.adc a m c).r).n = true ↔ 128 ≤ (spec.adc a m c).r.toNat) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [spec.adc]
  · simp [spec.adc]
  · simp only [spec.adc, spec.sOut, decide_eq_true_eq]; omega
  · generalize (spec.adc a m c).r = r
    simp only [spec.nz, decide_eq_true_eq]
    revert r; decide
  · simp only [spec.nz, decide_eq_true_eq]

/-- SBC is ADC of the one's complement — a real theorem for the borrow-arithmetic spec, and
true by definition for the fast layer. -/
theorem T_CPU_1_sbc_eq_adc_compl (a m : UInt8) (c : Bool) :
    spec.sbc a m c = spec.adc a (~~~m) c ∧ fast.sbc a m c = fast.adc a (~~~m) c := by
  refine ⟨?_, rfl⟩
  have ha := a.toNat_lt; have hm := m.toNat_lt
  have hn : (~~~m).toNat = 255 - m.toNat := by
    revert m; decide
  simp only [spec.sbc, spec.adc, Res.mk.injEq, hn]
  refine ⟨?_, ?_, ?_⟩
  · apply _root_.UInt8.toNat_inj.mp
    cases c <;> simp [_root_.UInt8.toNat_ofNat] <;> omega
  · cases c <;> simp <;> omega
  · simp only [spec.sval, hn]
    congr 1
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> split <;> split <;> split <;>
      omega

/-- CMP/CPX/CPY: the result and carry of subtraction with no borrow (`sbc reg m true`);
carry `↔ m ≤ reg`, `Z ↔ reg = m`, `N` = bit 7 of `reg − m`. -/
theorem T_CPU_1_cmp (reg m : UInt8) (f : Flags) :
    (spec.cmp reg m).r = (spec.sbc reg m true).r ∧
    (spec.cmp reg m).c = (spec.sbc reg m true).c ∧
    ((spec.cmp reg m).c = true ↔ m.toNat ≤ reg.toNat) ∧
    ((spec.nz f (spec.cmp reg m).r).z = true ↔ reg = m) ∧
    ((spec.nz f (spec.cmp reg m).r).n = true ↔ 128 ≤ (reg - m).toNat) := by
  have ha := reg.toNat_lt; have hm := m.toNat_lt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply _root_.UInt8.toNat_inj.mp
    simp [spec.cmp, spec.sbc]; omega
  · simp [spec.cmp, spec.sbc]
  · simp [spec.cmp]
  · simp [spec.nz, spec.cmp, ← _root_.UInt8.toNat_inj]
    omega
  · simp [spec.nz, spec.cmp, _root_.UInt8.toNat_sub]
    omega

/-! ### T-REF-2 (continued) -/

theorem T_REF_2_sbc (a m : UInt8) (c : Bool) : fast.sbc a m c = spec.sbc a m c := by
  rw [(T_CPU_1_sbc_eq_adc_compl a m c).1, (T_CPU_1_sbc_eq_adc_compl a m c).2, T_REF_2_adc]

theorem T_REF_2_cmp (reg m : UInt8) : fast.cmp reg m = spec.cmp reg m := by
  have ha := reg.toNat_lt; have hm := m.toNat_lt
  simp only [fast.cmp, spec.cmp, RC.mk.injEq]
  refine ⟨?_, ?_⟩
  · apply _root_.UInt8.toNat_inj.mp
    simp [_root_.UInt8.toNat_sub]; omega
  · simp only [_root_.UInt8.le_iff_toNat_le]

theorem T_REF_2_shifts :
    (∀ v, fast.asl v = spec.asl v) ∧ (∀ v, fast.lsr v = spec.lsr v) ∧
    (∀ v c, fast.rol v c = spec.rol v c) ∧ (∀ v c, fast.ror v c = spec.ror v c) := by
  decide

theorem T_REF_2_bit (a m : UInt8) : fast.bit a m = spec.bit a m := by
  simp only [fast.bit, spec.bit, BitRes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · generalize a &&& m = x
    revert x; decide
  · revert m; decide
  · revert m; decide

theorem T_REF_2_incdec :
    (∀ v, fast.inc v = spec.inc v) ∧ (∀ v, fast.dec v = spec.dec v) := by
  decide

theorem T_REF_2_nz (p r : UInt8) : Flags.ofByte (fast.nz p r) = spec.nz (Flags.ofByte p) r := by
  have hz : decide (r.toNat = 0) = (r == 0) := by revert r; decide
  have hn : decide (128 ≤ r.toNat) = (r &&& 0x80 != 0) := by revert r; decide
  simp only [fast.nz, spec.nz, Flags.ofByte, Flags.mk.injEq, hz, hn]
  cases h : r == 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.false_eq_true, iff_false, iff_true,
      Decidable.not_not] at h ⊢ <;> bv_decide

/-! ### T-CPU-2: shift/rotate algebra -/

/-- `ror ∘ rol = id` on `(value, carry)`, in both layers. -/
theorem T_CPU_2_ror_rol (v : UInt8) (c : Bool) :
    spec.ror (spec.rol v c).r (spec.rol v c).c = ⟨v, c⟩ ∧
    fast.ror (fast.rol v c).r (fast.rol v c).c = ⟨v, c⟩ := by
  revert v c; decide

/-- `rol ∘ ror = id` on `(value, carry)`, in both layers. -/
theorem T_CPU_2_rol_ror (v : UInt8) (c : Bool) :
    spec.rol (spec.ror v c).r (spec.ror v c).c = ⟨v, c⟩ ∧
    fast.rol (fast.ror v c).r (fast.ror v c).c = ⟨v, c⟩ := by
  revert v c; decide

/-- ASL is `×2 mod 256`, carry = old bit 7. -/
theorem T_CPU_2_asl (v : UInt8) :
    (spec.asl v).r.toNat = 2 * v.toNat % 256 ∧ (spec.asl v).c = v.toNat.testBit 7 := by
  revert v; decide

/-- LSR is `/2`, carry = old bit 0. -/
theorem T_CPU_2_lsr (v : UInt8) :
    (spec.lsr v).r.toNat = v.toNat / 2 ∧ (spec.lsr v).c = v.toNat.testBit 0 := by
  revert v; decide

end Nes.Cpu.Proofs
