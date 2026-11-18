import Nes.Cart.Mappers.MMC3

/-!
# T-CART-2 / T-CART-4 for MMC3 (mapper 4)

## Spec

* `Mmc3.prgOffset_lt` / `Mmc3.chrOffset_lt` (T-CART-2): every PRG / CHR offset is in range.
* `Mmc3.prgOffset_fixed_last`: with `|PRG| = 8 KiB · 2^k` (`k ≥ 1`), `$E000+i` reads byte
  `|PRG| - $2000 + i` in both PRG modes (the reset vector is always in the last bank).
* T-CART-4 (IRQ counter, "new"/Sharp behaviour; see `Nes.Cart.Mappers.MMC3`):
  * `T_CART_4_fires`: a rising A12 edge after the filter gap (`lowDots ≥ a12Gap`), with
    `counter = 1`, no reload pending and IRQs enabled, clocks the counter to 0 and asserts IRQ.
  * `T_CART_4_reload`: on such an edge, if `counter = 0` or the reload flag is set, the counter
    becomes the latch, the reload flag clears, and IRQ is asserted iff it was already pending or
    (`latch = 0` and IRQs are enabled).
  * `T_CART_4_decrement`: otherwise the counter decrements and IRQ is asserted iff already
    pending or (the result is 0 and IRQs are enabled).
  * `T_CART_4_filter`: a high A12 dot after fewer than `a12Gap` low dots does not clock the
    counter (counter, reload flag and IRQ unchanged).
  * `T_CART_4_high`: A12 staying high changes nothing.
  * `T_CART_4_low`: a low A12 dot only advances the (saturating) low-time counter.
  * `T_CART_4_disable`: a `$E000` write clears the pending IRQ and disables IRQs;
    `T_CART_4_disabled_no_irq`: while disabled, no A12 activity asserts IRQ.
  * `T_CART_4_c001`: a `$C001` write clears the counter and sets the reload flag.
-/

namespace Nes.Cart.Mmc3

/-! ## T-CART-2 -/

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

theorem prgOffset_fixed_last (rom : Rom) (s : State) (a : UInt16) (k : Nat) (hk : 1 ≤ k)
    (h : rom.prg.size = 8192 * 2 ^ k) (ha : 0xE000 ≤ a) :
    (prgOffset rom s a).val = rom.prg.size - 8192 + (a.toNat - 0xE000) := by
  have hu := a.toNat_lt
  have ha' : 57344 ≤ a.toNat := ha
  have hw : (a >>> 13) &&& 3 = 3 := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_and, UInt16.toNat_shiftRight]
    have h7 : a.toNat >>> 13 = 7 := by rw [Nat.shiftRight_eq_div_pow]; omega
    show a.toNat >>> 13 &&& 3 = 3
    rw [h7]; rfl
  have hlo : (a &&& 0x1FFF).toNat = a.toNat - 0xE000 := by
    rw [UInt16.toNat_and, show (0x1FFF : UInt16).toNat = 2 ^ 13 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; omega
  have hp : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  simp only [prgOffset, prgBank, hw, hlo, h, Nat.mul_div_cancel_left _ (show 0 < 8192 by decide)]
  simp only [show ((3 : UInt16) == 0) = false from rfl, show ((3 : UInt16) == 1) = false from rfl,
    show ((3 : UInt16) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have : (2 ^ k - 1) * 8192 + (a.toNat - 57344) < 8192 * 2 ^ k := by
    rw [Nat.sub_mul]; omega
  rw [Nat.mod_eq_of_lt this, Nat.sub_mul]; omega

/-! ## T-CART-4 -/

private theorem le_ne_zero {x : UInt8} (h : a12Gap ≤ x) : (x == 0) = false := by
  have : (10 : Nat) ≤ x.toNat := h
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro hx; subst hx; simp at this

theorem T_CART_4_fires (s : State) (hgap : a12Gap ≤ s.lowDots) (hc : s.irqCounter = 1)
    (hr : s.irqReload = false) (he : s.irqEnabled = true) :
    (ppuA12 true s).irqCounter = 0 ∧ irq (ppuA12 true s) = true := by
  simp [ppuA12, irq, clock, le_ne_zero hgap, hgap, hc, hr, he]

theorem T_CART_4_reload (s : State) (hgap : a12Gap ≤ s.lowDots)
    (h : s.irqCounter = 0 ∨ s.irqReload = true) :
    (ppuA12 true s).irqCounter = s.irqLatch ∧ (ppuA12 true s).irqReload = false ∧
    irq (ppuA12 true s) = (s.irqPending || (s.irqLatch == 0 && s.irqEnabled)) := by
  have hb : (s.irqCounter == 0 || s.irqReload) = true := by
    rcases h with h | h <;> simp [h]
  simp [ppuA12, irq, clock, le_ne_zero hgap, hgap, hb]

theorem T_CART_4_decrement (s : State) (hgap : a12Gap ≤ s.lowDots)
    (hc : s.irqCounter ≠ 0) (hr : s.irqReload = false) :
    (ppuA12 true s).irqCounter = s.irqCounter - 1 ∧
    irq (ppuA12 true s) = (s.irqPending || (s.irqCounter - 1 == 0 && s.irqEnabled)) := by
  simp [ppuA12, irq, clock, le_ne_zero hgap, hgap, hc, hr]

theorem T_CART_4_filter (s : State) (hgap : s.lowDots < a12Gap) :
    (ppuA12 true s).irqCounter = s.irqCounter ∧ (ppuA12 true s).irqReload = s.irqReload ∧
    irq (ppuA12 true s) = irq s := by
  have : ¬ a12Gap ≤ s.lowDots := fun h => absurd hgap (UInt8.not_lt.mpr h)
  by_cases h0 : s.lowDots = 0 <;> simp [ppuA12, this, h0, irq]

theorem T_CART_4_high (s : State) (h : s.lowDots = 0) : ppuA12 true s = s := by
  simp [ppuA12, h]

theorem T_CART_4_low (s : State) :
    ppuA12 false s = { s with lowDots := if s.lowDots == 255 then 255 else s.lowDots + 1 } := by
  unfold ppuA12
  by_cases h : s.lowDots = 255
  · cases s; simp_all
  · simp [h]

theorem T_CART_4_disable (rom : Rom) (s : State) (a : UInt16) (v : UInt8)
    (ha : a &&& 0xE001 = 0xE000) :
    (regWrite rom s a v).irqPending = false ∧ (regWrite rom s a v).irqEnabled = false ∧
    irq (regWrite rom s a v) = false := by
  have h8 : ¬ a < 0x8000 := by
    intro hlt
    have hlt' : a.toNat < 32768 := hlt
    have := congrArg UInt16.toNat ha
    rw [UInt16.toNat_and] at this
    have : a.toNat &&& 57345 ≤ a.toNat := Nat.and_le_left
    simp at *; omega
  simp [regWrite, irq, h8, ha]

theorem T_CART_4_disabled_no_irq (s : State) (b : Bool) (he : s.irqEnabled = false)
    (hp : s.irqPending = false) :
    irq (ppuA12 b s) = false ∧ (ppuA12 b s).irqEnabled = false := by
  unfold ppuA12
  split
  · split
    · simp [irq, he, hp]
    · split <;> simp [clock, irq, he, hp]
  · split <;> simp [irq, he, hp]

theorem T_CART_4_c001 (rom : Rom) (s : State) (a : UInt16) (v : UInt8)
    (ha : a &&& 0xE001 = 0xC001) :
    (regWrite rom s a v).irqCounter = 0 ∧ (regWrite rom s a v).irqReload = true := by
  have h8 : ¬ a < 0x8000 := by
    intro hlt
    have hlt' : a.toNat < 32768 := hlt
    have := congrArg UInt16.toNat ha
    rw [UInt16.toNat_and] at this
    have : a.toNat &&& 57345 ≤ a.toNat := Nat.and_le_left
    simp at *; omega
  simp [regWrite, h8, ha]

end Nes.Cart.Mmc3
