import Nes.Cart.Mapper

/-!
# T-CART-3 — the MMC1 shift register

PLAN §6.3: five consecutive writes with bit 7 clear commit the 5-bit value to the register
selected by `addr[14:13]` and reset the shift state; any write with bit 7 set resets the
shift state and forces PRG mode 3.

## Spec

* `serialValue v₁ … v₅ = Σ (vᵢ &&& 1) <<< (i-1)`: the 5-bit value the writes carry (LSB first).
* `T_CART_3_commit_serial`: from the reset shift state (`shift = 0`, `count = 0`), five
  `serialWrite`s with bit 7 clear set register `regIdx a₅` (the fifth write's address) to
  `serialValue v₁ … v₅` and leave `shift = 0`, `count = 0`.
* `T_CART_3_commit`: the same through the mapper's `regWrite` (addresses `≥ $8000`).
* `T_CART_3_reset_serial` / `T_CART_3_reset`: a write (to `≥ $8000`) with bit 7 set yields
  `shift = 0`, `count = 0` and `prgMode = 3`, from any state.
* `regWriteAt_consecutive`: a serial write on the cycle right after the previous one
  (`cyc ≠ 0`, `cyc = consecCycle`) leaves the shift state and all registers unchanged;
  `regWriteAt_eq_regWrite`: otherwise it acts as `regWrite` (up to `consecCycle`).
-/

namespace Nes.Cart.Mmc1

/-- The 5-bit value carried by five serial writes (bit 0 of each, first write = bit 0). -/
def serialValue (v₁ v₂ v₃ v₄ v₅ : UInt8) : UInt8 :=
  (v₁ &&& (1 : UInt8)) ||| ((v₂ &&& (1 : UInt8)) <<< (1 : UInt8)) |||
    ((v₃ &&& (1 : UInt8)) <<< (2 : UInt8)) ||| ((v₄ &&& (1 : UInt8)) <<< (3 : UInt8)) |||
    ((v₅ &&& (1 : UInt8)) <<< (4 : UInt8))

private theorem and_one (v : UInt8) : v &&& 1 = 0 ∨ v &&& 1 = 1 := by
  have h : (v &&& 1).toNat < 2 := by
    rw [UInt8.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have : (v &&& 1).toNat = (0 : UInt8).toNat ∨ (v &&& 1).toNat = (1 : UInt8).toNat := by
    simp only [UInt8.toNat_zero, UInt8.toNat_one]; omega
  exact this.imp UInt8.toNat_inj.mp UInt8.toNat_inj.mp

@[simp] theorem getReg_setReg (s : State) (i : UInt16) (x : UInt8) :
    getReg (setReg s i x) i = x := by
  unfold setReg getReg
  by_cases h0 : i == 0 <;> by_cases h1 : i == 1 <;> by_cases h2 : i == 2 <;> simp [h0, h1, h2]

@[simp] theorem setReg_shift (s : State) (i : UInt16) (x : UInt8) :
    (setReg s i x).shift = s.shift := by
  unfold setReg; split <;> (try split) <;> (try split) <;> rfl

@[simp] theorem setReg_count (s : State) (i : UInt16) (x : UInt8) :
    (setReg s i x).count = s.count := by
  unfold setReg; split <;> (try split) <;> (try split) <;> rfl

@[simp] theorem getReg_consecCycle (s : State) (i : UInt16) (c : UInt64) :
    getReg { s with consecCycle := c } i = getReg s i := rfl

theorem T_CART_3_commit_serial (s : State) (h₀ : s.shift = 0) (hc : s.count = 0)
    (a₁ a₂ a₃ a₄ a₅ : UInt16) (v₁ v₂ v₃ v₄ v₅ : UInt8)
    (h₁ : v₁ &&& 0x80 = 0) (h₂ : v₂ &&& 0x80 = 0) (h₃ : v₃ &&& 0x80 = 0)
    (h₄ : v₄ &&& 0x80 = 0) (h₅ : v₅ &&& 0x80 = 0) :
    let s' := serialWrite (serialWrite (serialWrite (serialWrite (serialWrite s a₁ v₁) a₂ v₂)
      a₃ v₃) a₄ v₄) a₅ v₅
    getReg s' (regIdx a₅) = serialValue v₁ v₂ v₃ v₄ v₅ ∧ s'.shift = 0 ∧ s'.count = 0 := by
  intro s'
  have e : ∀ v : UInt8, v &&& 0x80 = 0 → (v &&& 0x80 != 0) = false := by
    intro v h; simp [h]
  simp only [s', serialWrite, e _ h₁, e _ h₂, e _ h₃, e _ h₄, e _ h₅, h₀, hc]
  simp (config := { decide := true }) only [↓reduceIte, getReg_setReg,
    setReg_shift, setReg_count, and_true]
  rcases and_one v₁ with g₁ | g₁ <;> rcases and_one v₂ with g₂ | g₂ <;>
    rcases and_one v₃ with g₃ | g₃ <;> rcases and_one v₄ with g₄ | g₄ <;>
    rcases and_one v₅ with g₅ | g₅ <;>
    simp only [serialValue, g₁, g₂, g₃, g₄, g₅] <;> decide

theorem serialWrite_consecCycle (t : State) (a : UInt16) (v : UInt8) (c : UInt64) :
    serialWrite { t with consecCycle := c } a v = { serialWrite t a v with consecCycle := c } := by
  unfold serialWrite setReg
  split
  · rfl
  · split
    · rfl
    · split <;> (try split) <;> (try split) <;> rfl

theorem regWrite_serial (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (ha : 0x8000 ≤ a) :
    regWrite rom s a v = { serialWrite s a v with consecCycle := 1 } := by
  simp [regWrite, regWriteAt, ha]

/-- T-CART-3 (commit) through the mapper's register-write operation. -/
theorem T_CART_3_commit (rom : Rom) (s : State) (h₀ : s.shift = 0) (hc : s.count = 0)
    (a₁ a₂ a₃ a₄ a₅ : UInt16) (v₁ v₂ v₃ v₄ v₅ : UInt8)
    (ha₁ : 0x8000 ≤ a₁) (ha₂ : 0x8000 ≤ a₂) (ha₃ : 0x8000 ≤ a₃) (ha₄ : 0x8000 ≤ a₄)
    (ha₅ : 0x8000 ≤ a₅)
    (h₁ : v₁ &&& 0x80 = 0) (h₂ : v₂ &&& 0x80 = 0) (h₃ : v₃ &&& 0x80 = 0)
    (h₄ : v₄ &&& 0x80 = 0) (h₅ : v₅ &&& 0x80 = 0) :
    let s' := regWrite rom (regWrite rom (regWrite rom (regWrite rom (regWrite rom s a₁ v₁)
      a₂ v₂) a₃ v₃) a₄ v₄) a₅ v₅
    getReg s' (regIdx a₅) = serialValue v₁ v₂ v₃ v₄ v₅ ∧ s'.shift = 0 ∧ s'.count = 0 := by
  intro s'
  have := T_CART_3_commit_serial s h₀ hc a₁ a₂ a₃ a₄ a₅ v₁ v₂ v₃ v₄ v₅ h₁ h₂ h₃ h₄ h₅
  simp only [s', regWrite_serial _ _ _ _ ha₁, regWrite_serial _ _ _ _ ha₂,
    regWrite_serial _ _ _ _ ha₃, regWrite_serial _ _ _ _ ha₄, regWrite_serial _ _ _ _ ha₅,
    serialWrite_consecCycle, getReg_consecCycle]
  exact this

/-- T-CART-3 (reset), serial port: a write with bit 7 set clears the shift state and selects
PRG mode 3. -/
theorem T_CART_3_reset_serial (s : State) (a : UInt16) (v : UInt8) (hv : v &&& 0x80 ≠ 0) :
    (serialWrite s a v).shift = 0 ∧ (serialWrite s a v).count = 0 ∧
      prgMode (serialWrite s a v) = 3 := by
  have hn : ∀ n < 256, ((n ||| 12) >>> 2) &&& 3 = 3 := by
    set_option maxRecDepth 100000 in decide
  have hm : ∀ c : UInt8, ((c ||| 0x0C) >>> 2) &&& 3 = 3 := by
    intro c; apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_and, UInt8.toNat_shiftRight, UInt8.toNat_or]
    simpa using hn c.toNat c.toNat_lt
  simp [serialWrite, hv, prgMode, hm]

/-- T-CART-3 (reset) through the mapper's register-write operation. -/
theorem T_CART_3_reset (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (ha : 0x8000 ≤ a)
    (hv : v &&& 0x80 ≠ 0) :
    (regWrite rom s a v).shift = 0 ∧ (regWrite rom s a v).count = 0 ∧
      prgMode (regWrite rom s a v) = 3 := by
  have := T_CART_3_reset_serial s a v hv
  simp only [regWrite, regWriteAt, ha, ↓reduceIte]
  simpa [prgMode] using this

/-- A serial write on the cycle right after the previous one is dropped: shift state and
registers are unchanged. -/
theorem regWriteAt_consecutive (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (c : UInt64)
    (hc : c ≠ 0) (hcc : s.consecCycle = c) (ha : 0x8000 ≤ a) :
    regWriteAt rom s a v c = { s with consecCycle := c + 1 } := by
  simp [regWriteAt, ha, hc, hcc]

/-- Otherwise a timed write acts as the untimed one (up to `consecCycle`). -/
theorem regWriteAt_eq_regWrite (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (c : UInt64)
    (h : c = 0 ∨ s.consecCycle ≠ c) (ha : 0x8000 ≤ a) :
    regWriteAt rom s a v c = { regWrite rom s a v with consecCycle := c + 1 } := by
  have : (c != 0 && c == s.consecCycle) = false := by
    rcases h with h | h
    · simp [h]
    · simp [Ne.symm h]
  simp [regWrite, regWriteAt, ha, this]

end Nes.Cart.Mmc1
