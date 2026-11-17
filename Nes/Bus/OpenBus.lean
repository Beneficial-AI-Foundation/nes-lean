/-!
# `Nes.Bus.OpenBus` — the CPU data-bus latch

## Spec

* `OpenBus` holds the last value driven on the CPU data bus (by any read or write). Reads of
  addresses nobody decodes return it unchanged (the bus capacitance holds the value).
* `OpenBus.latch ob v` records `v` as the new bus value; the system bus calls it after every
  CPU read (with the value returned) and every write (with the value written).
* `mergeOpen mask value bus` is the byte seen by a *partially driven* read: bits set in `mask`
  come from the device (`value`), the rest from the bus latch (`bus`):
  `(value &&& mask) ||| (bus &&& ~~~mask)`. Examples: `$2002` drives bits 5–7
  (`mask = $E0`, bits 0–4 are open bus); `$4016/$4017` drive bits 0–4 (`mask = $1F`, bits 5–7
  are open bus — usually `$40` from the high address byte).
* `mergeOpen_full`: a fully driven read (`mask = $FF`) returns `value`;
  `mergeOpen_none`: an undriven read (`mask = 0`) returns `bus`.
-/

namespace Nes.Bus

/-- The last value on the CPU data bus. -/
structure OpenBus where
  last : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Record `v` as the value now on the bus. -/
@[inline] def OpenBus.latch (_ : OpenBus) (v : UInt8) : OpenBus := ⟨v⟩

/-- Combine a partially driven read: `mask` bits from `value`, the others from `bus`. -/
@[inline] def mergeOpen (mask value bus : UInt8) : UInt8 :=
  (value &&& mask) ||| (bus &&& ~~~mask)

theorem mergeOpen_full (value bus : UInt8) : mergeOpen 0xFF value bus = value := by
  have h : value &&& 0xFF = value := by
    apply UInt8.toNat_inj.mp; rw [UInt8.toNat_and]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) value.toNat_lt
  simp [mergeOpen, h]

theorem mergeOpen_none (value bus : UInt8) : mergeOpen 0 value bus = bus := by
  simp [mergeOpen]

end Nes.Bus
