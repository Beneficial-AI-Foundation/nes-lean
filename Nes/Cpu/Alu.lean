import Nes.Cpu.Types

/-!
# `Nes.Cpu.Alu` — the 2A03 ALU, as an arithmetic spec and a bit-trick implementation

The 2A03 is a 6502 without decimal mode: the `D` flag is storable but ADC/SBC ignore it, so
every operation here is binary.

Each operation has two definitions with *identical signatures*:

* `Alu.spec.op` — integer arithmetic on `toNat`/`Int` (carry = unsigned result out of
  `[0,255]`, overflow = signed result out of `[−128,127]`). Only used in proofs.
* `Alu.fast.op` — `UInt8`/`UInt16` bit tricks; the executor uses these.

so T-REF-2 is literally `∀ args, fast.op args = spec.op args` (and `fast.nz` vs `spec.nz` is
related through `Flags.ofByte`).

Design (hot path): the results are tiny structures of scalars (`Res`, `RC`, `BitRes`). Every
`fast` op is `@[inline]`, so at each use site the executor immediately projects the fields it
needs and Lean's compiler removes the constructor (case-of-constructor after inlining); no
structure is allocated on the hot path. The only `fast` op touching the status byte is
`fast.nz`, which updates `Z`/`N` in a raw `P` byte (same bits as `State.setZN`).

## Spec

* `spec.adc a m c`: with `s = a + m + c` (as naturals), result `s mod 256`, carry `s ≥ 256`,
  overflow `sA + sM + c ∉ [−128,127]` (signed values).
* `spec.sbc a m c`: with borrow `b = 1 − c`, result `(a − m − b) mod 256`, carry (no borrow)
  `a ≥ m + b`, overflow `sA − sM − b ∉ [−128,127]`. (T-CPU-1: `sbc a m c = adc a (~~~m) c`.)
* `spec.cmp r m`: result `(r − m) mod 256` (its Z/N are CMP's), carry `r ≥ m`.
* `spec.asl v`: `2v mod 256`, carry = bit 7. `spec.lsr v`: `v / 2`, carry = bit 0.
* `spec.rol v c`: `(2v + c) mod 256`, carry = bit 7. `spec.ror v c`: `v / 2 + 128c`, carry =
  bit 0. (T-CPU-2: `ror ∘ rol = id` on `(value, carry)`.)
* `spec.bit a m`: `Z ↔ a &&& m = 0`, `N` = bit 7 of `m`, `V` = bit 6 of `m`.
* `spec.inc v = (v + 1) mod 256`, `spec.dec v = (v + 255) mod 256`.
* `spec.nz f r`: flags `f` with `Z ↔ r = 0` and `N ↔ r ≥ 128`; `fast.nz p r` does the same on
  a raw status byte `p`.
-/

namespace Nes.Cpu.Alu

/-- Result of ADC/SBC: the 8-bit result, carry out, overflow. Z/N come from `r` via `nz`. -/
structure Res where
  r : UInt8
  c : Bool
  v : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Result of shifts/rotates/compares: the 8-bit result (for CMP only its Z/N matter) and
carry out. -/
structure RC where
  r : UInt8
  c : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Flags set by BIT. -/
structure BitRes where
  z : Bool
  v : Bool
  n : Bool
  deriving Repr, DecidableEq, Inhabited

namespace spec

/-- Two's-complement signed value of a byte, in `[−128,127]`. -/
def sval (x : UInt8) : Int := if x.toNat < 128 then x.toNat else (x.toNat : Int) - 256

/-- `true` iff the signed integer `i` does not fit in a signed byte. -/
def sOut (i : Int) : Bool := decide (i < -128 ∨ 127 < i)

def adc (a m : UInt8) (c : Bool) : Res :=
  let s := a.toNat + m.toNat + c.toNat
  { r := UInt8.ofNat s, c := decide (256 ≤ s), v := sOut (sval a + sval m + c.toNat) }

def sbc (a m : UInt8) (c : Bool) : Res :=
  let b := 1 - c.toNat
  { r := UInt8.ofNat (a.toNat + 512 - m.toNat - b), c := decide (m.toNat + b ≤ a.toNat),
    v := sOut (sval a - sval m - b) }

def cmp (reg m : UInt8) : RC :=
  { r := UInt8.ofNat (reg.toNat + 256 - m.toNat), c := decide (m.toNat ≤ reg.toNat) }

def asl (v : UInt8) : RC := { r := UInt8.ofNat (2 * v.toNat), c := decide (128 ≤ v.toNat) }

def lsr (v : UInt8) : RC := { r := UInt8.ofNat (v.toNat / 2), c := decide (v.toNat % 2 = 1) }

def rol (v : UInt8) (c : Bool) : RC :=
  { r := UInt8.ofNat (2 * v.toNat + c.toNat), c := decide (128 ≤ v.toNat) }

def ror (v : UInt8) (c : Bool) : RC :=
  { r := UInt8.ofNat (v.toNat / 2 + 128 * c.toNat), c := decide (v.toNat % 2 = 1) }

def bit (a m : UInt8) : BitRes :=
  { z := decide ((a &&& m).toNat = 0), v := decide ((m.toNat / 64) % 2 = 1),
    n := decide (128 ≤ m.toNat) }

def inc (v : UInt8) : UInt8 := UInt8.ofNat (v.toNat + 1)

def dec (v : UInt8) : UInt8 := UInt8.ofNat (v.toNat + 255)

/-- Set Z and N from a result byte, leaving the other flags unchanged. -/
def nz (f : Flags) (r : UInt8) : Flags :=
  { f with z := decide (r.toNat = 0), n := decide (128 ≤ r.toNat) }

end spec

namespace fast

/-- Carry-in as a byte. -/
@[inline] def cin (c : Bool) : UInt8 := if c then 1 else 0

@[inline] def adc (a m : UInt8) (c : Bool) : Res :=
  let s : UInt16 := a.toUInt16 + m.toUInt16 + (cin c).toUInt16
  let r := s.toUInt8
  { r := r, c := s &&& 0x100 != 0, v := (a ^^^ r) &&& (m ^^^ r) &&& 0x80 != 0 }

/-- SBC is ADC of the one's complement of the operand (carry = not borrow). -/
@[inline] def sbc (a m : UInt8) (c : Bool) : Res := adc a (~~~m) c

@[inline] def cmp (reg m : UInt8) : RC := { r := reg - m, c := m ≤ reg }

@[inline] def asl (v : UInt8) : RC := { r := v <<< 1, c := v &&& 0x80 != 0 }

@[inline] def lsr (v : UInt8) : RC := { r := v >>> 1, c := v &&& 0x01 != 0 }

@[inline] def rol (v : UInt8) (c : Bool) : RC :=
  { r := (v <<< 1) ||| cin c, c := v &&& 0x80 != 0 }

@[inline] def ror (v : UInt8) (c : Bool) : RC :=
  { r := (v >>> 1) ||| (if c then 0x80 else 0), c := v &&& 0x01 != 0 }

@[inline] def bit (a m : UInt8) : BitRes :=
  { z := a &&& m == 0, v := m &&& 0x40 != 0, n := m &&& 0x80 != 0 }

@[inline] def inc (v : UInt8) : UInt8 := v + 1

@[inline] def dec (v : UInt8) : UInt8 := v - 1

/-- Set Z and N in the raw status byte `p` from the result `r` (same as `State.setZN`). -/
@[inline] def nz (p r : UInt8) : UInt8 :=
  (p &&& 0x7D) ||| (if r == 0 then 0x02 else 0) ||| (r &&& 0x80)

end fast

/-! Sanity checks (cases from SingleStepTests `nes6502/v1/69.json`, ADC #imm). -/

-- A=$7E + #$4A, C=0 → $C8, C=0, V=1 (P $6C → $EC)
example : spec.adc 0x7E 0x4A false = ⟨0xC8, false, true⟩ := by decide
example : fast.adc 0x7E 0x4A false = ⟨0xC8, false, true⟩ := by decide
-- A=$E8 + #$F7, C=0 → $DF, C=1, V=0 (P $EA → $A9)
example : spec.adc 0xE8 0xF7 false = ⟨0xDF, true, false⟩ := by decide
example : fast.adc 0xE8 0xF7 false = ⟨0xDF, true, false⟩ := by decide
-- SBC: $50 − $B0 with C=1 → $A0, borrow (C=0), V=1
example : spec.sbc 0x50 0xB0 true = ⟨0xA0, false, true⟩ := by decide
example : fast.sbc 0x50 0xB0 true = ⟨0xA0, false, true⟩ := by decide
example : spec.cmp 0x10 0x10 = ⟨0, true⟩ ∧ fast.cmp 0x10 0x10 = ⟨0, true⟩ := by decide
example : spec.rol 0x81 true = ⟨0x03, true⟩ ∧ fast.rol 0x81 true = ⟨0x03, true⟩ := by decide
example : spec.ror 0x03 true = ⟨0x81, true⟩ ∧ fast.ror 0x03 true = ⟨0x81, true⟩ := by decide
example : spec.bit 0x0F 0xC0 = ⟨true, true, true⟩ ∧ fast.bit 0x0F 0xC0 = ⟨true, true, true⟩ := by
  decide
example : spec.dec 0 = 0xFF ∧ fast.dec 0 = 0xFF ∧ spec.inc 0xFF = 0 ∧ fast.inc 0xFF = 0 := by
  decide
example : fast.nz 0x6C 0xC8 = 0xEC ∧ fast.nz 0xEA 0xDF = 0xE8 := by decide

end Nes.Cpu.Alu
