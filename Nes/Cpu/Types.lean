import Nes.Prelude.Bits

/-!
# `Nes.Cpu.Types` — 2A03 registers, status flags, CPU state

The 2A03 is a 6502 without decimal mode: the `D` flag is storable but ignored by ADC/SBC.
The 12 JAM opcodes are modelled by the `halted` field.

Representation: the status register is stored as a raw byte `State.p : UInt8` (compiles to
bit ops on an unboxed scalar, no structure allocation, and the Harte/nestest final-state
diff on `p` is exact). The `Flags` structure is the *spec view* of the six real flags; the
B bit (4) and unused bit (5) exist only in the byte pushed by PHP/BRK/IRQ/NMI.

## Spec

* `Flags.toByte f b` packs the flags `f` into a byte: `C Z I D` in bits 0–3, `V N` in bits
  6–7, bit 5 always set, bit 4 equal to `b`.
* `Flags.ofByte x` reads the six flags out of `x`, ignoring bits 4 and 5.
* `Flags.ofByte_toByte`: packing then unpacking recovers the flags, whatever `b` was.
* `Flags.toByte_ofByte`: unpacking then repacking (with `b` taken from bit 4 of `x`)
  recovers `x` except that bit 5 is forced on: the result is `x ||| 0x20`.
* `State.flags s` is `Flags.ofByte s.p`; each accessor `s.c … s.n` is the matching field of
  `s.flags` (`State.flags_eq`), and each setter `s.setC b …` changes exactly that field of
  the view (`State.flags_setC` … `State.flags_setN`).
* `State.setZN s r` sets Z iff `r = 0` and N to bit 7 of `r`, leaving the other flags
  unchanged (`State.flags_setZN`).
-/

namespace Nes.Cpu

/-- The six architectural status flags (spec view of `P`). -/
structure Flags where
  c : Bool
  z : Bool
  i : Bool
  d : Bool
  v : Bool
  n : Bool
  deriving Repr, DecidableEq, Inhabited

namespace Flags

/-- Bit masks of the flags in `P`. -/
@[inline] def maskC : UInt8 := 0x01
@[inline] def maskZ : UInt8 := 0x02
@[inline] def maskI : UInt8 := 0x04
@[inline] def maskD : UInt8 := 0x08
@[inline] def maskB : UInt8 := 0x10
@[inline] def maskU : UInt8 := 0x20
@[inline] def maskV : UInt8 := 0x40
@[inline] def maskN : UInt8 := 0x80

/-- Pack flags into a status byte; bit 5 is always set, bit 4 is `b`. -/
def toByte (f : Flags) (b : Bool) : UInt8 :=
  (if f.c then 0x01 else 0) ||| (if f.z then 0x02 else 0) ||| (if f.i then 0x04 else 0) |||
  (if f.d then 0x08 else 0) ||| (if b then 0x10 else 0) ||| 0x20 |||
  (if f.v then 0x40 else 0) ||| (if f.n then 0x80 else 0)

/-- Unpack the six flags from a status byte, ignoring bits 4 and 5. -/
def ofByte (x : UInt8) : Flags :=
  { c := x &&& 0x01 != 0, z := x &&& 0x02 != 0, i := x &&& 0x04 != 0,
    d := x &&& 0x08 != 0, v := x &&& 0x40 != 0, n := x &&& 0x80 != 0 }

theorem ofByte_toByte (f : Flags) (b : Bool) : ofByte (toByte f b) = f := by
  obtain ⟨c, z, i, d, v, n⟩ := f
  cases c <;> cases z <;> cases i <;> cases d <;> cases v <;> cases n <;> cases b <;> decide

theorem toByte_ofByte (x : UInt8) : toByte (ofByte x) (x &&& 0x10 != 0) = x ||| 0x20 := by
  apply _root_.UInt8.eq_of_toBitVec_eq
  simp only [toByte, ofByte, bne_iff_ne, ne_eq]
  split <;> split <;> split <;> split <;> split <;> split <;> split <;>
    simp_all only [_root_.UInt8.toBitVec_or, _root_.UInt8.toBitVec_and,
      ← _root_.UInt8.toBitVec_inj, Decidable.not_not] <;> bv_decide

end Flags

/-- CPU register file. `p` is the raw status byte (see module doc for why). -/
structure State where
  a : UInt8
  x : UInt8
  y : UInt8
  sp : UInt8
  pc : UInt16
  p : UInt8
  halted : Bool
  deriving Repr, DecidableEq, Inhabited

namespace State

/-- Power-up state (nesdev): `A = X = Y = 0`, `SP = $FD`, `P = $34` (I set). `PC` is loaded
from the reset vector by the reset sequence, not here. -/
def init : State :=
  { a := 0, x := 0, y := 0, sp := 0xFD, pc := 0, p := 0x34, halted := false }

/-- Spec view of the status register. -/
@[inline] def flags (s : State) : Flags := Flags.ofByte s.p

@[inline] def getBit (s : State) (m : UInt8) : Bool := s.p &&& m != 0
@[inline] def setBit (s : State) (m : UInt8) (b : Bool) : State :=
  { s with p := if b then s.p ||| m else s.p &&& ~~~m }

@[inline] def c (s : State) : Bool := s.getBit Flags.maskC
@[inline] def z (s : State) : Bool := s.getBit Flags.maskZ
@[inline] def i (s : State) : Bool := s.getBit Flags.maskI
@[inline] def d (s : State) : Bool := s.getBit Flags.maskD
@[inline] def v (s : State) : Bool := s.getBit Flags.maskV
@[inline] def n (s : State) : Bool := s.getBit Flags.maskN

@[inline] def setC (s : State) (b : Bool) : State := s.setBit Flags.maskC b
@[inline] def setZ (s : State) (b : Bool) : State := s.setBit Flags.maskZ b
@[inline] def setI (s : State) (b : Bool) : State := s.setBit Flags.maskI b
@[inline] def setD (s : State) (b : Bool) : State := s.setBit Flags.maskD b
@[inline] def setV (s : State) (b : Bool) : State := s.setBit Flags.maskV b
@[inline] def setN (s : State) (b : Bool) : State := s.setBit Flags.maskN b

/-- Set Z and N from a result byte (the common case after loads/ALU ops). -/
@[inline] def setZN (s : State) (r : UInt8) : State :=
  { s with p := (s.p &&& 0x7D) ||| (if r == 0 then 0x02 else 0) ||| (r &&& 0x80) }

theorem flags_eq (s : State) : s.flags = ⟨s.c, s.z, s.i, s.d, s.v, s.n⟩ := rfl

/-- Close `(x != 0) = (y != 0)`-shaped goals: `bv_decide` does not support `bne` on `UInt8`,
so turn the `Bool` equation into an `Iff` of `Prop` (dis)equalities first. -/
local macro "flag_bv" : tactic =>
  `(tactic| (
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, Bool.false_eq_true, iff_false, iff_true, Decidable.not_not]
    bv_decide))

theorem flags_setC (s : State) (b : Bool) : (s.setC b).flags = { s.flags with c := b } := by
  cases b <;> simp only [setC, setBit, flags, Flags.ofByte, Flags.maskC, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setZ (s : State) (b : Bool) : (s.setZ b).flags = { s.flags with z := b } := by
  cases b <;> simp only [setZ, setBit, flags, Flags.ofByte, Flags.maskZ, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setI (s : State) (b : Bool) : (s.setI b).flags = { s.flags with i := b } := by
  cases b <;> simp only [setI, setBit, flags, Flags.ofByte, Flags.maskI, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setD (s : State) (b : Bool) : (s.setD b).flags = { s.flags with d := b } := by
  cases b <;> simp only [setD, setBit, flags, Flags.ofByte, Flags.maskD, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setV (s : State) (b : Bool) : (s.setV b).flags = { s.flags with v := b } := by
  cases b <;> simp only [setV, setBit, flags, Flags.ofByte, Flags.maskV, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setN (s : State) (b : Bool) : (s.setN b).flags = { s.flags with n := b } := by
  cases b <;> simp only [setN, setBit, flags, Flags.ofByte, Flags.maskN, Flags.mk.injEq,
    ite_true, ite_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

theorem flags_setZN (s : State) (r : UInt8) :
    (s.setZN r).flags = { s.flags with z := r == 0, n := r &&& 0x80 != 0 } := by
  simp only [setZN, flags, Flags.ofByte, Flags.mk.injEq]
  by_cases h : r = 0
  · subst h; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv
  · simp only [beq_iff_eq, h, ite_false]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> flag_bv

end State

end Nes.Cpu
