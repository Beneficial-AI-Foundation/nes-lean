import Nes.Cart.Ines

/-!
# `Nes.Cart.Mappers.NROM` — mapper 0

NROM has no registers. PRG-ROM (16 or 32 KiB) is at CPU `$8000–$FFFF`; a 16 KiB image is
mirrored into `$C000–$FFFF`. CHR (8 KiB ROM, or 8 KiB RAM when the image has none) is at
PPU `$0000–$1FFF`. PRG-RAM at `$6000–$7FFF` (Family BASIC, test ROMs) is always enabled;
it is generic board RAM handled by `Nes.Cart.CartState`.

## Spec

* `prgOffset rom s a` is `(a mod $8000) mod |PRG|`, a `Fin rom.prg.size`: for a 16 KiB
  image `$8000+i` and `$C000+i` read the same byte, for a 32 KiB image `$8000+i` reads byte
  `i`.
* `chrOffset rom s a` is `(a mod $2000) mod chrLen`, a `Fin rom.chrLen`.
* Register writes, the A12 line and IRQ do nothing; mirroring is the header's.
-/

namespace Nes.Cart.Nrom

/-- NROM has no mapper registers. -/
structure State where
  deriving DecidableEq, Repr, Inhabited

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF`. -/
@[inline] def prgOffset (rom : Rom) (_ : State) (addr : UInt16) : Fin rom.prg.size :=
  ⟨(addr &&& 0x7FFF).toNat % rom.prg.size, Nat.mod_lt _ rom.prg_pos⟩

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF`. -/
@[inline] def chrOffset (rom : Rom) (_ : State) (addr : UInt16) : Fin rom.chrLen :=
  ⟨(addr &&& 0x1FFF).toNat % rom.chrLen, Nat.mod_lt _ rom.chrLen_pos⟩

/-- CPU write to `$4020–$FFFF`: NROM has no registers. -/
@[inline] def regWrite (_ : Rom) (s : State) (_ : UInt16) (_ : UInt8) : State := s

/-- PPU A12 edge input: unused. -/
@[inline] def ppuA12 (_ : Bool) (s : State) : State := s

/-- IRQ line: never asserted. -/
@[inline] def irq (_ : State) : Bool := false

/-- Mirroring: hard-wired by the header. -/
@[inline] def mirroring (rom : Rom) (_ : State) : Mirroring := rom.mirroring

end Nes.Cart.Nrom
