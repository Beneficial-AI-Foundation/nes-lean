import Nes.Cart.Mappers.NROM

/-!
# `Nes.Cart.Mappers.AxROM` — mapper 7

AxROM (ANROM, AN1ROM, AMROM, AOROM; NESdev "AxROM") has one register, written at
`$8000–$FFFF`: bits 0–2 select the 32 KiB PRG-ROM bank at `$8000–$FFFF`, bit 4 selects which
1 KiB of CIRAM is used for all four nametables (single-screen mirroring). CHR is 8 KiB
(CHR-RAM), unbanked.

Design decisions:
* **Bus conflicts.** Only AMROM has them; ANROM/AN1ROM/AOROM gate the ROM during writes, and
  games for them (e.g. Battletoads) write without avoiding conflicts. So conflicts are
  modelled only for NES 2.0 submapper 2 (AND-type); submapper 0 (all iNES 1.0 images) and 1
  write the plain value (`busConflict`).
* **Bank width.** Three bits are kept (AOROM's 256 KiB maximum); `prgOffset` additionally
  reduces modulo the PRG size, so smaller images mirror.
* **PRG-RAM.** Real AxROM boards have none; `$6000–$7FFF` stays generic, always-enabled board
  RAM as for NROM/CNROM/UxROM.
* **Power-on.** The register is 0 (bank 0, nametable `singleLow`); AxROM games put a reset
  stub in every bank, so the choice is invisible to them.

## Spec

* `prgOffset rom s a` is `((s.reg mod 8)·$8000 + (a mod $8000)) mod |PRG|`.
* `chrOffset` is NROM's (`(a mod $2000) mod chrLen`).
* `regWrite rom s a v`: for `a ≥ $8000`, `reg := v' &&& $17` with `v' = v &&& prg[prgOffset a]`
  when `busConflict`, else `v' = v`; writes below `$8000` leave the register unchanged.
* `mirroring`: `singleLow` if bit 4 of `reg` is clear, else `singleHigh`.
* A12, IRQ: unused.
-/

namespace Nes.Cart.Axrom

/-- AxROM register state: PRG bank (bits 0–2) and nametable select (bit 4). -/
structure State where
  reg : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- The board has AND-type bus conflicts (AMROM: NES 2.0 submapper 2 only). -/
@[inline] def busConflict (rom : Rom) : Bool := rom.header.submapper == 2

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF`, through the 32 KiB bank. -/
@[inline] def prgOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.prg.size :=
  ⟨((s.reg &&& 7).toNat * 32768 + (addr &&& 0x7FFF).toNat) % rom.prg.size,
    Nat.mod_lt _ rom.prg_pos⟩

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF` (fixed, as NROM). -/
@[inline] def chrOffset (rom : Rom) (_ : State) (addr : UInt16) : Fin rom.chrLen :=
  Nrom.chrOffset rom {} addr

/-- CPU write to `$4020–$FFFF`: `$8000–$FFFF` latches the register. -/
@[inline] def regWrite (rom : Rom) (s : State) (addr : UInt16) (v : UInt8) : State :=
  if 0x8000 ≤ addr then
    let v := if busConflict rom then v &&& rom.prg[prgOffset rom s addr] else v
    { reg := v &&& 0x17 }
  else s

/-- PPU A12 edge input: unused. -/
@[inline] def ppuA12 (_ : Bool) (s : State) : State := s

/-- IRQ line: never asserted. -/
@[inline] def irq (_ : State) : Bool := false

/-- Mirroring: single-screen, CIRAM page selected by bit 4. -/
@[inline] def mirroring (_ : Rom) (s : State) : Mirroring :=
  if s.reg &&& 0x10 == 0 then .singleLow else .singleHigh

end Nes.Cart.Axrom
