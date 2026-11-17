import Nes.Cart.Mappers.NROM

/-!
# `Nes.Cart.Mappers.UxROM` — mapper 2

UxROM (UNROM, UOROM; NESdev "UxROM") has one register: a CPU write to `$8000–$FFFF`
selects the 16 KiB PRG-ROM bank at `$8000–$BFFF`; `$C000–$FFFF` is fixed to the last 16 KiB
bank. CHR is 8 KiB (almost always CHR-RAM), unbanked; mirroring is hard-wired by the header.

Design decisions:
* **Bus conflicts.** On UNROM/UOROM boards the PRG-ROM is not disabled during a write, so
  the latched value is the CPU's value ANDed with the PRG byte at the written address
  (NESdev "UxROM", "Bus conflict"). NES 2.0 submapper 1 marks a board without conflicts;
  submapper 0 (unspecified, all iNES 1.0 images) and 2 (AND-type) model them (`busConflict`).
  Software written for real boards avoids them, so the AND is invisible to it.
* **Bank width.** The full latched byte is kept; `prgOffset` reduces the computed offset
  modulo the PRG size, which for power-of-two images is masking the bank number with
  `banks - 1` (UNROM: 3 bits, UOROM: 4 bits).
* **PRG-RAM.** Real UxROM boards have none; `$6000–$7FFF` stays generic, always-enabled board
  RAM as for NROM/CNROM (test ROMs report status there; no UxROM game relies on open bus).

## Spec

* `prgOffset rom s a` is `(b·$4000 + (a mod $4000)) mod |PRG|` where `b = s.bank` for
  `a < $C000` and `b = |PRG|/$4000 - 1` (the last bank) otherwise.
* `chrOffset` is NROM's (`(a mod $2000) mod chrLen`).
* `regWrite rom s a v`: for `a ≥ $8000`, `bank := v &&& prg[prgOffset a]` when `busConflict`,
  else `bank := v`; writes below `$8000` leave the register unchanged.
* A12, IRQ: unused; mirroring is the header's. Power-on bank is 0.
-/

namespace Nes.Cart.Uxrom

/-- UxROM register state: the 16 KiB PRG bank at `$8000–$BFFF`. -/
structure State where
  bank : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- The board has AND-type bus conflicts (every submapper except 1). -/
@[inline] def busConflict (rom : Rom) : Bool := rom.header.submapper != 1

/-- Number of 16 KiB PRG banks. -/
@[inline] def banks (rom : Rom) : Nat := rom.prg.size / 16384

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF`. -/
@[inline] def prgOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.prg.size :=
  let b := if addr < 0xC000 then s.bank.toNat else banks rom - 1
  ⟨(b * 16384 + (addr &&& 0x3FFF).toNat) % rom.prg.size, Nat.mod_lt _ rom.prg_pos⟩

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF` (fixed, as NROM). -/
@[inline] def chrOffset (rom : Rom) (_ : State) (addr : UInt16) : Fin rom.chrLen :=
  Nrom.chrOffset rom {} addr

/-- CPU write to `$4020–$FFFF`: `$8000–$FFFF` latches the PRG bank (with the bus conflict). -/
@[inline] def regWrite (rom : Rom) (s : State) (addr : UInt16) (v : UInt8) : State :=
  if 0x8000 ≤ addr then
    { bank := if busConflict rom then v &&& rom.prg[prgOffset rom s addr] else v }
  else s

/-- PPU A12 edge input: unused. -/
@[inline] def ppuA12 (_ : Bool) (s : State) : State := s

/-- IRQ line: never asserted. -/
@[inline] def irq (_ : State) : Bool := false

/-- Mirroring: hard-wired by the header. -/
@[inline] def mirroring (rom : Rom) (_ : State) : Mirroring := rom.mirroring

end Nes.Cart.Uxrom
