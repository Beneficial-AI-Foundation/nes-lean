import Nes.Cart.Mappers.NROM

/-!
# `Nes.Cart.Mappers.CNROM` — mapper 3

CNROM has NROM's fixed PRG layout (16 or 32 KiB at CPU `$8000–$FFFF`, a 16 KiB image
mirrored into `$C000–$FFFF`) and one register: a CPU write to `$8000–$FFFF` selects which
8 KiB CHR-ROM bank appears at PPU `$0000–$1FFF`.

Design decisions:
* **Bus conflicts.** On most CNROM boards the ROM is not disabled during a write, so the
  value latched is the CPU's value ANDed with the PRG byte at the written address (NESdev
  "CNROM", "Bus conflict"). This is modelled: `regWrite` latches `v &&& prg[a]`. Software
  that avoids conflicts (e.g. blargg `ppu_read_buffer`, which writes bank `n` to a ROM table
  holding `n`) sees plain bank switching.
* **Bank mask.** The latched value is masked with `banks - 1` where `banks = chrLen / 8 KiB`
  (`bankMask`); `chrOffset` additionally reduces modulo `chrLen`, so the offset is in range
  for every image (`Fin rom.chrLen`), even one whose CHR size is not a power-of-two multiple
  of 8 KiB.
* **PRG-RAM.** Real CNROM boards have none, but `$6000–$7FFF` is kept as generic,
  always-enabled board RAM, exactly as for NROM: blargg's test ROMs report their status there
  and expect RAM, and no CNROM game relies on open bus at `$6000`.

## Spec

* `prgOffset` is `Nrom.prgOffset` (`(a mod $8000) mod |PRG|`).
* `chrOffset rom s a` is `(bank·$2000 + (a mod $2000)) mod chrLen`.
* `regWrite rom s a v`: for `a ≥ $8000`, `bank := (v &&& prg[prgOffset a]) &&& bankMask rom`;
  writes below `$8000` leave the register unchanged.
* A12, IRQ: unused; mirroring is the header's. Power-on bank is 0.
-/

namespace Nes.Cart.Cnrom

/-- CNROM register state: the selected 8 KiB CHR bank. -/
structure State where
  bank : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- `banks - 1`, where `banks = chrLen / 8 KiB` (0 if the CHR space is at most 8 KiB). -/
@[inline] def bankMask (rom : Rom) : UInt8 := (rom.chrLen / 8192 - 1).toUInt8

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF` (fixed, as NROM). -/
@[inline] def prgOffset (rom : Rom) (_ : State) (addr : UInt16) : Fin rom.prg.size :=
  Nrom.prgOffset rom {} addr

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF`, through the bank. -/
@[inline] def chrOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.chrLen :=
  ⟨(s.bank.toNat * 8192 + (addr &&& 0x1FFF).toNat) % rom.chrLen, Nat.mod_lt _ rom.chrLen_pos⟩

/-- CPU write to `$4020–$FFFF`: `$8000–$FFFF` latches the CHR bank, with the bus conflict
(the value is ANDed with the PRG-ROM byte at the address). -/
@[inline] def regWrite (rom : Rom) (s : State) (addr : UInt16) (v : UInt8) : State :=
  if 0x8000 ≤ addr then
    { bank := (v &&& rom.prg[prgOffset rom s addr]) &&& bankMask rom }
  else s

/-- PPU A12 edge input: unused. -/
@[inline] def ppuA12 (_ : Bool) (s : State) : State := s

/-- IRQ line: never asserted. -/
@[inline] def irq (_ : State) : Bool := false

/-- Mirroring: hard-wired by the header. -/
@[inline] def mirroring (rom : Rom) (_ : State) : Mirroring := rom.mirroring

end Nes.Cart.Cnrom
