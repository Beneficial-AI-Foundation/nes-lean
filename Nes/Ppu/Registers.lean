import Nes.Ppu.Types

/-!
# `Nes.Ppu.Registers` — CPU-facing PPU registers `$2000–$2007`

The CPU sees eight registers mirrored every 8 bytes over `$2000–$3FFF`; `cpuWrite`/`cpuRead`
dispatch on the low three address bits. VRAM is not owned here: a `$2007` write returns a
`VramWrite` effect for the PPU bus to perform, and a `$2007` read is delegated to a caller
supplied function (the buffered-read semantics are a separate item).

## Spec

Every CPU write stores the written byte `d` in `ioLatch`. Then, by register:

* `$2000` (`writeCtrl`): `ctrl := d`; `t` bits 10–11 := `d` bits 0–1; `nmiOut := d.7 ∧ vblank`
  (so enabling NMI while vblank is set raises the line at once: NMI retrigger, NESdev "NMI").
* `$2001` (`writeMask`): `mask := d`.
* `$2003` (`writeOamAddr`): `oamAddr := d`.
* `$2004` (`writeOamData`): `oam[oamAddr] := d`, `oamAddr += 1` (mod 256).
* `$2005` (`writeScroll`), first write (`w = false`): `t` bits 0–4 := `d >> 3` (coarse X),
  `x := d & 7`, `w := true`. Second write (`w = true`): `t` bits 5–9 := `d >> 3` (coarse Y),
  bits 12–14 := `d & 7` (fine Y), `w := false`.
* `$2006` (`writeAddr`), first write: `t` bits 8–13 := `d` bits 0–5, bit 14 := 0 (bit 15 too),
  `w := true`. Second write: `t` bits 0–7 := `d`, then `v := t`, `w := false`.
* `$2007` (`writeData`): emit `VramWrite (v & 0x3FFF) d`, then `incAddr`.
* `incAddr`: `v := (v + (32 if ctrl.2 else 1)) & 0x7FFF`.
* `$2002` read (`readStatus`): returns `status` bits 5–7 over `ioLatch` bits 0–4; clears vblank,
  `w := false`, `nmiOut := false`; `ioLatch :=` the returned byte. A read on a state at
  `(scanline, dot) = (241, 0)` — one PPU clock before the vblank flag is set (position = dot
  just executed, see `Nes.Ppu.Timing`) — also sets `suppressVbl`, so that frame's flag and NMI
  never happen (NESdev "PPU frame timing": "Reading $2002 one PPU clock before reads it as clear
  and never sets the flag or generates NMI for that frame").
* `$2004` read (`readOamData`): `oam[oamAddr]`, with bits 2–4 of attribute bytes
  (`oamAddr % 4 = 2`) reading as 0; `ioLatch :=` the returned byte.
* Reads of `$2000/1/3/5/6` return `ioLatch` and change nothing.
-/

namespace Nes.Ppu

/-- A VRAM write requested by a `$2007` write: 14-bit PPU address and data. -/
structure VramWrite where
  addr : UInt16
  data : UInt8
  deriving Repr, DecidableEq, Inhabited

namespace State

/-- `$2000` PPUCTRL write. -/
@[inline] def writeCtrl (s : State) (d : UInt8) : State :=
  { s with ctrl := d, t := (s.t &&& ~~~(0x0C00 : UInt16)) ||| ((d.toUInt16 &&& 0x03) <<< 10),
           nmiOut := d &&& 0x80 != 0 && s.vblank }

/-- `$2001` PPUMASK write. -/
@[inline] def writeMask (s : State) (d : UInt8) : State := { s with mask := d }

/-- `$2003` OAMADDR write. -/
@[inline] def writeOamAddr (s : State) (d : UInt8) : State := { s with oamAddr := d }

/-- `$2004` OAMDATA write. -/
@[inline] def writeOamData (s : State) (d : UInt8) : State :=
  { s with oam := s.oam.set! s.oamAddr.toNat d, oamAddr := s.oamAddr + 1 }

/-- `$2005` PPUSCROLL write (two-write sequence through `w`). -/
@[inline] def writeScroll (s : State) (d : UInt8) : State :=
  if !s.w then
    { s with t := (s.t &&& ~~~(0x001F : UInt16)) ||| (d >>> 3).toUInt16, x := d &&& 0x07, w := true }
  else
    { s with t := (s.t &&& ~~~(0x73E0 : UInt16)) ||| ((d.toUInt16 &&& 0x07) <<< 12) |||
                  ((d.toUInt16 &&& 0xF8) <<< 2), w := false }

/-- `$2006` PPUADDR write (two-write sequence through `w`). -/
@[inline] def writeAddr (s : State) (d : UInt8) : State :=
  if !s.w then
    { s with t := (s.t &&& (0x00FF : UInt16)) ||| ((d.toUInt16 &&& 0x3F) <<< 8), w := true }
  else
    let t := (s.t &&& (0xFF00 : UInt16)) ||| d.toUInt16
    { s with t := t, v := t, w := false }

/-- The VRAM address `v` puts on the PPU bus (14 bits). -/
@[inline] def vramAddr (s : State) : UInt16 := s.v &&& 0x3FFF

/-- Post-access `$2007` address increment (1 or 32 by `ctrl` bit 2). Outside rendering only;
the during-rendering glitch (coarse X and Y increment) belongs to the timing item. -/
@[inline] def incAddr (s : State) : State :=
  { s with v := (s.v + (if s.vramInc32 then 32 else 1)) &&& 0x7FFF }

/-- `$2007` PPUDATA write: the VRAM write to perform, and the incremented state. -/
@[inline] def writeData (s : State) (d : UInt8) : State × VramWrite :=
  (s.incAddr, ⟨s.vramAddr, d⟩)

/-- `$2002` PPUSTATUS read (with the vblank-race suppression at `(241, 0)`). -/
@[inline] def readStatus (s : State) : State × UInt8 :=
  let r := (s.status &&& 0xE0) ||| (s.ioLatch &&& 0x1F)
  let sup := s.suppressVbl || (s.dot == 0 && s.scanline == 241)
  ({ s with status := s.status &&& 0x7F, w := false, nmiOut := false, ioLatch := r,
            suppressVbl := sup }, r)

/-- `$2004` OAMDATA read (attribute bytes read with bits 2–4 clear). -/
@[inline] def readOamData (s : State) : State × UInt8 :=
  let b := getByte s.oam s.oamAddr.toNat
  let r := if s.oamAddr &&& 0x03 == 0x02 then b &&& 0xE3 else b
  ({ s with ioLatch := r }, r)

/-- CPU write to `$2000 + (addr & 7)`; a `$2007` write yields the VRAM write to perform. -/
def cpuWrite (s : State) (addr : UInt16) (d : UInt8) : State × Option VramWrite :=
  let s := { s with ioLatch := d }
  match (addr &&& 7).toNat with
  | 0 => (s.writeCtrl d, none)
  | 1 => (s.writeMask d, none)
  | 3 => (s.writeOamAddr d, none)
  | 4 => (s.writeOamData d, none)
  | 5 => (s.writeScroll d, none)
  | 6 => (s.writeAddr d, none)
  | 7 => let (s, wr) := s.writeData d; (s, some wr)
  | _ => (s, none)   -- `$2002` is read-only

/-- CPU read of `$2000 + (addr & 7)`; `read2007` implements the buffered `$2007` read. -/
@[inline] def cpuRead (read2007 : State → State × UInt8) (s : State) (addr : UInt16) :
    State × UInt8 :=
  match (addr &&& 7).toNat with
  | 2 => s.readStatus
  | 4 => s.readOamData
  | 7 => read2007 s
  | _ => (s, s.ioLatch)

end State

end Nes.Ppu
