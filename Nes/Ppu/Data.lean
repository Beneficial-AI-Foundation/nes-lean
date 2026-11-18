import Nes.Ppu.Registers
import Nes.Bus.Map

/-!
# `Nes.Ppu.Data` — `$2007` PPUDATA read buffer

VRAM is not owned by the PPU state: the read path is parameterised by `rd : UInt16 → UInt8`
(a 14-bit PPU-bus read of pattern tables / nametables, mirroring already applied by the
caller's bus) and `palRd : UInt8 → UInt8` (a palette RAM read at index 0–31, already
de-aliased: `$3F10/14/18/1C` arrive as `$00/04/08/0C`, via `Nes.Bus.paletteIndex`).
`read2007 rd palRd : State → State × UInt8` is the argument `State.cpuRead` expects.

## Spec

Let `a = v & $3FFF` (`State.vramAddr`).

* `a < $3F00` (buffered): the returned byte is the *old* `readBuffer`; the new `readBuffer` is
  `rd a`.
* `a ≥ $3F00` (palette): the returned byte is the palette byte immediately:
  bits 0–5 = `palRd (paletteIndex a) & $3F`, bits 6–7 = `ioLatch` bits 6–7 (2C02 open bus:
  palette RAM is 6 bits wide, the top two bits are whatever the PPU I/O latch holds). The
  new `readBuffer` is the nametable byte "underneath", `rd (a - $1000)` (`$2F00–$2FFF`).
* In both cases `ioLatch :=` the returned byte (it drove the PPU data bus), and then `v`
  increments by `incAddr` (`+1`, or `+32` when `ctrl` bit 2 is set, masked to 15 bits).
* `write2007 s d = s.writeData d`: emit `VramWrite a d`, then `incAddr`.

Not modelled (deliberately): PPUMASK greyscale (bit 0) masking the palette read value with
`$30`, and the during-rendering glitch where a `$2007` access increments coarse X and Y
(`incX`/`incY`) instead of `incAddr`; the latter belongs to the timing item.
-/

namespace Nes.Ppu

namespace State

/-- `$2007` PPUDATA read: buffered below `$3F00`, immediate (with open-bus bits 6–7) for
palette addresses, which still refill the buffer from the nametable byte at `a - $1000`. -/
@[specialize] def read2007 (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    State × UInt8 :=
  let a := s.vramAddr
  if a < 0x3F00 then
    let r := s.readBuffer
    ({ s with readBuffer := rd a, ioLatch := r }.incAddr, r)
  else
    let r := (palRd (Nes.Bus.paletteIndex a).val.toUInt8 &&& 0x3F) ||| (s.ioLatch &&& 0xC0)
    ({ s with readBuffer := rd (a - 0x1000), ioLatch := r }.incAddr, r)

/-- `$2007` PPUDATA write: the VRAM write to perform and the incremented state
(`writeData`; the caller routes palette addresses to palette RAM through `ppuDecode`). -/
@[inline] def write2007 (s : State) (d : UInt8) : State × VramWrite := s.writeData d

end State

end Nes.Ppu
