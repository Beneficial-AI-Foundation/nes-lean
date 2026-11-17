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

### Back-to-back reads (`read2007At now rd palRd`)

On hardware the buffer refill is a PPU-bus read that lands a little over one CPU cycle (≥ 3 dots)
after the CPU's `$2007` read, while `v` is incremented at once. A second `$2007` read on the very
next CPU cycle (the page-crossing dummy read of `lda $20F7,x`, or the DMC DMA halt repeating a
read) therefore still returns the buffer as it was *before* the previous refill, yet issues its
own refill from the already-incremented `v` (blargg `dmc_dma_during_read4/double_2007_read.s`:
accepted result `22 44 55 66 77` — the second read returns the stale `$22`, the buffer still
advances twice; `dma_2007_read.s`: 2–3 extra effective reads before the real one).
`read2007At now` is `read2007` plus: `prevBuffer :=` the old `readBuffer`,
`lastRead2007 := now` (`now` = CPU cycle); and when `now = lastRead2007 + 1` with a buffered
address, the returned byte (and `ioLatch`) is `prevBuffer` instead (`read2007At_settled`:
otherwise it returns exactly what `read2007` does).

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

/-- `$2007` PPUDATA read at CPU cycle `now`: `read2007`, except that a buffered read on the
CPU cycle right after another `$2007` read returns `prevBuffer` (the previous refill has not
landed yet). Records `prevBuffer` and `lastRead2007` for the next read. -/
@[specialize] def read2007At (now : UInt64) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8)
    (s : State) : State × UInt8 :=
  let (s', r) := read2007 rd palRd s
  if now == s.lastRead2007 + 1 && s.vramAddr < 0x3F00 then
    let r := s.prevBuffer
    ({ s' with ioLatch := r, prevBuffer := s.readBuffer, lastRead2007 := now }, r)
  else ({ s' with prevBuffer := s.readBuffer, lastRead2007 := now }, r)

/-- `$2007` PPUDATA write: the VRAM write to perform and the incremented state
(`writeData`; the caller routes palette addresses to palette RAM through `ppuDecode`). -/
@[inline] def write2007 (s : State) (d : UInt8) : State × VramWrite := s.writeData d

end State

end Nes.Ppu
