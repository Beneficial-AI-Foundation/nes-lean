import Nes.Ppu.Timing
import Nes.Ppu.Registers
import Nes.Ppu.Background
import Nes.Ppu.Sprites
import Nes.Ppu.Render

/-!
# `Nes.Ppu.Step` — one PPU dot: timing + background + sprites + pixel

`dot rd palRd s` runs one PPU clock. It composes the per-dot functions of the components in
the order their contracts require (see `Nes.Ppu.Timing` for the position convention:
`(scanline, dot)` of a state is the dot *just executed*):

1. `advance` — move to the next `(scanline, dot)` (with the odd-frame skip).
2. PPU address bus / A12: the address the PPU drives this dot. With rendering enabled on an
   active line (0–239, 261): `ppuAddrSprite` on dots 257–320 (sprite fetches), else
   `ppuAddrBg` (both evaluated on the state *before* the background work, per
   `Nes.Ppu.Background`). Otherwise the bus holds `v` (`vramAddr`). `a12 :=` bit 12.
3. `bgDot rd` — shifters, fetches, loopy updates of this dot.
4. `bgPixel` — background pixel of column `dot - 1` (after `bgDot`).
5. `Sprites.evalDot` on visible lines (0–239), `Sprites.fetchDot rd` on active lines; both only
   while rendering.
6. `Render.pixel palRd bgPx` — priority mux, sprite-0 hit, frame write (visible dots only; also
   writes the backdrop / `$3F0x` colour when rendering is disabled).
7. `dotEvents` — vblank set / flag clears / NMI line / frame-ready of this dot.
8. At pre-render dot 338: `renderLatch := rendering` (the odd-frame skip sample, see
   `Nes.Ppu.Timing`).

`rd` reads PPU address space (`$0000–$3EFF`: CHR and mirrored nametables); `palRd i` reads
palette RAM entry `i` (0–31, aliases `$10/$14/$18/$1C` resolved by the caller). Both are pure
readers: the PPU never writes VRAM while rendering. Mark callers' readers concrete so
`@[specialize]` erases the closures.

## Spec

* `dot rd palRd s = latch (dotEvents (render (advance s)))` where `render` is steps 2–6 above, and it
  changes `dot scanline frameOdd` exactly as `advance`.
* `a12` after `dot` is bit 12 of the address computed in step 2.
-/

namespace Nes.Ppu

open Nes.Ppu.Bg

/-- Address on the PPU bus for the dot `s` is at (state before the background work). -/
@[inline] def busAddr (s : State) : UInt16 :=
  if s.rendering && activeLine s.scanline then
    if 257 ≤ s.dot && s.dot ≤ 320 then Sprites.ppuAddrSprite s else ppuAddrBg s
  else s.vramAddr

/-- Rendering work of the dot `s` is at (steps 2–6 of the module doc). -/
@[specialize] def render (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) : State :=
  let s := { s with a12 := busAddr s &&& 0x1000 != 0 }
  if s.rendering then
    let s := bgDot rd s
    let bgPx := bgPixel s
    let s := if s.scanline < 240 then Sprites.evalDot s else s
    let s := if activeLine s.scanline then Sprites.fetchDot rd s else s
    Render.pixel palRd bgPx s
  else
    Render.pixel palRd 0 s

/-- One PPU clock. -/
@[specialize] def dot (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) : State :=
  let s := State.dotEvents (render rd palRd s.advance)
  if s.scanline == 261 && s.dot == 338 then { s with renderLatch := s.rendering } else s

end Nes.Ppu
