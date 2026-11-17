import Nes.Ppu.Types

/-!
# `Nes.Ppu.Background` — background fetch pipeline and shifters

Reference: NESdev wiki "PPU rendering" (frame timing diagram, "Cycles 1-256", "Cycles 321-336",
"Cycles 337-340") and "PPU scrolling" ("Tile and attribute fetching", "Wrapping around",
"At dot 256/257", "During dots 280 to 304 of the pre-render scanline").

## Ordering contract

`bgDot rd s` performs the background work of the *current* `(s.scanline, s.dot)`, i.e. it runs
**before** `Timing.tick` advances the dot. Within one PPU dot the integrator (`Ppu/Step.lean`)
must do, in order:

1. `ppuAddrBg s` (on the state *before* `bgDot`) is the address on the PPU bus this dot during
   background fetch dots (dots 1–256 and 321–340 of a rendering line); A12 is bit 12 of it.
   Every read `bgDot` performs is `rd (ppuAddrBg s)` (see the `fetch` step below).
2. `s ← bgDot rd s`: shift (dots 2–257, 322–337), reload (dots 9, 17, …, 257, 329, 337),
   fetch, then the loopy updates (`incX` at dots 8, 16, …, 256, 328, 336; `incY` at 256;
   `copyX` at 257; `copyY` at 280–304 of the pre-render line).
3. `bgPixel s` (on the state *after* `bgDot`, same dot): the background pixel for screen
   column `dot - 1` (meaningful on dots 1–256 of visible lines 0–239).
4. sprite work, pixel mux, then `Timing.tick`.

## Spec

* The work happens only when `rendering` (mask bits 3|4) and the line is visible (0–239) or the
  pre-render line (261); otherwise `bgDot rd s = s`.
* Fetch cadence on dots 1–256 and 321–336, with phase `p = (dot - 1) % 8`: `p = 0` nametable
  byte → `bgNextTile`, `p = 2` attribute byte → `bgNextAttr` (already reduced to the tile's 2-bit
  palette via `atSelect`), `p = 4` pattern low plane → `bgNextLo`, `p = 6` pattern high plane →
  `bgNextHi`. Dots 337 and 339 are the two (unused) nametable fetches; they load `bgNextTile`.
* Shifters: `bgPatLo/Hi` and `bgAttrLo/Hi` are 16-bit; bit 15 is the pixel at fine-X 0 of the
  current tile. `bgShift` shifts all four left by one. `bgReload` replaces their low bytes with the
  latched tile (`bgNextLo/Hi`) and `0x00`/`0xFF` per attribute bit, high bytes unchanged.
* T-PPU-6 hook: after `bgDot` at any reload dot `d`, the low byte of `bgPatLo/Hi` holds the pattern
  bits of the tile whose nametable entry was fetched at `d - 8` — the tile two tiles ahead of the
  one being drawn — and the high byte holds the current tile.
* `bgPixel s`: 4-bit background palette index `attr·4 + pattern` taken at bit `15 - x`; `0` when
  the pattern bits are 0 (transparent → backdrop), when background is disabled (`showBg` false),
  or for screen columns 0–7 (`dot ≤ 8`) when `bgLeft` is clear. `bgPixelRaw` is the unmasked
  selection.
-/

namespace Nes.Ppu

namespace Bg

/-- Nametable byte address for loopy `v`: `$2000 | (v & $0FFF)`. -/
@[inline] def ntAddr (v : UInt16) : UInt16 := 0x2000 ||| (v &&& 0x0FFF)

/-- Attribute byte address for loopy `v`:
`$23C0 | (v & $0C00) | ((v >> 4) & $38) | ((v >> 2) & $07)`. -/
@[inline] def atAddr (v : UInt16) : UInt16 :=
  let nt : UInt16 := v &&& 0x0C00
  let cy : UInt16 := (v >>> 4) &&& 0x38
  let cx : UInt16 := (v >>> 2) &&& 0x07
  0x23C0 ||| nt ||| cy ||| cx

/-- The tile's 2-bit palette from its attribute byte: quadrant chosen by coarse Y bit 1 and
coarse X bit 1 of `v`. -/
@[inline] def atSelect (v : UInt16) (b : UInt8) : UInt8 :=
  let y : UInt16 := (v >>> 4) &&& 0x04
  let sh : UInt16 := y ||| (v &&& 0x02)
  (b >>> sh.toUInt8) &&& 0x03

/-- Pattern address: background table (`ctrl` bit 4) + tile·16 + fine Y (+8 for the high
plane). -/
@[inline] def ptAddr (s : State) (hi : Bool) : UInt16 :=
  let tbl : UInt16 := if s.bgTable then 0x1000 else 0
  let tile : UInt16 := s.bgNextTile.toUInt16 <<< 4
  let fy : UInt16 := (s.v >>> 12) &&& 0x07
  tbl ||| tile ||| (if hi then 0x08 else 0) ||| fy

/-- Shift the four background shifters left by one. -/
@[inline] def bgShift (s : State) : State :=
  { s with bgPatLo := s.bgPatLo <<< 1, bgPatHi := s.bgPatHi <<< 1,
           bgAttrLo := s.bgAttrLo <<< 1, bgAttrHi := s.bgAttrHi <<< 1 }

/-- Load the latched next tile into the low bytes of the shifters. -/
@[inline] def bgReload (s : State) : State :=
  { s with
    bgPatLo := (s.bgPatLo &&& 0xFF00) ||| s.bgNextLo.toUInt16
    bgPatHi := (s.bgPatHi &&& 0xFF00) ||| s.bgNextHi.toUInt16
    bgAttrLo := (s.bgAttrLo &&& 0xFF00) ||| (if s.bgNextAttr &&& 1 != 0 then 0xFF else 0)
    bgAttrHi := (s.bgAttrHi &&& 0xFF00) ||| (if s.bgNextAttr &&& 2 != 0 then 0xFF else 0) }

/-- A line on which the background pipeline runs: visible (0–239) or pre-render (261). -/
@[inline] def activeLine (sl : UInt16) : Bool := sl < 240 || sl == 261

/-- Dots of the regular 8-dot fetch cadence: 1–256 and 321–336. -/
@[inline] def fetchDot (d : UInt16) : Bool := (1 ≤ d && d ≤ 256) || (321 ≤ d && d ≤ 336)

end Bg

open Bg

/-- The address the PPU drives for background fetches on the current dot (evaluate on the state
*before* `bgDot`). On dots 1–256 / 321–336 it is the address of the 2-dot fetch in progress
(NT, AT, PT low, PT high by phase); on dots 337–340 and 0 the nametable address. Dots 257–320
belong to the sprite fetches (the integrator uses the sprite address there), and when rendering
is off the bus holds `v` — both are the integrator's choice. -/
@[inline] def ppuAddrBg (s : State) : UInt16 :=
  let d := s.dot
  if fetchDot d then
    let p := (d - 1) &&& 7
    if p < 2 then ntAddr s.v
    else if p < 4 then atAddr s.v
    else ptAddr s (p ≥ 6)
  else ntAddr s.v

/-- Background work for the current `(scanline, dot)`, before the timing tick (see the module
ordering contract). `rd` reads PPU address space (`$0000`–`$3FFF`). -/
@[specialize] def bgDot (rd : UInt16 → UInt8) (s : State) : State :=
  if !(s.rendering && activeLine s.scanline) then s
  else
    let d := s.dot
    -- shift: dots 2–257 and 322–337
    let s := if (2 ≤ d && d ≤ 257) || (322 ≤ d && d ≤ 337) then bgShift s else s
    let p := (d - 1) &&& 7
    -- reload: dots 9, 17, …, 257 and 329, 337 (phase 0, after the shift)
    let s := if p == 0 && ((9 ≤ d && d ≤ 257) || d == 329 || d == 337) then bgReload s else s
    -- fetch (first dot of each 2-dot slot); dots 337/339 are nametable fetches
    let s :=
      if fetchDot d then
        if p == 0 then { s with bgNextTile := rd (ppuAddrBg s) }
        else if p == 2 then { s with bgNextAttr := atSelect s.v (rd (ppuAddrBg s)) }
        else if p == 4 then { s with bgNextLo := rd (ppuAddrBg s) }
        else if p == 6 then { s with bgNextHi := rd (ppuAddrBg s) }
        else s
      else if d == 337 || d == 339 then { s with bgNextTile := rd (ppuAddrBg s) }
      else s
    -- loopy updates
    let s := if fetchDot d && p == 7 then { s with v := Loopy.incX s.v } else s
    let s := if d == 256 then { s with v := Loopy.incY s.v } else s
    let s := if d == 257 then { s with v := Loopy.copyX s.v s.t } else s
    if s.scanline == 261 && 280 ≤ d && d ≤ 304 then { s with v := Loopy.copyY s.v s.t } else s

/-- Unmasked background pixel: `attr·4 + pattern` at shifter bit `15 - x` (0 if the pattern bits
are 0). -/
@[inline] def bgPixelRaw (s : State) : UInt8 :=
  let sh : UInt16 := 15 - (s.x &&& 7).toUInt16
  let p0 := ((s.bgPatLo >>> sh) &&& 1).toUInt8
  let p1 := ((s.bgPatHi >>> sh) &&& 1).toUInt8
  let a0 := ((s.bgAttrLo >>> sh) &&& 1).toUInt8
  let a1 := ((s.bgAttrHi >>> sh) &&& 1).toUInt8
  let pat := (p1 <<< 1) ||| p0
  if pat == 0 then 0 else (a1 <<< 3) ||| (a0 <<< 2) ||| pat

/-- Background pixel for screen column `dot - 1` (call after `bgDot` on the same dot): the 4-bit
palette index, 0 = transparent; honours `showBg` and the left-8-pixel `bgLeft` mask. -/
@[inline] def bgPixel (s : State) : UInt8 :=
  if !s.showBg || (!s.bgLeft && s.dot ≤ 8) then 0 else bgPixelRaw s

end Nes.Ppu
