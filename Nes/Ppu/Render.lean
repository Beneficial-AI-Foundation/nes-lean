import Nes.Ppu.Sprites

/-!
# `Nes.Ppu.Render` — sprite pixel, background/sprite priority mux, sprite-0 hit, frame write

Reference: NESdev wiki, "PPU rendering" (pixel output, priority multiplexer) and "PPU OAM"
(sprite 0 hits).

## Spec

`pixel palRd bgPx s` is the output of visible pixel `x = dot - 1` (dots 1–256) on line
`y = scanline` (0–239); it is the identity elsewhere. `bgPx` is the 4-bit background index
(bits 0–1 pattern, 2–3 palette; 0–1 = 0 means transparent) from the background pipeline;
`palRd i` reads palette RAM entry `i` (0–31).

* Sprite pixel (`spritePixel`): the first slot `i < sprCount` (slot order = OAM order) with
  `sprX[i] ≤ x < sprX[i] + 8` whose pattern bit at column `c = x - sprX[i]` (bit `7 - c` of
  the already h-flip-corrected `sprPatLo/Hi[i]`) is non-zero. The result packs pattern (bits
  0–1), palette (`attr` bits 0–1, in bits 2–3), behind-background priority (`attr` bit 5, in
  bit 4) and "is slot 0 while sprite 0 is on this line" (bit 7); 0 when no slot is opaque.
* Masks: the background index is forced transparent unless `mask.3` and (`x ≥ 8` or `mask.1`);
  the sprite pixel likewise with `mask.4` / `mask.2`.
* Mux (`muxIndex`): if the sprite is opaque and (background transparent or sprite in front)
  the palette index is `$10 | sprite palette·4 | pattern`; else if the background is opaque it
  is `bg palette·4 | pattern`; else 0 (universal background, `$3F00`).
* Sprite-0 hit: `status` bit 6 is set iff the (masked) sprite pixel comes from slot 0 with
  `spr0Line` and the (masked) background is opaque and `x ≠ 255` — priority does not matter.
  Since slot 0 is first in slot order, "slot 0 chosen" = "sprite 0 pixel opaque".
* Colour: `palRd index & $3F`, and `& $30` when `mask.0` (greyscale). With rendering disabled
  (`mask.3 = mask.4 = 0`) the colour is `palRd (v & $1F)` if `v` points into `$3F00–$3FFF`,
  else `palRd 0`, and no hit is possible.
* `frame[256·y + x] :=` that colour.

Ordering: call while `s.dot = x + 1`, before the timing tick advances `dot`; the hit flag is
therefore visible to a `$2002` read from dot `x + 2` on.
-/

namespace Nes.Ppu.Render

open Nes.Ppu Nes.Ppu.Sprites

/-- First opaque sprite slot at column `x` (packed, see module doc), scanning slots `i..n-1`. -/
def spritePixelAux (s : State) (x : UInt8) (n : Nat) : Nat → Nat → UInt8
  | 0, _ => 0
  | fuel + 1, i =>
    if i ≥ n then 0 else
    let sx := getByte s.sprX i
    if x ≥ sx && x - sx < 8 then
      let sh : UInt8 := 7 - (x - sx)
      let lo : UInt8 := (getByte s.sprPatLo i >>> sh) &&& (1 : UInt8)
      let hi : UInt8 := (getByte s.sprPatHi i >>> sh) &&& (1 : UInt8)
      let pat : UInt8 := lo ||| (hi <<< (1 : UInt8))
      if pat != 0 then
        let a := getByte s.sprAttr i
        let pal : UInt8 := (a &&& (3 : UInt8)) <<< (2 : UInt8)
        let pri : UInt8 := (a &&& (0x20 : UInt8)) >>> (1 : UInt8)
        let z : UInt8 := if i == 0 && s.spr0Line then 0x80 else 0
        pat ||| pal ||| pri ||| z
      else spritePixelAux s x n fuel (i + 1)
    else spritePixelAux s x n fuel (i + 1)

/-- Packed sprite pixel at column `x` (0 = transparent). -/
@[inline] def spritePixel (s : State) (x : UInt8) : UInt8 :=
  spritePixelAux s x (min s.sprCount.toNat 8) 8 0

/-- Background/sprite priority mux: palette index 0–31 from a 4-bit background index and a
packed sprite pixel. -/
@[inline] def muxIndex (bg spr : UInt8) : UInt8 :=
  let bgOpaque := bg &&& 3 != 0
  let sprOpaque := spr &&& 3 != 0
  if sprOpaque && (!bgOpaque || spr &&& 0x10 == 0) then 0x10 ||| (spr &&& 0x0F)
  else if bgOpaque then bg &&& 0x0F
  else 0

/-- Output pixel `x = dot - 1` of visible line `scanline` (see module doc). -/
@[specialize] def pixel (palRd : UInt8 → UInt8) (bgPx : UInt8) (s : State) : State :=
  let d := s.dot
  let y := s.scanline
  if d == 0 || d > 256 || y ≥ 240 then s else
  let x := (d - 1).toUInt8
  let idx := (y.toNat <<< 8) + x.toNat
  let grey : UInt8 := if s.mask &&& 0x01 != 0 then 0x30 else 0x3F
  if !s.rendering then
    let c := if s.v &&& 0x3F00 == 0x3F00 then palRd (s.v.toUInt8 &&& 0x1F) else palRd 0
    { s with frame := s.frame.set! idx (c &&& 0x3F &&& grey) }
  else
  let left := x < 8
  let bg := if s.showBg && (!left || s.bgLeft) then bgPx &&& 0x0F else 0
  let spr := if s.showSpr && (!left || s.sprLeft) then spritePixel s x else 0
  let hit := spr &&& 0x80 != 0 && bg &&& 3 != 0 && x != 255
  let c := palRd (muxIndex bg spr) &&& 0x3F &&& grey
  { s with frame := s.frame.set! idx c,
           status := if hit then s.status ||| 0x40 else s.status }

end Nes.Ppu.Render
