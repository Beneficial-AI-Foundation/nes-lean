import Nes.Ppu.Sprites

/-!
# `Nes.Ppu.Declarative` — reference renderer for a static frame (right-hand side of T-PPU-6)

A direct lookup, pixel by pixel, with no fetch pipeline, shifters or per-dot state: screen pixel
`(x, y)` → scrolled position → nametable → attribute → pattern → palette, plus the sprites that
the hardware's evaluation selects for that line (8-sprite limit, `Sprites.evalSpec`), the
priority mux and the masks. Plain `Nat` arithmetic: this is a spec, not the hot path.

## What it is meant to equal (T-PPU-6)

Let `s0` be a PPU state in vblank before a pre-render line (scanlines 241–260), and run
`Ppu.dot rd palRd` from `s0` through line 261 and lines 0–239. Then the `frame` written equals
`frame s0 rd palRd` provided that during that run

* there are no register writes: `ctrl`, `mask`, `t`, `x`, `oam` stay as in `s0` (in particular
  `$2005/$2006` writes would change `t`, and `oamAddr` is 0 at evaluation, as the pipeline
  assumes);
* VRAM, CHR and palette are fixed, i.e. `rd` and `palRd` are the same pure readers throughout
  (no CHR bank switches, no mid-frame raster effects);
* rendering is enabled (`mask` bit 3 or 4 set) for the whole frame.

`v` and the shifter/sprite state of `s0` do not matter: the pre-render line overwrites all 15
bits of `v` from `t` (copy X at dot 257, copy Y at 280–304) and prefetches the first two tiles of
line 0, and it clears the sprite slots (no sprites on line 0). No hypothesis on `t` is needed:
a coarse Y of 30/31 (out of range, only reachable by a `$2006`/`$2005` write) makes the rows
240–255 read attribute bytes as tiles and wrap at 256 to 0 *without* switching the vertical
nametable, which `scrollY` models.

## Spec

* Scroll. With `X0 = 8·coarseX(t) + x` and `Y0 = 8·coarseY(t) + fineY(t)`: screen column `x`
  shows column `(X0 + x) mod 256` of horizontal nametable `nt₀(t) ⊕ [X0 + x ≥ 256]`; screen
  line `y` shows row `(Y0 + y) mod 240` of vertical nametable `nt₁(t) ⊕ [Y0 + y ≥ 240]` when
  `Y0 < 240`, else row `(Y0 + y) mod 256` of nametable `nt₁(t)`.
* `bgPixel s0 rd x y`: 4-bit background index `palette·4 + pattern` (0 when the pattern bits are
  0) of that position: tile byte at `$2000 + $400·nt + 32·(row/8) + col/8`, attribute byte at
  `$23C0 + $400·nt + 8·(row/32) + col/32` (quadrant `(row/16 mod 2, col/16 mod 2)`), pattern at
  `$1000·ctrl.4 + 16·tile + row mod 8` (+8 for the high plane), bit `7 - col mod 8`. No masks.
* `spritePixel s0 rd x y`: for `y ≥ 1`, among the sprites `evalSpec oam (y-1) h` selects (OAM
  order; OAM Y = top line − 1), the first whose pattern bit at `x` is opaque, as
  `(palette index $10 + 4·attr.0-1 + pattern, behind-background = attr.5)`; `none` if none
  (and always on line 0). Sprite row `y-1-Y`, vertically flipped by `attr.7`; column `x - X`,
  horizontally flipped by `attr.6`; 8×8 pattern table `ctrl.3`, 8×16 table `tile.0` with the
  top half tile `tile & $FE`.
* `pixel s0 rd palRd x y`: background index masked to 0 unless `mask.3 ∧ (x ≥ 8 ∨ mask.1)`,
  sprite masked to `none` unless `mask.4 ∧ (x ≥ 8 ∨ mask.2)`; the opaque sprite wins unless it
  is behind an opaque background; index 0 (universal background, `$3F00`) when both are
  transparent; colour `palRd index & $3F`, or `& $30` with greyscale (`mask.0`). The index is
  never `$10/$14/$18/$1C` (a sprite pixel is opaque), so palette mirroring is left to `palRd`.
  Emphasis is not part of the frame.
* `frame s0 rd palRd`: the 256×240 row-major array of `pixel`.
-/

namespace Nes.Ppu.Declarative

open Nes.Ppu

/-- Bit `i` of byte `b`, as 0 or 1. -/
def bit (b : UInt8) (i : Nat) : Nat := b.toNat / 2 ^ i % 2

/-- Scrolled column of screen column `x` and its horizontal nametable bit. -/
def scrollX (s0 : State) (x : Nat) : Nat × Nat :=
  let x0 := 8 * (Loopy.coarseX s0.t).toNat + s0.x.toNat % 8
  ((x0 + x) % 256, ((Loopy.nt s0.t).toNat % 2 + (x0 + x) / 256) % 2)

/-- Scrolled row of screen line `y` and its vertical nametable bit (see module doc). -/
def scrollY (s0 : State) (y : Nat) : Nat × Nat :=
  let y0 := 8 * (Loopy.coarseY s0.t).toNat + (Loopy.fineY s0.t).toNat
  let ny := (Loopy.nt s0.t).toNat / 2
  if y0 < 240 then ((y0 + y) % 240, (ny + (y0 + y) / 240) % 2) else ((y0 + y) % 256, ny)

/-- Background index `palette·4 + pattern` at screen `(x, y)` (0 = transparent), unmasked. -/
def bgPixel (s0 : State) (rd : UInt16 → UInt8) (x y : Nat) : UInt8 :=
  let (col, nx) := scrollX s0 x
  let (row, ny) := scrollY s0 y
  let nt := 0x2000 + 0x400 * (2 * ny + nx)
  let tile := rd (nt + 32 * (row / 8) + col / 8).toUInt16
  let attr := rd (nt + 0x3C0 + 8 * (row / 32) + col / 32).toUInt16
  let pal := attr.toNat / 2 ^ (4 * (row / 16 % 2) + 2 * (col / 16 % 2)) % 4
  let pt := (if s0.bgTable then 0x1000 else 0) + 16 * tile.toNat + row % 8
  let pat := bit (rd pt.toUInt16) (7 - col % 8) + 2 * bit (rd (pt + 8).toUInt16) (7 - col % 8)
  if pat = 0 then 0 else (4 * pal + pat).toUInt8

/-- Sprite height: 16 in 8×16 mode, else 8. -/
def height (s0 : State) : Nat := if s0.sprTall then 16 else 8

/-- Pattern bits (0–3) of OAM sprite `n` at screen `(x, y)`, for a sprite in range of line
`y - 1`; 0 when column `x` is outside the sprite. -/
def spriteBits (s0 : State) (rd : UInt16 → UInt8) (n x y : Nat) : Nat :=
  let top := (getByte s0.oam (4 * n)).toNat
  let tile := (getByte s0.oam (4 * n + 1)).toNat
  let attr := getByte s0.oam (4 * n + 2)
  let sx := (getByte s0.oam (4 * n + 3)).toNat
  let row := if bit attr 7 = 1 then height s0 - 1 - (y - 1 - top) else y - 1 - top
  let addr := if s0.sprTall then 0x1000 * (tile % 2) + 16 * (tile - tile % 2 + row / 8) + row % 8
    else (if s0.sprTable then 0x1000 else 0) + 16 * tile + row
  let c := if bit attr 6 = 1 then x - sx else 7 - (x - sx)
  if sx ≤ x ∧ x < sx + 8 then bit (rd addr.toUInt16) c + 2 * bit (rd (addr + 8).toUInt16) c else 0

/-- The front-most opaque sprite at screen `(x, y)`, unmasked: its palette index (`$10`–`$1F`)
and whether it is behind the background. -/
def spritePixel (s0 : State) (rd : UInt16 → UInt8) (x y : Nat) : Option (UInt8 × Bool) :=
  if y = 0 then none else
  match (Sprites.evalSpec s0.oam (y - 1) (height s0)).1.find? (spriteBits s0 rd · x y ≠ 0) with
  | none => none
  | some n =>
    let attr := getByte s0.oam (4 * n + 2)
    some ((0x10 + 4 * (attr.toNat % 4) + spriteBits s0 rd n x y).toUInt8, bit attr 5 = 1)

/-- The 6-bit colour of screen pixel `(x, y)`, as stored in `State.frame`. -/
def pixel (s0 : State) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (x y : Nat) : UInt8 :=
  let bg := if s0.showBg ∧ (8 ≤ x ∨ s0.bgLeft) then bgPixel s0 rd x y else 0
  let spr := if s0.showSpr ∧ (8 ≤ x ∨ s0.sprLeft) then spritePixel s0 rd x y else none
  let idx := match spr with
    | some (i, behind) => if behind ∧ bg ≠ 0 then bg else i
    | none => bg
  palRd idx &&& (if s0.mask &&& 1 != 0 then 0x30 else 0x3F)

/-- The whole 256×240 frame, row-major. -/
def frame (s0 : State) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) : ByteArray :=
  ⟨(Array.range (frameWidth * frameHeight)).map fun i => pixel s0 rd palRd (i % 256) (i / 256)⟩

end Nes.Ppu.Declarative
