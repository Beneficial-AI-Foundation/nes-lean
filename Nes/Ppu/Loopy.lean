import Nes.Prelude.Bits

/-!
# `Nes.Ppu.Loopy` — the PPU scroll/address registers `v`, `t` ("loopy" registers)

Representation: `v` and `t` are stored as `UInt16` (15 bits used, bit 15 always 0 in
reachable states) instead of `BitVec 15`, because `BitVec` is `Nat`-backed (boxed) at run
time and these registers are touched every few dots on the hot path. The 15-bit layout is

```
  bit: 14 13 12 | 11 10 | 9 8 7 6 5 | 4 3 2 1 0
       fine Y   |  NT   | coarse Y  | coarse X
```

The *spec view* is `Fields`, a record of `BitVec` fields, read off a word by `toFields`; the
fast operations (`incX`, `incY`, `copyX`, `copyY`) are bit-twiddled on the raw `UInt16`, and
`Nes.Ppu.Proofs.Loopy` proves each one equals its field-level spec (T-REF-2 loopy).

## Spec

* `Fields` has `coarseX : BitVec 5`, `coarseY : BitVec 5`, `nt : BitVec 2` (bit 0 = horizontal
  nametable, bit 1 = vertical), `fineY : BitVec 3`.
* `toFields w` reads bits 0–4, 5–9, 10–11, 12–14 of `w`; `Fields.toWord f` packs them back.
  `coarseX w`, `coarseY w`, `nt w`, `fineY w` are the same fields as `UInt16`s.
* `Fields.incX f`: coarse X + 1; on coarse X = 31 it wraps to 0 and flips `nt` bit 0.
* `Fields.incY f`: fine Y + 1 if fine Y < 7; else fine Y := 0 and coarse Y is advanced:
  29 → 0 flipping `nt` bit 1; 31 → 0 without flipping; otherwise + 1.
* `Fields.copyX v t`: `v` with coarse X and `nt` bit 0 taken from `t`.
* `Fields.copyY v t`: `v` with coarse Y, fine Y and `nt` bit 1 taken from `t`.
* `incX`/`incY`/`copyX`/`copyY` on `UInt16` are the bit-twiddled versions (nesdev wiki
  "PPU scrolling" pseudocode); `maskX = 0x041F`, `maskY = 0x7BE0` are the bits `copyX`/`copyY`
  move.
-/

namespace Nes.Ppu.Loopy

/-- Field-level spec view of a loopy register. -/
structure Fields where
  coarseX : BitVec 5
  coarseY : BitVec 5
  nt : BitVec 2
  fineY : BitVec 3
  deriving Repr, DecidableEq, Inhabited

/-- Read the four fields of a loopy word (bit 15 is ignored). -/
def toFields (w : UInt16) : Fields :=
  { coarseX := w.toBitVec.setWidth 5
    coarseY := (w.toBitVec >>> 5).setWidth 5
    nt := (w.toBitVec >>> 10).setWidth 2
    fineY := (w.toBitVec >>> 12).setWidth 3 }

/-- Pack the fields into a loopy word (bit 15 clear). -/
def Fields.toWord (f : Fields) : UInt16 :=
  ⟨f.coarseX.setWidth 16 ||| (f.coarseY.setWidth 16 <<< 5) ||| (f.nt.setWidth 16 <<< 10) |||
    (f.fineY.setWidth 16 <<< 12)⟩

/-! ### Field accessors on the raw word -/

@[inline] def coarseX (w : UInt16) : UInt16 := w &&& 0x1F
@[inline] def coarseY (w : UInt16) : UInt16 := (w >>> 5) &&& 0x1F
@[inline] def nt (w : UInt16) : UInt16 := (w >>> 10) &&& 0x3
@[inline] def fineY (w : UInt16) : UInt16 := (w >>> 12) &&& 0x7

/-- Bits moved by `copyX`: coarse X and the horizontal nametable bit. -/
@[inline] def maskX : UInt16 := 0x041F
/-- Bits moved by `copyY`: coarse Y, fine Y and the vertical nametable bit. -/
@[inline] def maskY : UInt16 := 0x7BE0

/-! ### Field-level spec -/

namespace Fields

/-- Coarse X increment with horizontal nametable switch. -/
def incX (f : Fields) : Fields :=
  if f.coarseX = 31 then { f with coarseX := 0, nt := f.nt ^^^ 1 }
  else { f with coarseX := f.coarseX + 1 }

/-- Fine Y increment, carrying into coarse Y (with the row-29 nametable switch). -/
def incY (f : Fields) : Fields :=
  if f.fineY ≠ 7 then { f with fineY := f.fineY + 1 }
  else if f.coarseY = 29 then { f with fineY := 0, coarseY := 0, nt := f.nt ^^^ 2 }
  else if f.coarseY = 31 then { f with fineY := 0, coarseY := 0 }
  else { f with fineY := 0, coarseY := f.coarseY + 1 }

/-- Horizontal reload `v ← t` (dot 257). -/
def copyX (v t : Fields) : Fields :=
  { v with coarseX := t.coarseX, nt := (v.nt &&& 2) ||| (t.nt &&& 1) }

/-- Vertical reload `v ← t` (dots 280–304 of the pre-render line). -/
def copyY (v t : Fields) : Fields :=
  { v with coarseY := t.coarseY, fineY := t.fineY, nt := (v.nt &&& 1) ||| (t.nt &&& 2) }

end Fields

/-! ### Fast (bit-twiddled) operations -/

/-- Coarse X increment (nesdev): wrap at 31 and flip bit 10. -/
@[inline] def incX (v : UInt16) : UInt16 :=
  if v &&& 0x1F == 31 then (v &&& ~~~0x1F) ^^^ 0x0400 else v + 1

/-- Fine/coarse Y increment (nesdev). -/
@[inline] def incY (v : UInt16) : UInt16 :=
  if v &&& 0x7000 != 0x7000 then v + 0x1000
  else
    let v := v &&& ~~~0x7000
    let y := v &&& 0x03E0
    if y == 0x03A0 then (v &&& ~~~0x03E0) ^^^ 0x0800      -- coarse Y = 29
    else if y == 0x03E0 then v &&& ~~~0x03E0              -- coarse Y = 31
    else v + 0x20

/-- `v ← t` on coarse X and nametable bit 10. -/
@[inline] def copyX (v t : UInt16) : UInt16 := (v &&& ~~~maskX) ||| (t &&& maskX)

/-- `v ← t` on coarse Y, fine Y and nametable bit 11. -/
@[inline] def copyY (v t : UInt16) : UInt16 := (v &&& ~~~maskY) ||| (t &&& maskY)

end Nes.Ppu.Loopy
