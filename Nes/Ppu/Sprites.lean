import Nes.Ppu.Types

/-!
# `Nes.Ppu.Sprites` — sprite evaluation (dots 1–256) and sprite fetches (dots 257–320)

Reference: NESdev wiki, "PPU sprite evaluation" and "PPU rendering" (frame timing diagram).

## Evaluation (`evalDot`, visible lines 0–239, rendering enabled, dots 1–256)

Evaluation on scanline `L` selects the sprites drawn on line `L + 1`: sprite `n` (OAM bytes
`4n..4n+3` = Y, tile, attribute, X) is *in range* when `Y ≤ L < Y + h`, `h` = 8 or 16
(`ctrl` bit 5). Per-dot machine (odd dots read OAM into `evalLatch`, even dots act on it):

* Dots 1–64: secondary OAM clear; each even dot `d` writes `$FF` to `secOam[d/2 - 1]`.
* Dot 65: `evalN := 0`, `evalM := 0`, `evalSec := 0`, `spr0Next := false` (OAMADDR is assumed 0,
  as it is when the game does not write it during rendering).
* Odd dots 65–255: `evalLatch := oam[4·evalN + evalM]`.
* Even dots 66–256, with `n = evalN`, `m = evalM`, `b = evalLatch`; `evalN ≥ 64` means *done*:
  - copy phase (`evalSec < 32`): `secOam[evalSec] := b`. If `m = 0` and `b` is not in range,
    `n += 1` (the Y byte stays written but `evalSec` does not advance). Otherwise (`m = 0` in
    range, or `m ≠ 0`) `evalSec += 1`, `m += 1`, and `m = 4` wraps to 0 with `n += 1`; a
    sprite-0 hit at `m = 0, n = 0` sets `spr0Next`.
  - overflow phase (`evalSec = 32`, eight sprites found, secondary-OAM writes disabled): if `b`
    is in range, set `status` bit 5 and finish; else `n += 1` **and** `m := (m + 1) & 3` — the
    hardware bug: `m` is not reset, so later sprites are checked on their tile/attr/X byte.
  - done: nothing (the hardware keeps reading `oam[4n]` and fails to write).

The machine always finishes by dot 256 (≤ 64 + 3·8 = 88 read/act pairs of the 96 available),
so its result is `evalSpec`:

* `evalSpec oam L h = (sel, ovf)`: `hits` = the in-range OAM indices in increasing order,
  `sel = hits.take 8`; `ovf` is false when fewer than 8 hit, else with `k = hits[7]`,
  `ovf = ∃ j, k + 1 + j < 64 ∧ inRange oam[4(k+1+j) + j % 4]` (the diagonal walk).
* After dot 256, `secOam[0 .. 4·|sel|)` holds the selected sprites' four bytes in OAM order,
  `evalSec = 4·|sel|`, `spr0Next = (0 ∈ sel)`, and `status` bit 5 is set if `ovf` (never
  cleared here; the timing item clears it at pre-render dot 1). The remaining bytes are `$FF`
  except `secOam[4·|sel|]` when `|sel| < 8`, which may hold the last rejected Y byte.

## Fetch (`fetchDot`, lines 0–239 and 261, rendering enabled, dots 257–320)

Slot `i = (dot - 257) / 8`, phase `p = (dot - 257) % 8`. On the bus (`ppuAddrSprite`):
phases 0–3 a garbage nametable address `$2000 | (v & $0FFF)` (A12 = 0), phases 4–5 the
pattern low-plane address, 6–7 the high plane (`+ 8`). The pattern address of slot `i` with
`Y, tile, attr = secOam[4i], [4i+1], [4i+2]`, line `L` and `row = (L - Y) mod h`, vertically
flipped (`row := h - 1 - row`) when `attr` bit 7 is set:
8×8: `(ctrl.3 ? $1000 : 0) + 16·tile + row`; 8×16: `$1000·(tile & 1) + 16·((tile & $FE) + row/8)
+ row % 8`. Empty slots read the cleared secondary OAM, so they fetch tile `$FF`.

* Phase 0 of slot 0 (dot 257): `sprCount := evalSec / 4`, `spr0Line := spr0Next` on lines
  0–239; on line 261 `sprCount := 0`, `spr0Line := false` (no sprites on line 0).
* Phase 0: `sprAttr[i] := attr`, `sprX[i] := secOam[4i+3]`.
* Phase 5 / 7: `sprPatLo[i]` / `sprPatHi[i] := rd addr`, bit-reversed when `attr` bit 6
  (horizontal flip) is set, so bit 7 is always the leftmost pixel; 0 for slots `i ≥ sprCount`.
  `rd` is called for every slot (empty ones included), once per plane.
-/

namespace Nes.Ppu.Sprites

open Nes.Ppu

/-! ### Declarative spec -/

/-- Sprite with top byte `y` covers line `line` for height `h`. -/
def inRangeSpec (y : UInt8) (line h : Nat) : Bool := y.toNat ≤ line && line < y.toNat + h

/-- The overflow flag from the hardware's diagonal walk after the 8th hit at index `k`. -/
def overflowSpec (oam : ByteArray) (line h k : Nat) : Bool :=
  (List.range (64 - (k + 1))).any fun j => inRangeSpec (getByte oam (4 * (k + 1 + j) + j % 4)) line h

/-- Declarative sprite evaluation: the selected OAM indices (first ≤ 8 in-range sprites, in
OAM order) and the sprite-overflow flag as the buggy hardware computes it. -/
def evalSpec (oam : ByteArray) (line h : Nat) : List Nat × Bool :=
  let hits := (List.range 64).filter fun n => inRangeSpec (getByte oam (4 * n)) line h
  let ovf := match hits[7]? with
    | none => false
    | some k => overflowSpec oam line h k
  (hits.take 8, ovf)

/-! ### Evaluation state machine -/

/-- Sprite height: 16 in 8×16 mode, else 8. -/
@[inline] def height (s : State) : UInt16 := if s.sprTall then 16 else 8

/-- Fast in-range test on the line `line` (0–239). -/
@[inline] def inRange (y : UInt8) (line h : UInt16) : Bool :=
  let y16 := y.toUInt16
  y16 ≤ line && line - y16 < h

/-- One even-dot evaluation action on the latched byte. -/
@[inline] def evalAct (s : State) : State :=
  let n := s.evalN
  if n ≥ 64 then s else
  let m := s.evalM
  let b := s.evalLatch
  let hit := inRange b s.scanline (height s)
  if s.evalSec < 32 then
    let sec := s.secOam.set! s.evalSec.toNat b
    if m == 0 && !hit then
      { s with secOam := sec, evalN := n + 1 }
    else
      let spr0 := s.spr0Next || (m == 0 && n == 0)
      let m' := m + 1
      if m' == 4 then
        { s with secOam := sec, evalSec := s.evalSec + 1, evalM := 0, evalN := n + 1,
                 spr0Next := spr0 }
      else
        { s with secOam := sec, evalSec := s.evalSec + 1, evalM := m', spr0Next := spr0 }
  else if hit then
    { s with status := s.status ||| 0x20, evalN := 64 }
  else
    { s with evalN := n + 1, evalM := (m + 1) &&& 3 }

/-- Sprite evaluation work for the current `dot` (1–256) of a visible line. Call before the
timing tick advances `dot`, only when rendering is enabled. -/
@[inline] def evalDot (s : State) : State :=
  let d := s.dot
  if d == 0 || d > 256 then s
  else if d ≤ 64 then
    if d &&& 1 == 0 then { s with secOam := s.secOam.set! (d / 2 - 1).toNat 0xFF } else s
  else if d &&& 1 == 1 then
    let s := if d == 65 then { s with evalN := 0, evalM := 0, evalSec := 0, spr0Next := false }
             else s
    { s with evalLatch := getByte s.oam (4 * s.evalN.toNat + s.evalM.toNat) }
  else evalAct s

/-! ### Fetches -/

/-- Reverse the bits of a byte (horizontal flip). -/
@[inline] def rev8 (b : UInt8) : UInt8 :=
  let b := ((b &&& 0xF0) >>> 4) ||| ((b &&& 0x0F) <<< 4)
  let b := ((b &&& 0xCC) >>> 2) ||| ((b &&& 0x33) <<< 2)
  ((b &&& 0xAA) >>> 1) ||| ((b &&& 0x55) <<< 1)

/-- Low-plane pattern address of sprite slot `i` (0–7) for the next line, from secondary OAM. -/
@[inline] def patAddr (s : State) (i : Nat) : UInt16 :=
  let y := getByte s.secOam (4 * i)
  let tile := (getByte s.secOam (4 * i + 1)).toUInt16
  let attr := getByte s.secOam (4 * i + 2)
  let h : UInt16 := height s
  let row : UInt16 := (s.scanline - y.toUInt16) &&& (h - 1)
  let row : UInt16 := if attr &&& 0x80 != 0 then h - 1 - row else row
  if s.sprTall then
    let bank : UInt16 := (tile &&& (1 : UInt16)) <<< (12 : UInt16)
    let t2 : UInt16 := (tile &&& (0xFE : UInt16)) + (row >>> (3 : UInt16))
    bank + (t2 <<< 4) + (row &&& 7)
  else
    (if s.sprTable then (0x1000 : UInt16) else 0) + (tile <<< 4) + row

/-- The PPU bus address during sprite-fetch dot `s.dot` (257–320); A12 = bit 12 is what MMC3
watches. Outside 257–320 returns the garbage-nametable address. -/
@[inline] def ppuAddrSprite (s : State) : UInt16 :=
  let d := s.dot
  let nt := 0x2000 ||| (s.v &&& 0x0FFF)
  if d < 257 || d > 320 then nt else
  let k := d - 257
  let p := k &&& 7
  if p < 4 then nt
  else
    let a := patAddr s (k >>> 3).toNat
    if p < 6 then a else a + 8

/-- Sprite fetch work for the current `dot` (257–320) on lines 0–239 / 261. `rd` reads the PPU
bus (pattern tables). Call before the timing tick advances `dot`, only when rendering. -/
@[specialize] def fetchDot (rd : UInt16 → UInt8) (s : State) : State :=
  let d := s.dot
  if d < 257 || d > 320 then s else
  let k := d - 257
  let i := (k >>> 3).toNat
  let p := k &&& 7
  if p == 0 then
    let s := if i == 0 then
        if s.scanline < 240 then { s with sprCount := s.evalSec >>> 2, spr0Line := s.spr0Next }
        else { s with sprCount := 0, spr0Line := false }
      else s
    { s with sprAttr := s.sprAttr.set! i (getByte s.secOam (4 * i + 2)),
             sprX := s.sprX.set! i (getByte s.secOam (4 * i + 3)) }
  else if p == 5 || p == 7 then
    let a := patAddr s i
    let b := rd (if p == 5 then a else a + 8)
    let b := if i < s.sprCount.toNat then
        (if getByte s.sprAttr i &&& 0x40 != 0 then rev8 b else b) else 0
    if p == 5 then { s with sprPatLo := s.sprPatLo.set! i b }
    else { s with sprPatHi := s.sprPatHi.set! i b }
  else s

end Nes.Ppu.Sprites
