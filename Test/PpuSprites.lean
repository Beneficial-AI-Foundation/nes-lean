import Nes.Ppu.Render

/-!
# Sprite evaluation / fetch / render tests

(1) The per-dot evaluation machine (`Sprites.evalDot`) against the declarative `evalSpec` on
hand-made OAMs (incl. the NESdev overflow-bug false positive / false negative) and on
pseudo-random OAMs, 8×8 and 8×16. (2) Fetch addresses (8×16, vertical flip, A12). (3) One
rendered line with two overlapping sprites over background: priority, h-flip, palette,
sprite-0 hit dot, left-8 masks.
-/

namespace Test.PpuSprites

open Nes.Ppu Nes.Ppu.Sprites Nes.Ppu.Render

/-- OAM from a list of `(y, tile, attr, x)`, rest filled with Y = $F0 (off-screen). -/
def mkOam (l : List (UInt8 × UInt8 × UInt8 × UInt8)) : ByteArray := Id.run do
  let mut o := zeroBytes 256
  for i in [0:64] do o := o.set! (4 * i) 0xF0
  for ((y, t, a, x), i) in l.zipIdx do
    o := o.set! (4 * i) y |>.set! (4 * i + 1) t |>.set! (4 * i + 2) a |>.set! (4 * i + 3) x
  return o

/-- Run evaluation dots 1–256 on `line`. -/
def runEval (oam : ByteArray) (line : Nat) (tall : Bool) : State := Id.run do
  let mut s : State := { State.init with oam, scanline := line.toUInt16, mask := 0x1E,
                                         ctrl := if tall then 0x20 else 0 }
  for d in [1:257] do
    s := evalDot { s with dot := d.toUInt16 }
  return s

/-- Check the machine against the spec; returns an error message or `none`. -/
def checkEval (oam : ByteArray) (line : Nat) (tall : Bool) : Option String :=
  let h := if tall then 16 else 8
  let (sel, ovf) := evalSpec oam line h
  let s := runEval oam line tall
  let secOk := sel.zipIdx.all fun (n, k) =>
    (List.range 4).all fun b => getByte s.secOam (4 * k + b) == getByte oam (4 * n + b)
  let restOk := (List.range 32).all fun b =>
    b < 4 * sel.length || b == 4 * sel.length || getByte s.secOam b == 0xFF
  if s.evalSec.toNat != 4 * sel.length then some s!"count {s.evalSec.toNat / 4} ≠ {sel.length}"
  else if s.sprOverflow != ovf then some s!"overflow {s.sprOverflow} ≠ {ovf}"
  else if s.spr0Next != sel.contains 0 then some "spr0Next"
  else if !secOk then some "secOam contents"
  else if !restOk then some "secOam not cleared"
  else none

/-- Tiny LCG for pseudo-random OAMs. -/
def lcg (x : UInt32) : UInt32 := x * 1664525 + 1013904223

def randOam (seed : UInt32) : ByteArray := Id.run do
  let mut r := seed
  let mut o := zeroBytes 256
  for i in [0:256] do
    r := lcg r
    let b := (r >>> 24).toUInt8
    -- Y bytes and every other byte clustered near lines 40–70 so lines overflow often.
    let b := if i % 4 == 0 || (r >>> 8) % 3 == 0 then 40 + b % 32 else b
    o := o.set! i b
  return o

def evalCases : List (String × ByteArray × Nat × Bool) :=
  let spr (y : UInt8) : UInt8 × UInt8 × UInt8 × UInt8 := (y, 0, 0, 0)
  [ ("3 sprites", mkOam [spr 10, spr 100, spr 45, spr 50, spr 47], 50, false),
    ("none", mkOam [spr 10, spr 100], 50, false),
    ("sprite 0 edge", mkOam [spr 43, spr 42, spr 51], 50, false),
    ("8x16", mkOam [spr 40, spr 35, spr 34, spr 50], 49, true),
    ("exactly 8", mkOam (List.replicate 8 (spr 50)), 52, false),
    ("9 → overflow", mkOam (List.replicate 9 (spr 50)), 52, false),
    -- NESdev false negative: 9th in-range sprite checked on its tile byte (m = 1), which is out
    -- of range, so no overflow although 9 sprites cover the line.
    ("bug: false negative", mkOam (List.replicate 8 (spr 50) ++ [spr 200, (50, 200, 0, 0)]),
      52, false),
    -- NESdev false positive: only 8 sprites on the line, but sprite 9's tile byte (m = 1) is in
    -- range, so the overflow flag is set.
    ("bug: false positive", mkOam (List.replicate 8 (spr 50) ++ [spr 200, (200, 49, 0, 0)]),
      52, false),
    ("bug: m wraps to attr/X", mkOam (List.replicate 8 (spr 50) ++
      [spr 200, (200, 0, 0, 0), (200, 0, 0, 0), (200, 0, 0, 50)]), 52, false),
    ("8th is #63", mkOam (List.replicate 56 (spr 200) ++ List.replicate 8 (spr 50)), 52, false) ]

def specExpect : List (String × ByteArray × Nat × Nat × List Nat × Bool) :=
  let spr (y : UInt8) : UInt8 × UInt8 × UInt8 × UInt8 := (y, 0, 0, 0)
  [ ("spec 3", mkOam [spr 10, spr 100, spr 45, spr 50, spr 47], 50, 8, [2, 3, 4], false),
    ("spec 8x16", mkOam [spr 40, spr 35, spr 34, spr 50], 49, 16, [0, 1, 2], false),
    ("spec fneg", mkOam (List.replicate 8 (spr 50) ++ [spr 200, (50, 200, 0, 0)]), 52, 8,
      List.range 8, false),
    ("spec fpos", mkOam (List.replicate 8 (spr 50) ++ [spr 200, (200, 49, 0, 0)]), 52, 8,
      List.range 8, true),
    ("spec 9", mkOam (List.replicate 9 (spr 50)), 52, 8, List.range 8, true) ]

/-- CHR for the render test: tile 1 = right half lo plane; tile 2 = lo $FF, hi $80. -/
def chr (a : UInt16) : UInt8 :=
  let tile := (a >>> 4) &&& 0xFF
  let hiPlane := a &&& 8 != 0
  if tile == 1 then (if hiPlane then 0 else 0x0F)
  else if tile == 2 then (if hiPlane then 0x80 else 0xFF)
  else 0

def bgAt (x : Nat) : UInt8 := if 26 ≤ x && x ≤ 29 then 0x05 else 0

/-- Evaluate + fetch on line 9, then render line 10; returns the state and the first x at
which `status` bit 6 was observed set (256 if never). -/
def renderLine (oam : ByteArray) (mask : UInt8) : State × Nat := Id.run do
  let mut s : State := { State.init with oam, scanline := 9, mask }
  for d in [1:321] do
    s := { s with dot := d.toUInt16 }
    s := evalDot s
    s := fetchDot chr s
  s := { s with scanline := 10 }
  let mut hitX := 256
  for d in [1:257] do
    s := { s with dot := d.toUInt16 }
    s := pixel id (bgAt (d - 1)) s
    s := evalDot s
    if s.spr0Hit && hitX == 256 then hitX := d - 1
  return (s, hitX)

def run : IO UInt32 := do
  let mut fails : UInt32 := 0
  let mut nChecks := 0
  -- (1a) hand-made OAMs
  for (name, oam, line, tall) in evalCases do
    nChecks := nChecks + 1
    if let some e := checkEval oam line tall then
      IO.println s!"  eval {name}: {e}"; fails := fails + 1
  for (name, oam, line, h, sel, ovf) in specExpect do
    nChecks := nChecks + 1
    let r := evalSpec oam line h
    if r != (sel, ovf) then IO.println s!"  {name}: got {r}"; fails := fails + 1
  -- (1b) random OAMs, many lines, both heights
  for seed in [0:40] do
    let oam := randOam (seed.toUInt32 * 7919 + 1)
    for line in [30:90] do
      for tall in [false, true] do
        nChecks := nChecks + 1
        if let some e := checkEval oam line tall then
          if fails < 10 then IO.println s!"  eval rand seed {seed} line {line} tall {tall}: {e}"
          fails := fails + 1
  -- (2) fetch addresses
  let sec16 := (((((zeroBytes 32).set! 0 9).set! 1 3).set! 4 9).set! 5 3).set! 6 0x80
  let s16 : State := { State.init with scanline := 21, ctrl := 0x20, secOam := sec16 }
  let secA := ((zeroBytes 32).set! 0 20).set! 1 0x41
  let a12s : State := { State.init with scanline := 21, ctrl := 0x08, secOam := secA }
  let addrChecks : List (String × UInt16 × UInt16) :=
    [ ("8x16 row 12", patAddr s16 0, 0x1034), ("8x16 vflip", patAddr s16 1, 0x1023),
      ("8x8 tbl1", patAddr a12s 0, 0x1411),
      ("bus nt", ppuAddrSprite { a12s with dot := 257, v := 0x0123 }, 0x2123),
      ("bus lo", ppuAddrSprite { a12s with dot := 261 }, 0x1411),
      ("bus hi", ppuAddrSprite { a12s with dot := 264 }, 0x1419) ]
  for (name, got, exp) in addrChecks do
    nChecks := nChecks + 1
    if got != exp then IO.println s!"  fetch {name}: {got} ≠ {exp}"; fails := fails + 1
  -- (3) render: sprite 0 at X 20 (tile 1, front, pal 0); sprite 1 at X 24 (tile 2, behind bg,
  -- h-flip, pal 2); a third at X 0 for the left-8 mask.
  let oam := mkOam [(9, 1, 0x00, 20), (9, 2, 0x62, 24), (9, 1, 0x00, 0)]
  let (s, hitX) := renderLine oam 0x1E
  let row (s : State) (x : Nat) : UInt8 := getByte s.frame (10 * 256 + x)
  let exp : List (Nat × UInt8) :=
    [(0, 0), (4, 0x11), (7, 0x11), (8, 0), (19, 0), (20, 0), (23, 0), (24, 0x11), (25, 0x11),
     (26, 0x11), (27, 0x11), (28, 0x05), (29, 0x05), (30, 0x19), (31, 0x1B), (32, 0)]
  for (x, c) in exp do
    nChecks := nChecks + 1
    if row s x != c then IO.println s!"  render x={x}: {row s x} ≠ {c}"; fails := fails + 1
  nChecks := nChecks + 1
  if hitX != 26 then IO.println s!"  sprite-0 hit at x={hitX}, expected 26"; fails := fails + 1
  -- left-8 sprite mask off: sprite at X 0 hidden; sprite-0 behind-bg test with sprites off.
  let (s2, _) := renderLine oam 0x1A
  let (s3, hit3) := renderLine oam 0x0A
  for (name, ok) in [("left mask x=4", row s2 4 == 0), ("left mask x=24", row s2 24 == 0x11),
                     ("sprites off", row s3 24 == 0 && row s3 26 == 0x05),
                     ("no hit sprites off", hit3 == 256)] do
    nChecks := nChecks + 1
    if !ok then IO.println s!"  {name} failed"; fails := fails + 1
  IO.println s!"ppu sprites: {nChecks} checks, {fails} failures"
  return (if fails == 0 then 0 else 1)

end Test.PpuSprites
