import Nes.Ppu.Background

/-!
# Background pipeline test (`Nes.Ppu.Background`)

Flat 16 KiB PPU memory (`rd a := mem[a & $3FFF]`, four distinct nametables at $2000–$2FFF) filled
with pseudo-random bytes. Starting at the pre-render line with `t`/`x` set from a scroll, run
`bgDot` + a minimal dot/scanline counter through the pre-render line and visible lines 0–9, and
compare the 256 `bgPixel`s of each line with a directly computed reference
(nametable tile → pattern bits → attribute quadrant).
-/

namespace Test.PpuBg

open Nes Nes.Ppu

/-- Pseudo-random 16 KiB memory (xorshift). -/
def mkMem (seed : UInt32) : ByteArray := Id.run do
  let mut m := ByteArray.emptyWithCapacity 0x4000
  let mut x := seed
  for _ in [0:0x4000] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 17); x := x ^^^ (x <<< 5)
    m := m.push (x >>> 8).toUInt8
  return m

def rdOf (m : ByteArray) (a : UInt16) : UInt8 := getByte m (a &&& 0x3FFF).toNat

/-- Reference pixel at screen (px, line) for scroll (worldX0 ∈ 0..511, coarseY, fineY, ntY). -/
def refPixel (m : ByteArray) (ctrl mask : UInt8) (wx0 cy fy nty : Nat) (px line : Nat) : UInt8 :=
  if mask &&& 0x08 == 0 || (mask &&& 0x02 == 0 && px < 8) then 0 else
  let wx := (wx0 + px) % 512
  let wy := cy * 8 + fy + line            -- stays within one nametable for the lines tested
  let ntIdx := (wx / 256) + 2 * nty
  let col := (wx % 256) / 8
  let row := wy / 8
  let base := 0x2000 + ntIdx * 0x400
  let tile := (getByte m (base + row * 32 + col)).toNat
  let atb := getByte m (base + 0x3C0 + (row / 4) * 8 + col / 4)
  let sh := ((row &&& 2) <<< 1) ||| (col &&& 2)
  let pal := (atb >>> sh.toUInt8) &&& 3
  let tbl := if ctrl &&& 0x10 != 0 then 0x1000 else 0
  let lo := getByte m (tbl + tile * 16 + wy % 8)
  let hi := getByte m (tbl + tile * 16 + 8 + wy % 8)
  let bit := (7 - wx % 8).toUInt8
  let p := (((hi >>> bit) &&& 1) <<< 1) ||| ((lo >>> bit) &&& 1)
  if p == 0 then 0 else pal * 4 + p

/-- Minimal timing: dot 0–340, scanline 0–261 (no odd-frame skip). -/
def tick (s : State) : State :=
  if s.dot == 340 then { s with dot := 0, scanline := if s.scanline == 261 then 0 else s.scanline + 1 }
  else { s with dot := s.dot + 1 }

/-- One case; returns the number of mismatching pixels. -/
def runCase (m : ByteArray) (ctrl mask : UInt8) (wx0 cy fy nty : Nat) (lines : Nat) : IO Nat := do
  let rd := rdOf m
  let t : UInt16 := ((wx0 / 8 % 32) ||| (cy <<< 5) ||| ((wx0 / 256 % 2) <<< 10) ||| (nty <<< 11)
    ||| (fy <<< 12)).toUInt16
  let s0 : State := { State.init with ctrl := ctrl, mask := mask, t := t }
  let mut s : State := { s0 with x := (wx0 % 8).toUInt8, v := 0x1234, scanline := 261, dot := 0 }
  -- pre-render line
  for _ in [0:341] do s := tick (bgDot rd s)
  let mut bad := 0
  for line in [0:lines] do
    for _ in [0:341] do
      s := bgDot rd s
      let d := s.dot.toNat
      if 1 ≤ d && d ≤ 256 then
        let got := bgPixel s
        let exp := refPixel m ctrl mask wx0 cy fy nty (d - 1) line
        if got != exp then
          if bad < 5 then
            IO.println s!"  mismatch wx0={wx0} cy={cy} fy={fy} line={line} px={d-1}: got {got} exp {exp}"
          bad := bad + 1
      s := tick s
  return bad

def run : IO UInt32 := do
  let m := mkMem 0x9E3779B9
  -- (ctrl, mask, worldX0, coarseY, fineY, ntY)
  let cases : List (UInt8 × UInt8 × Nat × Nat × Nat × Nat) :=
    [ (0x00, 0x1E, 0, 0, 0, 0), (0x00, 0x1E, 5, 0, 0, 0), (0x10, 0x1E, 40, 3, 2, 0),
      (0x00, 0x1E, 133, 7, 5, 1), (0x10, 0x1E, 256 + 77, 12, 7, 0), (0x00, 0x1E, 500, 20, 6, 1),
      (0x00, 0x18, 13, 1, 3, 0), (0x00, 0x16, 21, 1, 3, 0) ]
  let mut bad := 0
  for (ctrl, mask, wx0, cy, fy, nty) in cases do
    bad := bad + (← runCase m ctrl mask wx0 cy fy nty 10)
  IO.println s!"ppu bg: {cases.length} scroll cases × 10 lines × 256 px, {bad} mismatches"
  return if bad == 0 then 0 else 1

end Test.PpuBg
