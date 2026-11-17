import Nes
import Nes.Ppu.Declarative

/-!
# Declarative renderer vs the PPU pipeline on static frames (T-PPU-6 evidence)

For each ROM of the golden set: run the console to a golden frame count, then on to scanline 260
(vblank, before the pre-render line), snapshot the PPU state `s0` and readers over the current
CHR / CIRAM / palette, and run **only** the PPU (`Ppu.dot` with those static readers, no CPU) from
`s0` until it reaches line 240. Its `frame` must equal `Declarative.frame s0` byte for byte.

Each snapshot is also checked under perturbations of the registers the renderer reads (scroll
`t`/`x` including coarse Y 30/31, `ctrl` pattern tables / 8×16, `mask` left-8 / layer /
greyscale bits) and with pseudo-random OAM (flips, priority, >8 sprites per line), so that
features a ROM's title screen does not use are exercised too. The suite skips when `testdata/`
is absent.
-/

namespace Test.Declarative

open Nes.Ppu

def dataDir : System.FilePath := "testdata"

/-- `(rom path relative to testdata, frames from power-on)`. -/
def roms : List (String × Nat) :=
  [("nes-test-roms/spritecans-2011/spritecans.nes", 600),
   ("nes-test-roms/other/BladeBuster.nes", 600),
   ("nes-test-roms/other/pulsar.nes", 240),
   ("nes-test-roms/240pee/240pee.nes", 240),
   ("nes-test-roms/other/oam3.nes", 240)]

def runFrames : Nat → Nes.System.Nes → Nes.System.Nes
  | 0, n => n
  | k + 1, n => runFrames k n.runFrame

/-- Run CPU cycles until the PPU is on scanline 260. -/
def toLine260 : Nat → Nes.System.Nes → Nes.System.Nes
  | 0, n => n
  | k + 1, n => if n.ppu.scanline == 260 then n else toLine260 k n.stepCycle

/-- Run the PPU alone until it reaches line 240. -/
def ppuFrame (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) : Nat → State → State
  | 0, s => s
  | k + 1, s => if s.scanline == 240 then s else ppuFrame rd palRd k (Nes.Ppu.dot rd palRd s)

/-- Pseudo-random OAM (xorshift32 from `seed`). -/
def randOam (seed : UInt32) : ByteArray := Id.run do
  let mut x := seed
  let mut a := ByteArray.emptyWithCapacity 256
  for i in [0:256] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 17); x := x ^^^ (x <<< 5)
    -- crowd sprite Y into the upper half so lines get > 8 sprites
    let b := if i % 4 == 0 then (x % 120).toUInt8 else x.toUInt8
    a := a.push b
  return a

/-- Register perturbations: `(name, state transform)`. -/
def variants : List (String × (State → State)) :=
  [("as-is", id),
   ("scroll t=$7FFF x=7", fun s => { s with t := 0x7FFF, x := 7 }),
   ("scroll cy=29 fy=5", fun s => { s with t := 0x5BAD, x := 3 }),
   ("scroll cy=30", fun s => { s with t := 0x23DF, x := 1 }),
   ("scroll cy=31 nt=3", fun s => { s with t := 0x7FE7 }),
   ("ctrl^$18 mask=$1E", fun s => { s with ctrl := s.ctrl ^^^ 0x18, mask := 0x1E }),
   ("8x16 mask=$19", fun s => { s with ctrl := s.ctrl ^^^ 0x20, mask := 0x19 }),
   ("bg only", fun s => { s with mask := 0x0A }),
   ("spr only left", fun s => { s with mask := 0x14 }),
   ("rand oam 8x8", fun s => { s with oam := randOam 0x1234567, mask := 0x18, x := 5,
                                        t := 0x1234 }),
   ("rand oam 8x16", fun s => { s with oam := randOam 0xBEEF, mask := 0x1F,
                                         ctrl := s.ctrl ||| 0x20 })]

/-- Compare one snapshot; returns the number of mismatched pixels (and prints the first few). -/
def check (label : String) (s0 : State) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) :
    IO Nat := do
  let hw := (ppuFrame rd palRd 100000 s0).frame
  let dc := Declarative.frame s0 rd palRd
  let mut bad := 0
  for i in [0:frameWidth * frameHeight] do
    let a := getByte hw i
    let b := getByte dc i
    if a != b then
      if bad < 5 then
        IO.println s!"  {label}: pixel ({i % 256}, {i / 256}) pipeline {a} declarative {b}"
      bad := bad + 1
  IO.println s!"declarative: {if bad == 0 then "ok  " else "FAIL"} {label}: {bad} pixels differ"
  return bad

def run : IO UInt32 := do
  unless ← dataDir.pathExists do
    IO.println "declarative: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut fails := 0
  for (rom, frames) in roms do
    let path := dataDir / rom
    unless ← path.pathExists do
      IO.println s!"declarative: SKIP {rom} (missing)"
      continue
    match Nes.Cart.Cart.load (← IO.FS.readBinFile path) with
    | .error e =>
      IO.println s!"declarative: FAIL {rom}: load error: {e}"
      fails := fails + 1
    | .ok c =>
      let n := toLine260 40000 (runFrames frames (Nes.System.Nes.powerOn c))
      let rd := fun a => Nes.System.Nes.ppuPeek n.cart n.ciram n.ciram_size a
      let palRd := fun i => Nes.System.Nes.palPeek n.pal n.pal_size i
      unless n.ppu.rendering do
        IO.println s!"declarative: note {rom}: rendering disabled at snapshot (mask {n.ppu.mask})"
      for (name, f) in variants do
        if (← check s!"{rom}@{frames} [{name}]" (f n.ppu) rd palRd) != 0 then
          fails := fails + 1
  IO.println s!"declarative: failures {fails}"
  return if fails == 0 then 0 else 1

end Test.Declarative
