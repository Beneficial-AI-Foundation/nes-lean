import Nes.System.Nes

/-!
# blargg PPU test ROMs on the real system

Drives `Nes.System.Nes` (CPU core + PPU + NROM cart; no APU) with blargg's PPU test ROMs:

* `$6000` protocol (`ppu_vbl_nmi`, `ppu_read_buffer`): `$6000` = status (`$80` running, `$81`
  "press reset", else final result, `$00` = pass) once `$6001–$6003` hold `$DE $B0 $61`;
  `$6004…` = zero-terminated text. PRG-RAM at `$6000` is the NROM cart's.
* 2005 shells (`sprite_hit_tests_2005.10.05`, `sprite_overflow_tests`): no `$6000` output. The
  result code is the zero-page byte `$F8` (`1` = passed, `n ≥ 2` = failed test `n`, see each
  readme), printed on screen as "PASSED" / "FAILED #n" with an ASCII tile set; the verdict is
  taken once the screen text shows one of those, the code from `$F8`.

`run` prints one line per ROM and a summary, and returns the number of failing ROMs (those in
`knownFail` are reported but not counted); it skips when the test data is absent.

Status: all `ppu_vbl_nmi` (10), `sprite_hit_tests_2005.10.05` (11), `sprite_overflow_tests` (5)
and `ppu_read_buffer` (1; a CNROM / mapper 3 cart) pass.
-/

namespace Test.BlarggPpu

open Nes.System

/-- Hex byte. -/
def hexByte (b : UInt8) : String :=
  let d (n : Nat) := Char.ofNat (if n < 10 then 48 + n else 55 + n)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- PRG-RAM byte at `$6000 + i`. -/
def prgRam (n : Nes) (i : Nat) : UInt8 := n.cart.st.prgRam.get! i

/-- `$6004…` text. -/
def statusText (n : Nes) : String := Id.run do
  let mut s := ""
  for i in [4:0x2000] do
    let c := prgRam n i
    if c == 0 then break
    s := s.push (Char.ofNat c.toNat)
  return s

def signatureOk (n : Nes) : Bool :=
  prgRam n 1 == 0xDE && prgRam n 2 == 0xB0 && prgRam n 3 == 0x61

/-- Nametable 0 (CIRAM page 0, 32×30 tiles) read as ASCII. -/
def screenText (n : Nes) : String := Id.run do
  let mut out := ""
  for row in [0:30] do
    let mut line := ""
    for col in [0:32] do
      let t := n.ciram.get! (row * 32 + col)
      line := line.push (if 0x20 ≤ t && t < 0x7F then Char.ofNat t.toNat else ' ')
    let l := line.trimAsciiEnd.toString
    unless l.isEmpty do out := out ++ l ++ " / "
  return out

def has (txt w : String) : Bool := (txt.splitOn w).length > 1

/-- Cycles between protocol checks. -/
def chunk : Nat := 100000

/-- Cycles to wait after a `$81` reset request (≈ 112 ms). -/
def resetDelay : Nat := 200000

/-- How a ROM reports. -/
inductive Proto where
  | status6000
  | zp2005
  deriving BEq

/-- Run one ROM: `(passed, code, text)`. -/
def runRom (path : System.FilePath) (proto : Proto) (maxCycles : Nat) :
    IO (Bool × UInt8 × String) := do
  let cart ← match Nes.Cart.Cart.load (← IO.FS.readBinFile path) with
    | .ok c => pure c
    | .error e => return (false, 0xFF, s!"load error: {e}")
  let mut n := Nes.powerOn cart
  let mut resetAt : Option UInt64 := none
  while n.clock.toNat < maxCycles do
    n := Nes.runCycles chunk n
    if let some t := resetAt then
      if n.clock ≥ t then
        n := n.reset; resetAt := none
      continue
    match proto with
    | .status6000 =>
      if signatureOk n then
        let st := prgRam n 0
        if st == 0x81 then resetAt := some (n.clock + resetDelay.toUInt64)
        else if st != 0x80 then
          n := Nes.runCycles 1000 n
          return (st == 0, st, statusText n)
    | .zp2005 =>
      let txt := screenText n
      if has txt "PASSED" || has txt "FAILED" || has txt "INTERNAL ERROR" then
        n := Nes.runCycles 200000 n   -- let the line finish printing
        let code := n.ram.get! 0xF8
        return (code == 1, code, screenText n)
  let extra := if proto == .status6000 then statusText n else screenText n
  return (false, 0xFF, s!"TIMEOUT after {n.clock} cycles at PC {n.cpu.ms.cpu.pc}; {extra}")

def romDir : System.FilePath := "testdata/nes-test-roms"

/-- ROMs that cannot pass yet, with the reason (reported, not counted as failures). -/
def knownFail : List (String × String) :=
  []

/-- The ROMs of this item, with protocol and cycle budget. -/
def roms : List (String × Proto × Nat) :=
  [ "01-vbl_basics", "02-vbl_set_time", "03-vbl_clear_time", "04-nmi_control",
    "05-nmi_timing", "06-suppression", "07-nmi_on_timing", "08-nmi_off_timing",
    "09-even_odd_frames", "10-even_odd_timing" ].map
      (fun r => (s!"ppu_vbl_nmi/rom_singles/{r}.nes", .status6000, 40000000)) ++
  [ ("ppu_read_buffer/test_ppu_read_buffer.nes", .status6000, 80000000) ] ++
  [ "01.basics", "02.alignment", "03.corners", "04.flip", "05.left_clip", "06.right_edge",
    "07.screen_bottom", "08.double_height", "09.timing_basics", "10.timing_order",
    "11.edge_timing" ].map
      (fun r => (s!"sprite_hit_tests_2005.10.05/{r}.nes", .zp2005, 30000000)) ++
  [ "1.Basics", "2.Details", "3.Timing", "4.Obscure", "5.Emulator" ].map
      (fun r => (s!"sprite_overflow_tests/{r}.nes", .zp2005, 30000000))

/-- Run the ROMs whose path contains `filter`; returns the number of failures. -/
def runFiltered (filter : String) : IO UInt32 := do
  unless ← romDir.pathExists do
    IO.println "blargg-ppu: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let sel := roms.filter fun (r, _) => has r filter || filter.isEmpty
  let mut fails : UInt32 := 0
  for (r, proto, maxCycles) in sel do
    let (ok, code, txt) ← runRom (romDir / r) proto maxCycles
    let known := knownFail.lookup r
    if !ok && known.isNone then fails := fails + 1
    let verdict := if ok then "PASS" else match known with
      | some why => s!"KNOWN FAIL ${hexByte code} [{why}]"
      | none => s!"FAIL ${hexByte code}"
    IO.println s!"blargg-ppu {r}: {verdict} ({txt.trimAscii})"
    if ok && known.isSome then IO.println s!"  note: {r} now passes; drop it from knownFail"
  let nKnown := (sel.filter fun (r, _) => (knownFail.lookup r).isSome).length
  IO.println s!"blargg-ppu: {sel.length - nKnown - fails.toNat}/{sel.length - nKnown} passed \
    ({nKnown} known failure(s) not counted)"
  return fails

/-- Run all ROMs; returns the number of failures. -/
def run : IO UInt32 := runFiltered ""

end Test.BlarggPpu
