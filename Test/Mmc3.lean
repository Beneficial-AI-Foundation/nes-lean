import Test.BlarggPpu

/-!
# MMC3 (mapper 4) IRQ test ROMs on the real system

Reuses `Test.BlarggPpu.runRom`:

* `mmc3_test_2/rom_singles` and `mmc3_test` (blargg's newer shells): `$6000` protocol.
* `mmc3_irq_tests` (2005-era shells): result code in zero-page `$F8` (`1` = passed,
  `n ≥ 2` = failed test `n`, see its readme), printed on screen as "PASSED" / "FAILED".

Status: all fifteen Sharp-MMC3 ROMs pass, with no emulator changes. Known failures: the three ROMs that expect the old /
NEC MMC3A (or MMC6) IRQ behaviour.

`run` prints one line per ROM and a summary, and returns the number of failing ROMs (those in
`knownFail` are reported but not counted); it skips when the test data is absent.
-/

namespace Test.Mmc3

open Test.BlarggPpu

/-- ROMs that cannot pass, with the reason (reported, not counted as failures). -/
def knownFail : List (String × String) :=
  [ ("mmc3_test_2/rom_singles/6-MMC3_alt.nes",
      "old/NEC MMC3A IRQ behaviour; the Sharp (new) MMC3 is modelled"),
    ("mmc3_test/6-MMC6.nes", "MMC6 IRQ behaviour (= old MMC3A); the Sharp (new) MMC3 is modelled"),
    ("mmc3_irq_tests/5.MMC3_rev_A.nes",
      "old/NEC MMC3A IRQ behaviour; the Sharp (new) MMC3 is modelled") ]

/-- The ROMs, with protocol and cycle budget. -/
def roms : List (String × Proto × Nat) :=
  [ "1-clocking", "2-details", "3-A12_clocking", "4-scanline_timing", "5-MMC3", "6-MMC3_alt" ].map
      (fun r => (s!"mmc3_test_2/rom_singles/{r}.nes", .status6000, 40000000)) ++
  [ "1-clocking", "2-details", "3-A12_clocking", "4-scanline_timing", "5-MMC3", "6-MMC6" ].map
      (fun r => (s!"mmc3_test/{r}.nes", .status6000, 40000000)) ++
  [ "1.Clocking", "2.Details", "3.A12_clocking", "4.Scanline_timing", "5.MMC3_rev_A",
    "6.MMC3_rev_B" ].map
      (fun r => (s!"mmc3_irq_tests/{r}.nes", .zp2005, 30000000))

/-- Result text on one line. -/
def oneLine (t : String) : String :=
  " ".intercalate ((t.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))

/-- Run the ROMs whose path contains `filter`; returns the number of failures. -/
def runFiltered (filter : String) : IO UInt32 := do
  unless ← romDir.pathExists do
    IO.println "mmc3: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
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
    IO.println s!"mmc3 {r}: {verdict} ({oneLine txt})"
    if ok && known.isSome then IO.println s!"  note: {r} now passes; drop it from knownFail"
  let nKnown := (sel.filter fun (r, _) => (knownFail.lookup r).isSome).length
  IO.println s!"mmc3: {sel.length - nKnown - fails.toNat}/{sel.length - nKnown} passed \
    ({nKnown} known failure(s) not counted)"
  return fails

/-- Run all ROMs; returns the number of failures. -/
def run : IO UInt32 := runFiltered ""

end Test.Mmc3
