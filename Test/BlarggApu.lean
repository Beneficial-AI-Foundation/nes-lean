import Test.BlarggPpu

/-!
# blargg APU test ROMs on the real system

Drives `Nes.System.Nes` (CPU + PPU + APU with DMC DMA) with blargg's APU / DMA test ROMs, through
`Test.BlarggPpu.runRom` (same two reporting protocols):

* `$6000` protocol: `apu_test/rom_singles` (8), `apu_reset` (6; they ask for a reset, `$81`),
  `dmc_dma_during_read4` (5), `sprdma_and_dmc_dma` (2).
* 2005 shell (result code at `$F8`, verdict on screen): `blargg_apu_2005.07.30` (11).

Status: all 8 `apu_test`, all 6 `apu_reset`, 4 of 5 `dmc_dma_during_read4` and all 11
`blargg_apu_2005.07.30` pass; `knownFail` has the rest. (On this system the CPU suite's
APU-dependent ROMs — `instr_misc` incl. `04-dummy_reads_apu`, `instr_timing`,
`cpu_exec_space_apu`, `cpu_interrupts_v2` — also pass; `Test.Blargg` still runs them on its
scaffolding.)

`run` prints one line per ROM and a summary, and returns the number of failing ROMs (those in
`knownFail` are reported but not counted); it skips when the test data is absent.
-/

namespace Test.BlarggApu

open Test.BlarggPpu Nes.System

/-- How a ROM reports. -/
inductive Report where
  /-- `$6000` status protocol (`Test.BlarggPpu`), with a `$81` reset request honoured once per
  request: after a reset the status must leave `$81` before another reset is taken (the
  `apu_reset` handlers run for ~2 frames before re-entering the shell, longer than a check
  chunk). -/
  | status6000
  /-- 2005 shell: the result code is printed on screen as `$NN` (`$01` = passed). -/
  | code2005
  /-- Old shell without `$6000`: "Passed" / "Failed" / "Error" on screen, or (ROMs that only
  print a CRC) one of the accepted CRCs. -/
  | screen (accept : List String)

/-- The first `$NN` (two hex digits) token of the screen text. -/
def dollarCode (txt : String) : Option UInt8 := Id.run do
  let cs := txt.toList.toArray
  let hex (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - 48)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none
  for i in [0:cs.size] do
    if h : i + 3 < cs.size then
      if cs[i] == '$' then
        match hex cs[i+1], hex cs[i+2] with
        | some a, some b => if cs[i+3] == ' ' then return some (a * 16 + b).toUInt8
        | _, _ => pure ()
  return none

/-- Any of `ws` occurs in `txt`. -/
def hasAny (txt : String) (ws : List String) : Bool := ws.any (has txt)

/-- Run one ROM: `(passed, code, text)`. -/
def runRom (path : System.FilePath) (rep : Report) (maxCycles : Nat) :
    IO (Bool × UInt8 × String) := do
  let cart ← match Nes.Cart.Cart.load (← IO.FS.readBinFile path) with
    | .ok c => pure c
    | .error e => return (false, 0xFF, s!"load error: {e}")
  let mut n := Nes.powerOn cart
  let mut resetAt : Option UInt64 := none
  let mut resetDone := false
  while n.clock.cpuCycles.toNat < maxCycles do
    n := Nes.runCycles chunk n
    if let some t := resetAt then
      if n.clock.cpuCycles ≥ t then
        n := n.reset; resetAt := none; resetDone := true
      continue
    match rep with
    | .status6000 =>
      if signatureOk n then
        let st := prgRam n 0
        if st == 0x81 then
          unless resetDone do resetAt := some (n.clock.cpuCycles + resetDelay.toUInt64)
        else
          resetDone := false
          if st != 0x80 then
            n := Nes.runCycles 1000 n
            return (st == 0, st, statusText n)
    | .code2005 =>
      if let some c := dollarCode (screenText n ++ " ") then
        n := Nes.runCycles 200000 n
        let c := (dollarCode (screenText n ++ " ")).getD c
        return (c == 1, c, screenText n)
    | .screen accept =>
      let txt := screenText n
      if hasAny txt ["Passed", "Failed", "Error"] || hasAny txt accept then
        n := Nes.runCycles 200000 n
        let txt := screenText n
        return (has txt "Passed" || hasAny txt accept, 0, txt)
  return (false, 0xFF, s!"TIMEOUT after {n.clock.cpuCycles} cycles at PC {n.cpu.ms.cpu.pc}; \
    {statusText n} {screenText n}")

/-- ROMs that cannot pass yet, with the reason (reported, not counted as failures). -/
def knownFail : List (String × String) :=
  [ ("sprdma_and_dmc_dma/sprdma_and_dmc_dma.nes",
      "DMC DMA at the edges of OAM DMA (the documented 1/3-cycle cases) not modelled: prints \
      528/526, CRC mismatch"),
    ("sprdma_and_dmc_dma/sprdma_and_dmc_dma_512.nes",
      "DMC DMA at the edges of OAM DMA (the documented 1/3-cycle cases) not modelled") ]

/-- The ROMs, with protocol and cycle budget. -/
def roms : List (String × Report × Nat) :=
  [ "1-len_ctr", "2-len_table", "3-irq_flag", "4-jitter", "5-len_timing", "6-irq_flag_timing",
    "7-dmc_basics", "8-dmc_rates" ].map
      (fun r => (s!"apu_test/rom_singles/{r}.nes", .status6000, 60000000)) ++
  [ "4015_cleared", "4017_timing", "4017_written", "irq_flag_cleared", "len_ctrs_enabled",
    "works_immediately" ].map
      (fun r => (s!"apu_reset/{r}.nes", .status6000, 40000000)) ++
  -- `dma_2007_read` / `double_2007_read` print only a CRC: the accepted ones are listed in their
  -- sources (they depend on the CPU-PPU alignment at power-on).
  [ ("dmc_dma_during_read4/dma_2007_read.nes", .screen ["159A7A8F", "5E3DF9C4"], 40000000),
    ("dmc_dma_during_read4/dma_2007_write.nes", .screen [], 40000000),
    ("dmc_dma_during_read4/dma_4016_read.nes", .screen [], 40000000),
    ("dmc_dma_during_read4/double_2007_read.nes",
      .screen ["85CFD627", "F018C287", "440EF923", "E52F41A5"], 40000000),
    ("dmc_dma_during_read4/read_write_2007.nes", .screen [], 40000000) ] ++
  [ "sprdma_and_dmc_dma", "sprdma_and_dmc_dma_512" ].map
      (fun r => (s!"sprdma_and_dmc_dma/{r}.nes", .status6000, 60000000)) ++
  [ "01.len_ctr", "02.len_table", "03.irq_flag", "04.clock_jitter", "05.len_timing_mode0",
    "06.len_timing_mode1", "07.irq_flag_timing", "08.irq_timing", "09.reset_timing",
    "10.len_halt_timing", "11.len_reload_timing" ].map
      (fun r => (s!"blargg_apu_2005.07.30/{r}.nes", .code2005, 30000000))

/-- Run the ROMs whose path contains `filter`; returns the number of failures. -/
def runFiltered (filter : String) : IO UInt32 := do
  unless ← romDir.pathExists do
    IO.println "blargg-apu: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
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
    IO.println s!"blargg-apu {r}: {verdict} ({txt.trimAscii})"
    if ok && known.isSome then IO.println s!"  note: {r} now passes; drop it from knownFail"
  let nKnown := (sel.filter fun (r, _) => (knownFail.lookup r).isSome).length
  IO.println s!"blargg-apu: {sel.length - nKnown - fails.toNat}/{sel.length - nKnown} passed \
    ({nKnown} known failure(s) not counted)"
  return fails

/-- Run all ROMs; returns the number of failures. -/
def run : IO UInt32 := runFiltered ""

end Test.BlarggApu
