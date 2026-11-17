import Nes
import Test.Axioms
import Test.CpuIsa
import Test.CpuMicro
import Test.Interrupts
import Test.Blargg
import Test.PpuBg
import Test.PpuSprites
import Test.Image
import Test.BlarggPpu
import Test.Golden
import Test.Mmc3
import Test.SaveState

/-- `lake test` driver. Each suite returns the number of failures.
`lake test -- --full` also runs the full Harte sweeps (2.56 M cases, ISA and per-cycle). -/
def main (args : List String) : IO UInt32 := do
  IO.println s!"axioms: {Test.Axioms.axiomsChecked} theorems checked"
  let mut fails : UInt32 := 0
  fails := fails + (← Test.Harte.runFast Test.CpuIsa.harteStep)
  fails := fails + (← Test.Nestest.runNestest Test.CpuIsa.nestestStep)
  fails := fails + (← Test.CpuMicro.sweep "micro trace (fast)" Test.Harte.fastSubset 100)
  fails := fails + (← Test.Interrupts.run)
  fails := fails + (← Test.Blargg.run)
  fails := fails + (← Test.PpuBg.run)
  fails := fails + (← Test.PpuSprites.run)
  fails := fails + (← Test.Image.run)
  fails := fails + (← Test.BlarggPpu.run)
  fails := fails + (← Test.Golden.run)
  fails := fails + (← Test.Mmc3.run)
  fails := fails + (← Test.SaveState.run)
  if args.contains "--full" then
    fails := fails + (← Test.CpuIsa.fullSweep)
    fails := fails + (← Test.CpuMicro.sweep "micro trace (full)" Test.CpuMicro.allOps 10000)
  IO.println s!"tests: {if fails == 0 then "PASS" else s!"{fails} failing suite(s)"}"
  return fails
