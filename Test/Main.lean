import Nes
import Test.Axioms
import Test.CpuIsa
import Test.CpuMicro
import Test.Interrupts

/-- `lake test` driver. Each suite returns the number of failures.
`lake test -- --full` also runs the full Harte sweeps (2.56 M cases, ISA and per-cycle). -/
def main (args : List String) : IO UInt32 := do
  IO.println s!"axioms: {Test.Axioms.axiomsChecked} theorems checked"
  let mut fails : UInt32 := 0
  fails := fails + (← Test.Harte.runFast Test.CpuIsa.harteStep)
  fails := fails + (← Test.Nestest.runNestest Test.CpuIsa.nestestStep)
  fails := fails + (← Test.CpuMicro.sweep "micro trace (fast)" Test.Harte.fastSubset 100)
  fails := fails + (← Test.Interrupts.run)
  if args.contains "--full" then
    fails := fails + (← Test.CpuIsa.fullSweep)
    fails := fails + (← Test.CpuMicro.sweep "micro trace (full)" Test.CpuMicro.allOps 10000)
  IO.println s!"tests: {if fails == 0 then "PASS" else s!"{fails} failing suite(s)"}"
  return fails
