import Nes
import Test.Axioms
import Test.CpuIsa

/-- `lake test` driver. Each suite returns the number of failures.
`lake test -- --full` also runs the full Harte sweep (2.56 M cases). -/
def main (args : List String) : IO UInt32 := do
  IO.println s!"axioms: {Test.Axioms.axiomsChecked} theorems checked"
  let mut fails : UInt32 := 0
  fails := fails + (← Test.Harte.runFast Test.CpuIsa.harteStep)
  fails := fails + (← Test.Nestest.runNestest Test.CpuIsa.nestestStep)
  if args.contains "--full" then
    fails := fails + (← Test.CpuIsa.fullSweep)
  IO.println s!"tests: {if fails == 0 then "PASS" else s!"{fails} failing suite(s)"}"
  return fails
