import Nes
import Test.Axioms

/-- `lake test` driver. Each suite returns the number of failures. -/
def main : IO UInt32 := do
  IO.println "nes-lean tests: no suites yet"
  IO.println s!"axioms: {Test.Axioms.axiomsChecked} theorems checked"
  return 0
