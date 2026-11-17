import Nes.Cpu.Isa
import Test.Harte
import Test.Nestest

/-!
# Adapters from the test harnesses to `Nes.Cpu.step`, and the full Harte sweep

`Test.Harte` and `Test.Nestest` are written against abstract step functions; this module
plugs the ISA model into both. `fullSweep` runs every case of every opcode file and also
checks the cycle count against the length of the recorded bus trace.
-/

namespace Test.CpuIsa

open Nes.Cpu

/-- Harte registers → `step`. -/
def harteStep : Test.Harte.StepFn := fun r m =>
  let s : State := { a := r.a, x := r.x, y := r.y, sp := r.s, pc := r.pc, p := r.p, halted := false }
  let (s', m', _) := step s m
  ({ pc := s'.pc, s := s'.sp, a := s'.a, x := s'.x, y := s'.y, p := s'.p }, m')

/-- nestest registers → `step`, accumulating cycles. -/
def nestestStep : Test.Nestest.StepFn := fun r m =>
  let s : State := { a := r.a, x := r.x, y := r.y, sp := r.sp, pc := r.pc, p := r.p, halted := false }
  let (s', m', c) := step s m
  ({ pc := s'.pc, sp := s'.sp, a := s'.a, x := s'.x, y := s'.y, p := s'.p, cyc := r.cyc + c }, m')

private def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList ((List.replicate (2 - d.length) '0' ++ d).map Char.toLower)

/-- Every case of all 256 opcode files: final state and cycle count. Returns failures. -/
def fullSweep (limit : Nat := 10000) : IO UInt32 := do
  unless ← Test.Harte.dataDir.pathExists do
    IO.println "harte full sweep: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut okFiles := 0
  let mut cases := 0
  let mut fails := 0
  let mut cycFails := 0
  for op in [0:256] do
    let cs ← Test.Harte.loadFile (Test.Harte.dataDir / s!"{hex2 op}.json")
    let mut fileOk := true
    for c in cs.extract 0 limit do
      cases := cases + 1
      if let some d := Test.Harte.runCase harteStep c then
        fails := fails + 1; fileOk := false
        if fails ≤ 20 then IO.println d
      let r := c.initial.regs
      let s : State := { a := r.a, x := r.x, y := r.y, sp := r.s, pc := r.pc, p := r.p, halted := false }
      let (_, _, n) := step s c.initial.toMem
      if n != c.cycles.size then
        cycFails := cycFails + 1; fileOk := false
        if cycFails ≤ 20 then IO.println s!"{c.name}: cycles {n} want {c.cycles.size}"
    if fileOk then okFiles := okFiles + 1
  IO.println s!"harte full sweep: {okFiles}/256 opcode files pass; {cases - fails}/{cases} final states; {cycFails} cycle mismatches"
  return (if fails + cycFails == 0 then 0 else 1)

end Test.CpuIsa
