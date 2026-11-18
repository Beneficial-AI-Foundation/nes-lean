import Nes.Cpu.Micro
import Nes.Cpu.Isa
import Test.Harte

/-!
# Per-cycle SingleStepTests runner for `Nes.Cpu.Micro`

For each case: run the micro-op machine from the initial state to the next instruction
boundary against flat memory and check
1. the final registers and listed RAM cells against the case,
2. the emitted bus trace against the recorded `cycles` exactly (address, value, read/write,
   including dummy reads and the RMW double write),
3. agreement with `Isa.step` (registers, memory, cycle count) — the executable side of
   T-REF-1.
-/

namespace Test.CpuMicro

open Nes Nes.Cpu Test.Harte

private def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList ((List.replicate (2 - d.length) '0' ++ d).map Char.toLower)

private def toRegs (s : State) : CpuRegs :=
  { pc := s.pc, s := s.sp, a := s.a, x := s.x, y := s.y, p := s.p }

/-- `none` if the case passes, else a one-line diagnosis. -/
def checkCase (c : Case) : Option String :=
  let r := c.initial.regs
  let s : State := { a := r.a, x := r.x, y := r.y, sp := r.s, pc := r.pc, p := r.p, halted := false }
  let m := c.initial.toMem
  let (ms, m', tr) := (MicroState.ofState s).runInstrTrace MicroState.maxCycles m
  let (si, mi, ni) := step s m
  let d := diff c.final (toRegs ms.cpu) m'
  let traceOk := tr.size == c.cycles.size &&
    (tr.zip c.cycles).all fun (e, x) => e.addr == x.addr && e.val == x.val && e.write == x.write
  let isaOk := ms.cpu == si && m' == mi && ni == tr.size && ms.pos == 0
  if d.isEmpty && traceOk && isaOk then none
  else some s!"{c.name}: diff={d} trace={traceOk} isa={isaOk}"

/-- Run `limit` cases of each opcode file in `ops`. Returns 0 on success, 1 on failure. -/
def sweep (label : String) (ops : List String) (limit : Nat) : IO UInt32 := do
  unless ← dataDir.pathExists do
    IO.println s!"{label}: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut okOps := 0
  let mut cases := 0
  let mut fails := 0
  for op in ops do
    let cs ← loadFile (dataDir / s!"{op}.json")
    let mut opFails := 0
    for c in cs.extract 0 limit do
      cases := cases + 1
      if let some msg := checkCase c then
        opFails := opFails + 1
        if fails + opFails ≤ 20 then IO.println s!"{op} {msg}"
    if opFails == 0 then okOps := okOps + 1
    fails := fails + opFails
  IO.println s!"{label}: {okOps}/{ops.length} opcodes; {cases - fails}/{cases} cases (state + bus trace + Isa agreement)"
  return (if fails == 0 then 0 else 1)

/-- All 256 opcode files. -/
def allOps : List String := (List.range 256).map hex2

end Test.CpuMicro
