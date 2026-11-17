import Lean

/-!
# SingleStepTests `nes6502` harness

Loader and final-state diff for Tom Harte's SingleStepTests `nes6502` suite
(`testdata/ProcessorTests/nes6502/v1/XX.json`, 10 000 cases per opcode, MIT; fetched by
`scripts/fetch-testdata.sh`). Each case gives an initial CPU/RAM state, the expected final
state after one instruction, and the per-cycle bus trace.

The harness is written against an abstract `StepFn` over a flat 64 KiB memory (the
`nes6502` set assumes no mirroring); the integrator adapts `Isa.step` to it. Only the RAM
addresses listed in `final.ram` are compared (the Harte convention). The bus trace is
parsed (`Case.cycles`) but not diffed here.
-/

namespace Test.Harte

open Lean

structure CpuRegs where
  pc : UInt16
  s : UInt8
  a : UInt8
  x : UInt8
  y : UInt8
  p : UInt8
  deriving Repr, BEq, Inhabited

structure Snapshot where
  regs : CpuRegs
  ram : Array (UInt16 × UInt8)
  deriving Repr, Inhabited

structure Cycle where
  addr : UInt16
  val : UInt8
  write : Bool
  deriving Repr, BEq, Inhabited

structure Case where
  name : String
  initial : Snapshot
  final : Snapshot
  cycles : Array Cycle
  deriving Repr, Inhabited

/-- Flat 64 KiB memory (PLAN §10: `Vector UInt8 n` is the one memory representation). -/
abbrev Mem := Vector UInt8 65536

/-- One instruction of the model under test. -/
abbrev StepFn := CpuRegs → Mem → CpuRegs × Mem

/-! ## JSON parsing -/

private def natIn (j : Json) (bound : Nat) (what : String) : Except String Nat := do
  let n ← j.getNat?
  if n < bound then pure n else throw s!"{what}: {n} out of range"

private def u8 (j : Json) : Except String UInt8 := (·.toUInt8) <$> natIn j 256 "byte"
private def u16 (j : Json) : Except String UInt16 := (·.toUInt16) <$> natIn j 65536 "address"

private def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field '{k}'"

private def parseSnapshot (j : Json) : Except String Snapshot := do
  let regs : CpuRegs := {
    pc := ← u16 (← field j "pc"), s := ← u8 (← field j "s"), a := ← u8 (← field j "a"),
    x := ← u8 (← field j "x"), y := ← u8 (← field j "y"), p := ← u8 (← field j "p") }
  let ram ← (← (← field j "ram").getArr?).mapM fun e => do
    let pair ← e.getArr?
    unless pair.size == 2 do throw "ram entry is not [addr, val]"
    pure ((← u16 pair[0]!), (← u8 pair[1]!))
  pure { regs, ram }

private def parseCycle (j : Json) : Except String Cycle := do
  let t ← j.getArr?
  unless t.size == 3 do throw "cycle entry is not [addr, val, kind]"
  let kind ← t[2]!.getStr?
  let write ← match kind with
    | "read" => pure false
    | "write" => pure true
    | k => throw s!"unknown cycle kind '{k}'"
  pure { addr := ← u16 t[0]!, val := ← u8 t[1]!, write }

private def parseCase (j : Json) : Except String Case := do
  let name ← (← field j "name").getStr?
  let ctx (e : String) := s!"case '{name}': {e}"
  let initial ← (parseSnapshot (← field j "initial")).mapError ctx
  let final ← (parseSnapshot (← field j "final")).mapError ctx
  let cycles ← ((← (← field j "cycles").getArr?).mapM parseCycle).mapError ctx
  pure { name, initial, final, cycles }

instance : FromJson Snapshot := ⟨parseSnapshot⟩
instance : FromJson Cycle := ⟨parseCycle⟩
instance : FromJson Case := ⟨parseCase⟩

/-- Load every case of one `nes6502` JSON file. -/
def loadFile (path : System.FilePath) : IO (Array Case) := do
  let text ← IO.FS.readFile path
  let j ← IO.ofExcept ((Json.parse text).mapError (s!"{path}: " ++ ·))
  let arr ← IO.ofExcept ((j.getArr?).mapError (s!"{path}: " ++ ·))
  IO.ofExcept ((arr.mapM parseCase).mapError (s!"{path}: " ++ ·))

/-! ## Running and diffing -/

/-- Zero-filled 64 KiB with the snapshot's RAM cells written. -/
def Snapshot.toMem (s : Snapshot) : Mem :=
  s.ram.foldl (fun m (a, v) => m.set a.toNat v (UInt16.toNat_lt a)) (Vector.replicate 65536 0)

private def hex8 (v : UInt8) : String :=
  let d := Nat.toDigits 16 v.toNat
  String.ofList (List.replicate (2 - d.length) '0' ++ d)

private def hex16 (v : UInt16) : String :=
  let d := Nat.toDigits 16 v.toNat
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- Diff of `got` against `exp`: registers, then the RAM cells listed in `exp.ram`. -/
def diff (exp : Snapshot) (got : CpuRegs) (mem : Mem) : Array String := Id.run do
  let mut out := #[]
  let r := exp.regs
  if got.pc != r.pc then out := out.push s!"pc={hex16 got.pc} want {hex16 r.pc}"
  for (n, g, w) in [("s", got.s, r.s), ("a", got.a, r.a), ("x", got.x, r.x),
                    ("y", got.y, r.y), ("p", got.p, r.p)] do
    if g != w then out := out.push s!"{n}={hex8 g} want {hex8 w}"
  for (a, w) in exp.ram do
    let g := mem.get ⟨a.toNat, UInt16.toNat_lt a⟩
    if g != w then out := out.push s!"[{hex16 a}]={hex8 g} want {hex8 w}"
  return out

/-- Run one case; `none` on pass, otherwise a human-readable diff (first few mismatches). -/
def runCase (step : StepFn) (c : Case) : Option String :=
  let (regs, mem) := step c.initial.regs c.initial.toMem
  let d := diff c.final regs mem
  if d.isEmpty then none
  else
    let shown := d.extract 0 6
    let more := if d.size > 6 then s!" (+{d.size - 6} more)" else ""
    some s!"{c.name}: {", ".intercalate shown.toList}{more}"

/-- Run the first `limit` cases of a file: `(passed, failed, first few diffs)`. -/
def runFile (step : StepFn) (path : System.FilePath) (limit : Nat) :
    IO (Nat × Nat × Array String) := do
  let cases ← loadFile path
  let mut pass := 0
  let mut fail := 0
  let mut diffs := #[]
  for c in cases.extract 0 limit do
    match runCase step c with
    | none => pass := pass + 1
    | some d =>
      fail := fail + 1
      if diffs.size < 3 then diffs := diffs.push d
  return (pass, fail, diffs)

/-! ## Fast subset for `lake test` -/

def dataDir : System.FilePath := "testdata/ProcessorTests/nes6502/v1"

/-- One opcode per instruction class / addressing-mode family (official and unofficial). -/
def fastSubset : List String :=
  [ "a9", "a5", "b5", "ad", "bd", "b9", "a1", "b1", -- LDA in every mode
    "69", "e9", "c9", "e0", "c0", "29", "09", "49", -- ALU, compares
    "0a", "4a", "2a", "6a", "06", "7e", "24", "2c", -- shifts/rotates, BIT
    "e6", "c6", "fe", "e8", "c8", "ca", "88",       -- inc/dec
    "85", "95", "9d", "91", "86", "84",             -- stores
    "4c", "6c", "20", "60", "00", "40",             -- jumps, BRK/RTI
    "f0", "d0", "10", "30", "90", "b0", "50", "70", -- branches
    "48", "68", "08", "28",                         -- stack
    "aa", "a8", "8a", "98", "ba", "9a",             -- transfers
    "18", "38", "58", "78", "b8", "d8", "f8", "ea", -- flags, NOP
    "a7", "87", "c7", "e7", "07", "27", "47", "67", -- unofficial RMW/LAX/SAX
    "0b", "4b", "6b", "cb", "eb", "bb", "04", "1a" ]

/-- Run `casesPerFile` cases of every `fastSubset` file; returns the number of failures.
Prints one line per file; skips (returns 0) if the test data is absent. -/
def runFast (step : StepFn) (casesPerFile : Nat := 100) : IO UInt32 := do
  unless ← dataDir.isDir do
    IO.println s!"harte: {dataDir} absent (run scripts/fetch-testdata.sh); skipped"
    return 0
  let mut failures : UInt32 := 0
  for op in fastSubset do
    let path := dataDir / s!"{op}.json"
    unless ← path.pathExists do
      IO.println s!"harte {op}: missing file"
      failures := failures + 1
      continue
    let (p, f, ds) ← runFile step path casesPerFile
    IO.println s!"harte {op}: {p}/{p + f} passed"
    for d in ds do IO.println s!"  {d}"
    failures := failures + f.toUInt32
  return failures

/-! ## Self-test of the harness itself -/

/-- Identity step must fail on `a9.json`; a step that cheats by looking up the expected
final state must pass. -/
def selfTest : IO Bool := do
  let path := dataDir / "a9.json"
  let cases ← loadFile path
  let idFails := cases.all fun c => (runCase (fun r m => (r, m)) c).isSome
  let cheat (c : Case) : StepFn := fun _ m =>
    (c.final.regs, c.final.ram.foldl (fun m (a, v) => m.set a.toNat v (UInt16.toNat_lt a)) m)
  let cheatPasses := cases.all fun c => (runCase (cheat c) c).isNone
  IO.println s!"harte selfTest: {cases.size} cases, identity all-fail={idFails}, cheat all-pass={cheatPasses}"
  if let some d := cases[0]? >>= runCase (fun r m => (r, m)) then IO.println s!"  e.g. {d}"
  return idFails && cheatPasses

end Test.Harte
