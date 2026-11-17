/-!
# nestest: golden-log CPU test

`nestest.nes` run in *automated mode* (start at `$C000` instead of the reset vector, no
PPU/input needed) exercises the official and unofficial 6502 instruction set. Its
golden `nestest.log` (Nintendulator format) records the CPU state *before* each
instruction, e.g.

```
C000  4C F5 C5  JMP $C5F5                       A:00 X:00 Y:00 P:24 SP:FD PPU:  0, 21 CYC:7
```

We step a CPU (abstracted as `StepFn`, so this harness does not depend on the CPU model)
and diff each produced line against the golden one, stopping at the first mismatch.

Compared columns: PC, raw instruction bytes, A, X, Y, P, SP, CYC.
**Not compared**: the disassembly text (including unofficial-opcode `*` markers and memory
annotations such as `= 00` / `@ 0300`) and the `PPU:` columns — we have no PPU until M3.

nestest also reports result codes in RAM: `$02` (official opcodes) and `$03` (unofficial
opcodes); `00` means all passed. The log diff is strictly stronger, so we do not check them.

This file holds test-only scaffolding (a tiny iNES loader); the real `Cart/Ines.lean`
arrives in M3.
-/

namespace Test.Nestest

/-! ## Trace lines -/

/-- One line of the golden log (CPU state before executing the instruction at `pc`). -/
structure TraceLine where
  pc : UInt16
  bytes : Array UInt8
  a : UInt8
  x : UInt8
  y : UInt8
  p : UInt8
  sp : UInt8
  cyc : Nat
  /-- PPU scanline / dot, parsed for information only (never compared). -/
  ppuLine : Nat := 0
  ppuDot : Nat := 0
  deriving Repr, Inhabited

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- Upper-case hex, zero-padded to `width` digits. -/
def hex (n width : Nat) : String :=
  (List.range width).reverse.foldl (fun s i => s.push (hexDigit (n / 16 ^ i % 16))) ""

def hex8 (b : UInt8) : String := hex b.toNat 2
def hex16 (w : UInt16) : String := hex w.toNat 4

/-- Characters `[start, start+len)` of `s`, as a `String`. -/
private def sub (s : String) (start len : Nat) : String :=
  String.ofList ((s.toList.drop start).take len)

private def trim (s : String) : String := s.trimAscii.toString

private def parseHex (s : String) : Except String Nat := do
  if s.isEmpty then throw "empty hex field"
  s.foldl (fun acc c => do
    let n ← acc
    let d ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else throw s!"bad hex digit '{c}' in \"{s}\""
    pure (n * 16 + d)) (pure 0)

private def parseDec (s : String) : Except String Nat :=
  match (trim s).toNat? with
  | some n => pure n
  | none => throw s!"bad decimal \"{s}\""

/-- Text following the first occurrence of `key` in `s`. -/
private def after (s key : String) : Except String String :=
  match s.splitOn key with
  | _ :: rest :: _ => pure rest
  | _ => throw s!"missing field {key}"

/-- A two-hex-digit register field `key` (e.g. `"A:"`). -/
private def reg (s key : String) : Except String UInt8 := do
  let n ← parseHex (sub (← after s key) 0 2)
  pure n.toUInt8

/-- Parse a golden-log line. The log is fixed-width: PC in columns 0–3, instruction bytes
in columns 6–13, disassembly from column 15, registers from column 48. -/
def parseLine (line : String) : Except String TraceLine := do
  let line := trim line
  if line.length < 48 then throw s!"line too short: \"{line}\""
  let pc ← parseHex (sub line 0 4)
  let bytes ← (sub line 6 8).splitOn " " |>.filter (· ≠ "")
    |>.mapM (fun b => return (← parseHex b).toUInt8)
  if bytes.isEmpty || bytes.length > 3 then throw s!"bad byte column: \"{line}\""
  let regs := sub line 48 line.length
  let a ← reg regs "A:"
  let x ← reg regs "X:"
  let y ← reg regs "Y:"
  let p ← reg regs "P:"
  let sp ← reg regs "SP:"
  let cyc ← parseDec (← after regs "CYC:")
  let ppu := ((← after regs "PPU:").splitOn "CYC:").headD ""
  let (ppuLine, ppuDot) ← match ppu.splitOn "," with
    | [l, d] => do pure (← parseDec l, ← parseDec d)
    | _ => throw s!"bad PPU field: \"{line}\""
  pure { pc := pc.toUInt16, bytes := bytes.toArray, a, x, y, p, sp, cyc, ppuLine, ppuDot }

/-- The compared columns only (no disassembly, no PPU), e.g.
`C000  4C F5 C5  A:00 X:00 Y:00 P:24 SP:FD CYC:7`. -/
def TraceLine.format (t : TraceLine) : String :=
  let bytes := " ".intercalate (t.bytes.toList.map hex8)
  s!"{hex16 t.pc}  {bytes}{"".pushn ' ' (8 - bytes.length)}  " ++
  s!"A:{hex8 t.a} X:{hex8 t.x} Y:{hex8 t.y} P:{hex8 t.p} SP:{hex8 t.sp} CYC:{t.cyc}"

/-! ## Test ROM loading (test-only iNES subset) -/

/-- Flat 64 KiB CPU address space (PLAN §10: `Vector UInt8 n` is the memory repr). -/
abbrev Mem := Vector UInt8 65536

/-- Load a mapper-0, one-PRG-bank iNES image: 16 KiB PRG mirrored at `$8000` and `$C000`,
everything else zero. -/
def loadNrom128 (rom : ByteArray) : Except String Mem := do
  if rom.size < 16 || rom.get! 0 != 0x4E || rom.get! 1 != 0x45 || rom.get! 2 != 0x53
      || rom.get! 3 != 0x1A then
    throw "not an iNES file"
  if rom.get! 4 != 1 then throw s!"expected 1 PRG bank, got {rom.get! 4}"
  let mapper := (rom.get! 6 >>> 4) ||| (rom.get! 7 &&& 0xF0)
  if mapper != 0 then throw s!"expected mapper 0, got {mapper}"
  let trainer := if rom.get! 6 &&& 0x04 != 0 then 512 else 0
  let base := 16 + trainer
  if rom.size < base + 0x4000 then throw "truncated PRG ROM"
  pure <| Vector.ofFn fun i =>
    if i.val ≥ 0x8000 then rom.get! (base + (i.val - 0x8000) % 0x4000) else 0

/-! ## Runner -/

/-- CPU registers plus the running cycle count. -/
structure Regs where
  pc : UInt16
  a : UInt8
  x : UInt8
  y : UInt8
  p : UInt8
  sp : UInt8
  cyc : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Execute one instruction (must update `cyc`). -/
abbrev StepFn := Regs → Mem → Regs × Mem

/-- Automated-mode initial state (the golden log's first line). -/
def initRegs : Regs := { pc := 0xC000, a := 0, x := 0, y := 0, p := 0x24, sp := 0xFD, cyc := 7 }

/-- The trace line our state produces. We have no decoder dependency here, so the
instruction length is taken from the golden line (`len`); the bytes are read from `mem`,
so a wrong PC or corrupted code still shows up as a diff. -/
def traceOf (r : Regs) (mem : Mem) (len : Nat) : TraceLine :=
  { pc := r.pc, a := r.a, x := r.x, y := r.y, p := r.p, sp := r.sp, cyc := r.cyc,
    bytes := (Array.range len).map fun k => mem[(r.pc.toNat + k) % 65536]! }

/-- Step through `golden`, comparing the state before each instruction to the golden line.
Returns the number of matching lines and, on mismatch, a diff report. -/
def run (step : StepFn) (mem : Mem) (golden : Array TraceLine) :
    IO (Nat × Option String) := do
  let mut r := initRegs
  let mut m := mem
  for h : i in [0:golden.size] do
    let want := golden[i]
    let got := traceOf r m want.bytes.size
    if got.format != want.format then
      let prev := if i == 0 then "(none)" else golden[i-1]!.format
      return (i, some s!"mismatch at line {i+1}:\n  prev:     {prev}\n  expected: {want.format}\n  got:      {got.format}")
    if i + 1 < golden.size then
      (r, m) := step r m
  return (golden.size, none)

def romPath : System.FilePath := "testdata/nes-test-roms/other/nestest.nes"
def logPath : System.FilePath := "testdata/nes-test-roms/other/nestest.log"

/-- Parse the whole golden log. -/
def loadGolden : IO (Array TraceLine) := do
  let lines := (← IO.FS.lines logPath).filter (trim · ≠ "")
  lines.mapIdxM fun i l => match parseLine l with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"{logPath}:{i+1}: {e}")

/-- Run nestest; 0 on full match (or skipped when `testdata/` is absent), else 1. -/
def runNestest (step : StepFn) : IO UInt32 := do
  unless (← romPath.pathExists) && (← logPath.pathExists) do
    IO.println "nestest: SKIPPED (testdata/ absent; run scripts/fetch-testdata.sh)"
    return 0
  let mem ← match loadNrom128 (← IO.FS.readBinFile romPath) with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"{romPath}: {e}")
  let golden ← loadGolden
  let (n, diff) ← run step mem golden
  IO.println s!"nestest: {n}/{golden.size} lines match"
  match diff with
  | none => return 0
  | some d => IO.println d; return 1

end Test.Nestest
