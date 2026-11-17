import Nes

open Nes.Cpu

/-! ## `--bench [N]`: instruction-level CPU throughput on the native binary (PLAN.md §4)

A self-contained 6502 program at `$8000` (no ROM), run for `N` instructions:

```
8000  A2 00     LDX #$00
8002  A0 10     LDY #$10
8004  BD 00 02  loop: LDA $0200,X   ; abs,X read (page cross never: X < $100, base $0200)
8007  69 03           ADC #$03
8009  9D 00 03        STA $0300,X   ; abs,X store
800C  2A              ROL A
800D  C9 80           CMP #$80
800F  20 20 80        JSR $8020
8012  E8              INX
8013  D0 EF           BNE loop
8015  88              DEY
8016  D0 EC           BNE loop
8018  4C 00 80        JMP $8000
8020  A5 10     sub:  LDA $10       ; zero-page read
8022  CA              DEX
8023  E8              INX
8024  60              RTS
```
-/

/-- The benchmark program, as `(address, bytes)` chunks. -/
def benchProgram : List (UInt16 × List UInt8) :=
  [(0x8000, [0xA2, 0x00, 0xA0, 0x10,
             0xBD, 0x00, 0x02, 0x69, 0x03, 0x9D, 0x00, 0x03, 0x2A, 0xC9, 0x80,
             0x20, 0x20, 0x80, 0xE8, 0xD0, 0xEF, 0x88, 0xD0, 0xEC, 0x4C, 0x00, 0x80]),
   (0x8020, [0xA5, 0x10, 0xCA, 0xE8, 0x60])]

/-- Flat 64 KiB memory with the benchmark program loaded. -/
def benchMem : Mem :=
  benchProgram.foldl (init := Vector.replicate 65536 0) fun m (addr, bytes) =>
    (bytes.foldl (init := (m, addr)) fun (m, a) b => (m.write a b, a + 1)).1

/-- Run `n` instructions, threading the memory linearly; returns final state, memory, cycles. -/
def benchRun : Nat → State → Mem → UInt64 → State × Mem × UInt64
  | 0, s, m, cyc => (s, m, cyc)
  | n + 1, s, m, cyc =>
    let (s', m', c) := step s m
    benchRun n s' m' (cyc + c.toUInt64)

def bench (n : Nat) : IO UInt32 := do
  let s0 : State := { State.init with pc := 0x8000 }
  let t0 ← IO.monoNanosNow
  let (s, m, cyc) := benchRun n s0 benchMem 0
  -- force the result before stopping the clock
  let chk := s.a.toNat + s.x.toNat + s.pc.toNat + (m.read 0x0300).toNat
  if chk == 0xFFFFFFFF then IO.println "unreachable"
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1.0e9
  let ips := n.toFloat / secs
  let cps := cyc.toFloat / secs
  IO.println s!"bench: {n} instr, {cyc} cycles in {secs} s"
  IO.println s!"bench: {ips / 1.0e6} M instr/s, {cps / 1.0e6} M cycles/s, \
    {cps / 1789773.0}x NTSC realtime (final pc={s.pc} a={s.a} chk={chk})"
  return 0

/-! ## `run`: headless ROM runner (PLAN.md §3.5, §5.6) -/

open Nes.Frontend

def usage : String :=
"usage:
  nes run <rom.nes> [--frames N] [--png out.png] [--ppm out.ppm] [--hash] [--every K]
                    [--input script]
  nes --bench [N]

run: power on with <rom.nes> (iNES), run N frames (default 60; a frame ends at vblank start),
  then write the final frame as PNG/PPM and print its FNV-1a 64 frame hash (the golden-hash
  definition, over the 256x240 palette-index bytes) and the frames/s achieved.
  --every K   write/print every K-th frame instead: out.png -> out-000120.png, ...
  --hash      print the hash of every frame (default: final frame, plus every K-th with --every)
  --input F   controller-1 script: one `frame buttons` pair per line; the buttons hold from
              that frame (0-based) until the next line. buttons = letters from `ABsSUDLR`
              (s = Select, S = Start), `-` = none, or a hex byte (`0x08`, `$08`, or bare
              `08` when not all letters; bit 0..7 = A B Select Start Up Down Left Right).
              `#` starts a comment.
              Example:  `0 -` / `30 S` / `32 -` / `90 AR`
--bench [N]: CPU-only instruction throughput benchmark (default 50 000 000 instructions)."

/-- Parse a button field: hex (`08`, `0x08`, `$08`) or letters `ABsSUDLR`, `-` for none. -/
def parseButtons (s : String) : Option UInt8 :=
  let hexOf (t : String) : Option UInt8 :=
    if t.isEmpty || t.length > 2 then none else
    t.foldl (fun acc c => acc.bind fun a =>
      let d := if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
        else none
      d.map fun d => a * 16 + d.toUInt8) (some 0)
  if s == "-" then some 0
  else if s.startsWith "0x" then hexOf (s.drop 2).toString
  else if s.startsWith "$" then hexOf (s.drop 1).toString
  else if s.all (fun c => "ABsSUDLR".toList.contains c) then
    some <| s.foldl (fun acc c => acc ||| match c with
      | 'A' => 0x01 | 'B' => 0x02 | 's' => 0x04 | 'S' => 0x08
      | 'U' => 0x10 | 'D' => 0x20 | 'L' => 0x40 | _ => 0x80) 0
  else hexOf s

/-- Parse an input script into `(frame, buttons)` events, sorted by frame. -/
def parseScript (txt : String) : Except String (Array (Nat × UInt8)) := do
  let mut out := #[]
  let mut ln := 0
  for line in txt.splitOn "\n" do
    ln := ln + 1
    let body := (line.splitOn "#").headD ""
    let ws := ((body.replace "\t" " ").replace "\r" " ").splitOn " " |>.filter (· ≠ "")
    match ws with
    | [] => pure ()
    | [f, b] =>
      match f.toNat?, parseButtons b with
      | some f, some b => out := out.push (f, b)
      | _, _ => throw s!"input script line {ln}: bad `{body}`"
    | _ => throw s!"input script line {ln}: expected `frame buttons`, got `{body}`"
  return out.qsort (fun a b => a.1 < b.1)

structure RunOpts where
  rom : String
  frames : Nat := 60
  png : Option String := none
  ppm : Option String := none
  hash : Bool := false
  every : Option Nat := none
  input : Option String := none

def parseRunOpts : List String → RunOpts → Except String RunOpts
  | [], o => .ok o
  | "--frames" :: n :: r, o => match n.toNat? with
    | some k => parseRunOpts r { o with frames := k }
    | none => .error s!"--frames: bad count {n}"
  | "--every" :: n :: r, o => match n.toNat? with
    | some k => if k == 0 then .error "--every: K must be > 0"
                else parseRunOpts r { o with every := some k }
    | none => .error s!"--every: bad count {n}"
  | "--png" :: p :: r, o => parseRunOpts r { o with png := some p }
  | "--ppm" :: p :: r, o => parseRunOpts r { o with ppm := some p }
  | "--input" :: p :: r, o => parseRunOpts r { o with input := some p }
  | "--hash" :: r, o => parseRunOpts r { o with hash := true }
  | a :: _, _ => .error s!"run: unexpected argument `{a}`"

/-- `out.png` → `out-000120.png`. -/
def numbered (path : String) (k : Nat) : String :=
  let p : System.FilePath := path
  let num := toString k
  let pad := "".pushn '0' (6 - num.length) ++ num
  match p.extension with
  | some e => (p.withExtension "").toString ++ s!"-{pad}." ++ e
  | none => path ++ s!"-{pad}"

def writeFrame (o : RunOpts) (n : Nes.System.Nes) (k : Option Nat) : IO Unit := do
  if o.png.isNone && o.ppm.isNone then return
  let rgb := toRgb n.ppu.frame n.ppu.emphasis
  let name (p : String) := match k with | some k => numbered p k | none => p
  if let some p := o.png then IO.FS.writeBinFile (name p) (png rgb 256 240)
  if let some p := o.ppm then IO.FS.writeBinFile (name p) (ppm rgb 256 240)

def runRom (o : RunOpts) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile o.rom
  let cart ← match Nes.Cart.Cart.load bytes with
    | .ok c => pure c
    | .error e => IO.eprintln s!"run: {o.rom}: {e}"; return 1
  let script ← match o.input with
    | none => pure #[]
    | some p => match parseScript (← IO.FS.readFile p) with
      | .ok s => pure s
      | .error e => IO.eprintln s!"run: {e}"; return 2
  let mut n := Nes.System.Nes.powerOn cart
  let mut si := 0
  let mut buttons : UInt8 := 0
  let mut busy : Nat := 0  -- nanoseconds spent emulating (excludes encoding/IO)
  for f in [0:o.frames] do
    while h : si < script.size do
      if script[si].1 ≤ f then buttons := script[si].2; si := si + 1 else break
    let t0 ← IO.monoNanosNow
    n := { n with pads := n.pads.setButtons buttons 0 }
    n := n.runFrame
    -- force the frame before stopping the clock
    let chk := n.ppu.frame.size + n.clock.toNat
    if chk == 0 then IO.println "unreachable"
    busy := busy + ((← IO.monoNanosNow) - t0)
    let k := f + 1
    let isLast := k == o.frames
    let sel := match o.every with | some e => k % e == 0 | none => isLast
    if sel && o.every.isSome then writeFrame o n (some k)
    if isLast && o.every.isNone then writeFrame o n none
    if (o.hash && o.every.isNone) || sel || isLast then
      IO.println s!"frame {k}: {hex64 (frameHash n.ppu.frame)}"
  let secs := busy.toFloat / 1.0e9
  IO.println s!"run: {o.frames} frames, {n.clock} CPU cycles in {secs} s = \
    {o.frames.toFloat / secs} frames/s ({o.frames.toFloat / secs / 60.0988}x NTSC realtime)"
  return 0

/-- Headless CLI entry point (PLAN.md §5.6). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bench"] => bench 50_000_000
  | ["--bench", n] =>
    match n.toNat? with
    | some k => bench k
    | none => IO.eprintln s!"--bench: bad count {n}"; return 2
  | "run" :: rom :: rest =>
    match parseRunOpts rest { rom } with
    | .ok o => runRom o
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  | ["--help"] | ["-h"] | ["help"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
