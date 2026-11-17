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

/-- Headless CLI entry point (PLAN.md §5.6). Filled in from M3 onward. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bench"] => bench 50_000_000
  | ["--bench", n] =>
    match n.toNat? with
    | some k => bench k
    | none => IO.eprintln s!"--bench: bad count {n}"; return 2
  | _ =>
    IO.println s!"nes-lean: no emulator yet (args: {args})"
    return 0
