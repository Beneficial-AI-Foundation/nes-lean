import Nes.Cpu.Core
import Test.Harte

/-!
# Cycle-exact interrupt tests for `Nes.Cpu.Core`

Hand-assembled snippets in flat memory, driven one cycle at a time with a per-cycle
interrupt-line schedule (cycle numbers are 1-based from the first cycle run). Vectors:
NMI → $9000, RESET → $8000, IRQ/BRK → $A000; both handlers are NOP sleds. Also checks that
with all lines idle `Core` reproduces `MicroState.runInstrTrace` on the Harte fast subset.
-/

namespace Test.Interrupts

open Nes Nes.Cpu Test.Harte

private def L (nmi irq : Bool) (reset := false) : IntLines := { nmi, irq, reset }

/-- Memory: `prog` at $8000, NOP sleds at $9000/$A000, vectors set. -/
private def mkMem (prog : List UInt8) : Nes.Cpu.Mem := Id.run do
  let mut m : Nes.Cpu.Mem := Vector.replicate 65536 0
  for i in [0:0x100] do
    m := m.write (0x9000 + i.toUInt16) 0xEA
    m := m.write (0xA000 + i.toUInt16) 0xEA
  for (b, i) in prog.zipIdx do
    m := m.write (0x8000 + i.toUInt16) b
  m := m.write 0xFFFA 0x00 |>.write 0xFFFB 0x90
  m := m.write 0xFFFC 0x00 |>.write 0xFFFD 0x80
  m := m.write 0xFFFE 0x00 |>.write 0xFFFF 0xA0
  return m

/-- CPU at $8000 with status `p`, SP = $FD. -/
private def start (p : UInt8) : Core := Core.ofState { State.init with pc := 0x8000, p }

/-- Run `n` cycles; `sched i` = lines in (1-based) cycle `i`. -/
private def sim (c : Core) (m : Nes.Cpu.Mem) (n : Nat) (sched : Nat → IntLines) :
    Core × Nes.Cpu.Mem × Array BusEvent := Id.run do
  let mut c := c
  let mut m := m
  let mut tr := #[]
  for i in [1:n+1] do
    let (c', m', e) := c.cycleEv (sched i) m
    c := c'; m := m'; tr := tr.push e
  return (c, m, tr)

/-- 1-based cycle numbers of reads of `a`. -/
private def readsOf (tr : Array BusEvent) (a : UInt16) : List Nat :=
  (tr.toList.zipIdx.filter fun (e, _) => e.addr == a && !e.write).map (·.2 + 1)

private def writes (tr : Array BusEvent) : List (UInt16 × UInt8) :=
  (tr.toList.filter (·.write)).map fun e => (e.addr, e.val)

private def ev (a : UInt16) (v : UInt8) (w := false) : BusEvent := ⟨a, v, w⟩

structure Acc where
  fails : Nat := 0
  total : Nat := 0
  msgs : Array String := #[]

private def check (acc : Acc) (name : String) (ok : Bool) (info : String := "") : Acc :=
  if ok then { acc with total := acc.total + 1 }
  else { acc with total := acc.total + 1, fails := acc.fails + 1,
                  msgs := acc.msgs.push s!"FAIL {name} {info}" }

/-- The hand-written scenarios. -/
def scenarios : Acc := Id.run do
  let mut acc : Acc := {}
  -- (1) IRQ with I = 0 (held asserted): LDA #$01 runs, then the 7-cycle sequence.
  do
    let m := mkMem [0xA9, 0x01, 0xEA, 0xEA]
    let (c, m', tr) := sim (start 0x20) m 9 fun _ => L false true
    let want := #[ev 0x8000 0xA9, ev 0x8001 0x01, ev 0x8002 0xEA, ev 0x8002 0xEA,
      ev 0x01FD 0x80 true, ev 0x01FC 0x02 true, ev 0x01FB 0x20 true,
      ev 0xFFFE 0x00, ev 0xFFFF 0xA0]
    acc := check acc "irq-trace" (tr == want) s!"{repr tr}"
    acc := check acc "irq-state" (c.ms.cpu.pc == 0xA000 && c.ms.cpu.i && c.ms.cpu.sp == 0xFA
      && c.ms.pos == 0)
    -- I is now set: the still-asserted line is never taken again.
    let (_, _, tr2) := sim c m' 60 fun _ => L false true
    acc := check acc "irq-masked-after" (readsOf tr2 0xFFFE).isEmpty
  -- (2) IRQ with I = 1 never taken.
  do
    let (c, _, tr) := sim (start 0x24) (mkMem (List.replicate 64 0xEA)) 100 fun _ => L false true
    acc := check acc "irq-I1" ((readsOf tr 0xFFFE).isEmpty && c.ms.cpu.pc == 0x8032)
  -- (3) NMI edge (held asserted from cycle 1): taken once, via $FFFA, B = 0.
  do
    let (c, _, tr) := sim (start 0x24) (mkMem (List.replicate 64 0xEA)) 59 fun _ => L true false
    acc := check acc "nmi-vector" (readsOf tr 0xFFFA == [8]) s!"{readsOf tr 0xFFFA}"
    acc := check acc "nmi-push" (writes tr == [(0x1FD, 0x80), (0x1FC, 0x01), (0x1FB, 0x24)])
      s!"{writes tr}"
    acc := check acc "nmi-once" ((readsOf tr 0xFFFE).isEmpty && c.ms.cpu.pc == 0x9000 + 25)
    -- Released then re-asserted: a second edge, a second NMI.
    let (_, _, tr2) := sim (start 0x24) (mkMem (List.replicate 64 0xEA)) 60
      fun i => L (i < 20 || i ≥ 30) false
    acc := check acc "nmi-second-edge" ((readsOf tr2 0xFFFA).length == 2)
  -- (4a) CLI with IRQ pending: one more instruction (NOP at $8001) runs first.
  do
    let (_, _, tr) := sim (start 0x24) (mkMem ([0x58] ++ List.replicate 16 0xEA)) 30
      fun _ => L false true
    acc := check acc "cli-delay" (readsOf tr 0xFFFE == [10]
      && writes tr == [(0x1FD, 0x80), (0x1FC, 0x02), (0x1FB, 0x20)]) s!"{writes tr}"
  -- (4b) SEI with IRQ pending: taken once right after SEI (pushed P has I set).
  do
    let (_, _, tr) := sim (start 0x20) (mkMem ([0x78] ++ List.replicate 16 0xEA)) 60
      fun _ => L false true
    acc := check acc "sei-taken-once" (readsOf tr 0xFFFE == [8]
      && writes tr == [(0x1FD, 0x80), (0x1FC, 0x01), (0x1FB, 0x24)]) s!"{writes tr}"
  -- (5) BRK hijacked by an NMI edge in cycle 3: $FFFA, pushed B = 1, NMI consumed.
  do
    let (c, _, tr) := sim (start 0x20) (mkMem [0x00, 0xFF]) 7 fun i => L (i ≥ 3) false
    acc := check acc "brk-hijack" (readsOf tr 0xFFFA == [6] && (readsOf tr 0xFFFE).isEmpty
      && writes tr == [(0x1FD, 0x80), (0x1FC, 0x02), (0x1FB, 0x30)] && c.ms.cpu.pc == 0x9000)
      s!"{writes tr} {readsOf tr 0xFFFA}"
    let (_, _, tr2) := sim (start 0x20) (mkMem [0x00, 0xFF]) 60 fun i => L (i ≥ 3) false
    acc := check acc "brk-hijack-consumed" ((readsOf tr2 0xFFFA) == [6])
    -- Edge in cycle 5 is too late: BRK uses $FFFE, NMI follows after one handler NOP.
    let (_, _, tr3) := sim (start 0x20) (mkMem [0x00, 0xFF]) 20 fun i => L (i ≥ 5) false
    acc := check acc "brk-late-nmi" (readsOf tr3 0xFFFE == [6] && readsOf tr3 0xFFFA == [15])
      s!"{readsOf tr3 0xFFFE} {readsOf tr3 0xFFFA}"
  -- (6) RESET: power-on and warm reset — no writes, PC from $FFFC, I set.
  do
    let (c, _, tr) := sim (Core.powerOn State.init) (mkMem [0xEA]) 7 fun _ => L false false
    acc := check acc "poweron" ((writes tr).isEmpty && readsOf tr 0xFFFC == [6]
      && c.ms.cpu.pc == 0x8000 && c.ms.cpu.i && c.ms.cpu.sp == 0xFD) s!"{repr c.ms.cpu}"
    let (c2, _, tr2) := sim (start 0x20) (mkMem (List.replicate 8 0xEA)) 9
      fun i => L false false (i == 2)
    acc := check acc "warm-reset" ((writes tr2).isEmpty && readsOf tr2 0xFFFC == [8]
      && c2.ms.cpu.pc == 0x8000 && c2.ms.cpu.i && c2.ms.cpu.sp == 0xFA) s!"{repr c2.ms.cpu}"
  -- (7) Taken branch without page cross polls only in cycle 1: an IRQ arriving in its cycle 2
  --     is serviced one instruction later. Control: a 3-cycle LDA zp is polled in cycle 2.
  do
    let (_, _, tr) := sim (start 0x20) (mkMem [0xD0, 0x00, 0xEA, 0xEA, 0xEA]) 15
      fun i => L false (i ≥ 2)
    acc := check acc "branch-delay" (readsOf tr 0xFFFE == [11]
      && writes tr == [(0x1FD, 0x80), (0x1FC, 0x03), (0x1FB, 0x20)]) s!"{writes tr}"
    let (_, _, tr2) := sim (start 0x20) (mkMem [0xA5, 0x00, 0xEA, 0xEA, 0xEA]) 15
      fun i => L false (i ≥ 2)
    acc := check acc "lda-zp-no-delay" (readsOf tr2 0xFFFE == [9]
      && writes tr2 == [(0x1FD, 0x80), (0x1FC, 0x02), (0x1FB, 0x22)]) s!"{writes tr2}"
    -- Taken branch crossing a page: also polled in cycle 3, so no delay.
    let c0 := Core.ofState { State.init with pc := 0x80FD, p := 0x20 }
    let (_, _, tr3) := sim c0
      (mkMem (List.replicate 0xFD 0xEA ++ [0xD0, 0x10] ++ List.replicate 64 0xEA)) 15
      fun i => L false (i ≥ 3)
    acc := check acc "branch-cross-no-delay" (readsOf tr3 0xFFFE == [10]
      && writes tr3 == [(0x1FD, 0x81), (0x1FC, 0x0F), (0x1FB, 0x20)]) s!"{writes tr3}"
  return acc

/-- With idle lines, `Core` runs one instruction exactly like `MicroState.runInstrTrace`. -/
def idleAgrees (c : Case) : Bool :=
  let r := c.initial.regs
  let s : State := { a := r.a, x := r.x, y := r.y, sp := r.s, pc := r.pc, p := r.p, halted := false }
  let m := c.initial.toMem
  let (ms, mm, tr) := (MicroState.ofState s).runInstrTrace MicroState.maxCycles m
  let rec go : Nat → Core → Nes.Cpu.Mem → Array BusEvent → Core × Nes.Cpu.Mem × Array BusEvent
    | 0, k, m, acc => (k, m, acc)
    | n + 1, k, m, acc =>
      let (k', m', e) := k.cycleEv Core.idle m
      if k'.ms.pos == 0 then (k', m', acc.push e) else go n k' m' (acc.push e)
  let (k, km, ktr) := go MicroState.maxCycles (Core.ofState s) m #[]
  k.ms.cpu == ms.cpu && km == mm && ktr == tr && k.ms.pos == 0 && !k.ms.intPending

def run : IO UInt32 := do
  let acc := scenarios
  for msg in acc.msgs do IO.println msg
  let mut cases := 0
  let mut hfails := 0
  if ← dataDir.isDir then
    for op in fastSubset do
      let cs ← loadFile (dataDir / s!"{op}.json")
      for c in cs.extract 0 100 do
        cases := cases + 1
        unless idleAgrees c do
          hfails := hfails + 1
          if hfails ≤ 5 then IO.println s!"FAIL idle core/micro {op} {c.name}"
  IO.println s!"interrupts: {acc.total - acc.fails}/{acc.total} scenario checks; idle Core = Micro on {cases - hfails}/{cases} Harte cases"
  return (if acc.fails == 0 && hfails == 0 then 0 else 1)

end Test.Interrupts
