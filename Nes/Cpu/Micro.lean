import Nes.Cpu.Isa

/-!
# `Nes.Cpu.Micro` — cycle-level 2A03 microcode

Microcode as *data*: every opcode's program is an `Array MicroOp`, interpreted one cycle at a
time by a tiny machine that emits exactly one `BusOp` per cycle (dummy reads and the RMW
double write included). This is what the emulator runs; `Isa.step` is its spec (T-REF-1).

## Spec

* Cycle 1 of every instruction (opcode fetch: read `PC`, `PC += 1`) is implicit: it is the cycle
  taken at an instruction boundary (`pos = 0`). `uops op` lists cycles 2, 3, … .
* `uops op = prefixFor cls mode ++ suffix cls` with `cls = classify (decode op)`:
  `modePrefix mode` (13 shared addressing programs) computes the effective address into `addr`
  (`base` = un-indexed address, `crossed` = indexing changed the high byte); `suffix cls`
  (one program per instruction class) performs the operand access and the instruction. `JSR`
  and `JMP abs` own their operand fetches (`prefixFor` is empty for them).
* Three micro-ops are *conditional* (they are skipped without taking a cycle):
  `indexFixup` is skipped iff `(decode op).pageCross && !crossed` (reads that did not cross);
  `branchTaken` is skipped iff the branch is not taken; `branchFixup` iff not (taken and the
  target is on another page). Hence `baseCycles e = e.cycles` for all 256 opcodes (checked
  below by `decide`), and the extra cycles are exactly `Isa.extraCycles`.
* One cycle = `busOp ms` (what goes on the bus) then `complete ms v` (`v` = byte read; ignored
  for writes), which applies the micro-op and advances `pos`, skipping conditional micro-ops.
  `atBoundary ms ↔ ms.pos = 0`.
* Stack conventions match `Isa`: push writes `$0100|SP` then `SP -= 1`; pulls do a dummy read
  at `$0100|SP`, then `SP += 1` before each real pull. PHP/BRK push `P|$30`; IRQ/NMI push
  `P|$20`; PLP/RTI load `(v & $CF) | $20`.
* JAM: cycles 2 and 3 read `PC+1`; afterwards `PC` is restored, `halted` set. A halted CPU at
  a boundary spends each cycle reading `$FFFF` and stays at the boundary.
* Interrupt hook: `requestInterrupt ms vec reset` sets `intPending`; at the next boundary the
  machine runs the 7-cycle interrupt-entry program (the BRK program with `op := $00`) instead of
  fetching an opcode: cycles 1–2 read `PC` without incrementing it, three pushes (`PCH`, `PCL`,
  `P|$20`; for `reset` they become reads of the stack while `SP` still decrements), then the
  vector `vec, vec+1` is read and `I` set. The vector fetch reads `ms.vec` at that cycle, so the
  interrupt logic may retarget it mid-sequence (NMI hijack); BRK starts with `vec = $FFFE`.
  Polling/hijack decisions live in `Nes.Cpu.Interrupts`, not here.
* `cycle ms m` runs one cycle against flat memory; `runInstr fuel ms m` runs to the next
  boundary returning the cycle count; `runInstrTrace` also returns the per-cycle `BusEvent`s.
  `maxCycles = 8` fuel suffices for every instruction and the interrupt sequence.
-/

namespace Nes

/-- One CPU bus cycle. -/
inductive BusOp where
  | read (a : UInt16)
  | write (a : UInt16) (v : UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- A completed bus cycle as recorded in traces: address, data, direction. -/
structure BusEvent where
  addr : UInt16
  val : UInt8
  write : Bool
  deriving DecidableEq, Repr, Inhabited

end Nes

namespace Nes.Cpu

/-- One-cycle micro-operations. "PC" reads also increment `PC` where noted. -/
inductive MicroOp where
  -- addressing
  | fetchZp        -- read PC, PC++, addr := zp
  | fetchLo        -- read PC, PC++, data := lo
  | fetchHi        -- read PC, PC++, addr := hi:data
  | fetchHiX       -- read PC, PC++, base := hi:data, addr := base + X
  | fetchHiY       -- read PC, PC++, base := hi:data, addr := base + Y
  | zpIndexX       -- dummy read addr, addr := (addr + X) & $FF
  | zpIndexY       -- dummy read addr, addr := (addr + Y) & $FF
  | indexFixup     -- dummy read at hi(base):lo(addr) (conditional for reads)
  | ptrLo          -- read addr, data := v
  | ptrHi          -- read (addr+1)&$FF, addr := v:data
  | ptrHiY         -- read (addr+1)&$FF, base := v:data, addr := base + Y
  -- operand access
  | readExec       -- read addr, execute
  | immExec        -- read PC, PC++, execute
  | impExec        -- dummy read PC, execute (implied / accumulator)
  | write          -- write the store value to addr
  | rmwRead        -- read addr, data := v
  | rmwDummyWrite  -- write old data back, compute the result
  | rmwWrite       -- write the result
  -- stack, control flow
  | dummyReadPc    -- dummy read PC
  | dummyReadStack -- dummy read $100|SP
  | peekStackInc   -- dummy read $100|SP, SP++
  | pullPInc       -- read $100|SP, P := (v & $CF)|$20, SP++
  | pullLoInc      -- read $100|SP, data := v, SP++
  | pullHiPc       -- read $100|SP, PC := v:data
  | pullExec       -- read $100|SP, execute PLA/PLP
  | pushExec       -- write PHA/PHP value to $100|SP, SP--
  | pushPch        -- write PCH to $100|SP, SP-- (read if writes suppressed)
  | pushPcl        -- write PCL to $100|SP, SP-- (read if writes suppressed)
  | pushStatus     -- write P|$20|B to $100|SP, SP-- (read if writes suppressed)
  | vecLo          -- read vec, data := v, I := 1
  | vecHi          -- read vec+1, PC := v:data
  | jmpHi          -- read PC, PC := v:data (JMP abs, JSR)
  | jmpIndLo       -- read addr, data := v
  | jmpIndHi       -- read hi(addr):lo(addr)+1, PC := v:data
  | rtsInc         -- dummy read PC, PC++
  | brkOperand     -- read PC, PC++ unless a hardware interrupt
  | branchFetch    -- read PC, PC++, addr := target, crossed := target on another page
  | branchTaken    -- dummy read PC, PCL := lo target (conditional: taken)
  | branchFixup    -- dummy read PC, PC := target (conditional: taken and crossed)
  | jamRead        -- read PC
  | jamHalt        -- read PC, PC--, halted := true
  deriving DecidableEq, Repr, Inhabited

/-- A micro-program: cycles 2, 3, … of an instruction. -/
abbrev MicroProgram := Array MicroOp

/-- Instruction classes: one suffix program each. -/
inductive Cls where
  | read | imm | imp | write | rmw | push | pull | jsr | rts | rti | brk
  | jmpAbs | jmpInd | branch | jam
  deriving DecidableEq, Repr, Inhabited

/-- Shared addressing-mode prefixes (everything before the operand access). -/
def modePrefix : AddrMode → MicroProgram
  | .imp | .acc | .imm | .rel => #[]
  | .zp => #[.fetchZp]
  | .zpx => #[.fetchZp, .zpIndexX]
  | .zpy => #[.fetchZp, .zpIndexY]
  | .abs | .ind => #[.fetchLo, .fetchHi]
  | .absx => #[.fetchLo, .fetchHiX, .indexFixup]
  | .absy => #[.fetchLo, .fetchHiY, .indexFixup]
  | .indx => #[.fetchZp, .zpIndexX, .ptrLo, .ptrHi]
  | .indy => #[.fetchZp, .ptrLo, .ptrHiY, .indexFixup]

/-- Instruction-class suffixes. -/
def suffix : Cls → MicroProgram
  | .read => #[.readExec]
  | .imm => #[.immExec]
  | .imp => #[.impExec]
  | .write => #[.write]
  | .rmw => #[.rmwRead, .rmwDummyWrite, .rmwWrite]
  | .push => #[.dummyReadPc, .pushExec]
  | .pull => #[.dummyReadPc, .peekStackInc, .pullExec]
  | .jsr => #[.fetchLo, .dummyReadStack, .pushPch, .pushPcl, .jmpHi]
  | .rts => #[.dummyReadPc, .peekStackInc, .pullLoInc, .pullHiPc, .rtsInc]
  | .rti => #[.dummyReadPc, .peekStackInc, .pullPInc, .pullLoInc, .pullHiPc]
  | .brk => #[.brkOperand, .pushPch, .pushPcl, .pushStatus, .vecLo, .vecHi]
  | .jmpAbs => #[.fetchLo, .jmpHi]
  | .jmpInd => #[.jmpIndLo, .jmpIndHi]
  | .branch => #[.branchFetch, .branchTaken, .branchFixup]
  | .jam => #[.jamRead, .jamHalt]

/-- The class of a decoded opcode. -/
def classify (e : Entry) : Cls :=
  match e.instr with
  | .JSR => .jsr
  | .JMP => if e.mode == .ind then .jmpInd else .jmpAbs
  | .RTS => .rts
  | .RTI => .rti
  | .BRK => .brk
  | .PHA | .PHP => .push
  | .PLA | .PLP => .pull
  | .JAM => .jam
  | .BPL | .BMI | .BVC | .BVS | .BCC | .BCS | .BNE | .BEQ => .branch
  | .STA | .STX | .STY | .SAX | .SHY | .SHX | .AHX | .TAS => .write
  | i =>
    match e.mode with
    | .imp | .acc => .imp
    | .imm => .imm
    | _ =>
      match i with
      | .ASL | .LSR | .ROL | .ROR | .INC | .DEC
      | .SLO | .RLA | .SRE | .RRA | .DCP | .ISC => .rmw
      | _ => .read

/-- The addressing prefix used by a class (`JSR`/`JMP abs` fetch their own operand). -/
def prefixFor (c : Cls) (m : AddrMode) : MicroProgram :=
  match c with
  | .jsr | .jmpAbs => #[]
  | _ => modePrefix m

/-- The micro-program of a decoded opcode. -/
def program (e : Entry) : MicroProgram :=
  let c := classify e
  prefixFor c e.mode ++ suffix c

/-- All 256 micro-programs, indexed by opcode byte. -/
def uopTable : Vector MicroProgram 256 := Vector.ofFn fun i => program (decodeFin i)

/-- The micro-program of an opcode byte. -/
@[inline] def uops (op : UInt8) : MicroProgram := uopTable[op.toNat]'(UInt8.toNat_lt op)

/-- Base cycle count of a program: the implicit opcode fetch plus every micro-op except the
branch penalties and, for page-crossing reads, the conditional fixup. -/
def baseCycles (e : Entry) : Nat :=
  1 + ((program e).filter fun u =>
    match u with
    | .branchTaken | .branchFixup => false
    | .indexFixup => !e.pageCross
    | _ => true).size

/-- The microcode's base cycle counts agree with the decode table for all 256 opcodes. -/
theorem baseCycles_eq : ∀ i : Fin 256, baseCycles (decodeFin i) = (decodeFin i).cycles.toNat := by
  decide +kernel

/-! ## Instruction semantics used by the execute micro-ops -/

/-- Read-class (and immediate) instructions applied to operand `v`. -/
@[inline] def execRead (e : Entry) (s : State) (v : UInt8) : State :=
  match e.instr with
  | .LDA => s.ldA v
  | .LDX => { s with x := v }.setZN v
  | .LDY => { s with y := v }.setZN v
  | .LAX =>
    let r := if e.mode == .imm then (s.a ||| 0xEE) &&& v else v
    { s with a := r, x := r }.setZN r
  | .ADC => s.arith (Alu.fast.adc s.a v s.c)
  | .SBC => s.arith (Alu.fast.sbc s.a v s.c)
  | .AND => s.ldA (s.a &&& v)
  | .ORA => s.ldA (s.a ||| v)
  | .EOR => s.ldA (s.a ^^^ v)
  | .CMP => s.compare (Alu.fast.cmp s.a v)
  | .CPX => s.compare (Alu.fast.cmp s.x v)
  | .CPY => s.compare (Alu.fast.cmp s.y v)
  | .BIT =>
    let r := Alu.fast.bit s.a v
    ((s.setZ r.z).setV r.v).setN r.n
  | .ANC => let r := s.a &&& v; (s.ldA r).setC (r &&& 0x80 != 0)
  | .ALR => let r := Alu.fast.lsr (s.a &&& v); (s.setC r.c).ldA r.r
  | .ARR =>
    let r := (Alu.fast.ror (s.a &&& v) s.c).r
    ((s.ldA r).setC (r &&& 0x40 != 0)).setV (((r >>> 6) ^^^ (r >>> 5)) &&& 1 != 0)
  | .SBX =>
    let r := Alu.fast.cmp (s.a &&& s.x) v
    { s with x := r.r }.compare r
  | .LAS => let r := v &&& s.sp; { s with a := r, x := r, sp := r }.setZN r
  | .XAA => s.ldA ((s.a ||| 0xEE) &&& s.x &&& v)
  | _ => s

/-- Implied and accumulator instructions. -/
@[inline] def execImp (i : Instr) (s : State) : State :=
  match i with
  | .ASL => let r := Alu.fast.asl s.a; ({ s with a := r.r }.setC r.c).setZN r.r
  | .LSR => let r := Alu.fast.lsr s.a; ({ s with a := r.r }.setC r.c).setZN r.r
  | .ROL => let r := Alu.fast.rol s.a s.c; ({ s with a := r.r }.setC r.c).setZN r.r
  | .ROR => let r := Alu.fast.ror s.a s.c; ({ s with a := r.r }.setC r.c).setZN r.r
  | .INX => let r := Alu.fast.inc s.x; { s with x := r }.setZN r
  | .INY => let r := Alu.fast.inc s.y; { s with y := r }.setZN r
  | .DEX => let r := Alu.fast.dec s.x; { s with x := r }.setZN r
  | .DEY => let r := Alu.fast.dec s.y; { s with y := r }.setZN r
  | .TAX => { s with x := s.a }.setZN s.a
  | .TAY => { s with y := s.a }.setZN s.a
  | .TXA => s.ldA s.x
  | .TYA => s.ldA s.y
  | .TSX => { s with x := s.sp }.setZN s.sp
  | .TXS => { s with sp := s.x }
  | .CLC => s.setC false
  | .SEC => s.setC true
  | .CLI => s.setI false
  | .SEI => s.setI true
  | .CLV => s.setV false
  | .CLD => s.setD false
  | .SED => s.setD true
  | _ => s

/-- Result byte written back by a read-modify-write instruction (`c` = carry before). -/
@[inline] def rmwResult (i : Instr) (c : Bool) (v : UInt8) : UInt8 :=
  match i with
  | .ASL | .SLO => (Alu.fast.asl v).r
  | .LSR | .SRE => (Alu.fast.lsr v).r
  | .ROL | .RLA => (Alu.fast.rol v c).r
  | .ROR | .RRA => (Alu.fast.ror v c).r
  | .INC | .ISC => Alu.fast.inc v
  | .DEC | .DCP => Alu.fast.dec v
  | _ => v

/-- Register/flag effect of a read-modify-write instruction on operand `v`. -/
@[inline] def rmwState (i : Instr) (s : State) (v : UInt8) : State :=
  match i with
  | .ASL => let r := Alu.fast.asl v; (s.setC r.c).setZN r.r
  | .LSR => let r := Alu.fast.lsr v; (s.setC r.c).setZN r.r
  | .ROL => let r := Alu.fast.rol v s.c; (s.setC r.c).setZN r.r
  | .ROR => let r := Alu.fast.ror v s.c; (s.setC r.c).setZN r.r
  | .INC => s.setZN (Alu.fast.inc v)
  | .DEC => s.setZN (Alu.fast.dec v)
  | .SLO => let r := Alu.fast.asl v; (s.setC r.c).ldA (s.a ||| r.r)
  | .RLA => let r := Alu.fast.rol v s.c; (s.setC r.c).ldA (s.a &&& r.r)
  | .SRE => let r := Alu.fast.lsr v; (s.setC r.c).ldA (s.a ^^^ r.r)
  | .RRA => let r := Alu.fast.ror v s.c; s.arith (Alu.fast.adc s.a r.r r.c)
  | .DCP => s.compare (Alu.fast.cmp s.a (Alu.fast.dec v))
  | .ISC => s.arith (Alu.fast.sbc s.a (Alu.fast.inc v) s.c)
  | _ => s

/-- Value a store instruction puts on the bus (before the unstable `& (H+1)` mask). -/
@[inline] def storeVal (i : Instr) (s : State) : UInt8 :=
  match i with
  | .STA => s.a
  | .STX | .SHX => s.x
  | .STY | .SHY => s.y
  | _ => s.a &&& s.x  -- SAX, AHX, TAS

/-- Is this one of the unstable `SHY/SHX/AHX/TAS` stores? -/
@[inline] def unstable (i : Instr) : Bool :=
  match i with
  | .SHY | .SHX | .AHX | .TAS => true
  | _ => false

/-! ## The micro-machine -/

/-- Cycle-level CPU state. `pos = 0`: at an instruction boundary; otherwise the next cycle runs
`(uops op)[pos - 1]`. -/
structure MicroState where
  cpu : State
  /-- Current opcode. -/
  op : UInt8 := 0
  /-- Position in the program (0 = boundary). -/
  pos : UInt8 := 0
  /-- Effective address (or zero-page pointer while it is being resolved). -/
  addr : UInt16 := 0
  /-- Un-indexed base address (for the page-fixup dummy read and the unstable stores). -/
  base : UInt16 := 0
  /-- Data latch (low byte of an address, RMW operand/result). -/
  data : UInt8 := 0
  /-- Indexing (or a taken branch) crossed a page. -/
  crossed : Bool := false
  /-- Set by the system: at the next boundary, start the interrupt sequence. -/
  intPending : Bool := false
  /-- The current BRK-program run is a hardware interrupt (no PC increment, B clear). -/
  inInt : Bool := false
  /-- Reset variant: the three pushes become reads. -/
  suppressWrites : Bool := false
  /-- Vector address read by `vecLo`/`vecHi`. -/
  vec : UInt16 := 0xFFFE
  deriving DecidableEq, Repr, Inhabited

namespace MicroState

/-- A machine at an instruction boundary with CPU state `s`. -/
@[inline] def ofState (s : State) : MicroState := { cpu := s }

@[inline] def atBoundary (ms : MicroState) : Bool := ms.pos == 0

/-- Ask for the interrupt-entry sequence at the next boundary, with vector address `vec`
(`$FFFA` NMI, `$FFFC` RESET, `$FFFE` IRQ); `reset` suppresses the stack writes. -/
@[inline] def requestInterrupt (ms : MicroState) (vec : UInt16) (reset : Bool) : MicroState :=
  { ms with intPending := true, vec, suppressWrites := reset }

/-- The micro-op the next cycle runs (only meaningful when `pos ≠ 0`). -/
@[inline] def curOp (ms : MicroState) : MicroOp :=
  (uops ms.op).getD (ms.pos.toNat - 1) .jamHalt

@[inline] def stackAddr (ms : MicroState) : UInt16 := 0x100 ||| ms.cpu.sp.toUInt16

/-- A stack push of `v`, or a read of the same address when writes are suppressed. -/
@[inline] def pushOp (ms : MicroState) (v : UInt8) : BusOp :=
  if ms.suppressWrites then .read ms.stackAddr else .write ms.stackAddr v

/-- The (unstable-store-adjusted) address and value of the `write` micro-op. -/
@[inline] def storeAddr (ms : MicroState) (i : Instr) (w : UInt8) : UInt16 :=
  if unstable i && ms.crossed then UInt16.ofLoHi (UInt16.lo ms.addr) w else ms.addr

@[inline] def storeByte (ms : MicroState) (i : Instr) : UInt8 :=
  let v := storeVal i ms.cpu
  if unstable i then v &&& (UInt16.hi ms.base + 1) else v

/-- What this cycle does on the bus. -/
@[inline] def busOp (ms : MicroState) : BusOp :=
  let s := ms.cpu
  if ms.pos == 0 then
    if !ms.intPending && s.halted then .read 0xFFFF else .read s.pc
  else
    match ms.curOp with
    | .fetchZp | .fetchLo | .fetchHi | .fetchHiX | .fetchHiY | .immExec | .impExec
    | .dummyReadPc | .jmpHi | .rtsInc | .brkOperand | .branchFetch | .branchTaken
    | .branchFixup | .jamRead | .jamHalt => .read s.pc
    | .zpIndexX | .zpIndexY | .ptrLo | .readExec | .rmwRead | .jmpIndLo => .read ms.addr
    | .indexFixup => .read (UInt16.ofLoHi (UInt16.lo ms.addr) (UInt16.hi ms.base))
    | .ptrHi | .ptrHiY => .read (UInt16.lo ms.addr + 1).toUInt16
    | .write =>
      let i := (decode ms.op).instr
      let w := ms.storeByte i
      .write (ms.storeAddr i w) w
    | .rmwDummyWrite | .rmwWrite => .write ms.addr ms.data
    | .dummyReadStack | .peekStackInc | .pullPInc | .pullLoInc | .pullHiPc | .pullExec =>
      .read ms.stackAddr
    | .pushExec =>
      .write ms.stackAddr (if (decode ms.op).instr == .PHP then s.p ||| 0x30 else s.a)
    | .pushPch => ms.pushOp (UInt16.hi s.pc)
    | .pushPcl => ms.pushOp (UInt16.lo s.pc)
    | .pushStatus => ms.pushOp (s.p ||| (if ms.inInt then 0x20 else 0x30))
    | .vecLo => .read ms.vec
    | .vecHi => .read (ms.vec + 1)
    | .jmpIndHi => .read (UInt16.ofLoHi (UInt16.lo ms.addr + 1) (UInt16.hi ms.addr))

/-- Effect of micro-op `u` given the byte `v` read this cycle (ignored for writes). -/
@[inline] def exec (ms : MicroState) (u : MicroOp) (v : UInt8) : MicroState :=
  let s := ms.cpu
  match u with
  | .fetchZp => { ms with cpu := { s with pc := s.pc + 1 }, addr := v.toUInt16 }
  | .fetchLo => { ms with cpu := { s with pc := s.pc + 1 }, data := v }
  | .fetchHi => { ms with cpu := { s with pc := s.pc + 1 }, addr := UInt16.ofLoHi ms.data v }
  | .fetchHiX =>
    let b := UInt16.ofLoHi ms.data v
    let ea := b + s.x.toUInt16
    { ms with cpu := { s with pc := s.pc + 1 }, base := b, addr := ea,
              crossed := UInt16.hi ea != UInt16.hi b }
  | .fetchHiY =>
    let b := UInt16.ofLoHi ms.data v
    let ea := b + s.y.toUInt16
    { ms with cpu := { s with pc := s.pc + 1 }, base := b, addr := ea,
              crossed := UInt16.hi ea != UInt16.hi b }
  | .zpIndexX => { ms with addr := (UInt16.lo ms.addr + s.x).toUInt16 }
  | .zpIndexY => { ms with addr := (UInt16.lo ms.addr + s.y).toUInt16 }
  | .indexFixup => ms
  | .ptrLo => { ms with data := v }
  | .ptrHi => { ms with addr := UInt16.ofLoHi ms.data v }
  | .ptrHiY =>
    let b := UInt16.ofLoHi ms.data v
    let ea := b + s.y.toUInt16
    { ms with base := b, addr := ea, crossed := UInt16.hi ea != UInt16.hi b }
  | .readExec => { ms with cpu := execRead (decode ms.op) s v }
  | .immExec => { ms with cpu := execRead (decode ms.op) { s with pc := s.pc + 1 } v }
  | .impExec => { ms with cpu := execImp (decode ms.op).instr s }
  | .write =>
    if (decode ms.op).instr == .TAS then { ms with cpu := { s with sp := s.a &&& s.x } } else ms
  | .rmwRead => { ms with data := v }
  | .rmwDummyWrite =>
    let i := (decode ms.op).instr
    { ms with cpu := rmwState i s ms.data, data := rmwResult i s.c ms.data }
  | .rmwWrite => ms
  | .dummyReadPc | .dummyReadStack | .jamRead => ms
  | .peekStackInc => { ms with cpu := { s with sp := s.sp + 1 } }
  | .pullPInc => { ms with cpu := { s with p := (v &&& 0xCF) ||| 0x20, sp := s.sp + 1 } }
  | .pullLoInc => { ms with cpu := { s with sp := s.sp + 1 }, data := v }
  | .pullHiPc | .vecHi | .jmpHi | .jmpIndHi =>
    { ms with cpu := { s with pc := UInt16.ofLoHi ms.data v } }
  | .pullExec =>
    if (decode ms.op).instr == .PLP then { ms with cpu := { s with p := (v &&& 0xCF) ||| 0x20 } }
    else { ms with cpu := s.ldA v }
  | .pushExec | .pushPch | .pushPcl | .pushStatus => { ms with cpu := { s with sp := s.sp - 1 } }
  | .vecLo => { ms with cpu := s.setI true, data := v }
  | .jmpIndLo => { ms with data := v }
  | .rtsInc => { ms with cpu := { s with pc := s.pc + 1 } }
  | .brkOperand => if ms.inInt then ms else { ms with cpu := { s with pc := s.pc + 1 } }
  | .branchFetch =>
    let next := s.pc + 1
    let t := branchTarget next v
    { ms with cpu := { s with pc := next }, addr := t, crossed := UInt16.hi t != UInt16.hi next }
  | .branchTaken =>
    { ms with cpu := { s with pc := UInt16.ofLoHi (UInt16.lo ms.addr) (UInt16.hi s.pc) } }
  | .branchFixup => { ms with cpu := { s with pc := ms.addr } }
  | .jamHalt => { ms with cpu := { s with pc := s.pc - 1, halted := true } }

/-- Is the conditional micro-op `u` skipped (takes no cycle) in state `ms`? -/
@[inline] def skips (ms : MicroState) (u : MicroOp) : Bool :=
  match u with
  | .indexFixup => (decode ms.op).pageCross && !ms.crossed
  | .branchTaken => !branchCond ms.cpu (decode ms.op).instr
  | .branchFixup => !(branchCond ms.cpu (decode ms.op).instr && ms.crossed)
  | _ => false

/-- Move `pos` past the micro-op just run, skipping (at most two) conditional micro-ops;
`pos := 0` at the end of the program. -/
@[inline] def advance (ms : MicroState) : MicroState :=
  let prog := uops ms.op
  let n := prog.size
  let i := ms.pos.toNat
  let i := if i < n && ms.skips (prog.getD i .jamHalt) then i + 1 else i
  let i := if i < n && ms.skips (prog.getD i .jamHalt) then i + 1 else i
  { ms with pos := if i < n then (i + 1).toUInt8 else 0 }

/-- Finish the cycle announced by `busOp ms`, given the byte read (ignored for writes). -/
@[inline] def complete (ms : MicroState) (v : UInt8) : MicroState :=
  if ms.pos == 0 then
    if ms.intPending then
      let s := ms.cpu
      { ms with op := 0, pos := 1, intPending := false, inInt := true,
                cpu := if ms.suppressWrites then { s with halted := false } else s }
    else if ms.cpu.halted then ms
    else
      { ms with op := v, pos := 1, inInt := false, suppressWrites := false, vec := 0xFFFE,
                crossed := false, cpu := { ms.cpu with pc := ms.cpu.pc + 1 } }
  else
    (ms.exec ms.curOp v).advance

/-- One cycle against flat memory. -/
@[inline] def cycle (ms : MicroState) (m : Mem) : MicroState × Mem :=
  match ms.busOp with
  | .read a => (ms.complete (m.read a), m)
  | .write a v => (ms.complete v, m.write a v)

/-- One cycle against flat memory, also returning the bus event. -/
@[inline] def cycleEv (ms : MicroState) (m : Mem) : MicroState × Mem × BusEvent :=
  match ms.busOp with
  | .read a => let v := m.read a; (ms.complete v, m, ⟨a, v, false⟩)
  | .write a v => (ms.complete v, m.write a v, ⟨a, v, true⟩)

/-- Enough fuel for any instruction or the interrupt sequence. -/
def maxCycles : Nat := 8

/-- Run cycles until the next instruction boundary (at least one cycle); returns the final
machine, memory and number of cycles taken. -/
def runInstr : Nat → MicroState → Mem → MicroState × Mem × Nat
  | 0, ms, m => (ms, m, 0)
  | fuel + 1, ms, m =>
    let (ms', m') := ms.cycle m
    if ms'.pos == 0 then (ms', m', 1)
    else
      let (ms'', m'', n) := runInstr fuel ms' m'
      (ms'', m'', n + 1)

/-- `runInstr`, also recording every bus cycle. -/
def runInstrTrace (fuel : Nat) (ms : MicroState) (m : Mem) :
    MicroState × Mem × Array BusEvent :=
  go fuel ms m #[]
where
  go : Nat → MicroState → Mem → Array BusEvent → MicroState × Mem × Array BusEvent
    | 0, ms, m, acc => (ms, m, acc)
    | fuel + 1, ms, m, acc =>
      let (ms', m', ev) := ms.cycleEv m
      let acc := acc.push ev
      if ms'.pos == 0 then (ms', m', acc) else go fuel ms' m' acc

end MicroState

/-- One instruction of the micro-machine from a boundary, in `Isa.step`'s shape (T-REF-1). -/
def microStep (s : State) (m : Mem) : State × Mem × Nat :=
  let (ms, m', n) := (MicroState.ofState s).runInstr MicroState.maxCycles m
  (ms.cpu, m', n)

end Nes.Cpu
