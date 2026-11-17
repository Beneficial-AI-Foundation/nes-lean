import Nes.Cpu.Types
import Nes.Cpu.Decode
import Nes.Cpu.Alu

/-!
# `Nes.Cpu.Isa` — instruction-level semantics of the 2A03

`step` executes one whole instruction: it is the trusted spec that the SingleStepTests
(`nes6502`) final states and nestest validate, and that the M2 micro-op model refines.

## Spec

* `Mem` is a flat 64 KiB `Vector UInt8 65536`; `Mem.read`/`Mem.write` index it by
  `UInt16.toNat` (total, no panics). The NES bus replaces it in M3.
* Operand resolution is split into small functions the T-CPU-5 lemmas talk about:
  - `zpIndexed b i = (b + i)` as a byte, so zero-page indexing never leaves page 0;
  - `absIndexed base i = (base + i, crossed)` with `crossed` true iff the high byte changed,
    i.e. `(base + i) / 256 ≠ base / 256`;
  - `zpPtr m z` reads a little-endian pointer from `z, z+1` with the high byte fetched from
    `(z + 1) mod 256`;
  - `indirectBug m ptr` (JMP indirect) fetches the high byte from `(ptr & $FF00) | ((ptr+1) & $FF)`,
    so `JMP ($xxFF)` reads its high byte from `$xx00`;
  - `branchTarget pc off` adds the sign-extended offset, wrapping modulo 2^16.
  `resolve s m mode = (ea, crossed)`; for `imm` the "address" is `pc + 1`, for `rel` it is the
  branch target and `crossed` says the target is on another page than the next instruction.
* All PC arithmetic is `UInt16`, so `PC` wraps `$FFFF → $0000`.
* Cycle count: `cycles(op)`, `+1` if `pageCross(op)` and the indexed address crossed a page,
  and for branches `+1` if taken and `+1` more if the target is on another page.
* Status byte on the stack: PHP/BRK push `P | $30` (B and bit 5 set); PLP/RTI load
  `(v & $CF) | $20` (B cleared, bit 5 set) — as recorded by the test data.
* No decimal mode: ADC/SBC/ARR/RRA/ISC ignore D.
* JAM: `halted := true`, every register (PC included) unchanged, base cycles. A halted CPU's
  `step` is a no-op costing 1 cycle.
* Unstable opcodes (constants as in the SingleStepTests data): `XAA`: `A := (A | $EE) & X & #`;
  `LAX #`: `A, X := (A | $EE) & #`; `SHY/SHX/AHX/TAS` store `reg & (H + 1)` where `H` is the high
  byte of the un-indexed base address, and on a page cross the stored value replaces the
  high byte of the effective address; `TAS` also sets `SP := A & X`.
-/

namespace Nes.Cpu

/-- Flat 64 KiB memory. -/
abbrev Mem := Vector UInt8 65536

namespace Mem

@[inline] def read (m : Mem) (a : UInt16) : UInt8 := m[a.toNat]'(UInt16.toNat_lt a)

@[inline] def write (m : Mem) (a : UInt16) (v : UInt8) : Mem := m.set a.toNat v (UInt16.toNat_lt a)

/-- Little-endian 16-bit read at `a, a+1` (wrapping at `$FFFF`). -/
@[inline] def read16 (m : Mem) (a : UInt16) : UInt16 := UInt16.ofLoHi (m.read a) (m.read (a + 1))

end Mem

/-! ## Operand resolution -/

/-- Zero-page indexed address: the sum wraps within page 0. -/
@[inline] def zpIndexed (b i : UInt8) : UInt16 := (b + i).toUInt16

/-- Absolute indexed address and whether it crossed a page. -/
@[inline] def absIndexed (base : UInt16) (i : UInt8) : UInt16 × Bool :=
  let ea := base + i.toUInt16
  (ea, UInt16.hi ea != UInt16.hi base)

/-- Pointer stored in zero page at `z`, `z+1` (the high-byte fetch wraps within page 0). -/
@[inline] def zpPtr (m : Mem) (z : UInt8) : UInt16 :=
  UInt16.ofLoHi (m.read z.toUInt16) (m.read (z + 1).toUInt16)

/-- `JMP (ptr)`: the high byte is fetched from the same page as the low byte. -/
@[inline] def indirectBug (m : Mem) (ptr : UInt16) : UInt16 :=
  UInt16.ofLoHi (m.read ptr) (m.read (UInt16.ofLoHi (UInt16.lo ptr + 1) (UInt16.hi ptr)))

/-- Branch target: `pc` plus the sign-extended offset. -/
@[inline] def branchTarget (pc : UInt16) (off : UInt8) : UInt16 :=
  if off < 0x80 then pc + off.toUInt16 else pc + off.toUInt16 - 0x100

/-- Instruction length in bytes for each addressing mode. -/
@[inline] def AddrMode.len : AddrMode → UInt16
  | .imp | .acc => 1
  | .imm | .zp | .zpx | .zpy | .indx | .indy | .rel => 2
  | .abs | .absx | .absy | .ind => 3

/-- Effective address of the operand and whether indexing crossed a page. -/
@[inline] def resolve (s : State) (m : Mem) (mode : AddrMode) : UInt16 × Bool :=
  let b1 := m.read (s.pc + 1)
  match mode with
  | .imp | .acc => (0, false)
  | .imm => (s.pc + 1, false)
  | .zp => (b1.toUInt16, false)
  | .zpx => (zpIndexed b1 s.x, false)
  | .zpy => (zpIndexed b1 s.y, false)
  | .abs => (m.read16 (s.pc + 1), false)
  | .absx => absIndexed (m.read16 (s.pc + 1)) s.x
  | .absy => absIndexed (m.read16 (s.pc + 1)) s.y
  | .ind => (indirectBug m (m.read16 (s.pc + 1)), false)
  | .indx => (zpPtr m (b1 + s.x), false)
  | .indy => absIndexed (zpPtr m b1) s.y
  | .rel =>
    let next := s.pc + 2
    let t := branchTarget next b1
    (t, UInt16.hi t != UInt16.hi next)

/-! ## Helpers -/

/-- Push a byte: write at `$0100 + SP`, then decrement `SP`. -/
@[inline] def push (s : State) (m : Mem) (v : UInt8) : State × Mem :=
  ({ s with sp := s.sp - 1 }, m.write (0x100 ||| s.sp.toUInt16) v)

/-- Pull a byte: increment `SP`, then read at `$0100 + SP`. -/
@[inline] def pull (s : State) (m : Mem) : State × UInt8 :=
  let sp := s.sp + 1
  ({ s with sp := sp }, m.read (0x100 ||| sp.toUInt16))

/-- Branch condition of a conditional-branch instruction (`false` for anything else). -/
@[inline] def branchCond (s : State) : Instr → Bool
  | .BPL => !s.n | .BMI => s.n
  | .BVC => !s.v | .BVS => s.v
  | .BCC => !s.c | .BCS => s.c
  | .BNE => !s.z | .BEQ => s.z
  | _ => false

/-- Load `A` with `r` and set Z/N. -/
@[inline] def State.ldA (s : State) (r : UInt8) : State := { s with a := r }.setZN r

/-- Apply an ADC/SBC result to `A`, C, V, Z, N. -/
@[inline] def State.arith (s : State) (r : Alu.Res) : State :=
  ((({ s with a := r.r }).setC r.c).setV r.v).setZN r.r

/-- Apply a compare result to C, Z, N. -/
@[inline] def State.compare (s : State) (r : Alu.RC) : State := (s.setC r.c).setZN r.r

/-- The unstable stores `SHY/SHX/AHX/TAS`: store `v & (H+1)` where `H` is the high byte of the
un-indexed base; on a page cross the stored value replaces the address's high byte. -/
@[inline] def unstableStore (m : Mem) (ea : UInt16) (idx : UInt8) (crossed : Bool) (v : UInt8) :
    Mem :=
  let h := UInt16.hi (ea - idx.toUInt16)
  let w := v &&& (h + 1)
  let addr := if crossed then UInt16.ofLoHi (UInt16.lo ea) w else ea
  m.write addr w

/-- Shift/rotate `f` on the accumulator (`acc`) or on memory at `ea`, setting C, Z, N. -/
@[inline] def shiftOp (acc : Bool) (s : State) (m : Mem) (ea : UInt16) (f : UInt8 → Alu.RC) :
    State × Mem :=
  if acc then
    let r := f s.a
    (({ s with a := r.r }.setC r.c).setZN r.r, m)
  else
    let r := f (m.read ea)
    ((s.setC r.c).setZN r.r, m.write ea r.r)

/-! ## Execution -/

/-- Execute the decoded instruction `e`. `ea`/`crossed` come from `resolve`; `pc'` is the address
of the next instruction. Returns the new state and memory (cycles are computed by `step`). -/
def exec (e : Entry) (s : State) (m : Mem) (ea : UInt16) (crossed : Bool) : State × Mem :=
  let s1 := { s with pc := s.pc + e.mode.len }
  let v := m.read ea
  let rmw := shiftOp (e.mode == .acc) s1 m ea
  match e.instr with
  -- loads and stores
  | .LDA => (s1.ldA v, m)
  | .LDX => ({ s1 with x := v }.setZN v, m)
  | .LDY => ({ s1 with y := v }.setZN v, m)
  | .LAX =>
    let r := if e.mode == .imm then (s.a ||| 0xEE) &&& v else v
    ({ s1 with a := r, x := r }.setZN r, m)
  | .STA => (s1, m.write ea s.a)
  | .STX => (s1, m.write ea s.x)
  | .STY => (s1, m.write ea s.y)
  | .SAX => (s1, m.write ea (s.a &&& s.x))
  -- arithmetic and logic
  | .ADC => (s1.arith (Alu.fast.adc s.a v s.c), m)
  | .SBC => (s1.arith (Alu.fast.sbc s.a v s.c), m)
  | .AND => (s1.ldA (s.a &&& v), m)
  | .ORA => (s1.ldA (s.a ||| v), m)
  | .EOR => (s1.ldA (s.a ^^^ v), m)
  | .CMP => (s1.compare (Alu.fast.cmp s.a v), m)
  | .CPX => (s1.compare (Alu.fast.cmp s.x v), m)
  | .CPY => (s1.compare (Alu.fast.cmp s.y v), m)
  | .BIT =>
    let r := Alu.fast.bit s.a v
    (((s1.setZ r.z).setV r.v).setN r.n, m)
  -- shifts, rotates, increments
  | .ASL => rmw Alu.fast.asl
  | .LSR => rmw Alu.fast.lsr
  | .ROL => rmw (Alu.fast.rol · s.c)
  | .ROR => rmw (Alu.fast.ror · s.c)
  | .INC => let r := Alu.fast.inc v; (s1.setZN r, m.write ea r)
  | .DEC => let r := Alu.fast.dec v; (s1.setZN r, m.write ea r)
  | .INX => let r := Alu.fast.inc s.x; ({ s1 with x := r }.setZN r, m)
  | .INY => let r := Alu.fast.inc s.y; ({ s1 with y := r }.setZN r, m)
  | .DEX => let r := Alu.fast.dec s.x; ({ s1 with x := r }.setZN r, m)
  | .DEY => let r := Alu.fast.dec s.y; ({ s1 with y := r }.setZN r, m)
  -- unofficial read-modify-write combinations
  | .SLO => let r := Alu.fast.asl v; ((s1.setC r.c).ldA (s.a ||| r.r), m.write ea r.r)
  | .RLA => let r := Alu.fast.rol v s.c; ((s1.setC r.c).ldA (s.a &&& r.r), m.write ea r.r)
  | .SRE => let r := Alu.fast.lsr v; ((s1.setC r.c).ldA (s.a ^^^ r.r), m.write ea r.r)
  | .RRA =>
    let r := Alu.fast.ror v s.c
    (s1.arith (Alu.fast.adc s.a r.r r.c), m.write ea r.r)
  | .DCP => let r := Alu.fast.dec v; (s1.compare (Alu.fast.cmp s.a r), m.write ea r)
  | .ISC => let r := Alu.fast.inc v; (s1.arith (Alu.fast.sbc s.a r s.c), m.write ea r)
  -- unofficial immediate-mode operations
  | .ANC => let r := s.a &&& v; ((s1.ldA r).setC (r &&& 0x80 != 0), m)
  | .ALR => let r := Alu.fast.lsr (s.a &&& v); ((s1.setC r.c).ldA r.r, m)
  | .ARR =>
    let r := (Alu.fast.ror (s.a &&& v) s.c).r
    (((s1.ldA r).setC (r &&& 0x40 != 0)).setV (((r >>> 6) ^^^ (r >>> 5)) &&& 1 != 0), m)
  | .SBX =>
    let t := s.a &&& s.x
    let r := Alu.fast.cmp t v
    ({ s1 with x := r.r }.compare r, m)
  | .LAS => let r := v &&& s.sp; ({ s1 with a := r, x := r, sp := r }.setZN r, m)
  | .XAA => (s1.ldA ((s.a ||| 0xEE) &&& s.x &&& v), m)
  -- unstable stores
  | .SHY => (s1, unstableStore m ea s.x crossed s.y)
  | .SHX => (s1, unstableStore m ea s.y crossed s.x)
  | .AHX => (s1, unstableStore m ea s.y crossed (s.a &&& s.x))
  | .TAS =>
    let sp := s.a &&& s.x
    ({ s1 with sp := sp }, unstableStore m ea s.y crossed sp)
  -- branches (target and taken condition from `resolve`/`branchCond`)
  | .BPL | .BMI | .BVC | .BVS | .BCC | .BCS | .BNE | .BEQ =>
    (if branchCond s e.instr then { s1 with pc := ea } else s1, m)
  -- jumps, calls, returns, interrupts
  | .JMP => ({ s with pc := ea }, m)
  | .JSR =>
    let ret := s.pc + 2
    let (s2, m2) := push s m (UInt16.hi ret)
    let (s3, m3) := push s2 m2 (UInt16.lo ret)
    ({ s3 with pc := ea }, m3)
  | .RTS =>
    let (s2, lo) := pull s m
    let (s3, hi) := pull s2 m
    ({ s3 with pc := UInt16.ofLoHi lo hi + 1 }, m)
  | .RTI =>
    let (s2, p) := pull s m
    let (s3, lo) := pull s2 m
    let (s4, hi) := pull s3 m
    ({ s4 with p := (p &&& 0xCF) ||| 0x20, pc := UInt16.ofLoHi lo hi }, m)
  | .BRK =>
    let ret := s.pc + 2
    let (s2, m2) := push s m (UInt16.hi ret)
    let (s3, m3) := push s2 m2 (UInt16.lo ret)
    let (s4, m4) := push s3 m3 (s.p ||| 0x30)
    ({ s4.setI true with pc := m4.read16 0xFFFE }, m4)
  -- stack
  | .PHA => let (s2, m2) := push s1 m s.a; (s2, m2)
  | .PHP => let (s2, m2) := push s1 m (s.p ||| 0x30); (s2, m2)
  | .PLA => let (s2, r) := pull s1 m; (s2.ldA r, m)
  | .PLP => let (s2, r) := pull s1 m; ({ s2 with p := (r &&& 0xCF) ||| 0x20 }, m)
  -- transfers
  | .TAX => ({ s1 with x := s.a }.setZN s.a, m)
  | .TAY => ({ s1 with y := s.a }.setZN s.a, m)
  | .TXA => (s1.ldA s.x, m)
  | .TYA => (s1.ldA s.y, m)
  | .TSX => ({ s1 with x := s.sp }.setZN s.sp, m)
  | .TXS => ({ s1 with sp := s.x }, m)
  -- flags
  | .CLC => (s1.setC false, m)
  | .SEC => (s1.setC true, m)
  | .CLI => (s1.setI false, m)
  | .SEI => (s1.setI true, m)
  | .CLV => (s1.setV false, m)
  | .CLD => (s1.setD false, m)
  | .SED => (s1.setD true, m)
  -- no-ops and halt
  | .NOP => (s1, m)
  | .JAM => ({ s with halted := true }, m)

/-- Extra cycles beyond `cycles(op)`: page-cross penalty, branch taken / branch to another page. -/
@[inline] def extraCycles (e : Entry) (s : State) (crossed : Bool) : Nat :=
  if e.mode == .rel then
    if branchCond s e.instr then (if crossed then 2 else 1) else 0
  else if e.pageCross && crossed then 1 else 0

/-- Execute one instruction: new state, new memory, cycles taken. A halted CPU stays put
(1 cycle, so that cycle-driven loops make progress). -/
def step (s : State) (m : Mem) : State × Mem × Nat :=
  if s.halted then (s, m, 1)
  else
    let e := decode (m.read s.pc)
    let (ea, crossed) := resolve s m e.mode
    let (s', m') := exec e s m ea crossed
    (s', m', e.cycles.toNat + extraCycles e s crossed)

end Nes.Cpu
