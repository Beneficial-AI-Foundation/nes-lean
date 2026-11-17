import Nes.Cpu.Decode

/-!
# `Nes.Cpu.Proofs.Decode` — T-CPU-3 (decoder structure) and T-CPU-4 (cycle table)

## Spec

* **T-CPU-3 (totality).** `decode` is total by construction: `table` is a
  `Vector Entry 256` indexed by `op.toNat < 256`, so every byte decodes, and
  `decode op = decodeFin ⟨op.toNat, _⟩` for every `op : UInt8` (`T_CPU_3_total`).
* **T-CPU-3 (JAM set).** For every opcode `i : Fin 256`, the entry is `JAM` iff `i` is one of
  the 12 bytes of `jamOpcodes` (`$02 $12 $22 $32 $42 $52 $62 $72 $92 $B2 $D2 $F2`), and those
  12 bytes are pairwise distinct (`T_CPU_3_jam`).
* **T-CPU-3 (`aaabbbcc` structure).** `structDecode` is an independent decoder written from the
  6502 bit layout `aaa bbb cc` (`cc = op &&& 3`, `aaa = op >>> 5`, `bbb = (op >>> 2) &&& 7`).
  On every official opcode the table agrees with it: `structDecode op = some (instr, mode)`
  (`T_CPU_3_struct`). Moreover `structDecode` covers *exactly* the official opcodes:
  `(structDecode op).isSome ↔ official` (`T_CPU_3_struct_exact`).
* **T-CPU-4 (base cycles).** For all 256 opcodes, `cycles = cycleFormula instr mode`, where
  `cycleFormula` is a structural formula by instruction class (`control`, `branch`, `read`,
  `store`, `rmw`) and addressing mode (`T_CPU_4_cycles`). No per-opcode exceptions are needed.
* **T-CPU-4 (page cross).** For all 256 opcodes, `pageCross = true` iff the instruction is in
  the explicit read list `pageCrossReads` (`ADC AND CMP EOR LDA LDX LDY ORA SBC LAX LAS NOP`)
  and the mode is `absx`, `absy` or `indy` (`T_CPU_4_pageCross`). In particular the unstable
  `AHX SHY SHX TAS` (stores) and `XAA` (immediate only) never take the penalty, and `LAS`
  (only `$BB`, absy) does.
-/

namespace Nes.Cpu.Proofs

open Nes.Cpu

/-! ### T-CPU-3: totality and JAM set -/

/-- `decode` is total by construction and agrees with `decodeFin`. -/
theorem T_CPU_3_total (op : UInt8) : decode op = decodeFin ⟨op.toNat, UInt8.toNat_lt op⟩ := rfl

/-- `JAM` decodes from exactly the 12 bytes of `jamOpcodes`, which are distinct. -/
theorem T_CPU_3_jam :
    jamOpcodes.Nodup ∧ jamOpcodes.length = 12 ∧
    ∀ i : Fin 256, (decodeFin i).instr = .JAM ↔ i.val ∈ jamOpcodes.map UInt8.toNat := by
  decide +kernel

/-! ### T-CPU-3: the `aaabbbcc` structural decoder -/

/-- `cc = 01`: the ALU group, `aaa` selects the operation, `bbb` the mode. -/
def structGroup1 (aaa bbb : Nat) : Option (Instr × AddrMode) :=
  let instr := match aaa with
    | 0 => Instr.ORA | 1 => .AND | 2 => .EOR | 3 => .ADC
    | 4 => .STA | 5 => .LDA | 6 => .CMP | _ => .SBC
  let mode := match bbb with
    | 0 => AddrMode.indx | 1 => .zp | 2 => .imm | 3 => .abs
    | 4 => .indy | 5 => .zpx | 6 => .absy | _ => .absx
  if instr = .STA ∧ mode = .imm then none else some (instr, mode)

/-- `cc = 10`: shifts/RMW, `STX`/`LDX`, plus the `x A` transfer row and `TXS`/`TSX`. -/
def structGroup2 (aaa bbb : Nat) : Option (Instr × AddrMode) :=
  let instr := match aaa with
    | 0 => Instr.ASL | 1 => .ROL | 2 => .LSR | 3 => .ROR
    | 4 => .STX | 5 => .LDX | 6 => .DEC | _ => .INC
  -- STX/LDX index with Y instead of X
  let xy := aaa = 4 ∨ aaa = 5
  match bbb with
  | 0 => if aaa = 5 then some (.LDX, .imm) else none
  | 1 => some (instr, .zp)
  | 2 => match aaa with
    | 4 => some (.TXA, .imp) | 5 => some (.TAX, .imp)
    | 6 => some (.DEX, .imp) | 7 => some (.NOP, .imp)
    | _ => some (instr, .acc)
  | 3 => some (instr, .abs)
  | 5 => some (instr, if xy then .zpy else .zpx)
  | 6 => match aaa with
    | 4 => some (.TXS, .imp) | 5 => some (.TSX, .imp) | _ => none
  | 7 => if aaa = 4 then none else some (instr, if xy then .absy else .absx)
  | _ => none

/-- `cc = 00`: control flow, branches, flag ops, stack ops, `BIT JMP STY LDY CPY CPX`. -/
def structGroup0 (aaa bbb : Nat) : Option (Instr × AddrMode) :=
  let instr? : Option Instr := match aaa with
    | 1 => some .BIT | 4 => some .STY | 5 => some .LDY | 6 => some .CPY | 7 => some .CPX
    | _ => none
  match bbb with
  | 0 => match aaa with
    | 0 => some (.BRK, .imp) | 1 => some (.JSR, .abs) | 2 => some (.RTI, .imp)
    | 3 => some (.RTS, .imp) | 5 => some (.LDY, .imm) | 6 => some (.CPY, .imm)
    | 7 => some (.CPX, .imm) | _ => none
  | 1 => instr?.map (·, .zp)
  | 2 => some (match aaa with
    | 0 => .PHP | 1 => .PLP | 2 => .PHA | 3 => .PLA
    | 4 => .DEY | 5 => .TAY | 6 => .INY | _ => .INX, .imp)
  | 3 => match aaa with
    | 2 => some (.JMP, .abs) | 3 => some (.JMP, .ind) | _ => instr?.map (·, .abs)
  | 4 => some (match aaa with
    | 0 => .BPL | 1 => .BMI | 2 => .BVC | 3 => .BVS
    | 4 => .BCC | 5 => .BCS | 6 => .BNE | _ => .BEQ, .rel)
  | 5 => match aaa with
    | 4 => some (.STY, .zpx) | 5 => some (.LDY, .zpx) | _ => none
  | 6 => some (match aaa with
    | 0 => .CLC | 1 => .SEC | 2 => .CLI | 3 => .SEI
    | 4 => .TYA | 5 => .CLV | 6 => .CLD | _ => .SED, .imp)
  | 7 => if aaa = 5 then some (.LDY, .absx) else none
  | _ => none

/-- The structural `aaabbbcc` decoder. `none` for opcodes it does not cover (all `cc = 11`
and the unofficial holes of the other groups). -/
def structDecode (op : UInt8) : Option (Instr × AddrMode) :=
  let cc := (op &&& 3).toNat
  let aaa := (op >>> 5).toNat
  let bbb := ((op >>> 2) &&& 7).toNat
  match cc with
  | 0 => structGroup0 aaa bbb
  | 1 => structGroup1 aaa bbb
  | 2 => structGroup2 aaa bbb
  | _ => none

/-- On official opcodes the table agrees with the `aaabbbcc` structural decoder. -/
theorem T_CPU_3_struct : ∀ op : Fin 256, (decodeFin op).official = true →
    structDecode (UInt8.ofNat op.val) = some ((decodeFin op).instr, (decodeFin op).mode) := by
  decide +kernel

/-- The structural decoder covers exactly the 151 official opcodes. -/
theorem T_CPU_3_struct_exact : ∀ op : Fin 256,
    (structDecode (UInt8.ofNat op.val)).isSome = (decodeFin op).official := by
  decide +kernel

/-! ### T-CPU-4: cycle table -/

/-- Instruction classes for the cycle formula. -/
inductive CycleClass where
  /-- Fetches an operand and does not write memory (incl. implied/accumulator ops). -/
  | read
  /-- Writes memory without reading it (incl. unstable `SAX AHX SHY SHX TAS`). -/
  | store
  /-- Read-modify-write (incl. unofficial `SLO RLA SRE RRA DCP ISC`). -/
  | rmw
  /-- Relative branches. -/
  | branch
  /-- Stack/control-flow with a fixed cost. -/
  | control
  deriving DecidableEq, Repr

/-- The class of each instruction (an explicit list per class; everything else is `read`). -/
def cycleClass : Instr → CycleClass
  | .STA | .STX | .STY | .SAX | .AHX | .SHY | .SHX | .TAS => .store
  | .ASL | .LSR | .ROL | .ROR | .INC | .DEC
  | .SLO | .RLA | .SRE | .RRA | .DCP | .ISC => .rmw
  | .BCC | .BCS | .BEQ | .BMI | .BNE | .BPL | .BVC | .BVS => .branch
  | .BRK | .JSR | .RTI | .RTS | .JMP | .PHA | .PHP | .PLA | .PLP | .JAM => .control
  | _ => .read

/-- Base cycles of a read-class instruction by addressing mode (no page cross). -/
def readCycles : AddrMode → Nat
  | .imp | .acc | .imm | .rel => 2
  | .zp => 3
  | .zpx | .zpy | .abs | .absx | .absy => 4
  | .indx => 6
  | .indy | .ind => 5

/-- The documented base-cycle formula by (class, mode). -/
def cycleFormula (i : Instr) (m : AddrMode) : Nat :=
  match cycleClass i with
  | .read => readCycles m
  | .store => match m with
    | .absx | .absy | .indy => readCycles m + 1  -- always pay the fix-up read
    | _ => readCycles m
  | .rmw => match m with
    | .acc => 2
    | .zp => 5 | .zpx => 6 | .abs => 6 | .absx | .absy => 7 | .indx | .indy => 8
    | _ => readCycles m
  | .branch => 2
  | .control => match i, m with
    | .BRK, _ => 7
    | .JSR, _ | .RTI, _ | .RTS, _ => 6
    | .JMP, .ind => 5
    | .JMP, _ => 3
    | .PHA, _ | .PHP, _ => 3
    | .PLA, _ | .PLP, _ => 4
    | _, _ => 3  -- JAM: opcode fetch + two reads, as SingleStepTests records

/-- The table's base cycles equal the structural formula, for all 256 opcodes. -/
theorem T_CPU_4_cycles : ∀ op : Fin 256,
    (decodeFin op).cycles.toNat = cycleFormula (decodeFin op).instr (decodeFin op).mode := by
  decide +kernel

/-- Read-class instructions that pay +1 on a page-crossing indexed effective address. -/
def pageCrossReads : List Instr :=
  [.ADC, .AND, .CMP, .EOR, .LDA, .LDX, .LDY, .ORA, .SBC, .LAX, .LAS, .NOP]

/-- The page-cross penalty applies to exactly the reads in `pageCrossReads` with an
indexed mode `absx`/`absy`/`indy`. -/
theorem T_CPU_4_pageCross : ∀ op : Fin 256,
    (decodeFin op).pageCross = true ↔
      ((decodeFin op).instr ∈ pageCrossReads ∧
        (decodeFin op).mode ∈ [AddrMode.absx, .absy, .indy]) := by
  decide +kernel

end Nes.Cpu.Proofs
