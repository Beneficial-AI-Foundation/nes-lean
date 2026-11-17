/-!
# `Nes.Cpu.Decode` — the 2A03 opcode table

Every one of the 256 opcode bytes decodes to an `Entry`: the instruction, its addressing
mode, its base cycle count, whether a page-crossing effective address costs one extra cycle,
and whether the opcode is one of the 151 official (documented) ones.

## Spec

* `AddrMode`: the 13 addressing modes (`imp`, `acc`, `imm`, `zp`, `zpx`, `zpy`, `abs`, `absx`,
  `absy`, `ind`, `indx` = `(zp,X)`, `indy` = `(zp),Y`, `rel`).
* `Instr`: the 56 official mnemonics, the unofficial ones (`LAX SAX DCP ISC SLO RLA SRE RRA
  ANC ALR ARR SBX LAS XAA AHX SHY SHX TAS`) and `JAM`. Unofficial NOPs reuse `NOP` and the
  unofficial `$EB` reuses `SBC`; they are distinguished by `Entry.official = false`.
* `table : Vector Entry 256`, `decode : UInt8 → Entry`, `decodeFin : Fin 256 → Entry`.
* `cycles` is the base count (no page cross, branch not taken). `pageCross = true` exactly for
  the reads with `absx`/`absy`/`indy` that take +1 cycle on a page cross; stores and RMW never
  do, and branches record `false` (their taken/page extra cycles are handled in execution).
* JAM (`$02 $12 $22 $32 $42 $52 $62 $72 $92 $B2 $D2 $F2`) halts the CPU; its `cycles` is 3,
  matching the SingleStepTests encoding (opcode fetch + two reads, then halted).
* All base cycle counts and page-cross flags were checked against every case of the
  SingleStepTests `nes6502/v1` data: for each opcode, the observed cycle-count set is exactly
  within `{cycles} ∪ {cycles+1 | pageCross} ∪ {cycles+1, cycles+2 | rel}` with minimum `cycles`.
-/

namespace Nes.Cpu

/-- The 13 6502 addressing modes. `indx` is `(zp,X)`, `indy` is `(zp),Y`. -/
inductive AddrMode where
  | imp | acc | imm | zp | zpx | zpy | abs | absx | absy | ind | indx | indy | rel
  deriving DecidableEq, Repr, Inhabited

/-- Instruction mnemonics: official, unofficial, and `JAM` (halt). -/
inductive Instr where
  -- official
  | ADC | AND | ASL | BCC | BCS | BEQ | BIT | BMI | BNE | BPL | BRK | BVC | BVS | CLC
  | CLD | CLI | CLV | CMP | CPX | CPY | DEC | DEX | DEY | EOR | INC | INX | INY | JMP
  | JSR | LDA | LDX | LDY | LSR | NOP | ORA | PHA | PHP | PLA | PLP | ROL | ROR | RTI
  | RTS | SBC | SEC | SED | SEI | STA | STX | STY | TAX | TAY | TSX | TXA | TXS | TYA
  -- stable unofficial
  | LAX | SAX | DCP | ISC | SLO | RLA | SRE | RRA | ANC | ALR | ARR | SBX | LAS
  -- unstable unofficial (canonical SingleStepTests behaviour)
  | XAA | AHX | SHY | SHX | TAS
  -- halt
  | JAM
  deriving DecidableEq, Repr, Inhabited

/-- One decoded opcode. `cycles` is the base cycle count; `pageCross` says a page-crossing
effective address adds one cycle; `official` marks the 151 documented opcodes. -/
structure Entry where
  instr : Instr
  mode : AddrMode
  cycles : UInt8
  pageCross : Bool
  official : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The 256-entry opcode table as an array literal, indexed by opcode byte. -/
def tableArray : Array Entry := #[
  ⟨.BRK, .imp, 7, false, true⟩, -- $00
  ⟨.ORA, .indx, 6, false, true⟩, -- $01
  ⟨.JAM, .imp, 3, false, false⟩, -- $02
  ⟨.SLO, .indx, 8, false, false⟩, -- $03
  ⟨.NOP, .zp, 3, false, false⟩, -- $04
  ⟨.ORA, .zp, 3, false, true⟩, -- $05
  ⟨.ASL, .zp, 5, false, true⟩, -- $06
  ⟨.SLO, .zp, 5, false, false⟩, -- $07
  ⟨.PHP, .imp, 3, false, true⟩, -- $08
  ⟨.ORA, .imm, 2, false, true⟩, -- $09
  ⟨.ASL, .acc, 2, false, true⟩, -- $0A
  ⟨.ANC, .imm, 2, false, false⟩, -- $0B
  ⟨.NOP, .abs, 4, false, false⟩, -- $0C
  ⟨.ORA, .abs, 4, false, true⟩, -- $0D
  ⟨.ASL, .abs, 6, false, true⟩, -- $0E
  ⟨.SLO, .abs, 6, false, false⟩, -- $0F
  ⟨.BPL, .rel, 2, false, true⟩, -- $10
  ⟨.ORA, .indy, 5, true, true⟩, -- $11
  ⟨.JAM, .imp, 3, false, false⟩, -- $12
  ⟨.SLO, .indy, 8, false, false⟩, -- $13
  ⟨.NOP, .zpx, 4, false, false⟩, -- $14
  ⟨.ORA, .zpx, 4, false, true⟩, -- $15
  ⟨.ASL, .zpx, 6, false, true⟩, -- $16
  ⟨.SLO, .zpx, 6, false, false⟩, -- $17
  ⟨.CLC, .imp, 2, false, true⟩, -- $18
  ⟨.ORA, .absy, 4, true, true⟩, -- $19
  ⟨.NOP, .imp, 2, false, false⟩, -- $1A
  ⟨.SLO, .absy, 7, false, false⟩, -- $1B
  ⟨.NOP, .absx, 4, true, false⟩, -- $1C
  ⟨.ORA, .absx, 4, true, true⟩, -- $1D
  ⟨.ASL, .absx, 7, false, true⟩, -- $1E
  ⟨.SLO, .absx, 7, false, false⟩, -- $1F
  ⟨.JSR, .abs, 6, false, true⟩, -- $20
  ⟨.AND, .indx, 6, false, true⟩, -- $21
  ⟨.JAM, .imp, 3, false, false⟩, -- $22
  ⟨.RLA, .indx, 8, false, false⟩, -- $23
  ⟨.BIT, .zp, 3, false, true⟩, -- $24
  ⟨.AND, .zp, 3, false, true⟩, -- $25
  ⟨.ROL, .zp, 5, false, true⟩, -- $26
  ⟨.RLA, .zp, 5, false, false⟩, -- $27
  ⟨.PLP, .imp, 4, false, true⟩, -- $28
  ⟨.AND, .imm, 2, false, true⟩, -- $29
  ⟨.ROL, .acc, 2, false, true⟩, -- $2A
  ⟨.ANC, .imm, 2, false, false⟩, -- $2B
  ⟨.BIT, .abs, 4, false, true⟩, -- $2C
  ⟨.AND, .abs, 4, false, true⟩, -- $2D
  ⟨.ROL, .abs, 6, false, true⟩, -- $2E
  ⟨.RLA, .abs, 6, false, false⟩, -- $2F
  ⟨.BMI, .rel, 2, false, true⟩, -- $30
  ⟨.AND, .indy, 5, true, true⟩, -- $31
  ⟨.JAM, .imp, 3, false, false⟩, -- $32
  ⟨.RLA, .indy, 8, false, false⟩, -- $33
  ⟨.NOP, .zpx, 4, false, false⟩, -- $34
  ⟨.AND, .zpx, 4, false, true⟩, -- $35
  ⟨.ROL, .zpx, 6, false, true⟩, -- $36
  ⟨.RLA, .zpx, 6, false, false⟩, -- $37
  ⟨.SEC, .imp, 2, false, true⟩, -- $38
  ⟨.AND, .absy, 4, true, true⟩, -- $39
  ⟨.NOP, .imp, 2, false, false⟩, -- $3A
  ⟨.RLA, .absy, 7, false, false⟩, -- $3B
  ⟨.NOP, .absx, 4, true, false⟩, -- $3C
  ⟨.AND, .absx, 4, true, true⟩, -- $3D
  ⟨.ROL, .absx, 7, false, true⟩, -- $3E
  ⟨.RLA, .absx, 7, false, false⟩, -- $3F
  ⟨.RTI, .imp, 6, false, true⟩, -- $40
  ⟨.EOR, .indx, 6, false, true⟩, -- $41
  ⟨.JAM, .imp, 3, false, false⟩, -- $42
  ⟨.SRE, .indx, 8, false, false⟩, -- $43
  ⟨.NOP, .zp, 3, false, false⟩, -- $44
  ⟨.EOR, .zp, 3, false, true⟩, -- $45
  ⟨.LSR, .zp, 5, false, true⟩, -- $46
  ⟨.SRE, .zp, 5, false, false⟩, -- $47
  ⟨.PHA, .imp, 3, false, true⟩, -- $48
  ⟨.EOR, .imm, 2, false, true⟩, -- $49
  ⟨.LSR, .acc, 2, false, true⟩, -- $4A
  ⟨.ALR, .imm, 2, false, false⟩, -- $4B
  ⟨.JMP, .abs, 3, false, true⟩, -- $4C
  ⟨.EOR, .abs, 4, false, true⟩, -- $4D
  ⟨.LSR, .abs, 6, false, true⟩, -- $4E
  ⟨.SRE, .abs, 6, false, false⟩, -- $4F
  ⟨.BVC, .rel, 2, false, true⟩, -- $50
  ⟨.EOR, .indy, 5, true, true⟩, -- $51
  ⟨.JAM, .imp, 3, false, false⟩, -- $52
  ⟨.SRE, .indy, 8, false, false⟩, -- $53
  ⟨.NOP, .zpx, 4, false, false⟩, -- $54
  ⟨.EOR, .zpx, 4, false, true⟩, -- $55
  ⟨.LSR, .zpx, 6, false, true⟩, -- $56
  ⟨.SRE, .zpx, 6, false, false⟩, -- $57
  ⟨.CLI, .imp, 2, false, true⟩, -- $58
  ⟨.EOR, .absy, 4, true, true⟩, -- $59
  ⟨.NOP, .imp, 2, false, false⟩, -- $5A
  ⟨.SRE, .absy, 7, false, false⟩, -- $5B
  ⟨.NOP, .absx, 4, true, false⟩, -- $5C
  ⟨.EOR, .absx, 4, true, true⟩, -- $5D
  ⟨.LSR, .absx, 7, false, true⟩, -- $5E
  ⟨.SRE, .absx, 7, false, false⟩, -- $5F
  ⟨.RTS, .imp, 6, false, true⟩, -- $60
  ⟨.ADC, .indx, 6, false, true⟩, -- $61
  ⟨.JAM, .imp, 3, false, false⟩, -- $62
  ⟨.RRA, .indx, 8, false, false⟩, -- $63
  ⟨.NOP, .zp, 3, false, false⟩, -- $64
  ⟨.ADC, .zp, 3, false, true⟩, -- $65
  ⟨.ROR, .zp, 5, false, true⟩, -- $66
  ⟨.RRA, .zp, 5, false, false⟩, -- $67
  ⟨.PLA, .imp, 4, false, true⟩, -- $68
  ⟨.ADC, .imm, 2, false, true⟩, -- $69
  ⟨.ROR, .acc, 2, false, true⟩, -- $6A
  ⟨.ARR, .imm, 2, false, false⟩, -- $6B
  ⟨.JMP, .ind, 5, false, true⟩, -- $6C
  ⟨.ADC, .abs, 4, false, true⟩, -- $6D
  ⟨.ROR, .abs, 6, false, true⟩, -- $6E
  ⟨.RRA, .abs, 6, false, false⟩, -- $6F
  ⟨.BVS, .rel, 2, false, true⟩, -- $70
  ⟨.ADC, .indy, 5, true, true⟩, -- $71
  ⟨.JAM, .imp, 3, false, false⟩, -- $72
  ⟨.RRA, .indy, 8, false, false⟩, -- $73
  ⟨.NOP, .zpx, 4, false, false⟩, -- $74
  ⟨.ADC, .zpx, 4, false, true⟩, -- $75
  ⟨.ROR, .zpx, 6, false, true⟩, -- $76
  ⟨.RRA, .zpx, 6, false, false⟩, -- $77
  ⟨.SEI, .imp, 2, false, true⟩, -- $78
  ⟨.ADC, .absy, 4, true, true⟩, -- $79
  ⟨.NOP, .imp, 2, false, false⟩, -- $7A
  ⟨.RRA, .absy, 7, false, false⟩, -- $7B
  ⟨.NOP, .absx, 4, true, false⟩, -- $7C
  ⟨.ADC, .absx, 4, true, true⟩, -- $7D
  ⟨.ROR, .absx, 7, false, true⟩, -- $7E
  ⟨.RRA, .absx, 7, false, false⟩, -- $7F
  ⟨.NOP, .imm, 2, false, false⟩, -- $80
  ⟨.STA, .indx, 6, false, true⟩, -- $81
  ⟨.NOP, .imm, 2, false, false⟩, -- $82
  ⟨.SAX, .indx, 6, false, false⟩, -- $83
  ⟨.STY, .zp, 3, false, true⟩, -- $84
  ⟨.STA, .zp, 3, false, true⟩, -- $85
  ⟨.STX, .zp, 3, false, true⟩, -- $86
  ⟨.SAX, .zp, 3, false, false⟩, -- $87
  ⟨.DEY, .imp, 2, false, true⟩, -- $88
  ⟨.NOP, .imm, 2, false, false⟩, -- $89
  ⟨.TXA, .imp, 2, false, true⟩, -- $8A
  ⟨.XAA, .imm, 2, false, false⟩, -- $8B
  ⟨.STY, .abs, 4, false, true⟩, -- $8C
  ⟨.STA, .abs, 4, false, true⟩, -- $8D
  ⟨.STX, .abs, 4, false, true⟩, -- $8E
  ⟨.SAX, .abs, 4, false, false⟩, -- $8F
  ⟨.BCC, .rel, 2, false, true⟩, -- $90
  ⟨.STA, .indy, 6, false, true⟩, -- $91
  ⟨.JAM, .imp, 3, false, false⟩, -- $92
  ⟨.AHX, .indy, 6, false, false⟩, -- $93
  ⟨.STY, .zpx, 4, false, true⟩, -- $94
  ⟨.STA, .zpx, 4, false, true⟩, -- $95
  ⟨.STX, .zpy, 4, false, true⟩, -- $96
  ⟨.SAX, .zpy, 4, false, false⟩, -- $97
  ⟨.TYA, .imp, 2, false, true⟩, -- $98
  ⟨.STA, .absy, 5, false, true⟩, -- $99
  ⟨.TXS, .imp, 2, false, true⟩, -- $9A
  ⟨.TAS, .absy, 5, false, false⟩, -- $9B
  ⟨.SHY, .absx, 5, false, false⟩, -- $9C
  ⟨.STA, .absx, 5, false, true⟩, -- $9D
  ⟨.SHX, .absy, 5, false, false⟩, -- $9E
  ⟨.AHX, .absy, 5, false, false⟩, -- $9F
  ⟨.LDY, .imm, 2, false, true⟩, -- $A0
  ⟨.LDA, .indx, 6, false, true⟩, -- $A1
  ⟨.LDX, .imm, 2, false, true⟩, -- $A2
  ⟨.LAX, .indx, 6, false, false⟩, -- $A3
  ⟨.LDY, .zp, 3, false, true⟩, -- $A4
  ⟨.LDA, .zp, 3, false, true⟩, -- $A5
  ⟨.LDX, .zp, 3, false, true⟩, -- $A6
  ⟨.LAX, .zp, 3, false, false⟩, -- $A7
  ⟨.TAY, .imp, 2, false, true⟩, -- $A8
  ⟨.LDA, .imm, 2, false, true⟩, -- $A9
  ⟨.TAX, .imp, 2, false, true⟩, -- $AA
  ⟨.LAX, .imm, 2, false, false⟩, -- $AB
  ⟨.LDY, .abs, 4, false, true⟩, -- $AC
  ⟨.LDA, .abs, 4, false, true⟩, -- $AD
  ⟨.LDX, .abs, 4, false, true⟩, -- $AE
  ⟨.LAX, .abs, 4, false, false⟩, -- $AF
  ⟨.BCS, .rel, 2, false, true⟩, -- $B0
  ⟨.LDA, .indy, 5, true, true⟩, -- $B1
  ⟨.JAM, .imp, 3, false, false⟩, -- $B2
  ⟨.LAX, .indy, 5, true, false⟩, -- $B3
  ⟨.LDY, .zpx, 4, false, true⟩, -- $B4
  ⟨.LDA, .zpx, 4, false, true⟩, -- $B5
  ⟨.LDX, .zpy, 4, false, true⟩, -- $B6
  ⟨.LAX, .zpy, 4, false, false⟩, -- $B7
  ⟨.CLV, .imp, 2, false, true⟩, -- $B8
  ⟨.LDA, .absy, 4, true, true⟩, -- $B9
  ⟨.TSX, .imp, 2, false, true⟩, -- $BA
  ⟨.LAS, .absy, 4, true, false⟩, -- $BB
  ⟨.LDY, .absx, 4, true, true⟩, -- $BC
  ⟨.LDA, .absx, 4, true, true⟩, -- $BD
  ⟨.LDX, .absy, 4, true, true⟩, -- $BE
  ⟨.LAX, .absy, 4, true, false⟩, -- $BF
  ⟨.CPY, .imm, 2, false, true⟩, -- $C0
  ⟨.CMP, .indx, 6, false, true⟩, -- $C1
  ⟨.NOP, .imm, 2, false, false⟩, -- $C2
  ⟨.DCP, .indx, 8, false, false⟩, -- $C3
  ⟨.CPY, .zp, 3, false, true⟩, -- $C4
  ⟨.CMP, .zp, 3, false, true⟩, -- $C5
  ⟨.DEC, .zp, 5, false, true⟩, -- $C6
  ⟨.DCP, .zp, 5, false, false⟩, -- $C7
  ⟨.INY, .imp, 2, false, true⟩, -- $C8
  ⟨.CMP, .imm, 2, false, true⟩, -- $C9
  ⟨.DEX, .imp, 2, false, true⟩, -- $CA
  ⟨.SBX, .imm, 2, false, false⟩, -- $CB
  ⟨.CPY, .abs, 4, false, true⟩, -- $CC
  ⟨.CMP, .abs, 4, false, true⟩, -- $CD
  ⟨.DEC, .abs, 6, false, true⟩, -- $CE
  ⟨.DCP, .abs, 6, false, false⟩, -- $CF
  ⟨.BNE, .rel, 2, false, true⟩, -- $D0
  ⟨.CMP, .indy, 5, true, true⟩, -- $D1
  ⟨.JAM, .imp, 3, false, false⟩, -- $D2
  ⟨.DCP, .indy, 8, false, false⟩, -- $D3
  ⟨.NOP, .zpx, 4, false, false⟩, -- $D4
  ⟨.CMP, .zpx, 4, false, true⟩, -- $D5
  ⟨.DEC, .zpx, 6, false, true⟩, -- $D6
  ⟨.DCP, .zpx, 6, false, false⟩, -- $D7
  ⟨.CLD, .imp, 2, false, true⟩, -- $D8
  ⟨.CMP, .absy, 4, true, true⟩, -- $D9
  ⟨.NOP, .imp, 2, false, false⟩, -- $DA
  ⟨.DCP, .absy, 7, false, false⟩, -- $DB
  ⟨.NOP, .absx, 4, true, false⟩, -- $DC
  ⟨.CMP, .absx, 4, true, true⟩, -- $DD
  ⟨.DEC, .absx, 7, false, true⟩, -- $DE
  ⟨.DCP, .absx, 7, false, false⟩, -- $DF
  ⟨.CPX, .imm, 2, false, true⟩, -- $E0
  ⟨.SBC, .indx, 6, false, true⟩, -- $E1
  ⟨.NOP, .imm, 2, false, false⟩, -- $E2
  ⟨.ISC, .indx, 8, false, false⟩, -- $E3
  ⟨.CPX, .zp, 3, false, true⟩, -- $E4
  ⟨.SBC, .zp, 3, false, true⟩, -- $E5
  ⟨.INC, .zp, 5, false, true⟩, -- $E6
  ⟨.ISC, .zp, 5, false, false⟩, -- $E7
  ⟨.INX, .imp, 2, false, true⟩, -- $E8
  ⟨.SBC, .imm, 2, false, true⟩, -- $E9
  ⟨.NOP, .imp, 2, false, true⟩, -- $EA
  ⟨.SBC, .imm, 2, false, false⟩, -- $EB
  ⟨.CPX, .abs, 4, false, true⟩, -- $EC
  ⟨.SBC, .abs, 4, false, true⟩, -- $ED
  ⟨.INC, .abs, 6, false, true⟩, -- $EE
  ⟨.ISC, .abs, 6, false, false⟩, -- $EF
  ⟨.BEQ, .rel, 2, false, true⟩, -- $F0
  ⟨.SBC, .indy, 5, true, true⟩, -- $F1
  ⟨.JAM, .imp, 3, false, false⟩, -- $F2
  ⟨.ISC, .indy, 8, false, false⟩, -- $F3
  ⟨.NOP, .zpx, 4, false, false⟩, -- $F4
  ⟨.SBC, .zpx, 4, false, true⟩, -- $F5
  ⟨.INC, .zpx, 6, false, true⟩, -- $F6
  ⟨.ISC, .zpx, 6, false, false⟩, -- $F7
  ⟨.SED, .imp, 2, false, true⟩, -- $F8
  ⟨.SBC, .absy, 4, true, true⟩, -- $F9
  ⟨.NOP, .imp, 2, false, false⟩, -- $FA
  ⟨.ISC, .absy, 7, false, false⟩, -- $FB
  ⟨.NOP, .absx, 4, true, false⟩, -- $FC
  ⟨.SBC, .absx, 4, true, true⟩, -- $FD
  ⟨.INC, .absx, 7, false, true⟩, -- $FE
  ⟨.ISC, .absx, 7, false, false⟩ -- $FF
]

/-- The 256-entry opcode table, indexed by opcode byte. -/
def table : Vector Entry 256 := ⟨tableArray, by decide +kernel⟩

/-- Decode an opcode byte. -/
@[inline] def decode (op : UInt8) : Entry :=
  table[op.toNat]'(UInt8.toNat_lt op)

/-- Decode an opcode given as `Fin 256` (convenient for `decide` over all opcodes). -/
@[inline] def decodeFin (i : Fin 256) : Entry := table[i]

/-- The 12 JAM opcodes. -/
def jamOpcodes : List UInt8 :=
  [0x02, 0x12, 0x22, 0x32, 0x42, 0x52, 0x62, 0x72, 0x92, 0xB2, 0xD2, 0xF2]

/-! ### Sanity facts -/

example : decode 0xA9 = ⟨.LDA, .imm, 2, false, true⟩ := by decide
example : decode 0xBD = ⟨.LDA, .absx, 4, true, true⟩ := by decide
example : decode 0x9D = ⟨.STA, .absx, 5, false, true⟩ := by decide
example : decode 0x00 = ⟨.BRK, .imp, 7, false, true⟩ := by decide
example : decode 0xEB = ⟨.SBC, .imm, 2, false, false⟩ := by decide
example : decode 0xB3 = ⟨.LAX, .indy, 5, true, false⟩ := by decide
example : decode 0xD0 = ⟨.BNE, .rel, 2, false, true⟩ := by decide

/-- Exactly 151 official opcodes. -/
example : ((List.finRange 256).filter (fun i => (decodeFin i).official)).length = 151 := by
  decide +kernel

/-- `JAM` decodes from exactly the 12 listed opcodes. -/
example : ∀ i : Fin 256,
    (decodeFin i).instr = .JAM ↔ (i.val % 16 = 2 ∧ i.val / 16 ∉ [8, 0xA, 0xC, 0xE]) := by
  decide +kernel

/-- Page-cross penalty only on indexed modes. -/
example : ∀ i : Fin 256, (decodeFin i).pageCross = true →
    (decodeFin i).mode = .absx ∨ (decodeFin i).mode = .absy ∨ (decodeFin i).mode = .indy := by
  decide +kernel

end Nes.Cpu
