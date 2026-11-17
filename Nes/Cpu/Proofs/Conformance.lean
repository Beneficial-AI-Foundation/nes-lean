import Nes.Cpu.Isa

/-!
# `Nes.Cpu.Proofs.Conformance` — T-CPU-8 (SingleStepTests cases as theorems)

## Spec

* A `HarteCase` is one SingleStepTests (`nes6502`) case transcribed verbatim: initial and final
  registers, the listed initial and final RAM cells, and the cycle count (the length of the
  case's `cycles` bus trace).
* `HarteCase.Holds c` is *stronger* than the test: for **every** memory `m` whose listed initial
  cells hold the listed values (all other 65 536 − k bytes arbitrary), `step c.init m` returns
  exactly the state `c.final`, a memory whose listed final cells hold the listed values, and
  `c.cycles` cycles. So each case also shows the instruction reads nothing outside its cells.
* Each `T_CPU_8_<op>_<name>` proves `Holds` for one case per instruction class. Proof method
  (`harte`): symbolic execution — `simp` unfolds `step`/`resolve`/`exec`, rewrites reads of `m`
  with the case's hypotheses and reads-after-writes with `harte_read_write`, folds the UInt
  arithmetic on literals; the decoded entry is given by a per-case `rfl` lemma `hd`, and any
  residual closed proposition is closed by `decide`. No native (compiled) evaluation is trusted.
* Why not `decide +kernel` on a concrete memory: the kernel evaluates `Vector`/`Array` through
  `List`, so a 64 KiB memory costs a walk to each address: 9 s for one LDA #imm case, 30 s for
  one STA abs case. The symbolic method takes ≈ 0.1 s per case.
* Source: SingleStepTests ProcessorTests (MIT), `nes6502/v1/<op>.json` at commit `bb11756`;
  the first case of each file, except BNE where the first *taken, page-crossing* case
  (4 cycles) is used. For JAM the data leaves `halted` implicit; our final state records
  `halted := true`.
-/

namespace Nes.Cpu.Proofs

open Nes.Cpu

/-- Reading back after a write: the written value at the written address, the old one elsewhere. -/
theorem harte_read_write (m : Mem) (a b : UInt16) (v : UInt8) :
    (m.write a v).read b = if a = b then v else m.read b := by
  simp only [Mem.read, Mem.write, Vector.getElem_set, UInt16.toNat_inj]

/-- One SingleStepTests case: registers, listed RAM cells, cycle count. -/
structure HarteCase where
  init : State
  initRam : List (UInt16 × UInt8)
  final : State
  finalRam : List (UInt16 × UInt8)
  cycles : Nat

/-- For every memory holding the case's initial cells, `step` yields the final registers, the
final cells and the cycle count. -/
def HarteCase.Holds (c : HarteCase) : Prop :=
  ∀ m : Mem, (∀ cell ∈ c.initRam, m.read cell.1 = cell.2) →
    let r := step c.init m
    r.1 = c.final ∧ (∀ cell ∈ c.finalRam, r.2.1.read cell.1 = cell.2) ∧ r.2.2 = c.cycles

/-- Symbolically execute `step` on a memory known only through the case's initial cells. Uses the
hypotheses in context (the decoded-entry lemma `hd`). -/
macro "harte" : tactic => `(tactic| (
  unfold HarteCase.Holds
  intro m h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h ⊢
  simp [step, exec, resolve, extraCycles, Mem.read16, push, pull, harte_read_write,
    zpPtr, zpIndexed, absIndexed, indirectBug, branchTarget, branchCond, shiftOp, AddrMode.len,
    State.ldA, State.arith, State.compare, unstableStore, UInt16.ofLoHi, UInt16.hi, UInt16.lo, *]
  all_goals decide))

/-- LDA immediate (load). Case `"a9 c3 7a"`, `nes6502/v1/a9.json`. -/
theorem T_CPU_8_a9_lda_imm : HarteCase.Holds
    { init := { pc := 0x83AE, sp := 0xD7, a := 0x16, x := 0xD6, y := 0x09, p := 0xA2, halted := false }
      initRam := [(0x83AE, 0xA9), (0x83AF, 0xC3), (0x83B0, 0x7A)]
      final := { pc := 0x83B0, sp := 0xD7, a := 0xC3, x := 0xD6, y := 0x09, p := 0xA0, halted := false }
      finalRam := [(0x83AE, 0xA9), (0x83AF, 0xC3), (0x83B0, 0x7A)]
      cycles := 2 } := by
  have hd : decode 0xA9 = ⟨.LDA, .imm, 2, false, true⟩ := rfl
  harte

/-- LDA abs,X (load, indexed). Case `"bd 48 17"`, `nes6502/v1/bd.json`. -/
theorem T_CPU_8_bd_lda_absx : HarteCase.Holds
    { init := { pc := 0x252A, sp := 0xF3, a := 0x31, x := 0x60, y := 0x5E, p := 0x26, halted := false }
      initRam := [(0x252A, 0xBD), (0x252B, 0x48), (0x252C, 0x17), (0x17A8, 0x29), (0x252D, 0x43)]
      final := { pc := 0x252D, sp := 0xF3, a := 0x29, x := 0x60, y := 0x5E, p := 0x24, halted := false }
      finalRam := [(0x17A8, 0x29), (0x252A, 0xBD), (0x252B, 0x48), (0x252C, 0x17), (0x252D, 0x43)]
      cycles := 4 } := by
  have hd : decode 0xBD = ⟨.LDA, .absx, 4, true, true⟩ := rfl
  harte

/-- STA absolute (store). Case `"8d aa 66"`, `nes6502/v1/8d.json`. -/
theorem T_CPU_8_8d_sta_abs : HarteCase.Holds
    { init := { pc := 0xC299, sp := 0x77, a := 0x10, x := 0x66, y := 0x9B, p := 0xE8, halted := false }
      initRam := [(0xC299, 0x8D), (0xC29A, 0xAA), (0xC29B, 0x66), (0xC29C, 0xD5)]
      final := { pc := 0xC29C, sp := 0x77, a := 0x10, x := 0x66, y := 0x9B, p := 0xE8, halted := false }
      finalRam := [(0x66AA, 0x10), (0xC299, 0x8D), (0xC29A, 0xAA), (0xC29B, 0x66), (0xC29C, 0xD5)]
      cycles := 4 } := by
  have hd : decode 0x8D = ⟨.STA, .abs, 4, false, true⟩ := rfl
  harte

/-- STA (zp),Y (store, indirect indexed). Case `"91 12 c4"`, `nes6502/v1/91.json`. -/
theorem T_CPU_8_91_sta_indy : HarteCase.Holds
    { init := { pc := 0x4A1B, sp := 0xB1, a := 0x32, x := 0xCA, y := 0x5E, p := 0xE1, halted := false }
      initRam := [(0x4A1B, 0x91), (0x4A1C, 0x12), (0x4A1D, 0xC4), (0x0012, 0x1D), (0x0013, 0xA0), (0xA07B, 0x9B)]
      final := { pc := 0x4A1D, sp := 0xB1, a := 0x32, x := 0xCA, y := 0x5E, p := 0xE1, halted := false }
      finalRam := [(0x0012, 0x1D), (0x0013, 0xA0), (0x4A1B, 0x91), (0x4A1C, 0x12), (0x4A1D, 0xC4), (0xA07B, 0x32)]
      cycles := 6 } := by
  have hd : decode 0x91 = ⟨.STA, .indy, 6, false, true⟩ := rfl
  harte

/-- ADC immediate (ALU/ADC). Case `"69 4a c2"`, `nes6502/v1/69.json`. -/
theorem T_CPU_8_69_adc_imm : HarteCase.Holds
    { init := { pc := 0x6856, sp := 0x7C, a := 0x7E, x := 0xB8, y := 0xDD, p := 0x6C, halted := false }
      initRam := [(0x6856, 0x69), (0x6857, 0x4A), (0x6858, 0xC2)]
      final := { pc := 0x6858, sp := 0x7C, a := 0xC8, x := 0xB8, y := 0xDD, p := 0xEC, halted := false }
      finalRam := [(0x6856, 0x69), (0x6857, 0x4A), (0x6858, 0xC2)]
      cycles := 2 } := by
  have hd : decode 0x69 = ⟨.ADC, .imm, 2, false, true⟩ := rfl
  harte

/-- SBC immediate (SBC). Case `"e9 20 ae"`, `nes6502/v1/e9.json`. -/
theorem T_CPU_8_e9_sbc_imm : HarteCase.Holds
    { init := { pc := 0xEA78, sp := 0xAB, a := 0x32, x := 0xA8, y := 0xB3, p := 0x6A, halted := false }
      initRam := [(0xEA78, 0xE9), (0xEA79, 0x20), (0xEA7A, 0xAE)]
      final := { pc := 0xEA7A, sp := 0xAB, a := 0x11, x := 0xA8, y := 0xB3, p := 0x29, halted := false }
      finalRam := [(0xEA78, 0xE9), (0xEA79, 0x20), (0xEA7A, 0xAE)]
      cycles := 2 } := by
  have hd : decode 0xE9 = ⟨.SBC, .imm, 2, false, true⟩ := rfl
  harte

/-- AND absolute (logic). Case `"2d 13 74"`, `nes6502/v1/2d.json`. -/
theorem T_CPU_8_2d_and_abs : HarteCase.Holds
    { init := { pc := 0x57BB, sp := 0x5F, a := 0x96, x := 0x0F, y := 0x9B, p := 0xE3, halted := false }
      initRam := [(0x57BB, 0x2D), (0x57BC, 0x13), (0x57BD, 0x74), (0x7413, 0xDD), (0x57BE, 0x1A)]
      final := { pc := 0x57BE, sp := 0x5F, a := 0x94, x := 0x0F, y := 0x9B, p := 0xE1, halted := false }
      finalRam := [(0x57BB, 0x2D), (0x57BC, 0x13), (0x57BD, 0x74), (0x57BE, 0x1A), (0x7413, 0xDD)]
      cycles := 4 } := by
  have hd : decode 0x2D = ⟨.AND, .abs, 4, false, true⟩ := rfl
  harte

/-- BIT absolute (bit test). Case `"2c 9a 9c"`, `nes6502/v1/2c.json`. -/
theorem T_CPU_8_2c_bit_abs : HarteCase.Holds
    { init := { pc := 0xF449, sp := 0xBC, a := 0xD4, x := 0x4C, y := 0xFC, p := 0x24, halted := false }
      initRam := [(0xF449, 0x2C), (0xF44A, 0x9A), (0xF44B, 0x9C), (0x9C9A, 0xC4), (0xF44C, 0x8A)]
      final := { pc := 0xF44C, sp := 0xBC, a := 0xD4, x := 0x4C, y := 0xFC, p := 0xE4, halted := false }
      finalRam := [(0x9C9A, 0xC4), (0xF449, 0x2C), (0xF44A, 0x9A), (0xF44B, 0x9C), (0xF44C, 0x8A)]
      cycles := 4 } := by
  have hd : decode 0x2C = ⟨.BIT, .abs, 4, false, true⟩ := rfl
  harte

/-- CMP immediate (compare). Case `"c9 3d ea"`, `nes6502/v1/c9.json`. -/
theorem T_CPU_8_c9_cmp_imm : HarteCase.Holds
    { init := { pc := 0xBA01, sp := 0x5D, a := 0xE5, x := 0x32, y := 0x7C, p := 0xE7, halted := false }
      initRam := [(0xBA01, 0xC9), (0xBA02, 0x3D), (0xBA03, 0xEA)]
      final := { pc := 0xBA03, sp := 0x5D, a := 0xE5, x := 0x32, y := 0x7C, p := 0xE5, halted := false }
      finalRam := [(0xBA01, 0xC9), (0xBA02, 0x3D), (0xBA03, 0xEA)]
      cycles := 2 } := by
  have hd : decode 0xC9 = ⟨.CMP, .imm, 2, false, true⟩ := rfl
  harte

/-- ASL absolute (shift, RMW). Case `"0e 15 88"`, `nes6502/v1/0e.json`. -/
theorem T_CPU_8_0e_asl_abs : HarteCase.Holds
    { init := { pc := 0x69A2, sp := 0x12, a := 0x58, x := 0x67, y := 0x52, p := 0x2B, halted := false }
      initRam := [(0x69A2, 0x0E), (0x69A3, 0x15), (0x69A4, 0x88), (0x8815, 0xF0), (0x69A5, 0x23)]
      final := { pc := 0x69A5, sp := 0x12, a := 0x58, x := 0x67, y := 0x52, p := 0xA9, halted := false }
      finalRam := [(0x69A2, 0x0E), (0x69A3, 0x15), (0x69A4, 0x88), (0x69A5, 0x23), (0x8815, 0xE0)]
      cycles := 6 } := by
  have hd : decode 0x0E = ⟨.ASL, .abs, 6, false, true⟩ := rfl
  harte

/-- ROR accumulator (rotate). Case `"6a 40 0c"`, `nes6502/v1/6a.json`. -/
theorem T_CPU_8_6a_ror_acc : HarteCase.Holds
    { init := { pc := 0x6148, sp := 0x6A, a := 0x82, x := 0x70, y := 0xBC, p := 0x2C, halted := false }
      initRam := [(0x6148, 0x6A), (0x6149, 0x40), (0x614A, 0x0C)]
      final := { pc := 0x6149, sp := 0x6A, a := 0x41, x := 0x70, y := 0xBC, p := 0x2C, halted := false }
      finalRam := [(0x6148, 0x6A), (0x6149, 0x40), (0x614A, 0x0C)]
      cycles := 2 } := by
  have hd : decode 0x6A = ⟨.ROR, .acc, 2, false, true⟩ := rfl
  harte

/-- INC absolute (inc, RMW). Case `"ee c2 b7"`, `nes6502/v1/ee.json`. -/
theorem T_CPU_8_ee_inc_abs : HarteCase.Holds
    { init := { pc := 0xB5E6, sp := 0xED, a := 0x07, x := 0x12, y := 0xC9, p := 0x67, halted := false }
      initRam := [(0xB5E6, 0xEE), (0xB5E7, 0xC2), (0xB5E8, 0xB7), (0xB7C2, 0x63), (0xB5E9, 0x6A)]
      final := { pc := 0xB5E9, sp := 0xED, a := 0x07, x := 0x12, y := 0xC9, p := 0x65, halted := false }
      finalRam := [(0xB5E6, 0xEE), (0xB5E7, 0xC2), (0xB5E8, 0xB7), (0xB5E9, 0x6A), (0xB7C2, 0x64)]
      cycles := 6 } := by
  have hd : decode 0xEE = ⟨.INC, .abs, 6, false, true⟩ := rfl
  harte

/-- DEX (dec register). Case `"ca 3c 68"`, `nes6502/v1/ca.json`. -/
theorem T_CPU_8_ca_dex : HarteCase.Holds
    { init := { pc := 0xC699, sp := 0x78, a := 0xD3, x := 0x8F, y := 0x53, p := 0x6B, halted := false }
      initRam := [(0xC699, 0xCA), (0xC69A, 0x3C), (0xC69B, 0x68)]
      final := { pc := 0xC69A, sp := 0x78, a := 0xD3, x := 0x8E, y := 0x53, p := 0xE9, halted := false }
      finalRam := [(0xC699, 0xCA), (0xC69A, 0x3C), (0xC69B, 0x68)]
      cycles := 2 } := by
  have hd : decode 0xCA = ⟨.DEX, .imp, 2, false, true⟩ := rfl
  harte

/-- BNE taken across a page (branch). Case `"d0 c6 5d"`, `nes6502/v1/d0.json`. -/
theorem T_CPU_8_d0_bne : HarteCase.Holds
    { init := { pc := 0x7711, sp := 0x58, a := 0x70, x := 0xD9, y := 0xE5, p := 0x60, halted := false }
      initRam := [(0x7711, 0xD0), (0x7712, 0xC6), (0x7713, 0x5D), (0x77D9, 0x5D), (0x76D9, 0x3C)]
      final := { pc := 0x76D9, sp := 0x58, a := 0x70, x := 0xD9, y := 0xE5, p := 0x60, halted := false }
      finalRam := [(0x76D9, 0x3C), (0x7711, 0xD0), (0x7712, 0xC6), (0x7713, 0x5D), (0x77D9, 0x5D)]
      cycles := 4 } := by
  have hd : decode 0xD0 = ⟨.BNE, .rel, 2, false, true⟩ := rfl
  harte

/-- JMP absolute (jump). Case `"4c 7a 8b"`, `nes6502/v1/4c.json`. -/
theorem T_CPU_8_4c_jmp_abs : HarteCase.Holds
    { init := { pc := 0xBE13, sp := 0x9C, a := 0xE2, x := 0x5C, y := 0x52, p := 0x2C, halted := false }
      initRam := [(0xBE13, 0x4C), (0xBE14, 0x7A), (0xBE15, 0x8B), (0x8B7A, 0x6B)]
      final := { pc := 0x8B7A, sp := 0x9C, a := 0xE2, x := 0x5C, y := 0x52, p := 0x2C, halted := false }
      finalRam := [(0x8B7A, 0x6B), (0xBE13, 0x4C), (0xBE14, 0x7A), (0xBE15, 0x8B)]
      cycles := 3 } := by
  have hd : decode 0x4C = ⟨.JMP, .abs, 3, false, true⟩ := rfl
  harte

/-- JMP indirect (jump). Case `"6c a5 12"`, `nes6502/v1/6c.json`. -/
theorem T_CPU_8_6c_jmp_ind : HarteCase.Holds
    { init := { pc := 0xEB78, sp := 0x4D, a := 0x94, x := 0xE3, y := 0x61, p := 0xA8, halted := false }
      initRam := [(0xEB78, 0x6C), (0xEB79, 0xA5), (0xEB7A, 0x12), (0x12A5, 0x50), (0x12A6, 0x25), (0x2550, 0x68)]
      final := { pc := 0x2550, sp := 0x4D, a := 0x94, x := 0xE3, y := 0x61, p := 0xA8, halted := false }
      finalRam := [(0x12A5, 0x50), (0x12A6, 0x25), (0x2550, 0x68), (0xEB78, 0x6C), (0xEB79, 0xA5), (0xEB7A, 0x12)]
      cycles := 5 } := by
  have hd : decode 0x6C = ⟨.JMP, .ind, 5, false, true⟩ := rfl
  harte

/-- JSR (call). Case `"20 ab 9d"`, `nes6502/v1/20.json`. -/
theorem T_CPU_8_20_jsr : HarteCase.Holds
    { init := { pc := 0x98BF, sp := 0xEA, a := 0x85, x := 0x51, y := 0xF2, p := 0x67, halted := false }
      initRam := [(0x98BF, 0x20), (0x98C0, 0xAB), (0x98C1, 0x9D), (0x01EA, 0xC3), (0x9DAB, 0xB5)]
      final := { pc := 0x9DAB, sp := 0xE8, a := 0x85, x := 0x51, y := 0xF2, p := 0x67, halted := false }
      finalRam := [(0x01E9, 0xC1), (0x01EA, 0x98), (0x98BF, 0x20), (0x98C0, 0xAB), (0x98C1, 0x9D), (0x9DAB, 0xB5)]
      cycles := 6 } := by
  have hd : decode 0x20 = ⟨.JSR, .abs, 6, false, true⟩ := rfl
  harte

/-- RTS (return). Case `"60 8d 97"`, `nes6502/v1/60.json`. -/
theorem T_CPU_8_60_rts : HarteCase.Holds
    { init := { pc := 0xCDE1, sp := 0xF5, a := 0x50, x := 0x8A, y := 0x04, p := 0xEF, halted := false }
      initRam := [(0xCDE1, 0x60), (0xCDE2, 0x8D), (0xCDE3, 0x97), (0x01F5, 0xB8), (0x01F6, 0xC7), (0x01F7, 0xD9), (0xD9C7, 0xBC), (0xD9C8, 0x90)]
      final := { pc := 0xD9C8, sp := 0xF7, a := 0x50, x := 0x8A, y := 0x04, p := 0xEF, halted := false }
      finalRam := [(0x01F5, 0xB8), (0x01F6, 0xC7), (0x01F7, 0xD9), (0xCDE1, 0x60), (0xCDE2, 0x8D), (0xCDE3, 0x97), (0xD9C7, 0xBC), (0xD9C8, 0x90)]
      cycles := 6 } := by
  have hd : decode 0x60 = ⟨.RTS, .imp, 6, false, true⟩ := rfl
  harte

/-- PHA (stack push). Case `"48 06 3b"`, `nes6502/v1/48.json`. -/
theorem T_CPU_8_48_pha : HarteCase.Holds
    { init := { pc := 0x5FA3, sp := 0x5F, a := 0x98, x := 0xA9, y := 0x6E, p := 0xE5, halted := false }
      initRam := [(0x5FA3, 0x48), (0x5FA4, 0x06), (0x5FA5, 0x3B)]
      final := { pc := 0x5FA4, sp := 0x5E, a := 0x98, x := 0xA9, y := 0x6E, p := 0xE5, halted := false }
      finalRam := [(0x015F, 0x98), (0x5FA3, 0x48), (0x5FA4, 0x06), (0x5FA5, 0x3B)]
      cycles := 3 } := by
  have hd : decode 0x48 = ⟨.PHA, .imp, 3, false, true⟩ := rfl
  harte

/-- PLA (stack pull). Case `"68 34 89"`, `nes6502/v1/68.json`. -/
theorem T_CPU_8_68_pla : HarteCase.Holds
    { init := { pc := 0xE92C, sp := 0x36, a := 0x28, x := 0x50, y := 0x15, p := 0x69, halted := false }
      initRam := [(0xE92C, 0x68), (0xE92D, 0x34), (0xE92E, 0x89), (0x0136, 0x1E), (0x0137, 0x60)]
      final := { pc := 0xE92D, sp := 0x37, a := 0x60, x := 0x50, y := 0x15, p := 0x69, halted := false }
      finalRam := [(0x0136, 0x1E), (0x0137, 0x60), (0xE92C, 0x68), (0xE92D, 0x34), (0xE92E, 0x89)]
      cycles := 4 } := by
  have hd : decode 0x68 = ⟨.PLA, .imp, 4, false, true⟩ := rfl
  harte

/-- PHP (push status). Case `"08 7e 48"`, `nes6502/v1/08.json`. -/
theorem T_CPU_8_08_php : HarteCase.Holds
    { init := { pc := 0xB944, sp := 0xC8, a := 0x46, x := 0x2A, y := 0x60, p := 0xA4, halted := false }
      initRam := [(0xB944, 0x08), (0xB945, 0x7E), (0xB946, 0x48)]
      final := { pc := 0xB945, sp := 0xC7, a := 0x46, x := 0x2A, y := 0x60, p := 0xA4, halted := false }
      finalRam := [(0x01C8, 0xB4), (0xB944, 0x08), (0xB945, 0x7E), (0xB946, 0x48)]
      cycles := 3 } := by
  have hd : decode 0x08 = ⟨.PHP, .imp, 3, false, true⟩ := rfl
  harte

/-- PLP (pull status). Case `"28 87 5a"`, `nes6502/v1/28.json`. -/
theorem T_CPU_8_28_plp : HarteCase.Holds
    { init := { pc := 0xC561, sp := 0x3A, a := 0x1C, x := 0xC1, y := 0x4D, p := 0xE5, halted := false }
      initRam := [(0xC561, 0x28), (0xC562, 0x87), (0xC563, 0x5A), (0x013A, 0xAD), (0x013B, 0x88)]
      final := { pc := 0xC562, sp := 0x3B, a := 0x1C, x := 0xC1, y := 0x4D, p := 0xA8, halted := false }
      finalRam := [(0x013A, 0xAD), (0x013B, 0x88), (0xC561, 0x28), (0xC562, 0x87), (0xC563, 0x5A)]
      cycles := 4 } := by
  have hd : decode 0x28 = ⟨.PLP, .imp, 4, false, true⟩ := rfl
  harte

/-- BRK (interrupt). Case `"00 35 26"`, `nes6502/v1/00.json`. -/
theorem T_CPU_8_00_brk : HarteCase.Holds
    { init := { pc := 0xE881, sp := 0xF2, a := 0x04, x := 0x47, y := 0x38, p := 0x61, halted := false }
      initRam := [(0xE881, 0x00), (0xE882, 0x35), (0xE883, 0x26), (0xFFFE, 0x15), (0xFFFF, 0x23), (0x2315, 0xE5)]
      final := { pc := 0x2315, sp := 0xEF, a := 0x04, x := 0x47, y := 0x38, p := 0x65, halted := false }
      finalRam := [(0x01F0, 0x71), (0x01F1, 0x83), (0x01F2, 0xE8), (0x2315, 0xE5), (0xE881, 0x00), (0xE882, 0x35), (0xE883, 0x26), (0xFFFE, 0x15), (0xFFFF, 0x23)]
      cycles := 7 } := by
  have hd : decode 0x00 = ⟨.BRK, .imp, 7, false, true⟩ := rfl
  harte

/-- RTI (return from interrupt). Case `"40 6b a8"`, `nes6502/v1/40.json`. -/
theorem T_CPU_8_40_rti : HarteCase.Holds
    { init := { pc := 0x2BA4, sp := 0x8E, a := 0xB1, x := 0xF6, y := 0x74, p := 0xAD, halted := false }
      initRam := [(0x2BA4, 0x40), (0x2BA5, 0x6B), (0x2BA6, 0xA8), (0x018E, 0xA7), (0x018F, 0xAF), (0x0190, 0x3F), (0x0191, 0x9A), (0x9A3F, 0x26)]
      final := { pc := 0x9A3F, sp := 0x91, a := 0xB1, x := 0xF6, y := 0x74, p := 0xAF, halted := false }
      finalRam := [(0x018E, 0xA7), (0x018F, 0xAF), (0x0190, 0x3F), (0x0191, 0x9A), (0x2BA4, 0x40), (0x2BA5, 0x6B), (0x2BA6, 0xA8), (0x9A3F, 0x26)]
      cycles := 6 } := by
  have hd : decode 0x40 = ⟨.RTI, .imp, 6, false, true⟩ := rfl
  harte

/-- CLC (flags). Case `"18 2d db"`, `nes6502/v1/18.json`. -/
theorem T_CPU_8_18_clc : HarteCase.Holds
    { init := { pc := 0xB522, sp := 0xA9, a := 0x8A, x := 0x4B, y := 0x8F, p := 0xE0, halted := false }
      initRam := [(0xB522, 0x18), (0xB523, 0x2D), (0xB524, 0xDB)]
      final := { pc := 0xB523, sp := 0xA9, a := 0x8A, x := 0x4B, y := 0x8F, p := 0xE0, halted := false }
      finalRam := [(0xB522, 0x18), (0xB523, 0x2D), (0xB524, 0xDB)]
      cycles := 2 } := by
  have hd : decode 0x18 = ⟨.CLC, .imp, 2, false, true⟩ := rfl
  harte

/-- SEC (flags). Case `"38 b8 e1"`, `nes6502/v1/38.json`. -/
theorem T_CPU_8_38_sec : HarteCase.Holds
    { init := { pc := 0x580D, sp := 0x29, a := 0xA9, x := 0x78, y := 0xDE, p := 0x64, halted := false }
      initRam := [(0x580D, 0x38), (0x580E, 0xB8), (0x580F, 0xE1)]
      final := { pc := 0x580E, sp := 0x29, a := 0xA9, x := 0x78, y := 0xDE, p := 0x65, halted := false }
      finalRam := [(0x580D, 0x38), (0x580E, 0xB8), (0x580F, 0xE1)]
      cycles := 2 } := by
  have hd : decode 0x38 = ⟨.SEC, .imp, 2, false, true⟩ := rfl
  harte

/-- TAX (transfer). Case `"aa cf 8d"`, `nes6502/v1/aa.json`. -/
theorem T_CPU_8_aa_tax : HarteCase.Holds
    { init := { pc := 0x0248, sp := 0x70, a := 0xBF, x := 0x71, y := 0xC3, p := 0x2C, halted := false }
      initRam := [(0x0248, 0xAA), (0x0249, 0xCF), (0x024A, 0x8D)]
      final := { pc := 0x0249, sp := 0x70, a := 0xBF, x := 0xBF, y := 0xC3, p := 0xAC, halted := false }
      finalRam := [(0x0248, 0xAA), (0x0249, 0xCF), (0x024A, 0x8D)]
      cycles := 2 } := by
  have hd : decode 0xAA = ⟨.TAX, .imp, 2, false, true⟩ := rfl
  harte

/-- TXS (transfer to SP). Case `"9a 27 d7"`, `nes6502/v1/9a.json`. -/
theorem T_CPU_8_9a_txs : HarteCase.Holds
    { init := { pc := 0x1513, sp := 0xF9, a := 0x64, x := 0x59, y := 0xB9, p := 0xE0, halted := false }
      initRam := [(0x1513, 0x9A), (0x1514, 0x27), (0x1515, 0xD7)]
      final := { pc := 0x1514, sp := 0x59, a := 0x64, x := 0x59, y := 0xB9, p := 0xE0, halted := false }
      finalRam := [(0x1513, 0x9A), (0x1514, 0x27), (0x1515, 0xD7)]
      cycles := 2 } := by
  have hd : decode 0x9A = ⟨.TXS, .imp, 2, false, true⟩ := rfl
  harte

/-- LAX zp (unofficial load). Case `"a7 1d 86"`, `nes6502/v1/a7.json`. -/
theorem T_CPU_8_a7_lax_zp : HarteCase.Holds
    { init := { pc := 0x3DCE, sp := 0xA1, a := 0x27, x := 0xD7, y := 0x4E, p := 0xA2, halted := false }
      initRam := [(0x3DCE, 0xA7), (0x3DCF, 0x1D), (0x3DD0, 0x86), (0x001D, 0x95)]
      final := { pc := 0x3DD0, sp := 0xA1, a := 0x95, x := 0x95, y := 0x4E, p := 0xA0, halted := false }
      finalRam := [(0x001D, 0x95), (0x3DCE, 0xA7), (0x3DCF, 0x1D), (0x3DD0, 0x86)]
      cycles := 3 } := by
  have hd : decode 0xA7 = ⟨.LAX, .zp, 3, false, false⟩ := rfl
  harte

/-- DCP zp (unofficial RMW+compare). Case `"c7 ec 4b"`, `nes6502/v1/c7.json`. -/
theorem T_CPU_8_c7_dcp_zp : HarteCase.Holds
    { init := { pc := 0xF570, sp := 0x1E, a := 0x2C, x := 0x82, y := 0x7F, p := 0x2E, halted := false }
      initRam := [(0xF570, 0xC7), (0xF571, 0xEC), (0xF572, 0x4B), (0x00EC, 0xEB)]
      final := { pc := 0xF572, sp := 0x1E, a := 0x2C, x := 0x82, y := 0x7F, p := 0x2C, halted := false }
      finalRam := [(0x00EC, 0xEA), (0xF570, 0xC7), (0xF571, 0xEC), (0xF572, 0x4B)]
      cycles := 5 } := by
  have hd : decode 0xC7 = ⟨.DCP, .zp, 5, false, false⟩ := rfl
  harte

/-- JAM (halt). Case `"02 5e c8"`, `nes6502/v1/02.json`. -/
theorem T_CPU_8_02_jam : HarteCase.Holds
    { init := { pc := 0x6D29, sp := 0x4F, a := 0x67, x := 0xEA, y := 0x1F, p := 0xE1, halted := false }
      initRam := [(0x6D29, 0x02), (0x6D2A, 0x5E), (0x6D2B, 0xC8)]
      final := { pc := 0x6D29, sp := 0x4F, a := 0x67, x := 0xEA, y := 0x1F, p := 0xE1, halted := true }
      finalRam := [(0x6D29, 0x02), (0x6D2A, 0x5E), (0x6D2B, 0xC8)]
      cycles := 3 } := by
  have hd : decode 0x02 = ⟨.JAM, .imp, 3, false, false⟩ := rfl
  harte

end Nes.Cpu.Proofs
