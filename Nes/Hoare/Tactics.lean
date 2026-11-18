import Nes.Hoare.Rules

/-!
# `Nes.Hoare.Tactics` — discharging single instructions

## Spec

* `hoare_step` proves a one-instruction `Triple` / `CTriple` / `TripleM` goal
  `{P} e ⟶ x {Q}`: it applies `*.of_step`, introduces `s m hP hpc`, unfolds the `codeAt`
  facts in `hP` into byte equations, and symbolically executes `step s m` with `simp`:
  `s.halted = false` and `s.pc = e` from the context select the running branch and the opcode
  address, the opcode byte selects one of the 256 `dec_NN` lemmas, and reads of the operand
  bytes / read-after-write (`read_write`) are rewritten with the hypotheses. Literal address
  comparisons (`$0010 = $8002`) and UInt arithmetic on literals are folded by `simp`'s simprocs.
  Leftover goals (e.g. a flag formula, an `Agree` obligation) are left to the user;
  `hoare_step` never fails silently on a closed goal, it just may leave goals.
* `hoare_run n` does the same for `n` instructions of straight-line code at once
  (`Triple.of_steps n`, `steps_succ`): no intermediate assertions are needed.
* `hoare_simp` is the underlying `simp` call (usable after any manual unfolding).

Requirements on the precondition: it must give `s.halted = false` and the code bytes as
`codeAt m base [...]` (or as explicit `m.read a = b` conjuncts) with *literal* addresses; the
post-state's code bytes are re-derived through `read_write`, so stores into the code region
are handled (they would simply change the next opcode).

## Worked example

`LDA #$05; STA $10` at `$8000` (`A9 05 85 10`): `{halted = false ∧ code} $8000 ⟶ $8004
{m[$10] = 5}`, once by two `hoare_step`s glued with `Triple.seq` at `$8002` (intermediate
assertion `A = 5`), once by `hoare_run 2`, and with its cycle count (2 + 3 = 5) as a `CTriple`.
`ex_countdown` shows the loop rule on `loop: DEX; BNE loop`.
-/

namespace Nes.Hoare

open Nes Nes.Cpu Nes.Cpu.Proofs

/-! ## Register/flag views of the setters

`(s.setX b).f` for every setter (`setC … setN`, `setZN`) and every register and flag, so
`hoare_simp` keeps `setZN`/`setC` folded and still reads registers and flags through them
(flag results come out as `b`, `r == 0`, `r &&& 0x80 != 0`, or the old flag). -/

namespace FlagLemmas

theorem setC_a (s : State) (b : Bool) : (s.setC b).a = s.a := rfl
theorem setC_x (s : State) (b : Bool) : (s.setC b).x = s.x := rfl
theorem setC_y (s : State) (b : Bool) : (s.setC b).y = s.y := rfl
theorem setC_sp (s : State) (b : Bool) : (s.setC b).sp = s.sp := rfl
theorem setC_pc (s : State) (b : Bool) : (s.setC b).pc = s.pc := rfl
theorem setC_halted (s : State) (b : Bool) : (s.setC b).halted = s.halted := rfl
theorem setC_c (s : State) (b : Bool) : (s.setC b).c = b :=
  congrArg Flags.c (State.flags_setC s b)
theorem setC_z (s : State) (b : Bool) : (s.setC b).z = s.z :=
  congrArg Flags.z (State.flags_setC s b)
theorem setC_i (s : State) (b : Bool) : (s.setC b).i = s.i :=
  congrArg Flags.i (State.flags_setC s b)
theorem setC_d (s : State) (b : Bool) : (s.setC b).d = s.d :=
  congrArg Flags.d (State.flags_setC s b)
theorem setC_v (s : State) (b : Bool) : (s.setC b).v = s.v :=
  congrArg Flags.v (State.flags_setC s b)
theorem setC_n (s : State) (b : Bool) : (s.setC b).n = s.n :=
  congrArg Flags.n (State.flags_setC s b)
theorem setZ_a (s : State) (b : Bool) : (s.setZ b).a = s.a := rfl
theorem setZ_x (s : State) (b : Bool) : (s.setZ b).x = s.x := rfl
theorem setZ_y (s : State) (b : Bool) : (s.setZ b).y = s.y := rfl
theorem setZ_sp (s : State) (b : Bool) : (s.setZ b).sp = s.sp := rfl
theorem setZ_pc (s : State) (b : Bool) : (s.setZ b).pc = s.pc := rfl
theorem setZ_halted (s : State) (b : Bool) : (s.setZ b).halted = s.halted := rfl
theorem setZ_c (s : State) (b : Bool) : (s.setZ b).c = s.c :=
  congrArg Flags.c (State.flags_setZ s b)
theorem setZ_z (s : State) (b : Bool) : (s.setZ b).z = b :=
  congrArg Flags.z (State.flags_setZ s b)
theorem setZ_i (s : State) (b : Bool) : (s.setZ b).i = s.i :=
  congrArg Flags.i (State.flags_setZ s b)
theorem setZ_d (s : State) (b : Bool) : (s.setZ b).d = s.d :=
  congrArg Flags.d (State.flags_setZ s b)
theorem setZ_v (s : State) (b : Bool) : (s.setZ b).v = s.v :=
  congrArg Flags.v (State.flags_setZ s b)
theorem setZ_n (s : State) (b : Bool) : (s.setZ b).n = s.n :=
  congrArg Flags.n (State.flags_setZ s b)
theorem setI_a (s : State) (b : Bool) : (s.setI b).a = s.a := rfl
theorem setI_x (s : State) (b : Bool) : (s.setI b).x = s.x := rfl
theorem setI_y (s : State) (b : Bool) : (s.setI b).y = s.y := rfl
theorem setI_sp (s : State) (b : Bool) : (s.setI b).sp = s.sp := rfl
theorem setI_pc (s : State) (b : Bool) : (s.setI b).pc = s.pc := rfl
theorem setI_halted (s : State) (b : Bool) : (s.setI b).halted = s.halted := rfl
theorem setI_c (s : State) (b : Bool) : (s.setI b).c = s.c :=
  congrArg Flags.c (State.flags_setI s b)
theorem setI_z (s : State) (b : Bool) : (s.setI b).z = s.z :=
  congrArg Flags.z (State.flags_setI s b)
theorem setI_i (s : State) (b : Bool) : (s.setI b).i = b :=
  congrArg Flags.i (State.flags_setI s b)
theorem setI_d (s : State) (b : Bool) : (s.setI b).d = s.d :=
  congrArg Flags.d (State.flags_setI s b)
theorem setI_v (s : State) (b : Bool) : (s.setI b).v = s.v :=
  congrArg Flags.v (State.flags_setI s b)
theorem setI_n (s : State) (b : Bool) : (s.setI b).n = s.n :=
  congrArg Flags.n (State.flags_setI s b)
theorem setD_a (s : State) (b : Bool) : (s.setD b).a = s.a := rfl
theorem setD_x (s : State) (b : Bool) : (s.setD b).x = s.x := rfl
theorem setD_y (s : State) (b : Bool) : (s.setD b).y = s.y := rfl
theorem setD_sp (s : State) (b : Bool) : (s.setD b).sp = s.sp := rfl
theorem setD_pc (s : State) (b : Bool) : (s.setD b).pc = s.pc := rfl
theorem setD_halted (s : State) (b : Bool) : (s.setD b).halted = s.halted := rfl
theorem setD_c (s : State) (b : Bool) : (s.setD b).c = s.c :=
  congrArg Flags.c (State.flags_setD s b)
theorem setD_z (s : State) (b : Bool) : (s.setD b).z = s.z :=
  congrArg Flags.z (State.flags_setD s b)
theorem setD_i (s : State) (b : Bool) : (s.setD b).i = s.i :=
  congrArg Flags.i (State.flags_setD s b)
theorem setD_d (s : State) (b : Bool) : (s.setD b).d = b :=
  congrArg Flags.d (State.flags_setD s b)
theorem setD_v (s : State) (b : Bool) : (s.setD b).v = s.v :=
  congrArg Flags.v (State.flags_setD s b)
theorem setD_n (s : State) (b : Bool) : (s.setD b).n = s.n :=
  congrArg Flags.n (State.flags_setD s b)
theorem setV_a (s : State) (b : Bool) : (s.setV b).a = s.a := rfl
theorem setV_x (s : State) (b : Bool) : (s.setV b).x = s.x := rfl
theorem setV_y (s : State) (b : Bool) : (s.setV b).y = s.y := rfl
theorem setV_sp (s : State) (b : Bool) : (s.setV b).sp = s.sp := rfl
theorem setV_pc (s : State) (b : Bool) : (s.setV b).pc = s.pc := rfl
theorem setV_halted (s : State) (b : Bool) : (s.setV b).halted = s.halted := rfl
theorem setV_c (s : State) (b : Bool) : (s.setV b).c = s.c :=
  congrArg Flags.c (State.flags_setV s b)
theorem setV_z (s : State) (b : Bool) : (s.setV b).z = s.z :=
  congrArg Flags.z (State.flags_setV s b)
theorem setV_i (s : State) (b : Bool) : (s.setV b).i = s.i :=
  congrArg Flags.i (State.flags_setV s b)
theorem setV_d (s : State) (b : Bool) : (s.setV b).d = s.d :=
  congrArg Flags.d (State.flags_setV s b)
theorem setV_v (s : State) (b : Bool) : (s.setV b).v = b :=
  congrArg Flags.v (State.flags_setV s b)
theorem setV_n (s : State) (b : Bool) : (s.setV b).n = s.n :=
  congrArg Flags.n (State.flags_setV s b)
theorem setN_a (s : State) (b : Bool) : (s.setN b).a = s.a := rfl
theorem setN_x (s : State) (b : Bool) : (s.setN b).x = s.x := rfl
theorem setN_y (s : State) (b : Bool) : (s.setN b).y = s.y := rfl
theorem setN_sp (s : State) (b : Bool) : (s.setN b).sp = s.sp := rfl
theorem setN_pc (s : State) (b : Bool) : (s.setN b).pc = s.pc := rfl
theorem setN_halted (s : State) (b : Bool) : (s.setN b).halted = s.halted := rfl
theorem setN_c (s : State) (b : Bool) : (s.setN b).c = s.c :=
  congrArg Flags.c (State.flags_setN s b)
theorem setN_z (s : State) (b : Bool) : (s.setN b).z = s.z :=
  congrArg Flags.z (State.flags_setN s b)
theorem setN_i (s : State) (b : Bool) : (s.setN b).i = s.i :=
  congrArg Flags.i (State.flags_setN s b)
theorem setN_d (s : State) (b : Bool) : (s.setN b).d = s.d :=
  congrArg Flags.d (State.flags_setN s b)
theorem setN_v (s : State) (b : Bool) : (s.setN b).v = s.v :=
  congrArg Flags.v (State.flags_setN s b)
theorem setN_n (s : State) (b : Bool) : (s.setN b).n = b :=
  congrArg Flags.n (State.flags_setN s b)
theorem setZN_a (s : State) (r : UInt8) : (s.setZN r).a = s.a := rfl
theorem setZN_x (s : State) (r : UInt8) : (s.setZN r).x = s.x := rfl
theorem setZN_y (s : State) (r : UInt8) : (s.setZN r).y = s.y := rfl
theorem setZN_sp (s : State) (r : UInt8) : (s.setZN r).sp = s.sp := rfl
theorem setZN_pc (s : State) (r : UInt8) : (s.setZN r).pc = s.pc := rfl
theorem setZN_halted (s : State) (r : UInt8) : (s.setZN r).halted = s.halted := rfl
theorem setZN_c (s : State) (r : UInt8) : (s.setZN r).c = s.c :=
  congrArg Flags.c (State.flags_setZN s r)
theorem setZN_z (s : State) (r : UInt8) : (s.setZN r).z = (r == 0) :=
  congrArg Flags.z (State.flags_setZN s r)
theorem setZN_i (s : State) (r : UInt8) : (s.setZN r).i = s.i :=
  congrArg Flags.i (State.flags_setZN s r)
theorem setZN_d (s : State) (r : UInt8) : (s.setZN r).d = s.d :=
  congrArg Flags.d (State.flags_setZN s r)
theorem setZN_v (s : State) (r : UInt8) : (s.setZN r).v = s.v :=
  congrArg Flags.v (State.flags_setZN s r)
theorem setZN_n (s : State) (r : UInt8) : (s.setZN r).n = (r &&& 0x80 != 0) :=
  congrArg Flags.n (State.flags_setZN s r)

/-- A structure literal whose status byte is some `s.p` has `s`'s flags. -/
theorem mk_p_c (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).c = s.c := rfl
theorem mk_p_z (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).z = s.z := rfl
theorem mk_p_i (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).i = s.i := rfl
theorem mk_p_d (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).d = s.d := rfl
theorem mk_p_v (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).v = s.v := rfl
theorem mk_p_n (a x y sp : UInt8) (pc : UInt16) (h : Bool) (s : State) :
    (State.mk a x y sp pc s.p h).n = s.n := rfl

end FlagLemmas

open FlagLemmas in
set_option maxRecDepth 8000 in
/-- Symbolic execution of `step` on a memory known through hypotheses. -/
macro "hoare_simp" : tactic => `(tactic| (
  set_option maxRecDepth 8000 in
  simp [step, exec, resolve, extraCycles, Mem.read16, push, pull, read_write,
    zpPtr, zpIndexed, absIndexed, indirectBug, branchTarget, branchCond, shiftOp, AddrMode.len,
    State.ldA, State.arith, State.compare, unstableStore, UInt16.ofLoHi, UInt16.hi, UInt16.lo,
    codeAt_cons, codeAt_nil, Alu.fast.inc, Alu.fast.dec, Alu.fast.cmp, Alu.fast.asl, Alu.fast.lsr,
    mk_p_c, mk_p_z, mk_p_i, mk_p_d, mk_p_v, mk_p_n,
    setC_a, setC_x, setC_y, setC_sp, setC_pc, setC_halted, setC_c, setC_z,
    setC_i, setC_d, setC_v, setC_n, setZ_a, setZ_x, setZ_y, setZ_sp,
    setZ_pc, setZ_halted, setZ_c, setZ_z, setZ_i, setZ_d, setZ_v, setZ_n,
    setI_a, setI_x, setI_y, setI_sp, setI_pc, setI_halted, setI_c, setI_z,
    setI_i, setI_d, setI_v, setI_n, setD_a, setD_x, setD_y, setD_sp,
    setD_pc, setD_halted, setD_c, setD_z, setD_i, setD_d, setD_v, setD_n,
    setV_a, setV_x, setV_y, setV_sp, setV_pc, setV_halted, setV_c, setV_z,
    setV_i, setV_d, setV_v, setV_n, setN_a, setN_x, setN_y, setN_sp,
    setN_pc, setN_halted, setN_c, setN_z, setN_i, setN_d, setN_v, setN_n,
    setZN_a, setZN_x, setZN_y, setZN_sp, setZN_pc, setZN_halted, setZN_c, setZN_z,
    setZN_i, setZN_d, setZN_v, setZN_n,
      dec_00, dec_01, dec_02, dec_03, dec_04, dec_05, dec_06, dec_07, dec_08, dec_09, dec_0A, dec_0B,
      dec_0C, dec_0D, dec_0E, dec_0F, dec_10, dec_11, dec_12, dec_13, dec_14, dec_15, dec_16, dec_17,
      dec_18, dec_19, dec_1A, dec_1B, dec_1C, dec_1D, dec_1E, dec_1F, dec_20, dec_21, dec_22, dec_23,
      dec_24, dec_25, dec_26, dec_27, dec_28, dec_29, dec_2A, dec_2B, dec_2C, dec_2D, dec_2E, dec_2F,
      dec_30, dec_31, dec_32, dec_33, dec_34, dec_35, dec_36, dec_37, dec_38, dec_39, dec_3A, dec_3B,
      dec_3C, dec_3D, dec_3E, dec_3F, dec_40, dec_41, dec_42, dec_43, dec_44, dec_45, dec_46, dec_47,
      dec_48, dec_49, dec_4A, dec_4B, dec_4C, dec_4D, dec_4E, dec_4F, dec_50, dec_51, dec_52, dec_53,
      dec_54, dec_55, dec_56, dec_57, dec_58, dec_59, dec_5A, dec_5B, dec_5C, dec_5D, dec_5E, dec_5F,
      dec_60, dec_61, dec_62, dec_63, dec_64, dec_65, dec_66, dec_67, dec_68, dec_69, dec_6A, dec_6B,
      dec_6C, dec_6D, dec_6E, dec_6F, dec_70, dec_71, dec_72, dec_73, dec_74, dec_75, dec_76, dec_77,
      dec_78, dec_79, dec_7A, dec_7B, dec_7C, dec_7D, dec_7E, dec_7F, dec_80, dec_81, dec_82, dec_83,
      dec_84, dec_85, dec_86, dec_87, dec_88, dec_89, dec_8A, dec_8B, dec_8C, dec_8D, dec_8E, dec_8F,
      dec_90, dec_91, dec_92, dec_93, dec_94, dec_95, dec_96, dec_97, dec_98, dec_99, dec_9A, dec_9B,
      dec_9C, dec_9D, dec_9E, dec_9F, dec_A0, dec_A1, dec_A2, dec_A3, dec_A4, dec_A5, dec_A6, dec_A7,
      dec_A8, dec_A9, dec_AA, dec_AB, dec_AC, dec_AD, dec_AE, dec_AF, dec_B0, dec_B1, dec_B2, dec_B3,
      dec_B4, dec_B5, dec_B6, dec_B7, dec_B8, dec_B9, dec_BA, dec_BB, dec_BC, dec_BD, dec_BE, dec_BF,
      dec_C0, dec_C1, dec_C2, dec_C3, dec_C4, dec_C5, dec_C6, dec_C7, dec_C8, dec_C9, dec_CA, dec_CB,
      dec_CC, dec_CD, dec_CE, dec_CF, dec_D0, dec_D1, dec_D2, dec_D3, dec_D4, dec_D5, dec_D6, dec_D7,
      dec_D8, dec_D9, dec_DA, dec_DB, dec_DC, dec_DD, dec_DE, dec_DF, dec_E0, dec_E1, dec_E2, dec_E3,
      dec_E4, dec_E5, dec_E6, dec_E7, dec_E8, dec_E9, dec_EA, dec_EB, dec_EC, dec_ED, dec_EE, dec_EF,
      dec_F0, dec_F1, dec_F2, dec_F3, dec_F4, dec_F5, dec_F6, dec_F7, dec_F8, dec_F9, dec_FA, dec_FB,
      dec_FC, dec_FD, dec_FE, dec_FF, *]))

/-- Discharge a one-instruction triple by symbolic execution. -/
macro "hoare_step" : tactic => `(tactic| (
  first
  | apply Triple.of_step
  | apply CTriple.of_step
  | apply TripleM.of_step
  intro $(Lean.mkIdent `s) $(Lean.mkIdent `m) $(Lean.mkIdent `hP) $(Lean.mkIdent `hpc)
  try simp [codeAt_cons, codeAt_nil] at $(Lean.mkIdent `hP):ident
  hoare_simp))

/-- Discharge an `n`-instruction straight-line triple by symbolic execution. -/
macro "hoare_run " n:num : tactic => `(tactic| (
  first
  | apply Triple.of_steps $n
  | apply CTriple.of_steps $n
  | apply TripleM.of_steps $n
  intro $(Lean.mkIdent `s) $(Lean.mkIdent `m) $(Lean.mkIdent `hP) $(Lean.mkIdent `hpc)
  try simp [codeAt_cons, codeAt_nil] at $(Lean.mkIdent `hP):ident
  simp only [steps_succ, steps_zero]
  hoare_simp))

/-! ## Worked example: `LDA #$05; STA $10` -/

/-- The code bytes of the example at `$8000`. -/
def exCode : List UInt8 := [0xA9, 0x05, 0x85, 0x10]

/-- Two `hoare_step`s glued by `Triple.seq`. -/
theorem ex_lda_sta :
    Triple (fun s m => s.halted = false ∧ codeAt m 0x8000 exCode) 0x8000 0x8004
      (fun _ m => m.read 0x10 = 5) := by
  apply Triple.seq (mid := 0x8002)
    (R := fun s m => s.halted = false ∧ codeAt m 0x8000 exCode ∧ s.a = 5)
  · unfold exCode; hoare_step
  · unfold exCode; hoare_step

/-- The same by running both instructions at once. -/
theorem ex_lda_sta_run :
    Triple (fun s m => s.halted = false ∧ codeAt m 0x8000 exCode) 0x8000 0x8004
      (fun _ m => m.read 0x10 = 5) := by
  unfold exCode; hoare_run 2

/-- With the cycle count: 2 (LDA #) + 3 (STA zp). -/
theorem ex_lda_sta_cycles :
    CTriple (fun s m => s.halted = false ∧ codeAt m 0x8000 exCode) 0x8000 0x8004
      (fun _ m => m.read 0x10 = 5) 5 := by
  unfold exCode; hoare_run 2

/-! ## Worked example: a counted loop with `Triple.loop_branch`

`loop: DEX; BNE loop` at `$8000` (`CA D0 FD`), from any `X ≠ 0`, exits at `$8003` with
`X = 0`. Measure `X`; the body assertion `R k` records `Z = (X == 0)` for the branch. -/

theorem uint8_sub_one_toNat (x : UInt8) (h : ¬ x = 0) : (x - 1).toNat + 1 = x.toNat := by
  have : x.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.mp (by simpa using e))
  rw [UInt8.toNat_sub_of_le]
  · simp; omega
  · rw [UInt8.le_iff_toNat_le]; simp; omega

theorem ex_countdown :
    Triple (fun s m => s.halted = false ∧ codeAt m 0x8000 [0xCA, 0xD0, 0xFD] ∧ s.x ≠ 0)
      0x8000 0x8003 (fun s _ => s.x = 0) := by
  refine Triple.loop_branch (b := 0x8001) (off := 0xFD) (op := 0xD0) (instr := .BNE)
    (R := fun k s m => s.halted = false ∧ codeAt m 0x8000 [0xCA, 0xD0, 0xFD] ∧
      s.x.toNat + 1 = k ∧ s.z = (s.x == 0))
    (fun s _ => s.x.toNat) .bne (by decide) ?_ ?_ ?_ ?_
  · -- body: one DEX
    intro k
    hoare_step
    rw [← hP.2, uint8_sub_one_toNat _ hP.1.2.2]
  · intro k s m ⟨hh, hc, _⟩
    simp only [codeAt_cons, codeAt_nil, and_true] at hc
    exact ⟨hh, hc.2.1, hc.2.2⟩
  · -- branch taken: `Z = 0`, so `X ≠ 0` and the measure dropped
    intro k s m ⟨hh, hc, hk, hz⟩ hb
    simp only [branchCond, hz, Bool.not_eq_true', beq_eq_false_iff_ne] at hb
    exact ⟨⟨hh, hc, hb⟩, by simp only; omega⟩
  · -- fall through: `Z = 1`, so `X = 0`
    intro k s m ⟨_, _, _, hz⟩ hb
    simpa [branchCond, hz] using hb

end Nes.Hoare
