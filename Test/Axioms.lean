import Lean
import Nes

/-!
# Axiom check

`registry` lists every headline theorem of the project. **Every headline theorem gets
added to `registry`.** When this module is elaborated (which `lake build Test` and hence
`lake test` do), each registered theorem is looked up and its axiom closure is computed
with `Lean.collectAxioms`; the build fails with an error if a theorem is missing or uses
an axiom outside the policy below.

## Policy

An axiom is accepted iff
* it is one of `allowedAxioms` (the three standard axioms), or
* it is an auxiliary native-evaluation axiom `<thm>._native.<tactic>.ax_*` whose `<tactic>`
  is listed in `allowedNativeTactics`.

Everything else is rejected, in particular `forbiddenAxioms` (`sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`) and the `_native.native_decide` axioms that
`native_decide` generates.

Note (Lean v4.36.0): `bv_decide` no longer goes through `Lean.ofReduceBool`. When it has
to run its LRAT checker it adds a per-theorem axiom
`<thm>._native.bv_decide.ax_*  : verifyBVExpr .. = true`, i.e. it trusts the compiler
exactly like `native_decide` does (which now yields `<thm>._native.native_decide.ax_*`).
Allowing `bv_decide` therefore means trusting compiled evaluation for those proofs;
that trust is confined to the single knob `allowedNativeTactics`.
-/

namespace Test.Axioms

open Lean

/-- Headline theorems. Every headline theorem gets added here. -/
def registry : List Name :=
  [ `Nes.Bits.smoke_bv_decide
  , `Nes.Bits.smoke_omega
  , `Nes.Cpu.Proofs.T_CPU_3_total
  , `Nes.Cpu.Proofs.T_CPU_3_jam
  , `Nes.Cpu.Proofs.T_CPU_3_struct
  , `Nes.Cpu.Proofs.T_CPU_3_struct_exact
  , `Nes.Cpu.Proofs.T_CPU_4_cycles
  , `Nes.Cpu.Proofs.T_CPU_4_pageCross
  , `Nes.Cpu.Proofs.T_CPU_1_adc
  , `Nes.Cpu.Proofs.T_CPU_1_sbc_eq_adc_compl
  , `Nes.Cpu.Proofs.T_CPU_1_cmp
  , `Nes.Cpu.Proofs.T_CPU_2_ror_rol
  , `Nes.Cpu.Proofs.T_CPU_2_rol_ror
  , `Nes.Cpu.Proofs.T_CPU_2_asl
  , `Nes.Cpu.Proofs.T_CPU_2_lsr
  , `Nes.Cpu.Proofs.T_REF_2_adc
  , `Nes.Cpu.Proofs.T_REF_2_sbc
  , `Nes.Cpu.Proofs.T_REF_2_cmp
  , `Nes.Cpu.Proofs.T_REF_2_shifts
  , `Nes.Cpu.Proofs.T_REF_2_bit
  , `Nes.Cpu.Proofs.T_REF_2_incdec
  , `Nes.Cpu.Proofs.T_REF_2_nz
  , `Nes.Cpu.Proofs.T_CPU_5_zp_page0
  , `Nes.Cpu.Proofs.T_CPU_5_zpPtr
  , `Nes.Cpu.Proofs.T_CPU_5_pageCross
  , `Nes.Cpu.Proofs.T_CPU_5_pageCross_unwrapped
  , `Nes.Cpu.Proofs.T_CPU_5_resolve_indexed
  , `Nes.Cpu.Proofs.T_CPU_5_step_cycles
  , `Nes.Cpu.Proofs.T_CPU_5_step_cycles_branch
  , `Nes.Cpu.Proofs.T_CPU_5_jmp_ind_hiAddr
  , `Nes.Cpu.Proofs.T_CPU_5_jmp_ind_bug
  , `Nes.Cpu.Proofs.T_CPU_5_jmp_ind_nobug
  , `Nes.Cpu.Proofs.T_CPU_5_pc_wrap
  , `Nes.Cpu.Proofs.T_CPU_5_branchTarget
  , `Nes.Cpu.Proofs.T_CPU_8_a9_lda_imm
  , `Nes.Cpu.Proofs.T_CPU_8_bd_lda_absx
  , `Nes.Cpu.Proofs.T_CPU_8_8d_sta_abs
  , `Nes.Cpu.Proofs.T_CPU_8_91_sta_indy
  , `Nes.Cpu.Proofs.T_CPU_8_69_adc_imm
  , `Nes.Cpu.Proofs.T_CPU_8_e9_sbc_imm
  , `Nes.Cpu.Proofs.T_CPU_8_2d_and_abs
  , `Nes.Cpu.Proofs.T_CPU_8_2c_bit_abs
  , `Nes.Cpu.Proofs.T_CPU_8_c9_cmp_imm
  , `Nes.Cpu.Proofs.T_CPU_8_0e_asl_abs
  , `Nes.Cpu.Proofs.T_CPU_8_6a_ror_acc
  , `Nes.Cpu.Proofs.T_CPU_8_ee_inc_abs
  , `Nes.Cpu.Proofs.T_CPU_8_ca_dex
  , `Nes.Cpu.Proofs.T_CPU_8_d0_bne
  , `Nes.Cpu.Proofs.T_CPU_8_4c_jmp_abs
  , `Nes.Cpu.Proofs.T_CPU_8_6c_jmp_ind
  , `Nes.Cpu.Proofs.T_CPU_8_20_jsr
  , `Nes.Cpu.Proofs.T_CPU_8_60_rts
  , `Nes.Cpu.Proofs.T_CPU_8_48_pha
  , `Nes.Cpu.Proofs.T_CPU_8_68_pla
  , `Nes.Cpu.Proofs.T_CPU_8_08_php
  , `Nes.Cpu.Proofs.T_CPU_8_28_plp
  , `Nes.Cpu.Proofs.T_CPU_8_00_brk
  , `Nes.Cpu.Proofs.T_CPU_8_40_rti
  , `Nes.Cpu.Proofs.T_CPU_8_18_clc
  , `Nes.Cpu.Proofs.T_CPU_8_38_sec
  , `Nes.Cpu.Proofs.T_CPU_8_aa_tax
  , `Nes.Cpu.Proofs.T_CPU_8_9a_txs
  , `Nes.Cpu.Proofs.T_CPU_8_a7_lax_zp
  , `Nes.Cpu.Proofs.T_CPU_8_c7_dcp_zp
  , `Nes.Cpu.Proofs.T_CPU_8_02_jam
  , `Nes.Cpu.Proofs.T_CPU_6_pull_push
  , `Nes.Cpu.Proofs.T_CPU_6_stack_page
  , `Nes.Cpu.Proofs.T_CPU_6_pha_pla
  , `Nes.Cpu.Proofs.T_CPU_6_php_plp
  , `Nes.Cpu.Proofs.T_CPU_6_jsr_rts
  , `Nes.Cpu.Proofs.T_CPU_6_jsr_rts_direct
  , `Nes.Cpu.Proofs.Refinement.prefix_spec
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_of_classes
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_read
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_imm
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_imp
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_write
  , `Nes.Cpu.Proofs.Refinement.T_REF_1
  , `Nes.Cpu.Proofs.Refinement.all_classes_refine
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_rmw
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_branch
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_jsr
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_rts
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_rti
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_brk
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_jmpAbs
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_jmpInd
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_push
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_pull
  , `Nes.Cpu.Proofs.Refinement.T_REF_1_jam
  , `Nes.Cpu.Proofs.T_CPU_7_irq_masked
  , `Nes.Cpu.Proofs.T_CPU_7_hijack_decision
  , `Nes.Cpu.Proofs.T_CPU_7_entry
  , `Nes.Cpu.Proofs.T_CPU_7_brk
  , `Nes.Cpu.Proofs.T_CPU_7_entry_irq
  , `Nes.Cpu.Proofs.T_CPU_7_B_only_pushed
  , `Nes.Cpu.Proofs.T_CPU_7_hijack
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_latch
  , `Nes.Cpu.Proofs.T_CPU_7_boundary_bound
  , `Nes.Cpu.Proofs.T_CPU_7_irq_masked_core
  , `Nes.Cpu.Proofs.T_CPU_7_irq_masked_run ]

/-- The standard axioms any theorem may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms that must never appear (named explicitly for clear error messages; the check is
an allowlist, so any axiom not allowed above is rejected anyway). -/
def forbiddenAxioms : List Name := [``sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat]

/-- Tactics whose `<thm>._native.<tactic>.ax_*` auxiliary axioms are accepted.
`native_decide` must never be added here. -/
def allowedNativeTactics : List Name := [`bv_decide]

/-- If `ax` is an auxiliary native axiom `<thm>._native.<tactic>.ax_*`, return `<tactic>`. -/
def nativeTactic? (ax : Name) : Option Name :=
  match ax.components.dropWhile (· != `_native) with
  | _ :: tac :: _ => some tac
  | _ => none

/-- Is `ax` acceptable under the policy? -/
def axiomAllowed (ax : Name) : Bool :=
  !forbiddenAxioms.contains ax &&
  (allowedAxioms.contains ax ||
    match nativeTactic? ax with
    | some tac => allowedNativeTactics.contains tac
    | none => false)

/-- Check every registered theorem; return the list of problems (empty = pass). -/
def checkRegistry (names : List Name) : CoreM (List String) := do
  let mut problems : List String := []
  for n in names do
    unless (← getEnv).contains n do
      problems := problems ++ [s!"{n}: not found (missing theorem or missing import)"]
      continue
    let axs ← collectAxioms n
    let bad := axs.toList.filter (!axiomAllowed ·)
    unless bad.isEmpty do
      problems := problems ++ [s!"{n}: forbidden axioms {bad}"]
  return problems

/-- Elaboration-time gate: fails the build if any registered theorem is bad. -/
def runCheck (names : List Name) : CoreM Unit := do
  let problems ← checkRegistry names
  unless problems.isEmpty do
    throwError m!"axiom check failed:\n{String.intercalate "\n" problems}"

run_meta runCheck registry

/-- Number of theorems checked (the check above ran at build time). -/
def axiomsChecked : Nat := registry.length

end Test.Axioms
