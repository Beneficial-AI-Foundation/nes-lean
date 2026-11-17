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
  , `Nes.Cpu.Proofs.T_CPU_7_irq_masked_run
  , `Nes.Cpu.Proofs.runSched_const
  , `Nes.Cpu.Proofs.runSched_add
  , `Nes.Cpu.Proofs.T_CPU_7_hijack_mid
  , `Nes.Cpu.Proofs.T_CPU_7_hijack_late
  , `Nes.Cpu.Proofs.hj_quiet_run
  , `Nes.Cpu.Proofs.T_CPU_7_irq_masked_opcode
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_taken
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_latency
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_latency_edge
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_latency_edge_irq
  , `Nes.Cpu.Proofs.T_CPU_7_nmi_latency_mid
  , `Nes.Input.Proofs.controller_reads_in_order
  , `Nes.Input.Proofs.controller_after_8
  , `Nes.Input.Proofs.controller_strobe_high
  , `Nes.Ppu.Proofs.T_PPU_2_incX_32
  , `Nes.Ppu.Proofs.T_PPU_2_incY_29
  , `Nes.Ppu.Proofs.T_PPU_2_incY_31
  , `Nes.Ppu.Proofs.T_PPU_2_copyX
  , `Nes.Ppu.Proofs.T_PPU_2_copyY
  , `Nes.Ppu.Proofs.T_PPU_2_2005_pair
  , `Nes.Ppu.Proofs.T_PPU_2_2006_pair
  , `Nes.Ppu.Proofs.T_REF_2_incX
  , `Nes.Ppu.Proofs.T_REF_2_incY
  , `Nes.Ppu.Proofs.T_REF_2_copyX
  , `Nes.Ppu.Proofs.T_REF_2_copyY
  , `Nes.Ppu.Proofs.T_REF_2_loopy
  , `Nes.Bus.Proofs.T_BUS_1_ram
  , `Nes.Bus.Proofs.T_BUS_1_ppuReg
  , `Nes.Bus.Proofs.T_BUS_1_ppu_wrap
  , `Nes.Bus.Proofs.T_BUS_1_palette
  , `Nes.Bus.Proofs.T_BUS_1_palette_aliases
  , `Nes.Bus.Proofs.T_BUS_1_palette_period
  , `Nes.Bus.Proofs.T_BUS_1_nametable_fold
  , `Nes.Bus.Proofs.T_BUS_1_nametable_idem
  , `Nes.Bus.Proofs.T_BUS_1_nametable
  , `Nes.Bus.Proofs.T_BUS_1_ciram_horizontal
  , `Nes.Bus.Proofs.T_BUS_1_ciram_vertical
  , `Nes.Bus.Proofs.T_BUS_1_ciram_singleLow
  , `Nes.Bus.Proofs.T_BUS_1_ciram_singleHigh
  , `Nes.Cart.parse_serialize
  , `Nes.Cart.parse_of_bad_magic
  , `Nes.Cart.MapperState.prgOffset_lt
  , `Nes.Cart.MapperState.chrOffset_lt
  , `Nes.Cart.Nrom.prgOffset_16k_mirror
  , `Nes.Cart.Cart.cpuWrite_rom
  , `Nes.Cart.Cart.ppuWrite_rom
  , `Nes.Cart.Cart.run_rom
  , `Nes.Cart.Cart.run_cpuRead_prg_nrom
  , `Nes.Cart.Cart.run_ppuRead_chr_nrom
  , `Nes.Ppu.Proofs.T_PPU_1_frame_dots
  , `Nes.Ppu.Proofs.T_PPU_1_odd_frame
  , `Nes.Ppu.Proofs.T_PPU_1_vblank_set
  , `Nes.Ppu.Proofs.T_PPU_1_vblank_clear
  , `Nes.Ppu.Proofs.T_PPU_1_cpu_cycles
  , `Nes.Ppu.Proofs.T_PPU_1_frame_rate
  , `Nes.Ppu.Proofs.T_PPU_7_buffered
  , `Nes.Ppu.Proofs.T_PPU_7_palette
  , `Nes.Ppu.Proofs.T_PPU_7_increment
  , `Nes.Ppu.Proofs.T_PPU_7_two_reads
  , `Nes.Ppu.Proofs.T_PPU_5_nmi_at_vblank
  , `Nes.Ppu.Proofs.T_PPU_5_retrigger
  , `Nes.Ppu.Proofs.T_PPU_5_toggle
  , `Nes.Ppu.Proofs.T_PPU_5_retrigger_cpuWrite
  , `Nes.Ppu.Proofs.T_PPU_5_suppress
  , `Nes.Cart.Cnrom.prgOffset_lt
  , `Nes.Cart.Cnrom.chrOffset_lt
  , `Nes.Cart.Cnrom.regWrite_bank_le
  , `Nes.Cart.Cnrom.regWrite_bank_lt
  , `Nes.Cart.Cnrom.chrOffset_banked
  , `Nes.Cart.Mmc1.T_CART_3_commit_serial
  , `Nes.Cart.Mmc1.T_CART_3_commit
  , `Nes.Cart.Mmc1.T_CART_3_reset_serial
  , `Nes.Cart.Mmc1.T_CART_3_reset
  , `Nes.Cart.Mmc3.T_CART_4_fires
  , `Nes.Cart.Mmc3.T_CART_4_reload
  , `Nes.Cart.Mmc3.T_CART_4_decrement
  , `Nes.Cart.Mmc3.T_CART_4_filter
  , `Nes.Cart.Mmc3.T_CART_4_high
  , `Nes.Cart.Mmc3.T_CART_4_low
  , `Nes.Cart.Mmc3.T_CART_4_disable
  , `Nes.Cart.Mmc3.T_CART_4_disabled_no_irq
  , `Nes.Cart.Mmc3.T_CART_4_c001
  , `Nes.Cart.Mmc3.prgOffset_lt
  , `Nes.Cart.Mmc3.chrOffset_lt
  , `Nes.Cart.Cart.run_kind
  , `Nes.Cart.Cart.run_cpuRead_prg
  , `Nes.Cart.Cart.run_ppuRead_chr
  , `Nes.System.Proofs.T_SYS_1_clock
  , `Nes.System.Proofs.T_SYS_1_powerOn
  , `Nes.System.Proofs.T_SYS_3_frame
  , `Nes.System.Proofs.T_SYS_3_frames
  , `Nes.System.Proofs.T_SYS_2_machine
  , `Nes.System.Proofs.T_SYS_2_oam_dma
  , `Nes.System.Proofs.SaveState.T_REF_3_roundtrip
  , `Nes.System.Proofs.SaveState.T_REF_3_injective
  , `Nes.System.Proofs.Determinism.T_REF_4_prefix
  , `Nes.System.Proofs.Determinism.T_REF_4_split
  , `Nes.System.Proofs.Determinism.T_REF_4_script_prefix
  , `Nes.System.Proofs.Determinism.T_REF_4_script_state
  , `Nes.System.Proofs.Determinism.T_REF_4_hashes
  , `Nes.System.Proofs.Determinism.T_REF_4_replay
  , `Nes.System.Proofs.T_SYS_4_step_cpu
  , `Nes.System.Proofs.T_SYS_4_apuIrq
  , `Nes.System.Proofs.T_SYS_4_irq_wiring
  , `Nes.System.Proofs.T_SYS_4_dots
  , `Nes.System.Proofs.T_SYS_4_cpu_projection
  , `Nes.System.Proofs.T_SYS_4_cpu_projection_mem
  , `Nes.System.Proofs.T_SYS_4_nmi
  , `Nes.Apu.Proofs.T_APU_3_wrap
  , `Nes.Apu.Proofs.T_APU_3_length
  , `Nes.Apu.Proofs.T_APU_3_loop
  , `Nes.Apu.Proofs.T_APU_3_irq
  , `Nes.Apu.Proofs.T_APU_3_stall
  , `Nes.Apu.Proofs.dmc_output_bounds
  , `Nes.Apu.Proofs.T_APU_1_four_step
  , `Nes.Apu.Proofs.T_APU_1_five_step
  , `Nes.Apu.Proofs.T_APU_1_irq
  , `Nes.Apu.Proofs.T_APU_1_immediate
  , `Nes.Apu.Proofs.lengthTable_values
  , `Nes.Apu.Proofs.length_halt
  , `Nes.Apu.Proofs.envelope_decay
  , `Nes.Apu.Proofs.sweep_mute
  , `Nes.Apu.Proofs.pulse1_negate_ones_complement
  , `Nes.Apu.Proofs.pulse2_negate_twos_complement
  , `Nes.Apu.Proofs.noise_lfsr_period
  , `Nes.Apu.Proofs.T_APU_2_mono_p1
  , `Nes.Apu.Proofs.T_APU_2_mono_p2
  , `Nes.Apu.Proofs.T_APU_2_mono_t
  , `Nes.Apu.Proofs.T_APU_2_mono_n
  , `Nes.Apu.Proofs.T_APU_2_mono_d
  , `Nes.Apu.Proofs.T_APU_2_max
  , `Nes.Apu.Proofs.T_APU_2_bounds
  , `Nes.Apu.Proofs.T_APU_2_pulseTable
  , `Nes.Apu.Proofs.T_APU_2_tndTable
  , `Nes.Apu.Proofs.T_APU_2_pulseTable_err
  , `Nes.Apu.Proofs.T_APU_2_tndTable_err ]

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
