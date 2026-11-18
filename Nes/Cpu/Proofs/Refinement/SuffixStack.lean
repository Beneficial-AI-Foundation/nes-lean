import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement.SuffixStack` — T-REF-1 for the `push`, `pull` and `jam` classes

## Spec

* `T_REF_1_push : ClassRefines .push` (PHA, PHP: 3 cycles, PHP pushes `P|$30`).
* `T_REF_1_pull : ClassRefines .pull` (PLA, PLP: 4 cycles, PLP loads `(v&$CF)|$20`).
* `T_REF_1_jam : ClassRefines .jam` (the 12 JAM opcodes: 3 cycles, PC restored, halted).

All three classes use the implied mode (empty prefix, checked by the `*_table` facts over the
256 opcodes with `decide +kernel`), so after `runInstr_prefix` the 2-3 suffix cycles are
unfolded by `simp` directly; for `pull`, splitting PLA/PLP first keeps that `simp` small.
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

theorem stk_push_table : ∀ i : Fin 256, classify (decodeFin i) = .push →
    ((decodeFin i).instr = .PHA ∨ (decodeFin i).instr = .PHP) ∧ (decodeFin i).mode = .imp ∧
    (decodeFin i).cycles.toNat = 3 ∧ (decodeFin i).pageCross = false := by
  decide +kernel

theorem T_REF_1_push : ClassRefines .push := by
  intro s m h hc
  obtain ⟨hi, hmode, hcy, hpc⟩ := stk_push_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hi hmode hcy hpc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc, hmode] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
    List.length_nil, suffix] at h1 hu
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, bump, hmode, hcy, hpc,
    extraCycles, resolve]
  simp [runInstr, MicroState.cycle, busOp, complete, curOp, hu, advance, skips, MicroState.exec]
  rcases hi with hi | hi <;> simp [exec, hi, hmode, push, stackAddr, AddrMode.len, h]

theorem stk_pull_table : ∀ i : Fin 256, classify (decodeFin i) = .pull →
    ((decodeFin i).instr = .PLA ∨ (decodeFin i).instr = .PLP) ∧ (decodeFin i).mode = .imp ∧
    (decodeFin i).cycles.toNat = 4 ∧ (decodeFin i).pageCross = false := by
  decide +kernel

theorem T_REF_1_pull : ClassRefines .pull := by
  intro s m h hc
  obtain ⟨hi, hmode, hcy, hpc⟩ := stk_pull_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hi hmode hcy hpc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc, hmode] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
    List.length_nil, suffix] at h1 hu
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, bump, hmode, hcy, hpc,
    extraCycles, resolve]
  rcases hi with hi | hi <;>
    simp [runInstr, MicroState.cycle, busOp, complete, curOp, hu, advance, skips, MicroState.exec,
      hi] <;>
    simp [exec, hi, hmode, pull, stackAddr, AddrMode.len, h]

theorem jam_table : ∀ i : Fin 256, classify (decodeFin i) = .jam →
    (decodeFin i).instr = .JAM ∧ (decodeFin i).mode = .imp ∧
    (decodeFin i).cycles.toNat = 3 ∧ (decodeFin i).pageCross = false := by
  decide +kernel

theorem T_REF_1_jam : ClassRefines .jam := by
  intro s m h hc
  obtain ⟨hi, hmode, hcy, hpc⟩ := jam_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hi hmode hcy hpc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc, hmode] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
    List.length_nil, suffix] at h1 hu
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, bump, hmode, hcy, hpc,
    extraCycles, resolve]
  simp [runInstr, MicroState.cycle, busOp, complete, curOp, hu, advance, skips, MicroState.exec]
  simp [exec, hi, h]

end Nes.Cpu.Proofs.Refinement
