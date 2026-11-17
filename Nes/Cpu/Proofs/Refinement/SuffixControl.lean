import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement.SuffixControl` — T-REF-1 for the control-flow classes

## Spec

* `T_REF_1_rts`, `T_REF_1_rti`, `T_REF_1_brk`, `T_REF_1_jmpAbs`, `T_REF_1_jmpInd`:
  `ClassRefines c` for these single-opcode classes (`$60`, `$40`, `$00`, `$4C`, `$6C`).
* `T_REF_1_jsr`: the micro-machine (like the hardware) reads the target's high byte after the
  two pushes. Proving this first exposed that `Isa.step` read it before them (wrong when `JSR`
  at `$01FC` with `SP = $FE` overwrites its own operand byte `$01FE`); `Isa.exec` was fixed.

Method: each class has one opcode (`ctl_<c>_op`, `decide +kernel` over the 256 entries), so
both sides are unfolded symbolically with that opcode's concrete program and table entry.
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

theorem ctl_jmpAbs_op : ∀ i : Fin 256, classify (decodeFin i) = .jmpAbs → i = 0x4C := by
  decide +kernel

theorem ctl_uops_4C : uops 0x4C = #[.fetchLo, .jmpHi] := by decide +kernel
theorem ctl_decode_4C : decode 0x4C = ⟨.JMP, .abs, 3, false, true⟩ := by decide +kernel

theorem ctl_op_eq {op : UInt8} {c : Cls} {k : Fin 256}
    (ht : ∀ i : Fin 256, classify (decodeFin i) = c → i = k)
    (hc : classify (decode op) = c) : op = UInt8.ofNat k.val := by
  have := ht ⟨_, op.toNat_lt⟩ (by rw [← decode_eq_decodeFin]; exact hc)
  apply UInt8.toNat_inj.mp
  rw [← this]; simp

theorem ctl_jsr_op : ∀ i : Fin 256, classify (decodeFin i) = .jsr → i = 0x20 := by
  decide +kernel

theorem ctl_uops_20 : uops 0x20 = #[.fetchLo, .dummyReadStack, .pushPch, .pushPcl, .jmpHi] := by decide +kernel
theorem ctl_decode_20 : decode 0x20 = ⟨.JSR, .abs, 6, false, true⟩ := by decide +kernel

theorem ctl_read_write_ne (m : Mem) (a b : UInt16) (v : UInt8) (hab : a ≠ b) :
    (m.write b v).read a = m.read a := by
  simp only [Mem.read, Mem.write]
  rw [Vector.getElem_set_ne]
  intro h; exact hab (UInt16.toNat_inj.mp h.symm)

/-- T-REF-1 for `JSR`, provided the operand's high byte (`PC + 2`) is not one of the two stack
bytes the instruction pushes. Without that hypothesis the statement is false: the hardware (and
`Micro`) fetches the high byte *after* the pushes, while `Isa.step` reads it before. -/
theorem T_REF_1_jsr : ClassRefines .jsr := by
  intro s m h hc
  have hop : m.read s.pc = 0x20 := ctl_op_eq ctl_jsr_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_20,
    skips, ctl_decode_20, bump, stackAddr, pushOp]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc, push, pull]

theorem ctl_rts_op : ∀ i : Fin 256, classify (decodeFin i) = .rts → i = 0x60 := by
  decide +kernel

theorem ctl_uops_60 : uops 0x60 = #[.dummyReadPc, .peekStackInc, .pullLoInc, .pullHiPc, .rtsInc] := by decide +kernel
theorem ctl_decode_60 : decode 0x60 = ⟨.RTS, .imp, 6, false, true⟩ := by decide +kernel

theorem T_REF_1_rts : ClassRefines .rts := by
  intro s m h hc
  have hop : m.read s.pc = 0x60 := ctl_op_eq ctl_rts_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_60,
    skips, ctl_decode_60, bump, stackAddr, pushOp]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc, push, pull]

theorem ctl_rti_op : ∀ i : Fin 256, classify (decodeFin i) = .rti → i = 0x40 := by
  decide +kernel

theorem ctl_uops_40 : uops 0x40 = #[.dummyReadPc, .peekStackInc, .pullPInc, .pullLoInc, .pullHiPc] := by decide +kernel
theorem ctl_decode_40 : decode 0x40 = ⟨.RTI, .imp, 6, false, true⟩ := by decide +kernel

theorem T_REF_1_rti : ClassRefines .rti := by
  intro s m h hc
  have hop : m.read s.pc = 0x40 := ctl_op_eq ctl_rti_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_40,
    skips, ctl_decode_40, bump, stackAddr, pushOp]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc, push, pull]

theorem ctl_brk_op : ∀ i : Fin 256, classify (decodeFin i) = .brk → i = 0x00 := by
  decide +kernel

theorem ctl_uops_00 : uops 0x00 = #[.brkOperand, .pushPch, .pushPcl, .pushStatus, .vecLo, .vecHi] := by decide +kernel
theorem ctl_decode_00 : decode 0x00 = ⟨.BRK, .imp, 7, false, true⟩ := by decide +kernel

theorem T_REF_1_brk : ClassRefines .brk := by
  intro s m h hc
  have hop : m.read s.pc = 0x00 := ctl_op_eq ctl_brk_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_00,
    skips, ctl_decode_00, bump, stackAddr, pushOp]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc, push, pull, State.setI,
    State.setBit]

theorem ctl_jmpInd_op : ∀ i : Fin 256, classify (decodeFin i) = .jmpInd → i = 0x6C := by
  decide +kernel

theorem ctl_uops_6C : uops 0x6C = #[.fetchLo, .fetchHi, .jmpIndLo, .jmpIndHi] := by decide +kernel
theorem ctl_decode_6C : decode 0x6C = ⟨.JMP, .ind, 5, false, true⟩ := by decide +kernel

theorem T_REF_1_jmpInd : ClassRefines .jmpInd := by
  intro s m h hc
  have hop : m.read s.pc = 0x6C := ctl_op_eq ctl_jmpInd_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_6C,
    skips, ctl_decode_6C, bump, stackAddr, pushOp]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc, push, pull, indirectBug]

theorem T_REF_1_jmpAbs : ClassRefines .jmpAbs := by
  intro s m h hc
  have hop : m.read s.pc = 0x4C := ctl_op_eq ctl_jmpAbs_op hc
  simp only [microStep, step, h, hop, Bool.false_eq_true, ↓reduceIte]
  rw [show maxCycles = 7 + 1 from rfl, runInstr_fetch _ _ _ h, hop]
  simp [runInstr, fetched, cycle, busOp, curOp, complete, MicroState.exec, advance, ctl_uops_4C,
    skips, ctl_decode_4C, bump]
  simp [exec, resolve, extraCycles, Mem.read16, UInt16.add_assoc]

end Nes.Cpu.Proofs.Refinement
