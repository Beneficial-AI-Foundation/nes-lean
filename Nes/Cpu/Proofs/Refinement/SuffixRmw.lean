import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement.SuffixRmw` — T-REF-1 for the read-modify-write class

## Spec

* `rmw_suffix`: the RMW suffix `rmwRead, rmwDummyWrite, rmwWrite` takes 3 cycles: read the
  operand `v` at `addr`, write `v` back (dummy write) while computing `rmwState`/`rmwResult`,
  write the result; the net memory effect is a single write of the result at `addr`.
* `exec_rmw`: `Isa.exec` of an RMW instruction on a memory operand (`rmwOk`) is
  `rmwState` on the registers and a write of `rmwResult` at the effective address.
* `rmw_table` (`decide +kernel`): every `rmw`-class opcode is `rmwOk`, resolves an address
  (not `ind`/`rel`), has no page-cross penalty (the fixup cycle of `absx/absy/indy` is always
  taken), and `prefixCycles + 4 = cycles`.
* `T_REF_1_rmw : ClassRefines .rmw` (66 opcodes).
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

theorem rmw_write_write (m : Mem) (a : UInt16) (v w : UInt8) :
    (m.write a v).write a w = m.write a w := by
  simp [Mem.write, Vector.set_set]

private theorem rmw_toUInt8_ne (n : Nat) (h0 : 0 < n) (h : n < 256) : n.toUInt8 ≠ 0 := by
  intro h'; have := congrArg UInt8.toNat h'; simp at this; omega

/-- Last two cycles of the RMW suffix: dummy write of the old value, write of the result. -/
theorem rmw_suffix2 (f : Nat) (ms : MicroState) (m : Mem) (p : MicroProgram)
    (hu : uops ms.op = p ++ #[.rmwRead, .rmwDummyWrite, .rmwWrite])
    (hpos : ms.pos.toNat = p.size + 2) (hp : p.size ≤ 4) :
    runInstr (f + 1 + 1) ms m =
      ({ ms with cpu := rmwState (decode ms.op).instr ms.cpu ms.data,
                 data := rmwResult (decode ms.op).instr ms.cpu.c ms.data, pos := 0 },
       (m.write ms.addr ms.data).write ms.addr
          (rmwResult (decode ms.op).instr ms.cpu.c ms.data), 2) := by
  have hp0 : ms.pos ≠ 0 := by intro h0; simp [h0] at hpos
  have hcur : ms.curOp = .rmwDummyWrite := by
    simp [curOp, hu, hpos, Array.getElem?_append]
  have h2 : (ms.pos.toNat + 1).toUInt8.toNat = p.size + 3 := by
    rw [hpos]; simp; omega
  have hne : (ms.pos.toNat + 1).toUInt8 ≠ 0 := rmw_toUInt8_ne _ (by omega) (by omega)
  have hc : ms.cycle m = ({ ms with
      cpu := rmwState (decode ms.op).instr ms.cpu ms.data,
      data := rmwResult (decode ms.op).instr ms.cpu.c ms.data,
      pos := (ms.pos.toNat + 1).toUInt8 }, m.write ms.addr ms.data) := by
    simp only [cycle, busOp, hp0, hcur, complete, beq_iff_eq, ↓reduceIte, Bool.false_eq_true]
    rw [advance_one _ (by simp [hu, hpos]) (by simp [hu, hpos, Array.getElem?_append, skips])]
    simp [MicroState.exec]
  rw [runInstr_cyc _ _ _ _ _ hc hne]
  rw [runInstr_last f _ _ (p ++ #[.rmwRead, .rmwDummyWrite]) .rmwWrite]
  rotate_left
  · simpa using hu
  · simpa using h2
  have hcur' : ({ ms with
      cpu := rmwState (decode ms.op).instr ms.cpu ms.data,
      data := rmwResult (decode ms.op).instr ms.cpu.c ms.data,
      pos := (ms.pos.toNat + 1).toUInt8 } : MicroState).curOp = .rmwWrite := by
    simp only [curOp_eq]; rw [h2]; simp [hu, Array.getElem?_append]
  simp only [busOp, hne, hcur', beq_iff_eq, ↓reduceIte, MicroState.exec, bump]

/-- The RMW suffix: read, dummy write of the old value, write of the result. -/
theorem rmw_suffix (f : Nat) (ms : MicroState) (m : Mem) (p : MicroProgram)
    (hu : uops ms.op = p ++ #[.rmwRead, .rmwDummyWrite, .rmwWrite])
    (hpos : ms.pos.toNat = p.size + 1) (hp : p.size ≤ 4) :
    runInstr (f + 1 + 1 + 1) ms m =
      ({ ms with cpu := rmwState (decode ms.op).instr ms.cpu (m.read ms.addr),
                 data := rmwResult (decode ms.op).instr ms.cpu.c (m.read ms.addr), pos := 0 },
       m.write ms.addr (rmwResult (decode ms.op).instr ms.cpu.c (m.read ms.addr)), 3) := by
  have hp0 : ms.pos ≠ 0 := by intro h0; simp [h0] at hpos
  have hcur : ms.curOp = .rmwRead := by simp [curOp, hu, hpos, Array.getElem?_append]
  have h1 : (ms.pos.toNat + 1).toUInt8.toNat = p.size + 2 := by
    rw [hpos]; simp; omega
  have hne : (ms.pos.toNat + 1).toUInt8 ≠ 0 := rmw_toUInt8_ne _ (by omega) (by omega)
  have hc : ms.cycle m =
      ({ ms with data := m.read ms.addr, pos := (ms.pos.toNat + 1).toUInt8 }, m) := by
    simp only [cycle, busOp, hp0, hcur, complete, beq_iff_eq, ↓reduceIte, Bool.false_eq_true]
    rw [advance_one _ (by simp [hu, hpos]) (by simp [hu, hpos, Array.getElem?_append, skips])]
    simp [MicroState.exec]
  rw [runInstr_cyc _ _ _ _ _ hc hne, show f + 2 = f + 1 + 1 from rfl, rmw_suffix2 f _ m p (by exact hu) (by simpa using h1) hp]
  simp [bump, rmw_write_write]

/-! ## Class `rmw`: `Isa.exec` agrees with the micro helpers -/

/-- Read-modify-write instructions on a memory operand. -/
def rmwOk (e : Entry) : Bool :=
  match e.instr with
  | .ASL | .LSR | .ROL | .ROR | .INC | .DEC
  | .SLO | .RLA | .SRE | .RRA | .DCP | .ISC => e.mode != .acc
  | _ => false

theorem exec_rmw (e : Entry) (hr : rmwOk e = true) (s : State) (m : Mem) (ea : UInt16)
    (cr : Bool) :
    exec e s m ea cr =
      (rmwState e.instr { s with pc := s.pc + e.mode.len } (m.read ea),
       m.write ea (rmwResult e.instr s.c (m.read ea))) := by
  obtain ⟨i, mode, cy, pcr, off⟩ := e
  cases i <;> simp only [rmwOk, bne_iff_ne, ne_eq] at hr <;>
    first
      | (exact absurd hr (by decide))
      | (simp [exec, rmwState, rmwResult, shiftOp, hr, State.c, State.getBit])

theorem rmw_table : ∀ i : Fin 256, classify (decodeFin i) = .rmw →
    rmwOk (decodeFin i) = true ∧ resolvesAddr (decodeFin i).mode = true ∧
    (decodeFin i).mode ≠ .ind ∧ (decodeFin i).mode ≠ .rel ∧ (decodeFin i).pageCross = false ∧
    (∀ c : Bool, prefixCycles (decodeFin i).mode false c + 4 = (decodeFin i).cycles.toNat) := by
  decide +kernel

theorem rmw_prefix_size (mode : AddrMode) : (modePrefix mode).size ≤ 4 := by
  cases mode <;> decide

/-- T-REF-1 for every read-modify-write opcode (official shifts/rotates/INC/DEC on memory and
the unofficial `SLO/RLA/SRE/RRA/DCP/ISC`), every addressing mode: the micro-machine computes
`Isa.step`'s registers, memory and cycle count. -/
theorem T_REF_1_rmw : ClassRefines .rmw := by
  intro s m h hc
  obtain ⟨hr, hres, hind, hrel, hpc, hcyc⟩ := rmw_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hr hres hind hrel hpc hcyc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hres, ↓reduceIte, prefixAddr_eq s m _ hind, hpc] at h1
  have hk := prefixCycles_le (decode (m.read s.pc)).mode false
    (resolve s m (decode (m.read s.pc)).mode).2
  have hcy := hcyc (resolve s m (decode (m.read s.pc)).mode).2
  generalize prefixCycles (decode (m.read s.pc)).mode false
    (resolve s m (decode (m.read s.pc)).mode).2 = K at h1 hk hcy
  rw [show 7 - K = (4 - K) + 1 + 1 + 1 by omega,
    rmw_suffix (p := modePrefix (decode (m.read s.pc)).mode)] at h1
  rotate_left
  · exact hu
  · exact prefix_pos _
  · exact rmw_prefix_size _
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, exec_rmw _ hr,
    extraCycles_nonrel _ _ _ hrel, bump, hpc]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · simp only [UInt16.add_assoc, prefixPcInc_len _ hres]
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega

end Nes.Cpu.Proofs.Refinement
