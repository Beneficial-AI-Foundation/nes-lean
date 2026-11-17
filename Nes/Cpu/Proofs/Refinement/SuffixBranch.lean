import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement.SuffixBranch` — T-REF-1 for the conditional branches

## Spec

* `branch_suffix`: the branch suffix `branchFetch, branchTaken, branchFixup` run from its first
  micro-op leaves `PC` = next instruction (not taken, 1 cycle), `hi(next):lo(target)` (taken,
  2 cycles) or the target (taken to another page, 3 cycles), and never writes memory.
* `T_REF_1_branch : ClassRefines .branch` — BPL BMI BVC BVS BCC BCS BNE BEQ (mode `rel`):
  2 / 3 / 4 cycles, matching `cycles + extraCycles`.

Method: `runInstr_prefix` (the `rel` prefix is empty), `branch_suffix` by symbolic execution
with a case split on taken / crossed, `exec_branch`, and `branch_table` (`decide +kernel`).
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

/-- Branch conditions only read the flags. -/
theorem branchCond_pc (s : State) (pc : UInt16) (i : Instr) :
    branchCond { s with pc := pc } i = branchCond s i := by
  cases i <;> rfl

/-- The branch suffix from its first micro-op: registers, memory, cycles. -/
theorem branch_suffix (ms : MicroState) (m : Mem)
    (hu : uops ms.op = #[.branchFetch, .branchTaken, .branchFixup]) (hpos : ms.pos = 1) :
    let next := ms.cpu.pc + 1
    let t := branchTarget next (m.read ms.cpu.pc)
    let cr := UInt16.hi t != UInt16.hi next
    let c := branchCond ms.cpu (decode ms.op).instr
    (runInstr 7 ms m).1.cpu = (if c then (if cr then { ms.cpu with pc := t } else
        { ms.cpu with pc := UInt16.ofLoHi (UInt16.lo t) (UInt16.hi next) })
      else { ms.cpu with pc := next }) ∧
    (runInstr 7 ms m).2.1 = m ∧
    (runInstr 7 ms m).2.2 = (if c then (if cr then 3 else 2) else 1) := by
  dsimp only
  have hsz : (uops ms.op).size = 3 := by simp [hu]
  have h1 : ms.cycle m = ((ms.exec .branchFetch (m.read ms.cpu.pc)).advance, m) := by
    simp [cycle, busOp, curOp, hu, hpos, complete]
  rw [show (7 : Nat) = 6 + 1 from rfl, runInstr_succ, h1]
  simp only [advance, skips, exec_op, exec_pos, hu, hpos, MicroState.exec, branchCond_pc]
  generalize hcr : (UInt16.hi (branchTarget (ms.cpu.pc + 1) (m.read ms.cpu.pc)) != UInt16.hi (ms.cpu.pc + 1)) = cr' at *
  generalize hcc : branchCond ms.cpu (decode ms.op).instr = c' at *
  cases c' <;> cases cr' <;> simp [Array.getD_eq_getD_getElem?]
  all_goals
    rw [show (6 : Nat) = 5 + 1 from rfl, runInstr_succ]
    simp [cycle, busOp, curOp, complete, advance, skips, hu, MicroState.exec, branchCond_pc, hcc,
      Array.getD_eq_getD_getElem?, bump]
  rw [show (5 : Nat) = 4 + 1 from rfl, runInstr_succ]
  simp [cycle, busOp, curOp, complete, advance, skips, hu, MicroState.exec, branchCond_pc, hcc,
    Array.getD_eq_getD_getElem?, bump]

/-- Conditional-branch instructions. -/
def branchOk : Instr → Bool
  | .BPL | .BMI | .BVC | .BVS | .BCC | .BCS | .BNE | .BEQ => true
  | _ => false

/-- `Isa.exec` of a branch. -/
theorem exec_branch (e : Entry) (hb : branchOk e.instr = true) (s : State) (m : Mem)
    (ea : UInt16) (cr : Bool) :
    exec e s m ea cr =
      (if branchCond s e.instr then { s with pc := ea } else { s with pc := s.pc + e.mode.len }, m) := by
  obtain ⟨i, mode, cy, pcr, off⟩ := e
  cases i <;> simp only [branchOk] at hb <;>
    first | (exact absurd hb (by decide)) | (simp only [exec] <;> rfl)

/-- Table facts for the branch class, over all 256 opcodes. -/
theorem branch_table : ∀ i : Fin 256, classify (decodeFin i) = .branch →
    branchOk (decodeFin i).instr = true ∧ (decodeFin i).mode = .rel ∧
    (decodeFin i).cycles.toNat = 2 := by
  decide +kernel

/-- T-REF-1 for the 8 conditional branches: not taken (2 cycles), taken to the same page (3),
taken to another page (4). -/
theorem T_REF_1_branch : ClassRefines .branch := by
  intro s m h hc
  obtain ⟨hb, hmode, hcy⟩ := branch_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hb hmode hcy
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc, hmode] at hu
  simp only [modePrefix, suffix, List.size_toArray, List.length_nil] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
    List.length_nil, Nat.zero_add, UInt16.add_zero,
    show (Nat.toUInt8 0 + 1 : UInt8) = 1 from rfl] at h1
  simp only [Array.empty_append] at hu
  obtain ⟨e1, e2, e3⟩ := branch_suffix
    { cpu := { s with pc := s.pc + 1 }, op := m.read s.pc, pos := 1, base := base, data := data }
    m hu rfl
  dsimp only at e1 e2 e3
  simp only [branchCond_pc, UInt16.add_assoc, show (1 : UInt16) + 1 = 2 from rfl] at e1 e3
  simp only [h] at e1 e2 e3
  simp only [microStep, h1, bump, step, h, Bool.false_eq_true, ↓reduceIte, resolve,
    hmode, exec_branch _ hb, extraCycles, hcy, AddrMode.len, beq_self_eq_true]
  rw [e1, e2, e3]
  generalize branchTarget (s.pc + 2) (m.read (s.pc + 1)) = t
  cases branchCond s (decode (m.read s.pc)).instr <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hx : UInt16.hi t = UInt16.hi (s.pc + 2)
  · rw [← hx, UInt16.ofLoHi_lo_hi]; simp
  · simp [hx]

end Nes.Cpu.Proofs.Refinement
