import Nes.Cpu.Micro

/-!
# `Nes.Cpu.Proofs.Refinement.Core` — T-REF-1 framework: running the micro-machine symbolically

## Spec

* `bump k r` adds `k` to the cycle count of a `runInstr` result.
* `runInstr_succ`: one equation step of `runInstr` (one cycle, stop at a boundary).
* `runInstr_fetch`: from a non-halted boundary state `ofState s`, the first cycle is the opcode
  fetch and leaves `fetched s (m.read s.pc)` (pos 1, `PC + 1`, all latches at their defaults).
* `uops_eq`: `uops op = program (decode op)` (the table is the pointwise program).
* `advance_one/two/end`: `advance` moves to the next micro-op, skips one conditional micro-op,
  or ends the instruction, under the obvious conditions on the program.
* `exec_op`, `exec_pos`: micro-op effects never touch `op` / `pos`.
* Tactics: `cyc` (one cycle, next micro-op not skipped), `cyc_skip` (one cycle, next micro-op
  skipped), `cyc_start`, `skp`. They expect the program as a hypothesis
  `uops ms.op = #[…] ++ rest` (concrete head) in context, plus `hc'` saying `rest[0]` is never
  skipped, and close side conditions by `simp [*]`.

Design (T-REF-1): compositional. The microcode is `prefixFor cls mode ++ suffix cls`, so the
refinement proof is split into 13 addressing-prefix lemmas (`Refinement.Prefix`), ~15
class-suffix lemmas, and table facts over the 256 opcodes checked by `decide +kernel`. A
prefix lemma has the shape `runInstr (f + k) ms m = bump k (runInstr f ms' m)`: it consumes `k`
cycles and hands an explicit machine `ms'` to the rest of the program, with the same memory
(prefixes only read).
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

/-- Add `k` cycles to a `runInstr` result. -/
def bump (k : Nat) (r : MicroState × Mem × Nat) : MicroState × Mem × Nat := (r.1, r.2.1, r.2.2 + k)

/-- One step of `runInstr`: run a cycle, stop if it reached a boundary. -/
theorem runInstr_succ (f : Nat) (ms : MicroState) (m : Mem) :
    runInstr (f + 1) ms m =
      if (ms.cycle m).1.pos == 0 then ((ms.cycle m).1, (ms.cycle m).2, 1)
      else bump 1 (runInstr f (ms.cycle m).1 (ms.cycle m).2) := by
  simp only [runInstr, bump]

/-- The machine right after the opcode-fetch cycle. -/
def fetched (s : State) (op : UInt8) : MicroState :=
  { cpu := { s with pc := s.pc + 1 }, op := op, pos := 1 }

theorem runInstr_fetch (f : Nat) (s : State) (m : Mem) (h : s.halted = false) :
    runInstr (f + 1) (ofState s) m = bump 1 (runInstr f (fetched s (m.read s.pc)) m) := by
  rw [runInstr_succ]
  simp [cycle, busOp, ofState, complete, h, fetched]


/-- Conditional micro-ops (the only ones `skips` can skip). -/
def isCond : MicroOp → Bool
  | .indexFixup | .branchTaken | .branchFixup => true
  | _ => false

theorem skips_of_not_isCond (ms : MicroState) (u : MicroOp) (h : isCond u = false) :
    ms.skips u = false := by
  cases u <;> simp_all [isCond, skips]

@[simp] theorem exec_op (ms : MicroState) (u : MicroOp) (v : UInt8) : (ms.exec u v).op = ms.op := by
  cases u <;> simp only [MicroState.exec] <;> split <;> rfl

@[simp] theorem exec_pos (ms : MicroState) (u : MicroOp) (v : UInt8) : (ms.exec u v).pos = ms.pos := by
  cases u <;> simp only [MicroState.exec] <;> split <;> rfl

theorem advance_one (ms : MicroState) (hi : ms.pos.toNat < (uops ms.op).size)
    (hs : ms.skips ((uops ms.op).getD ms.pos.toNat .jamHalt) = false) :
    ms.advance = { ms with pos := (ms.pos.toNat + 1).toUInt8 } := by
  simp only [advance, hs, hi, decide_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem advance_two (ms : MicroState) (hi : ms.pos.toNat + 1 < (uops ms.op).size)
    (hs : ms.skips ((uops ms.op).getD ms.pos.toNat .jamHalt) = true)
    (hs' : ms.skips ((uops ms.op).getD (ms.pos.toNat + 1) .jamHalt) = false) :
    ms.advance = { ms with pos := (ms.pos.toNat + 2).toUInt8 } := by
  have : ms.pos.toNat < (uops ms.op).size := by omega
  simp only [advance, hs, hs', hi, this, decide_true, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, ↓reduceIte]

theorem advance_end (ms : MicroState) (hi : (uops ms.op).size ≤ ms.pos.toNat) :
    ms.advance = { ms with pos := 0 } := by
  have : ¬ ms.pos.toNat < (uops ms.op).size := by omega
  simp only [advance, this, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem uops_eq (op : UInt8) : uops op = program (decode op) := by
  simp [uops, uopTable, decodeFin, decode]

theorem curOp_eq (ms : MicroState) : ms.curOp = (uops ms.op).getD (ms.pos.toNat - 1) .jamHalt := rfl

/-- Run one cycle whose successor is not a boundary. -/
theorem runInstr_cyc (f : Nat) (ms ms' : MicroState) (m m' : Mem) (hc : ms.cycle m = (ms', m'))
    (hp : ms'.pos ≠ 0) : runInstr (f + 1) ms m = bump 1 (runInstr f ms' m') := by
  rw [runInstr_succ, hc]; simp [hp]

/-- Decide whether the next micro-op is skipped. -/
macro "skp" : tactic => `(tactic|
  first
    | (simp [*, Array.getElem?_append]; done)
    | (simp [*, Array.getElem?_append, skips, MicroState.exec, UInt16.add_assoc, UInt16.lo]; done)
    | (simp [*, Array.getElem?_append, skips, MicroState.exec, UInt16.add_assoc, UInt16.lo]; assumption))

/-- Unfold one cycle of `runInstr` (the micro-op at `pos` is computed from `uops`). -/
macro "cyc_start" : tactic => `(tactic| (
  rw [runInstr_succ]
  simp only [cycle, busOp, curOp_eq, complete, *]
  simp [Array.getElem?_append]))

/-- One prefix cycle whose successor micro-op is not skipped. -/
macro "cyc" : tactic => `(tactic| (
  cyc_start
  rw [advance_one _ (by simp [*]; omega) (by skp)]
  simp [MicroState.exec, *]))

/-- One prefix cycle whose successor micro-op is skipped (and the one after it is not). -/
macro "cyc_skip" : tactic => `(tactic| (
  cyc_start
  rw [advance_two _ (by simp [*]; omega) (by skp)
    (by skp)]
  simp [MicroState.exec, *]))

end Nes.Cpu.Proofs.Refinement
