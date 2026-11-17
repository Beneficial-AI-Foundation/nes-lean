import Nes.Cpu.Proofs.Refinement.SuffixRmw
import Nes.Cpu.Proofs.Refinement.SuffixBranch
import Nes.Cpu.Proofs.Refinement.SuffixControl
import Nes.Cpu.Proofs.Refinement.SuffixStack
import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement` — T-REF-1 (top level)

The framework, the 13 addressing-prefix lemmas and the first instruction classes live in
`Refinement/Core.lean`, `Refinement/Prefix.lean` and `Refinement/Classes.lean`. The
remaining suffix classes live in `Refinement/Suffix*.lean`; this module assembles
`∀ c, ClassRefines c` and concludes T-REF-1 via `T_REF_1_of_classes`.
-/

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu

/-- Every instruction class refines the ISA. -/
theorem all_classes_refine : ∀ c, ClassRefines c := by
  intro c
  cases c
  · exact T_REF_1_read
  · exact T_REF_1_imm
  · exact T_REF_1_imp
  · exact T_REF_1_write
  · exact T_REF_1_rmw
  · exact T_REF_1_push
  · exact T_REF_1_pull
  · exact T_REF_1_jsr
  · exact T_REF_1_rts
  · exact T_REF_1_rti
  · exact T_REF_1_brk
  · exact T_REF_1_jmpAbs
  · exact T_REF_1_jmpInd
  · exact T_REF_1_branch
  · exact T_REF_1_jam

/-- **T-REF-1.** For every opcode and every non-halted state, running the micro-op machine
from a fresh instruction boundary (no pending interrupt) to the next boundary against pure
memory yields exactly `Isa.step`'s registers, memory and cycle count (base cycles plus
page-cross and branch penalties). -/
theorem T_REF_1 (s : State) (m : Mem) (h : s.halted = false) : microStep s m = step s m :=
  T_REF_1_of_classes all_classes_refine s m h

end Nes.Cpu.Proofs.Refinement
