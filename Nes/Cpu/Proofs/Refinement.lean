import Nes.Cpu.Proofs.Refinement.Classes

/-!
# `Nes.Cpu.Proofs.Refinement` — T-REF-1 (top level)

The framework, the 13 addressing-prefix lemmas and the first instruction classes live in
`Refinement/Core.lean`, `Refinement/Prefix.lean` and `Refinement/Classes.lean`. The
remaining suffix classes live in `Refinement/Suffix*.lean`; this module assembles
`∀ c, ClassRefines c` and concludes T-REF-1 via `T_REF_1_of_classes`.
-/
