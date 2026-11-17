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
  , `Nes.Cpu.Proofs.T_CPU_4_pageCross ]

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
