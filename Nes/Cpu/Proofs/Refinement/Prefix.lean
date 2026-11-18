import Nes.Cpu.Proofs.Refinement.Core

/-!
# `Nes.Cpu.Proofs.Refinement.Prefix` — T-REF-1: the 13 addressing-mode prefixes

## Spec

`PrefixSpec mode`: let `ms` be the machine right after the opcode fetch of an instruction that
starts in state `s` (`PreCtx`: `pos = 1`, `cpu = s` with `PC + 1`, `crossed = false`), whose
program is `modePrefix mode ++ rest` with `rest` non-empty and not starting with a conditional
micro-op. Then there are latch values `base`, `data` such that, for any fuel `f`,
`runInstr (f + k) ms m = bump k (runInstr f ms' m)` where
* `k = prefixCycles mode pageCross crossed` = number of prefix micro-ops, minus one when the
  `indexFixup` of `absx/absy/indy` is skipped (read opcode, no page cross);
* `ms'` is `ms` with `PC` advanced by the operand bytes (`prefixPcInc`), `pos` pointing at the
  first micro-op of `rest`, `addr`/`crossed` = `Isa.resolve s m mode` for the modes that resolve
  an address (`ind`: the pointer `m.read16 (s.pc + 1)`, see `prefixAddr`), unchanged for
  `imp/acc/imm/rel` (whose operand, if any, is fetched by the suffix);
* the memory passed on is `m` itself: prefixes perform no writes;
* for the indexed modes `base = addr - index` (the un-indexed base, used by `SHY/SHX/AHX/TAS`).

`prefix_<mode>` proves `PrefixSpec` for each of the 13 modes; `prefix_spec` collects them.
Method: symbolic execution of `runInstr` cycle by cycle (`cyc`, `cyc_skip`), with a case
split on the page-cross condition for the three fixup modes.
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

/-! ## Addressing prefixes -/

/-- Does the prefix of `mode` resolve an operand address? -/
def resolvesAddr : AddrMode → Bool
  | .imp | .acc | .imm | .rel => false
  | _ => true

/-- Operand bytes fetched (PC increments) by `modePrefix mode`. -/
def prefixPcInc : AddrMode → UInt16
  | .imp | .acc | .imm | .rel => 0
  | .zp | .zpx | .zpy | .indx | .indy => 1
  | .abs | .absx | .absy | .ind => 2

/-- Modes whose prefix ends in the (conditional) `indexFixup`. -/
def hasFixup : AddrMode → Bool
  | .absx | .absy | .indy => true
  | _ => false

/-- Index register added by an indexed mode. -/
def indexReg (s : State) : AddrMode → UInt8
  | .absx => s.x
  | .absy | .indy => s.y
  | _ => 0

/-- What the prefix leaves in `(addr, crossed)`: `Isa.resolve`'s effective address, except for
`JMP (ind)` whose prefix stops at the pointer (the suffix does the buggy indirection). -/
def prefixAddr (s : State) (m : Mem) : AddrMode → UInt16 × Bool
  | .ind => (m.read16 (s.pc + 1), false)
  | mode => resolve s m mode

/-- Cycles spent in `modePrefix mode`: one per micro-op, minus the skipped `indexFixup`
(read with `pageCross` that did not cross). -/
def prefixCycles (mode : AddrMode) (pageCross crossed : Bool) : Nat :=
  (modePrefix mode).size - (if hasFixup mode && pageCross && !crossed then 1 else 0)

/-- The machine just after the opcode fetch of an instruction starting in `s`, whose program is
`modePrefix mode ++ rest` with a non-empty, non-conditional-headed `rest`. -/
structure PreCtx (s : State) (ms : MicroState) (mode : AddrMode) (rest : MicroProgram) : Prop where
  pos : ms.pos = 1
  cpu : ms.cpu = { s with pc := s.pc + 1 }
  crossed : ms.crossed = false
  prog : uops ms.op = modePrefix mode ++ rest
  rest_ne : rest.size ≠ 0
  rest_nc : isCond (rest.getD 0 .jamHalt) = false

/-- Spec of an addressing prefix: running it takes `prefixCycles` cycles, only reads (memory is
unchanged), advances PC past the operand bytes, leaves `prefixAddr` in `addr`/`crossed` (for the
modes that resolve an address) and the un-indexed base in `base`, and stops at the suffix. -/
def PrefixSpec (mode : AddrMode) : Prop :=
  ∀ (s : State) (m : Mem) (ms : MicroState) (rest : MicroProgram) (f : Nat), PreCtx s ms mode rest →
    ∃ base data,
      let r := if resolvesAddr mode then prefixAddr s m mode else (ms.addr, ms.crossed)
      let k := prefixCycles mode (decode ms.op).pageCross r.2
      runInstr (f + k) ms m =
        bump k (runInstr f
          { ms with cpu := { s with pc := s.pc + 1 + prefixPcInc mode },
                    pos := (modePrefix mode).size.toUInt8 + 1,
                    addr := r.1, crossed := r.2, base := base, data := data } m) ∧
      (hasFixup mode = true → base = r.1 - (indexReg s mode).toUInt16)

set_option hygiene false in
/-- Open a `PrefixSpec` goal: destructure the context, pick the `base`/`data` witnesses. -/
macro "prefix_intro" b:term:max d:term:max : tactic => `(tactic| (
  intro s m ms rest f ⟨hpos, hcpu, hcr, hu, hr, hc⟩
  have hc' := fun ms => skips_of_not_isCond ms _ hc
  rw [Array.getD_eq_getD_getElem?] at hc'
  simp only [modePrefix] at hu
  refine ⟨$b, $d, ?_, by simp [hasFixup, resolvesAddr, prefixAddr, resolve, absIndexed, zpPtr,
    indexReg, Mem.read16, UInt16.add_assoc]⟩
  simp only [resolvesAddr, prefixCycles, hasFixup, prefixAddr, modePrefix, prefixPcInc,
    List.size_toArray, List.length_cons, List.length_nil, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, Nat.sub_zero, ite_true, Nat.reduceAdd]))

theorem mod256_mod256 (x : UInt16) : x % 256 % 256 = x % 256 := by
  apply UInt16.toNat_inj.mp; simp [UInt16.toNat_mod]

/-- Close the final equation between the computed and the spec'd post-prefix machine. -/
macro "prefix_close" : tactic => `(tactic| (
  simp [bump, resolve, zpIndexed, absIndexed, zpPtr, Mem.read16, UInt16.add_assoc, UInt16.lo, mod256_mod256, *]))

theorem prefix_imp : PrefixSpec .imp := by
  prefix_intro ms.base ms.data
  cases ms; simp_all [bump]

theorem prefix_zp : PrefixSpec .zp := by
  prefix_intro ms.base ms.data
  cyc
  prefix_close

theorem prefix_zpx : PrefixSpec .zpx := by
  prefix_intro ms.base ms.data
  rw [show f + 2 = f + 1 + 1 from rfl]
  cyc; cyc
  prefix_close

theorem prefix_zpy : PrefixSpec .zpy := by
  prefix_intro ms.base ms.data
  rw [show f + 2 = f + 1 + 1 from rfl]
  cyc; cyc
  prefix_close

theorem prefix_abs : PrefixSpec .abs := by
  prefix_intro ms.base (m.read (s.pc + 1))
  rw [show f + 2 = f + 1 + 1 from rfl]
  cyc; cyc
  prefix_close

theorem prefix_ind : PrefixSpec .ind := by
  prefix_intro ms.base (m.read (s.pc + 1))
  rw [show f + 2 = f + 1 + 1 from rfl]
  cyc; cyc
  prefix_close

theorem prefix_acc : PrefixSpec .acc := by
  prefix_intro ms.base ms.data
  cases ms; simp_all [bump]

theorem prefix_imm : PrefixSpec .imm := by
  prefix_intro ms.base ms.data
  cases ms; simp_all [bump]

theorem prefix_rel : PrefixSpec .rel := by
  prefix_intro ms.base ms.data
  cases ms; simp_all [bump]

theorem prefix_indx : PrefixSpec .indx := by
  prefix_intro ms.base (m.read (m.read (s.pc + 1) + s.x).toUInt16)
  rw [show f + 4 = f + 1 + 1 + 1 + 1 from rfl]
  cyc; cyc; cyc; cyc
  prefix_close

theorem prefix_absx : PrefixSpec .absx := by
  prefix_intro (UInt16.ofLoHi (m.read (s.pc + 1)) (m.read (s.pc + 2))) (m.read (s.pc + 1))
  split <;> rename_i hx <;>
    simp [resolve, absIndexed, Mem.read16, UInt16.add_assoc] at hx
  · rw [show f + (3 - 1) = f + 1 + 1 from rfl]
    cyc; cyc_skip
    prefix_close
  · rw [show f + (3 - 0) = f + 1 + 1 + 1 from rfl]
    cyc; cyc; cyc
    prefix_close

theorem prefix_absy : PrefixSpec .absy := by
  prefix_intro (UInt16.ofLoHi (m.read (s.pc + 1)) (m.read (s.pc + 2))) (m.read (s.pc + 1))
  split <;> rename_i hx <;>
    simp [resolve, absIndexed, Mem.read16, UInt16.add_assoc] at hx
  · rw [show f + (3 - 1) = f + 1 + 1 from rfl]
    cyc; cyc_skip
    prefix_close
  · rw [show f + (3 - 0) = f + 1 + 1 + 1 from rfl]
    cyc; cyc; cyc
    prefix_close

theorem prefix_indy : PrefixSpec .indy := by
  prefix_intro (zpPtr m (m.read (s.pc + 1))) (m.read (m.read (s.pc + 1)).toUInt16)
  split <;> rename_i hx <;>
    simp [resolve, absIndexed, zpPtr, UInt16.add_assoc] at hx
  · rw [show f + (4 - 1) = f + 1 + 1 + 1 from rfl]
    cyc; cyc; cyc_skip
    prefix_close
  · rw [show f + (4 - 0) = f + 1 + 1 + 1 + 1 from rfl]
    cyc; cyc; cyc; cyc
    prefix_close


theorem prefix_spec : ∀ mode, PrefixSpec mode
  | .imp => prefix_imp | .acc => prefix_acc | .imm => prefix_imm | .rel => prefix_rel
  | .zp => prefix_zp | .zpx => prefix_zpx | .zpy => prefix_zpy | .abs => prefix_abs
  | .absx => prefix_absx | .absy => prefix_absy | .ind => prefix_ind | .indx => prefix_indx
  | .indy => prefix_indy

end Nes.Cpu.Proofs.Refinement
