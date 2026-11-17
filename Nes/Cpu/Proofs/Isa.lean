import Nes.Cpu.Isa

/-!
# `Nes.Cpu.Proofs.Isa` — T-CPU-5 (addressing-mode laws)

## Spec

Throughout, `m : Mem`, `b i z : UInt8`, `base ptr pc : UInt16`.

* **Zero page stays in page 0.** `zpIndexed b i` (the `zp,X` / `zp,Y` address) is
  `(b + i) mod 256` numerically, hence `< 256` (`T_CPU_5_zp_page0`). The `(zp,X)` / `(zp),Y`
  pointer fetch `zpPtr m z` reads its low byte from `z` and its high byte from
  `(z + 1) mod 256`, both in page 0 (`T_CPU_5_zpPtr`).
* **Page-cross condition.** `absIndexed base i = (ea, crossed)` has
  `ea = (base + i) mod 2^16` and `crossed ↔ ea / 256 ≠ base / 256` (`T_CPU_5_pageCross`).
  Because `i < 256`, the 64 KiB wrap does not matter: `crossed` is also equivalent to the
  unwrapped condition `(base + i) / 256 ≠ base / 256` of PLAN §6.2
  (`T_CPU_5_pageCross_unwrapped`); e.g. `base = $FFFF, i = 1` gives `ea = $0000` and
  `crossed = true` under both readings. `resolve` routes `abs,X`, `abs,Y` and `(zp),Y` through
  this one function (`T_CPU_5_resolve_indexed`).
* **Page-cross cycle.** For a non-branch opcode, `step` costs `cycles(op)` plus exactly one
  extra cycle iff `pageCross(op) ∧ crossed` (`T_CPU_5_step_cycles`); for a branch, `+1` if
  taken and `+2` if taken to another page (`T_CPU_5_step_cycles_branch`).
* **`JMP ($xxFF)` bug.** `indirectBug m ptr` reads its high byte from
  `(ptr & $FF00) | ((ptr + 1) & $FF)` (`T_CPU_5_jmp_ind_hiAddr`); hence when `ptr.lo = $FF`
  the high byte comes from `ptr & $FF00` (= `$xx00`, not `$xx00 + $100`)
  (`T_CPU_5_jmp_ind_bug`), and otherwise `indirectBug m ptr = m.read16 ptr`
  (`T_CPU_5_jmp_ind_nobug`).
* **PC wraps `$FFFF → $0000`.** A 1-byte NOP (`$EA`) at `pc = $FFFF` on a non-halted CPU
  leaves `pc = $0000`, memory unchanged, 2 cycles (`T_CPU_5_pc_wrap`). `branchTarget` is
  `pc + off` (`off < $80`) or `pc + off − 256` (`off ≥ $80`) modulo 2^16
  (`T_CPU_5_branchTarget`).

Method: `toNat` bridging (`UInt16.toNat_add`, `UInt8.toNat_toUInt16`, `toNat_hi`) and `omega`
for the arithmetic laws; `bv_decide` for the bit-level pointer arithmetic of `JMP (ind)`;
targeted `simp only` unfolding of `step` for the cycle and PC-wrap facts.
-/

namespace Nes.Cpu.Proofs

open Nes Nes.Cpu

/-! ### Zero page -/

theorem T_CPU_5_zp_page0 (b i : UInt8) :
    (zpIndexed b i).toNat = (b.toNat + i.toNat) % 256 ∧ (zpIndexed b i).toNat < 256 := by
  simp only [zpIndexed, _root_.UInt8.toNat_toUInt16, _root_.UInt8.toNat_add, true_and]
  omega

theorem T_CPU_5_zpPtr (m : Mem) (z : UInt8) :
    zpPtr m z = UInt16.ofLoHi (m[z.toNat]'(by have := z.toNat_lt; omega))
      (m[(z.toNat + 1) % 256]'(by omega)) := by
  simp only [zpPtr, Mem.read, _root_.UInt8.toNat_toUInt16, _root_.UInt8.toNat_add]
  rfl

/-! ### Page crossing -/

theorem T_CPU_5_pageCross (base : UInt16) (i : UInt8) :
    (absIndexed base i).1.toNat = (base.toNat + i.toNat) % 65536 ∧
    ((absIndexed base i).2 = true ↔ (base.toNat + i.toNat) % 65536 / 256 ≠ base.toNat / 256) := by
  simp only [absIndexed, bne_iff_ne, ne_eq, ← _root_.UInt8.toNat_inj, UInt16.toNat_hi,
    _root_.UInt16.toNat_add, _root_.UInt8.toNat_toUInt16, and_self]

theorem T_CPU_5_pageCross_unwrapped (base : UInt16) (i : UInt8) :
    (absIndexed base i).2 = true ↔ (base.toNat + i.toNat) / 256 ≠ base.toNat / 256 := by
  rw [(T_CPU_5_pageCross base i).2]
  have := i.toNat_lt; have := base.toNat_lt
  omega

/-- `abs,X`, `abs,Y` and `(zp),Y` all compute `(ea, crossed)` with `absIndexed`. -/
theorem T_CPU_5_resolve_indexed (s : State) (m : Mem) :
    resolve s m .absx = absIndexed (m.read16 (s.pc + 1)) s.x ∧
    resolve s m .absy = absIndexed (m.read16 (s.pc + 1)) s.y ∧
    resolve s m .indy = absIndexed (zpPtr m (m.read (s.pc + 1))) s.y :=
  ⟨rfl, rfl, rfl⟩

theorem T_CPU_5_step_cycles (s : State) (m : Mem) (hh : s.halted = false)
    (hrel : (decode (m.read s.pc)).mode ≠ .rel) :
    (step s m).2.2 = (decode (m.read s.pc)).cycles.toNat +
      (if (decode (m.read s.pc)).pageCross && (resolve s m (decode (m.read s.pc)).mode).2
        then 1 else 0) := by
  simp only [step, hh, extraCycles, Bool.false_eq_true, ite_false]
  simp [hrel]

theorem T_CPU_5_step_cycles_branch (s : State) (m : Mem) (hh : s.halted = false)
    (hrel : (decode (m.read s.pc)).mode = .rel) :
    (step s m).2.2 = (decode (m.read s.pc)).cycles.toNat +
      (if branchCond s (decode (m.read s.pc)).instr then
        (if (resolve s m .rel).2 then 2 else 1) else 0) := by
  simp only [step, hh, extraCycles, Bool.false_eq_true, ite_false]
  simp [hrel]

/-! ### `JMP (ind)` -/

theorem T_CPU_5_jmp_ind_hiAddr (m : Mem) (ptr : UInt16) :
    indirectBug m ptr =
      UInt16.ofLoHi (m.read ptr) (m.read ((ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF))) := by
  have : UInt16.ofLoHi (UInt16.lo ptr + 1) (UInt16.hi ptr) =
      (ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF) := by
    simp only [UInt16.ofLoHi, UInt16.lo, UInt16.hi]
    bv_decide
  simp only [indirectBug, this]

theorem T_CPU_5_jmp_ind_bug (m : Mem) (ptr : UInt16) (h : UInt16.lo ptr = 0xFF) :
    indirectBug m ptr = UInt16.ofLoHi (m.read ptr) (m.read (ptr &&& 0xFF00)) := by
  have : (ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF) = ptr &&& 0xFF00 := by
    simp only [UInt16.lo] at h
    bv_decide
  rw [T_CPU_5_jmp_ind_hiAddr, this]

theorem T_CPU_5_jmp_ind_nobug (m : Mem) (ptr : UInt16) (h : UInt16.lo ptr ≠ 0xFF) :
    indirectBug m ptr = m.read16 ptr := by
  have : (ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF) = ptr + 1 := by
    simp only [UInt16.lo] at h
    bv_decide
  rw [T_CPU_5_jmp_ind_hiAddr, this]
  rfl

/-! ### PC wrap -/

theorem decode_EA : decode 0xEA = ⟨.NOP, .imp, 2, false, true⟩ := by decide

theorem T_CPU_5_pc_wrap (s : State) (m : Mem) (hh : s.halted = false) (hpc : s.pc = 0xFFFF)
    (hop : m.read 0xFFFF = 0xEA) :
    (step s m).1.pc = 0x0000 ∧ (step s m).2.1 = m ∧ (step s m).2.2 = 2 := by
  simp only [step, hh, hpc, hop, decode_EA, Bool.false_eq_true, ite_false]
  refine ⟨?_, rfl, rfl⟩
  show s.pc + 1 = 0
  rw [hpc]
  decide

theorem T_CPU_5_branchTarget (pc : UInt16) (off : UInt8) :
    (branchTarget pc off).toNat =
      if off.toNat < 128 then (pc.toNat + off.toNat) % 65536
      else (pc.toNat + off.toNat + 65280) % 65536 := by
  unfold branchTarget
  have := off.toNat_lt; have := pc.toNat_lt
  by_cases h : off < 0x80
  · have h' : off.toNat < 128 := by simpa [_root_.UInt8.lt_iff_toNat_lt] using h
    simp only [h, h', ite_true, _root_.UInt16.toNat_add, _root_.UInt8.toNat_toUInt16]
  · have h' : ¬ off.toNat < 128 := by simpa [_root_.UInt8.lt_iff_toNat_lt] using h
    simp only [h, h', ite_false, _root_.UInt16.toNat_add, _root_.UInt16.toNat_sub,
      _root_.UInt8.toNat_toUInt16, show (256 : UInt16).toNat = 256 from rfl]
    omega

end Nes.Cpu.Proofs
