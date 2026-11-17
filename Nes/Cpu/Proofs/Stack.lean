import Nes.Cpu.Isa

/-!
# `Nes.Cpu.Proofs.Stack` — T-CPU-6 (stack discipline)

## Spec

Throughout, `s : State`, `m : Mem`, `v : UInt8`. `stackAddr sp = $0100 | sp` is the address
`push`/`pull` of `Nes.Cpu.Isa` use: `push` writes at `stackAddr s.sp` then decrements `SP`;
`pull` increments `SP` then reads at `stackAddr (s.sp + 1)`.

* **Pull after push** (`T_CPU_6_pull_push`): `pull (push s m v)` returns exactly `(s, v)` —
  the value pushed and the original state, SP included — and the pushed memory differs from
  `m` only at the cell `stackAddr s.sp`.
* **Stack page** (`T_CPU_6_stack_page`): `stackAddr sp` is numerically `256 + sp`, so every
  stack access lies in `$0100–$01FF`; `push` writes at `stackAddr s.sp` and `pull` reads at
  `stackAddr (s.sp + 1)`, and SP itself is a byte, so wraps within the page.
* **`PHA; PLA`** (`T_CPU_6_pha_pla`): `$48` at `pc` and `$68` at `pc + 1` on a running CPU,
  with `pc + 1` not the pushed stack cell (else PHA overwrites the PLA opcode): two `step`s
  give `{ s with pc := pc + 2 }.setZN s.a` — A, SP, X, Y unchanged, N/Z set from A — memory
  `m` with `A` written at `stackAddr s.sp`, and 3 + 4 cycles.
* **`PHP; PLP`** (`T_CPU_6_php_plp`): likewise with `$08`, `$28`: the result is
  `{ s with pc := pc + 2, p := (s.p & $CF) | $20 }` — P unchanged except B (bit 4) cleared and
  bit 5 set, i.e. `p' & $CF = p & $CF` — and SP unchanged; PHP pushed `P | $30`.
* **`JSR … RTS`** (`T_CPU_6_jsr_rts`, general form): let `JSR abs` (`$20`) run at `s.pc`
  giving `(s₁, m₁)`. For *any* later `(s₂, m₂)` with `RTS` (`$60`) at `s₂.pc`, not halted,
  `s₂.sp = s₁.sp` (the code in between restored SP), and the two stacked cells
  `stackAddr s.sp`, `stackAddr (s.sp − 1)` holding what `m₁` holds there, `RTS` returns to
  `s.pc + 3` with `SP = s.sp`. Nothing is assumed about the code in between beyond these
  observable conditions. `T_CPU_6_jsr_rts_direct`: `JSR t` immediately followed by `RTS` at
  `t` (with `t` not one of the two stacked cells) returns to `s.pc + 3`, SP restored, 12 cycles.

Method: per-opcode `step` lemmas (`decode $NN = … := rfl`, then `simp only` over
`step`/`resolve`/`exec`/`push`/`pull`), read-after-write via `Vector.getElem_set`, and
`bv_decide` for the UInt8/UInt16 arithmetic (`$0100 | sp`, `sp − 1 + 1`, `pc + 1 + 1`).
-/

namespace Nes.Cpu.Proofs

open Nes Nes.Cpu

/-- Address of the stack cell for stack pointer `sp`. -/
@[inline] def stackAddr (sp : UInt8) : UInt16 := 0x100 ||| sp.toUInt16

theorem stack_read_write (m : Mem) (a b : UInt16) (v : UInt8) :
    (m.write a v).read b = if a = b then v else m.read b := by
  simp only [Mem.read, Mem.write, Vector.getElem_set, UInt16.toNat_inj]

theorem stackAddr_eq_add (sp : UInt8) : stackAddr sp = 0x100 + sp.toUInt16 := by
  unfold stackAddr; bv_decide

theorem stackAddr_toNat (sp : UInt8) : (stackAddr sp).toNat = 256 + sp.toNat := by
  rw [stackAddr_eq_add, _root_.UInt16.toNat_add, _root_.UInt8.toNat_toUInt16,
    show (0x100 : UInt16).toNat = 256 from rfl]
  have := sp.toNat_lt
  omega

theorem stackAddr_inj {a b : UInt8} : stackAddr a = stackAddr b ↔ a = b := by
  constructor
  · intro h
    have := congrArg UInt16.toNat h
    rw [stackAddr_toNat, stackAddr_toNat] at this
    exact _root_.UInt8.toNat_inj.mp (by omega)
  · rintro rfl; rfl

theorem stackAddr_sub_one_ne (sp : UInt8) : stackAddr sp ≠ stackAddr (sp - 1) := by
  rw [ne_eq, stackAddr_inj]; bv_decide

/-! ### Push / pull -/

theorem T_CPU_6_pull_push (s : State) (m : Mem) (v : UInt8) :
    pull (push s m v).1 (push s m v).2 = (s, v) ∧
    (push s m v).2 = m.write (stackAddr s.sp) v ∧
    (∀ a, a ≠ stackAddr s.sp → (push s m v).2.read a = m.read a) := by
  refine ⟨?_, rfl, ?_⟩
  · simp only [push, pull, _root_.UInt8.sub_add_cancel]
    refine Prod.ext rfl ?_
    show (m.write (stackAddr s.sp) v).read (stackAddr s.sp) = v
    simp [stack_read_write]
  · intro a ha
    show (m.write (stackAddr s.sp) v).read a = m.read a
    simp only [stack_read_write, Ne.symm ha, ↓reduceIte]

theorem T_CPU_6_stack_page (sp : UInt8) (s : State) (m : Mem) (v : UInt8) :
    (stackAddr sp).toNat = 256 + sp.toNat ∧
    0x100 ≤ (stackAddr sp).toNat ∧ (stackAddr sp).toNat ≤ 0x1FF ∧
    (push s m v).2 = m.write (stackAddr s.sp) v ∧
    (pull s m).2 = m.read (stackAddr (s.sp + 1)) := by
  have := sp.toNat_lt
  refine ⟨stackAddr_toNat sp, ?_, ?_, rfl, rfl⟩ <;> rw [stackAddr_toNat] <;> omega

/-! ### Per-opcode `step` lemmas -/

theorem decode_48 : decode 0x48 = ⟨.PHA, .imp, 3, false, true⟩ := rfl
theorem decode_68 : decode 0x68 = ⟨.PLA, .imp, 4, false, true⟩ := rfl
theorem decode_08 : decode 0x08 = ⟨.PHP, .imp, 3, false, true⟩ := rfl
theorem decode_28 : decode 0x28 = ⟨.PLP, .imp, 4, false, true⟩ := rfl
theorem decode_20 : decode 0x20 = ⟨.JSR, .abs, 6, false, true⟩ := rfl
theorem decode_60 : decode 0x60 = ⟨.RTS, .imp, 6, false, true⟩ := rfl

theorem step_pha (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x48) :
    step s m = ({ s with pc := s.pc + 1, sp := s.sp - 1 }, m.write (stackAddr s.sp) s.a, 3) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_48, Bool.false_eq_true, ite_false]
  rfl

theorem step_php (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x08) :
    step s m = ({ s with pc := s.pc + 1, sp := s.sp - 1 },
      m.write (stackAddr s.sp) (s.p ||| 0x30), 3) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_08, Bool.false_eq_true, ite_false]
  rfl

theorem step_pla (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x68) :
    step s m =
      (({ s with pc := s.pc + 1, sp := s.sp + 1, a := m.read (stackAddr (s.sp + 1)) }).setZN
        (m.read (stackAddr (s.sp + 1))), m, 4) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_68, Bool.false_eq_true, ite_false]
  rfl

theorem step_plp (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x28) :
    step s m =
      ({ s with pc := s.pc + 1, sp := s.sp + 1, p := (m.read (stackAddr (s.sp + 1)) &&& 0xCF) ||| 0x20 },
        m, 4) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_28, Bool.false_eq_true, ite_false]
  rfl

theorem step_jsr (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x20) :
    step s m = ({ s with sp := s.sp - 1 - 1, pc := m.read16 (s.pc + 1) },
      (m.write (stackAddr s.sp) (UInt16.hi (s.pc + 2))).write (stackAddr (s.sp - 1))
        (UInt16.lo (s.pc + 2)), 6) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_20, Bool.false_eq_true, ite_false]
  rfl

theorem step_rts (s : State) (m : Mem) (hh : s.halted = false) (h : m.read s.pc = 0x60) :
    step s m =
      ({ s with
          sp := s.sp + 1 + 1
          pc := UInt16.ofLoHi (m.read (stackAddr (s.sp + 1))) (m.read (stackAddr (s.sp + 1 + 1))) + 1 },
        m, 6) := by
  obtain ⟨a, x, y, sp, pc, p, halted⟩ := s
  subst hh
  simp only at h
  simp only [step, h, decode_60, Bool.false_eq_true, ite_false]
  rfl

/-! ### `PHA; PLA` and `PHP; PLP` -/

theorem T_CPU_6_pha_pla (s : State) (m : Mem) (hh : s.halted = false)
    (h1 : m.read s.pc = 0x48) (h2 : m.read (s.pc + 1) = 0x68)
    (hc : s.pc + 1 ≠ stackAddr s.sp) :
    let r1 := step s m
    let r2 := step r1.1 r1.2.1
    r2.1 = ({ s with pc := s.pc + 2 }).setZN s.a ∧ r2.1.a = s.a ∧ r2.1.sp = s.sp ∧
    r2.2.1 = m.write (stackAddr s.sp) s.a ∧ r1.2.2 + r2.2.2 = 7 := by
  have h2' : (m.write (stackAddr s.sp) s.a).read (s.pc + 1) = 0x68 := by
    simp only [stack_read_write, Ne.symm hc, ↓reduceIte, h2]
  have e := step_pla { s with pc := s.pc + 1, sp := s.sp - 1 } (m.write (stackAddr s.sp) s.a)
    hh h2'
  simp only [step_pha s m hh h1, e, _root_.UInt8.sub_add_cancel, stack_read_write, ↓reduceIte,
    show s.pc + 1 + 1 = s.pc + 2 by bv_decide]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (cases s; rfl)

theorem T_CPU_6_php_plp (s : State) (m : Mem) (hh : s.halted = false)
    (h1 : m.read s.pc = 0x08) (h2 : m.read (s.pc + 1) = 0x28)
    (hc : s.pc + 1 ≠ stackAddr s.sp) :
    let r1 := step s m
    let r2 := step r1.1 r1.2.1
    r2.1 = { s with pc := s.pc + 2, p := (s.p &&& 0xCF) ||| 0x20 } ∧
    r2.1.p &&& 0xCF = s.p &&& 0xCF ∧ r2.1.sp = s.sp ∧
    r2.2.1 = m.write (stackAddr s.sp) (s.p ||| 0x30) ∧ r1.2.2 + r2.2.2 = 7 := by
  have h2' : (m.write (stackAddr s.sp) (s.p ||| 0x30)).read (s.pc + 1) = 0x28 := by
    simp only [stack_read_write, Ne.symm hc, ↓reduceIte, h2]
  have e := step_plp { s with pc := s.pc + 1, sp := s.sp - 1 }
    (m.write (stackAddr s.sp) (s.p ||| 0x30)) hh h2'
  simp only [step_php s m hh h1, e, _root_.UInt8.sub_add_cancel, stack_read_write, ↓reduceIte,
    show s.pc + 1 + 1 = s.pc + 2 by bv_decide,
    show (s.p ||| 0x30) &&& 0xCF ||| 0x20 = s.p &&& 0xCF ||| 0x20 by bv_decide]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | bv_decide

/-! ### `JSR … RTS` -/

/-- General form: whatever runs between `JSR` and `RTS`, if it restores SP and leaves the two
stacked return-address cells as `JSR` wrote them, `RTS` returns to the instruction after the
`JSR` with SP restored. -/
theorem T_CPU_6_jsr_rts (s : State) (m : Mem) (hh : s.halted = false) (hj : m.read s.pc = 0x20)
    (s₂ : State) (m₂ : Mem) (hh₂ : s₂.halted = false) (hr : m₂.read s₂.pc = 0x60)
    (hsp : s₂.sp = (step s m).1.sp)
    (hhi : m₂.read (stackAddr s.sp) = (step s m).2.1.read (stackAddr s.sp))
    (hlo : m₂.read (stackAddr (s.sp - 1)) = (step s m).2.1.read (stackAddr (s.sp - 1))) :
    (step s₂ m₂).1.pc = s.pc + 3 ∧ (step s₂ m₂).1.sp = s.sp := by
  rw [step_jsr s m hh hj] at hsp hhi hlo
  simp only [stack_read_write, ↓reduceIte, Ne.symm (stackAddr_sub_one_ne s.sp)] at hhi hlo
  simp only at hsp
  rw [step_rts s₂ m₂ hh₂ hr]
  simp only [hsp, show s.sp - 1 - 1 + 1 = s.sp - 1 by bv_decide,
    show s.sp - 1 + 1 = s.sp by bv_decide, hhi, hlo, UInt16.ofLoHi_lo_hi]
  exact ⟨by bv_decide, trivial⟩

/-- Direct form: `JSR t` immediately followed by `RTS` at `t`. -/
theorem T_CPU_6_jsr_rts_direct (s : State) (m : Mem) (hh : s.halted = false)
    (hj : m.read s.pc = 0x20) (hr : m.read (m.read16 (s.pc + 1)) = 0x60)
    (ht1 : m.read16 (s.pc + 1) ≠ stackAddr s.sp)
    (ht2 : m.read16 (s.pc + 1) ≠ stackAddr (s.sp - 1)) :
    let r1 := step s m
    let r2 := step r1.1 r1.2.1
    r2.1.pc = s.pc + 3 ∧ r2.1.sp = s.sp ∧ r1.2.2 + r2.2.2 = 12 := by
  have hr' : (step s m).2.1.read (step s m).1.pc = 0x60 := by
    rw [step_jsr s m hh hj]
    simp only [stack_read_write, Ne.symm ht1, Ne.symm ht2, ↓reduceIte, hr]
  have hh' : (step s m).1.halted = false := by rw [step_jsr s m hh hj]; exact hh
  obtain ⟨hpc, hsp⟩ := T_CPU_6_jsr_rts s m hh hj _ _ hh' hr' rfl rfl rfl
  refine ⟨hpc, hsp, ?_⟩
  rw [step_rts _ _ hh' hr', step_jsr s m hh hj]
  rfl

end Nes.Cpu.Proofs
