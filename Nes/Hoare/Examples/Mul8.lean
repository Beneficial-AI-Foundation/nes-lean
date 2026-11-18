import Nes.Hoare.Tactics
import Nes.Cpu.Proofs.Alu

/-!
# `Nes.Hoare.Examples.Mul8` — a verified 8×8→16 shift-and-add multiply

## Spec

The classic 6502 shift-and-add multiply (multiplier bits consumed LSB first by `LSR`, partial
product shifted right through `A:$12` by `ROR`), at `$8000`:

```
$8000  A9 00     LDA #$00
$8002  A2 08     LDX #$08
$8004  46 11     LSR $11        ; C := bit 0 of the multiplier
$8006  90 03     loop: BCC skip
$8008  18        CLC
$8009  65 10     ADC $10        ; add the multiplicand to the high byte
$800B  6A        skip: ROR A    ; shift the 9-bit sum C:A right ...
$800C  66 12     ROR $12        ; ... into the low byte
$800E  46 11     LSR $11        ; C := next multiplier bit
$8010  CA        DEX
$8011  D0 F3     BNE loop
$8013  85 13     STA $13
$8015            (exit)
```

Inputs: multiplicand `a` in `$10`, multiplier `b` in `$11`. Output: the 16-bit product in
`$13` (high, also left in `A`) and `$12` (low). `$11` is consumed (ends as 0); the initial
contents of `$12` are irrelevant (shifted out). Exhaustively tested before proving: all 65 536
`(a, b)` pairs run on `Cpu.step` give `a * b`, in `171 + 4·popcount(b)` cycles (171..203).

* `mul8Acc` / `mul8_acc_step`: the loop invariant, in `Nat`. With `X = x` at the loop head
  (`k = 8 - x` iterations done): C = bit `k` of `b`, `$11 = b >> (k+1)`, and
  `A·2^k + ($12 >> x) = a · (b mod 2^k)` (the partial product of the low `k` multiplier bits;
  the top `k` bits of `$12` hold its low part). `mul8_acc_step` is one iteration.
* `mul8_loop`: the loop `$8006 ⟶ $8013`, by `Triple.loop_branch` (measure `X`), the body split
  at the `BCC` with `Triple.branch`.
* `mul8_spec`: the whole routine with a ghost initial memory `m0`; `mul8_correct`: the
  product `$13·256 + $12 = a·b` (and `A = $13`); `mul8_footprint`: as a `TripleM`, only
  `$11..$13` (`mul8F`) change.
-/

namespace Nes.Hoare.Examples

open Nes Nes.Cpu Nes.Cpu.Proofs Nes.Hoare

/-- The routine's bytes at `$8000`. -/
def mul8Code : List UInt8 := [0xA9, 0x00, 0xA2, 0x08, 0x46, 0x11, 0x90, 0x03, 0x18, 0x65, 0x10,
  0x6A, 0x66, 0x12, 0x46, 0x11, 0xCA, 0xD0, 0xF3, 0x85, 0x13]

/-- The footprint: `$11` (consumed multiplier), `$12`, `$13` (product). -/
def mul8F : Region := region 0x11 3

/-! ## The invariant, in `Nat` -/

/-- Loop-head invariant with `X = x`: `k = 8 - x` iterations done. -/
def mul8Acc (a b x A cin q l : Nat) : Prop :=
  cin = b / 2 ^ (8 - x) % 2 ∧ q = b / 2 ^ (8 - x + 1) ∧
    A * 2 ^ (8 - x) + l / 2 ^ x = a * (b % 2 ^ (8 - x))

/-- One iteration: add `cin·a` to `A` (9-bit sum `S`), shift `S` right into `l`, shift `q`. -/
theorem mul8_acc_step {a b x A cin q l : Nat} (hx1 : 1 ≤ x) (hx8 : x ≤ 8)
    (h : mul8Acc a b x A cin q l) :
    mul8Acc a b (x - 1) ((A + cin * a) / 2) (q % 2) (q / 2)
      (l / 2 + 128 * ((A + cin * a) % 2)) := by
  obtain ⟨hc, hq, hP⟩ := h
  have e : 8 - (x - 1) = 8 - x + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [e, hq]
  · rw [e, hq, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · rw [e, Nat.mod_pow_succ, Nat.mul_add, ← hc]
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ (8 - x)) with hb' | hb' <;> rw [hb'] at hc <;>
      subst hc <;>
      have : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 := by omega
    all_goals
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceAdd, Nat.mod_one, Nat.mul_zero,
        Nat.div_one, Nat.mul_one] at hP ⊢ <;> omega

theorem mul8_acc_init {a b l : Nat} (hl : l < 256) : mul8Acc a b 8 0 (b % 2) (b / 2) l := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.mod_one] <;> omega

theorem mul8_acc_done {a b A cin q l : Nat} (hb : b < 256) (h : mul8Acc a b 0 A cin q l) :
    A * 256 + l = a * b := by
  obtain ⟨_, _, hP⟩ := h
  simpa [Nat.mod_eq_of_lt hb] using hP

/-! ## ALU facts used (from the `fast` definitions, by `decide` / T-REF-2) -/

theorem mul8_ror (v : UInt8) (c : Bool) :
    (Alu.fast.ror v c).r.toNat = v.toNat / 2 + 128 * c.toNat ∧
    (Alu.fast.ror v c).c = decide (v.toNat % 2 = 1) := by
  revert v c; decide

theorem mul8_lsr (q : UInt8) :
    (Alu.fast.lsr q).r.toNat = q.toNat / 2 ∧ (Alu.fast.lsr q).c = decide (q.toNat % 2 = 1) := by
  revert q; decide

theorem mul8_adc (A v : UInt8) :
    (Alu.fast.adc A v false).r.toNat + 256 * (Alu.fast.adc A v false).c.toNat =
      A.toNat + v.toNat := by
  rw [T_REF_2_adc]
  simp only [Alu.spec.adc]
  have := A.toNat_lt; have := v.toNat_lt
  by_cases h : 256 ≤ A.toNat + v.toNat <;> simp [h] <;> omega

theorem mul8_decide_toNat (n : Nat) : (decide (n % 2 = 1)).toNat = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-! ## Straight-line segments (ghost memory `M`, by symbolic execution) -/

/-- `LDA #0; LDX #8; LSR $11`. -/
theorem mul8_seg_init (M : Mem) :
    Triple (fun s m => s.halted = false ∧ codeAt M 0x8000 mul8Code ∧ m = M) 0x8000 0x8006
      (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ s.a = 0 ∧ s.x = 8 ∧
        s.c = (Alu.fast.lsr (M.read 0x11)).c ∧
        m = M.write 0x11 (Alu.fast.lsr (M.read 0x11)).r) := by
  unfold mul8Code; hoare_run 3

/-- `CLC; ADC $10` (the `BCC` fell through). -/
theorem mul8_seg_add (M : Mem) (A X : UInt8) :
    Triple (fun s m => s.halted = false ∧ codeAt M 0x8000 mul8Code ∧ m = M ∧ s.a = A ∧
        s.x = X) 0x8008
      0x800B
      (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m = M ∧
        s.a = (Alu.fast.adc A (M.read 0x10) false).r ∧
        s.c = (Alu.fast.adc A (M.read 0x10) false).c ∧ s.x = X) := by
  unfold mul8Code; hoare_run 2

/-- `ROR A; ROR $12; LSR $11; DEX`. -/
theorem mul8_seg_tail (M : Mem) (A X : UInt8) (c : Bool) :
    Triple (fun s m => s.halted = false ∧ codeAt M 0x8000 mul8Code ∧ m = M ∧ s.a = A ∧
        s.c = c ∧ s.x = X) 0x800B 0x8011
      (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ s.a = (Alu.fast.ror A c).r ∧
        m = (M.write 0x12 (Alu.fast.ror (M.read 0x12) (Alu.fast.ror A c).c).r).write 0x11
          (Alu.fast.lsr (M.read 0x11)).r ∧
        s.c = (Alu.fast.lsr (M.read 0x11)).c ∧ s.x = X - 1 ∧ s.z = (X - 1 == 0)) := by
  unfold mul8Code; hoare_run 4

/-- `STA $13`. -/
theorem mul8_seg_exit (M : Mem) (A : UInt8) :
    Triple (fun s m => s.halted = false ∧ codeAt M 0x8000 mul8Code ∧ m = M ∧ s.a = A) 0x8013
      0x8015 (fun s m => s.a = A ∧ m = M.write 0x13 A) := by
  unfold mul8Code; hoare_run 1

/-! ## The loop -/

theorem mul8_code_bytes {m : Mem} (h : codeAt m 0x8000 mul8Code) :
    m.read 0x8006 = 0x90 ∧ m.read 0x8007 = 0x03 ∧ m.read 0x8011 = 0xD0 ∧
      m.read 0x8012 = 0xF3 := by
  simp [mul8Code] at h; simp [h]

/-- Loop-head invariant (`lo ≤ X`; `lo = 1` at the head, `0` after `DEX`). -/
def mul8Inv (a b : UInt8) (m0 : Mem) (lo : Nat) : Assn := fun s m =>
  s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m.read 0x10 = a ∧ Agree mul8F m0 m ∧
    lo ≤ s.x.toNat ∧ s.x.toNat ≤ 8 ∧
    mul8Acc a.toNat b.toNat s.x.toNat s.a.toNat s.c.toNat (m.read 0x11).toNat (m.read 0x12).toNat

/-- At `skip` (`$800B`): `C:A` holds the 9-bit sum `A0 + cin·a` of the head values. -/
def mul8Mid (a b : UInt8) (m0 : Mem) (n : Nat) : Assn := fun s m =>
  s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m.read 0x10 = a ∧ Agree mul8F m0 m ∧
    1 ≤ s.x.toNat ∧ s.x.toNat ≤ 8 ∧ s.x.toNat = n ∧
    ∃ A0 cin, mul8Acc a.toNat b.toNat s.x.toNat A0 cin (m.read 0x11).toNat (m.read 0x12).toNat ∧
      s.a.toNat + 256 * s.c.toNat = A0 + cin * a.toNat

/-- At the `BNE` (`$8011`), after `DEX`; `n` is the measure at the head. -/
def mul8R (a b : UInt8) (m0 : Mem) (n : Nat) : Assn := fun s m =>
  mul8Inv a b m0 0 s m ∧ s.z = (s.x == 0) ∧ s.x.toNat + 1 = n

theorem mul8_F11 : mul8F 0x11 := by unfold mul8F region; decide
theorem mul8_F12 : mul8F 0x12 := by unfold mul8F region; decide
theorem mul8_F13 : mul8F 0x13 := by unfold mul8F region; decide

/-- `skip ⟶ BNE`: the shift and the counter. -/
theorem mul8_tail (a b : UInt8) (m0 : Mem) (n : Nat) :
    Triple (mul8Mid a b m0 n) 0x800B 0x8011 (mul8R a b m0 n) := by
  intro s m ⟨hM, hpc⟩
  obtain ⟨hh, hc, h10, hag, hx1, hx8, hxn, A0, cin, hacc, hS⟩ := hM
  obtain ⟨k, hpc', hh', hc', ha', hm', hc'', hx', hz'⟩ :=
    mul8_seg_tail m s.a s.x s.c s m ⟨⟨hh, hc, rfl, rfl, rfl, rfl⟩, hpc⟩
  refine ⟨k, hpc', ?_⟩
  generalize steps k s m = r at *
  obtain ⟨s', m', _⟩ := r
  simp only at *
  subst hm'
  have hstep := mul8_acc_step hx1 hx8 hacc
  rw [← hS] at hstep
  have hr := mul8_ror s.a s.c
  have hr2 := mul8_ror (m.read 0x12) (Alu.fast.ror s.a s.c).c
  have hl := mul8_lsr (m.read 0x11)
  have hx0 : s.x ≠ 0 := fun e => by rw [e] at hx1; simp at hx1
  have hxs := uint8_sub_one_toNat _ hx0
  have hct : (Alu.fast.ror s.a s.c).c.toNat = s.a.toNat % 2 := by
    rw [hr.2, mul8_decide_toNat]
  have e1 : (s.a.toNat + 256 * s.c.toNat) / 2 = (Alu.fast.ror s.a s.c).r.toNat := by
    rw [hr.1]; omega
  have e2 : (s.a.toNat + 256 * s.c.toNat) % 2 = (Alu.fast.ror s.a s.c).c.toNat := by
    rw [hct]; omega
  have e3 : (m.read 0x12).toNat / 2 + 128 * (Alu.fast.ror s.a s.c).c.toNat =
      (Alu.fast.ror (m.read 0x12) (Alu.fast.ror s.a s.c).c).r.toNat := hr2.1.symm
  rw [e1, e2, e3] at hstep
  refine ⟨⟨hh', hc', ?_, ?_, Nat.zero_le _, ?_, ?_⟩, ?_, ?_⟩
  · simp [read_write, h10]
  · exact (hag.write _ mul8_F12).write _ mul8_F11
  · rw [hx']; omega
  · have e4 : s.x.toNat - 1 = s'.x.toNat := by rw [hx']; omega
    have e5 : (m.read 0x11).toNat % 2 = s'.c.toNat := by rw [hc'', hl.2, mul8_decide_toNat]
    have e6 : (m.read 0x11).toNat / 2 = (Alu.fast.lsr (m.read 0x11)).r.toNat := hl.1.symm
    rw [e4, e5, e6, ← ha'] at hstep
    simpa [read_write] using hstep
  · rw [hz', hx']
  · rw [hx']; omega

/-- The loop body `$8006 ⟶ $8011`, split at the `BCC`. -/
theorem mul8_body (a b : UInt8) (m0 : Mem) (n : Nat) :
    Triple (fun s m => mul8Inv a b m0 1 s m ∧ s.x.toNat = n) 0x8006 0x8011 (mul8R a b m0 n) := by
  refine Triple.branch (op := 0x90) (off := 0x03) .bcc (fun _ _ _ h => h) ?_ ?_ ?_
  · intro s m ⟨⟨hh, hc, _⟩, _⟩ _
    exact ⟨hh, (mul8_code_bytes hc).1, (mul8_code_bytes hc).2.1⟩
  · -- taken (C = 0): nothing added
    refine (mul8_tail a b m0 n).pre ?_
    intro s m ⟨⟨⟨hh, hc, h10, hag, hx1, hx8, hacc⟩, hn⟩, hb⟩
    simp only [branchCond, Bool.not_eq_true'] at hb
    refine ⟨hh, hc, h10, hag, hx1, hx8, hn, s.a.toNat, s.c.toNat, hacc, ?_⟩
    simp [hb]
  · -- fall through (C = 1): `CLC; ADC $10`
    refine Triple.seq (mid := 0x800B) ?_ (mul8_tail a b m0 n)
    intro s m ⟨⟨⟨⟨hh, hc, h10, hag, hx1, hx8, hacc⟩, hn⟩, hb⟩, hpc⟩
    simp only [branchCond, Bool.not_eq_false'] at hb
    obtain ⟨k, hpc', hh', _, hm', ha', hca', hx⟩ :=
      mul8_seg_add m s.a s.x s m ⟨⟨hh, hc, rfl, rfl, rfl⟩, hpc⟩
    refine ⟨k, hpc', ?_⟩
    have hadd := mul8_adc s.a (m.read 0x10)
    rw [← ha', ← hca'] at hadd
    unfold mul8Mid
    rw [hm', hx]
    refine ⟨hh', hc, h10, hag, hx1, hx8, hn, s.a.toNat, s.c.toNat, hacc, ?_⟩
    rw [hadd, hb, h10]; simp

/-- **The loop** `$8006 ⟶ $8013`: eight iterations (measure `X`), ending with `X = 0`. -/
theorem mul8_loop (a b : UInt8) (m0 : Mem) :
    Triple (mul8Inv a b m0 1) 0x8006 0x8013 (fun s m => mul8Inv a b m0 0 s m ∧ s.x = 0) :=
  Triple.loop_branch (b := 0x8011) (op := 0xD0) (off := 0xF3) (instr := .BNE)
    (R := mul8R a b m0) (fun s _ => s.x.toNat) .bne (by decide) (mul8_body a b m0)
    (fun _ _ _ ⟨⟨hh, hc, _⟩, _⟩ => ⟨hh, (mul8_code_bytes hc).2.2⟩)
    (by
      intro n s m ⟨⟨hh, hc, h10, hag, _, hx8, hacc⟩, hz, hn⟩ hb
      simp only [branchCond, hz, Bool.not_eq_true', beq_eq_false_iff_ne] at hb
      have : s.x.toNat ≠ 0 := fun e => hb (UInt8.toNat_inj.mp (by simpa using e))
      exact ⟨⟨hh, hc, h10, hag, show 1 ≤ s.x.toNat by omega, hx8, hacc⟩,
        show s.x.toNat < n by omega⟩)
    (by
      intro n s m ⟨hI, hz, _⟩ hb
      simp only [branchCond, hz, Bool.not_eq_false', beq_iff_eq] at hb
      exact ⟨hI, hb⟩)

/-- **The routine** with a ghost initial memory `m0`: product and footprint. -/
theorem mul8_spec (a b : UInt8) (m0 : Mem) :
    Triple (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m.read 0x10 = a ∧
        m.read 0x11 = b ∧ Agree mul8F m0 m) 0x8000 0x8015
      (fun s m => (m.read 0x13).toNat * 256 + (m.read 0x12).toNat = a.toNat * b.toNat ∧
        s.a = m.read 0x13 ∧ Agree mul8F m0 m) := by
  refine Triple.seq (mid := 0x8006) ?_ (Triple.seq (mid := 0x8013) (mul8_loop a b m0) ?_)
  · intro s m ⟨⟨hh, hc, h10, h11, hag⟩, hpc⟩
    obtain ⟨k, hpc', hh', hc', ha', hx', hc'', hm'⟩ := mul8_seg_init m s m ⟨⟨hh, hc, rfl⟩, hpc⟩
    refine ⟨k, hpc', ?_⟩
    generalize steps k s m = r at *
    obtain ⟨s', m', _⟩ := r
    simp only at *
    subst hm'
    have hl := mul8_lsr (m.read 0x11)
    rw [h11] at hl hc'' hc' ⊢
    refine ⟨hh', hc', ?_, hag.write _ mul8_F11, by rw [hx']; decide, by rw [hx']; decide, ?_⟩
    · simp [read_write, h10]
    · have hacc := mul8_acc_init (a := a.toNat) (b := b.toNat) (m.read 0x12).toNat_lt
      rw [hx', ha', hc'', hl.2, mul8_decide_toNat]
      simp only [read_write, show ¬ ((0x11 : UInt16) = 0x12) from by decide, ↓reduceIte, hl.1]
      simpa using hacc
  · intro s m ⟨⟨⟨hh, hc, h10, hag, _, _, hacc⟩, hx0⟩, hpc⟩
    obtain ⟨k, hpc', ha', hm'⟩ := mul8_seg_exit m s.a s m ⟨⟨hh, hc, rfl, rfl⟩, hpc⟩
    refine ⟨k, hpc', ?_⟩
    generalize steps k s m = r at *
    obtain ⟨s', m', _⟩ := r
    simp only at *
    subst hm'
    rw [hx0] at hacc
    have := mul8_acc_done b.toNat_lt (by simpa using hacc)
    refine ⟨?_, ?_, hag.write _ mul8_F13⟩
    · simpa [read_write, ha'] using this
    · simp [read_write, ha']

/-- **Correctness**: `$13·256 + $12 = a·b` (and `A = $13`). -/
theorem mul8_correct (a b : UInt8) :
    Triple (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m.read 0x10 = a ∧
        m.read 0x11 = b) 0x8000 0x8015
      (fun s m => (m.read 0x13).toNat * 256 + (m.read 0x12).toNat = a.toNat * b.toNat ∧
        s.a = m.read 0x13) := by
  intro s m ⟨⟨hh, hc, h10, h11⟩, hpc⟩
  obtain ⟨k, hpc', h1, h2, _⟩ := mul8_spec a b m s m ⟨⟨hh, hc, h10, h11, Agree.refl _ _⟩, hpc⟩
  exact ⟨k, hpc', h1, h2⟩

/-- **Footprint**: only `$11..$13` change. -/
theorem mul8_footprint (a b : UInt8) :
    TripleM (fun s m => s.halted = false ∧ codeAt m 0x8000 mul8Code ∧ m.read 0x10 = a ∧
        m.read 0x11 = b) 0x8000 0x8015
      (fun s m => (m.read 0x13).toNat * 256 + (m.read 0x12).toNat = a.toNat * b.toNat ∧
        s.a = m.read 0x13) mul8F := by
  intro s m ⟨hh, hc, h10, h11⟩ hpc
  obtain ⟨k, hpc', h1, h2, h3⟩ := mul8_spec a b m s m ⟨⟨hh, hc, h10, h11, Agree.refl _ _⟩, hpc⟩
  exact ⟨k, hpc', ⟨h1, h2⟩, h3⟩

end Nes.Hoare.Examples
