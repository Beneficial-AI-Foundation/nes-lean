import Nes.Hoare.Tactics
import Nes.Cpu.Proofs.Alu

/-!
# `Nes.Hoare.Examples.Add16` — a verified 16-bit add

## Spec

The classic little-endian 16-bit add, assembled at `$8000` (13 bytes, exit `$800D`):

```
$8000  18        CLC
$8001  A5 10     LDA $10    ; lo(x)
$8003  65 12     ADC $12    ; + lo(y)
$8005  85 14     STA $14    ; lo(z)
$8007  A5 11     LDA $11    ; hi(x)
$8009  65 13     ADC $13    ; + hi(y) + carry
$800B  85 15     STA $15    ; hi(z)
```

With `x = m[$10] + 256·m[$11]` and `y = m[$12] + 256·m[$13]` (the initial memory, named by the
ghost bytes `a0 a1 b0 b1`):

* `add16_correct` (`Triple`): from any state that is running (`halted = false`) with the code in
  place, the routine reaches `$800D` with `m'[$14] + 256·m'[$15] = (x + y) % 65536` and
  `C' ↔ x + y ≥ 65536` (carry-out of the 16-bit sum). Nothing is assumed about the registers
  or the status byte `P`: the initial carry is cleared by `CLC`, and the decimal flag `D` is
  irrelevant (the 2A03 has no decimal mode; `Cpu.Isa`'s ADC ignores `D`).
* `add16_footprint` (`TripleM`): the run modifies memory only in `{$14, $15}`; in particular
  the operands and the code itself are unchanged (the postcondition also re-states `codeAt`).
* `add16_cycles` (`CTriple`): exactly 20 cycles (CLC 2 + six zero-page ops × 3).
* `add16_frame`: the frame rule (`Triple.frame`) carries an unrelated assertion (`m[$0200] = v`)
  across the routine, using only the footprint and an `Indep` side condition.

All are total-correctness statements about `Cpu.step` (see `Nes.Hoare.Logic`).
-/

namespace Nes.Hoare.Examples

open Nes Nes.Cpu Nes.Cpu.Proofs Nes.Hoare

/-- The routine's bytes (`CLC; LDA $10; ADC $12; STA $14; LDA $11; ADC $13; STA $15`). -/
def add16Code : List UInt8 :=
  [0x18, 0xA5, 0x10, 0x65, 0x12, 0x85, 0x14, 0xA5, 0x11, 0x65, 0x13, 0x85, 0x15]

/-- Precondition: running, code at `$8000`, operand bytes named `a0 a1` (x) and `b0 b1` (y). -/
def add16Pre (a0 a1 b0 b1 : UInt8) : Assn := fun s m =>
  s.halted = false ∧ codeAt m 0x8000 add16Code ∧
    m.read 0x10 = a0 ∧ m.read 0x11 = a1 ∧ m.read 0x12 = b0 ∧ m.read 0x13 = b1

/-- The 16-bit operands and their sum, as naturals. -/
def add16Sum (a0 a1 b0 b1 : UInt8) : Nat :=
  (a0.toNat + 256 * a1.toNat) + (b0.toNat + 256 * b1.toNat)

/-- Byte-level postcondition: exactly what the two `ADC`s compute. -/
def add16PostRaw (a0 a1 b0 b1 : UInt8) : Assn := fun s m =>
  m.read 0x14 = (Alu.fast.adc a0 b0 false).r ∧
    m.read 0x15 = (Alu.fast.adc a1 b1 (Alu.fast.adc a0 b0 false).c).r ∧
    s.c = (Alu.fast.adc a1 b1 (Alu.fast.adc a0 b0 false).c).c ∧
    codeAt m 0x8000 add16Code

/-- The arithmetic postcondition: a 16-bit add with carry-out. -/
def add16Post (a0 a1 b0 b1 : UInt8) : Assn := fun s m =>
  (m.read 0x14).toNat + 256 * (m.read 0x15).toNat = add16Sum a0 a1 b0 b1 % 65536 ∧
    (s.c = true ↔ 65536 ≤ add16Sum a0 a1 b0 b1)

/-- The footprint: `$14` and `$15`. -/
def add16Out : Region := region 0x14 2

/-! ## Symbolic execution -/

/-- The whole run, by symbolic execution, with its cycle count. -/
theorem add16_raw_cycles (a0 a1 b0 b1 : UInt8) :
    CTriple (add16Pre a0 a1 b0 b1) 0x8000 0x800D (add16PostRaw a0 a1 b0 b1) 20 := by
  unfold add16Pre add16PostRaw add16Code; hoare_run 7

/-- The whole run, by symbolic execution, with its memory footprint. -/
theorem add16_raw_footprint (a0 a1 b0 b1 : UInt8) :
    TripleM (add16Pre a0 a1 b0 b1) 0x8000 0x800D (add16PostRaw a0 a1 b0 b1) add16Out := by
  unfold add16Pre add16PostRaw add16Code; hoare_run 7
  exact ((Agree.refl _ _).write _ (by unfold add16Out region; decide)).write _
    (by unfold add16Out region; decide)

/-! ## The ALU argument: two 8-bit adds with carry chain = one 16-bit add -/

theorem add16_alu (a0 a1 b0 b1 : UInt8) (s : State) (m : Mem)
    (h : add16PostRaw a0 a1 b0 b1 s m) : add16Post a0 a1 b0 b1 s m := by
  obtain ⟨h14, h15, hc, -⟩ := h
  have l := T_CPU_1_adc a0 b0 false ⟨false, false, false, false, false, false⟩
  have hh := T_CPU_1_adc a1 b1 (Alu.fast.adc a0 b0 false).c ⟨false, false, false, false, false, false⟩
  rw [← T_REF_2_adc] at l hh
  obtain ⟨lr, lc, -⟩ := l
  obtain ⟨hr, hcar, -⟩ := hh
  have := a0.toNat_lt; have := a1.toNat_lt; have := b0.toNat_lt; have := b1.toNat_lt
  unfold add16Post add16Sum
  rw [h14, h15, hc, lr, hr, hcar]
  revert lc
  cases (Alu.fast.adc a0 b0 false).c <;> simp <;> omega

/-! ## The theorems -/

/-- **Correctness**: `{running ∧ code ∧ x, y in $10–$13} $8000 ⟶ $800D
{m'[$14] + 256·m'[$15] = (x + y) mod 2^16 ∧ (C' ↔ x + y ≥ 2^16)}`, for any registers and `P`. -/
theorem add16_correct (a0 a1 b0 b1 : UInt8) :
    Triple
      (fun s m => s.halted = false ∧ codeAt m 0x8000 add16Code ∧
        m.read 0x10 = a0 ∧ m.read 0x11 = a1 ∧ m.read 0x12 = b0 ∧ m.read 0x13 = b1)
      0x8000 0x800D
      (fun s m =>
        (m.read 0x14).toNat + 256 * (m.read 0x15).toNat =
            ((a0.toNat + 256 * a1.toNat) + (b0.toNat + 256 * b1.toNat)) % 65536 ∧
          (s.c = true ↔ 65536 ≤ (a0.toNat + 256 * a1.toNat) + (b0.toNat + 256 * b1.toNat))) :=
  (add16_raw_cycles a0 a1 b0 b1).toTriple.post (add16_alu a0 a1 b0 b1)

/-- **Footprint**: the run changes memory only at `$14`/`$15`; the code is still in place. -/
theorem add16_footprint (a0 a1 b0 b1 : UInt8) :
    TripleM (add16Pre a0 a1 b0 b1) 0x8000 0x800D
      (fun s m => add16Post a0 a1 b0 b1 s m ∧ codeAt m 0x8000 add16Code) (region 0x14 2) :=
  (add16_raw_footprint a0 a1 b0 b1).conseq (fun _ _ h => h)
    (fun s m h => ⟨add16_alu a0 a1 b0 b1 s m h, h.2.2.2⟩)

/-- **Cycles**: exactly 20 (CLC 2 + 6 × 3 for the zero-page `LDA`/`ADC`/`STA`). -/
theorem add16_cycles (a0 a1 b0 b1 : UInt8) :
    CTriple (add16Pre a0 a1 b0 b1) 0x8000 0x800D (add16Post a0 a1 b0 b1) 20 :=
  (add16_raw_cycles a0 a1 b0 b1).conseq (fun _ _ h => h) (add16_alu a0 a1 b0 b1)

/-- **Frame**: any assertion about memory outside `$14`/`$15` (here `m[$0200] = v`) survives the
routine — derived from the footprint by `Triple.frame`, without re-running the code. -/
theorem add16_frame (a0 a1 b0 b1 v : UInt8) :
    Triple (fun s m => add16Pre a0 a1 b0 b1 s m ∧ m.read 0x0200 = v) 0x8000 0x800D
      (fun s m => (add16Post a0 a1 b0 b1 s m ∧ codeAt m 0x8000 add16Code) ∧
        m.read 0x0200 = v) :=
  Triple.frame (R := fun m => m.read 0x0200 = v) (add16_footprint a0 a1 b0 b1)
    (fun _ _ hag h => (hag 0x0200 (by unfold region; decide)).trans h)

end Nes.Hoare.Examples
