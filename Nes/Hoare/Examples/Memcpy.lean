import Nes.Hoare.Tactics

/-!
# `Nes.Hoare.Examples.Memcpy` — a verified small-block copy

## Spec

The routine, at `$8000` (10 bytes, `memcpyCode`):

```
$8000  A0 00     LDY #$00
$8002  B1 00     loop: LDA ($00),Y   ; A := m[src + Y]
$8004  91 02           STA ($02),Y   ; m[dst + Y] := A
$8006  C8              INY
$8007  CA              DEX
$8008  D0 F8           BNE loop
$800A            (exit)
```

Inputs: the count `n` (`1 ≤ n ≤ 256`) in `X` as `UInt8.ofNat n` (so `X = 0` means 256), the
source pointer `src` at `$00/$01` and the destination pointer `dst` at `$02/$03` (little
endian). `memcpyPre n src dst` collects these plus `halted = false` and the code bytes.

Hypotheses (separation, via `Region.Disjoint` on `region lo len`):
* `region src n` and `region dst n` are disjoint (no overlapping copy);
* `region dst n` is disjoint from the pointers `region 0 4` and from the code
  `region $8000 10`. The source block is only read, so it may overlap the pointers or code.

Address arithmetic is honest 16-bit: the `i`-th byte is at `dst + UInt16.ofNat i` (mod 2^16),
exactly what `(zp),Y` computes, so blocks that wrap past `$FFFF` are covered — no no-wrap
hypothesis is needed (the `region` predicate wraps the same way).

Theorems:
* `memcpy_correct`: `{memcpyPre ∧ m = m0} $8000 ⟶ $800A {∀ i < n, m[dst+i] = m0[src+i] ∧
  m[src+i] = m0[src+i]}` (total correctness).
* `memcpy_footprint`: a `TripleM` with footprint `region dst n` — every cell outside
  `[dst, dst+n)` (the source, the pointers, the code, the stack) is unchanged.
* `memcpy_spec`: both at once (`memcpyPost`), from which the two above are corollaries.
* Loop invariant `memcpyInv n src dst m0` at `$8002`: `∃ j < n, Y = j ∧ X = ofNat (n - j) ∧`
  memory agrees with `m0` outside `region dst n` `∧` the prefix `[0, j)` is copied. Measure
  `n - Y`. `memcpy_body` is the per-iteration triple (`$8002 ⟶ $8008`, post
  `memcpyBodyPost`, with `Z = (X == 0)` for the branch), `memcpy_loop` closes the loop with
  `Triple.loop_branch`, `memcpy_init` is the `LDY #$00` step.
* `memcpy_body_run` is the symbolic execution of the four body instructions.

Cycle counts are not stated (the `(zp),Y` page-cross penalty makes them data-dependent).
-/

namespace Nes.Hoare.Examples

open Nes Nes.Cpu Nes.Cpu.Proofs Nes.Hoare

/-- The routine's bytes, loaded at `$8000`. -/
def memcpyCode : List UInt8 :=
  [0xA0, 0x00, 0xB1, 0x00, 0x91, 0x02, 0xC8, 0xCA, 0xD0, 0xF8]

/-- The four body instructions `LDA ($00),Y; STA ($02),Y; INY; DEX`, run symbolically. -/
theorem memcpy_body_run (s : State) (m : Mem) (src dst : UInt16) (hh : s.halted = false)
    (hpc : s.pc = 0x8002)
    (c0 : m.read 0x8002 = 0xB1) (c1 : m.read 0x8003 = 0x00) (c2 : m.read 0x8004 = 0x91)
    (c3 : m.read 0x8005 = 0x02) (c4 : m.read 0x8006 = 0xC8) (c5 : m.read 0x8007 = 0xCA)
    (hs : zpPtr m 0 = src) (hd : zpPtr m 2 = dst)
    (n6 : dst + s.y.toUInt16 ≠ 0x8006) (n7 : dst + s.y.toUInt16 ≠ 0x8007) :
    (steps 4 s m).1.pc = 0x8008 ∧ (steps 4 s m).1.halted = false ∧
    (steps 4 s m).1.y = s.y + 1 ∧ (steps 4 s m).1.x = s.x - 1 ∧
    (steps 4 s m).1.z = (s.x - 1 == 0) ∧
    (steps 4 s m).2.1 = m.write (dst + s.y.toUInt16) (m.read (src + s.y.toUInt16)) := by
  simp only [steps_succ, steps_zero]
  simp [step, exec, resolve, extraCycles, absIndexed, read_write, AddrMode.len, State.ldA,
    Alu.fast.inc, Alu.fast.dec, dec_B1, dec_91, dec_C8, dec_CA, hh, hpc, c0, c1, c2, c3, c4, c5, hs, hd,
    n6, n7, FlagLemmas.setZN_pc, FlagLemmas.setZN_halted, FlagLemmas.setZN_a, FlagLemmas.setZN_x,
    FlagLemmas.setZN_y, FlagLemmas.setZN_z]

/-- A byte widened to 16 bits is its numeric value. -/
theorem memcpy_toUInt16 (y : UInt8) : y.toUInt16 = UInt16.ofNat y.toNat := by
  apply UInt16.toNat_inj.mp
  simp

/-- `ofNat (a+1) - 1 = ofNat a` in `UInt8`. -/
theorem memcpy_ofNat_sub (a : Nat) : UInt8.ofNat (a + 1) - 1 = UInt8.ofNat a := by
  rw [UInt8.ofNat_add]
  simp

/-- A byte literal below 256 is zero only if the number is. -/
theorem memcpy_ofNat_eq_zero (a : Nat) (h : a < 256) (h0 : UInt8.ofNat a = 0) : a = 0 := by
  have := congrArg UInt8.toNat h0
  simp at this
  omega

/-- Offset recovery: `(a + i) - a = i` for `i < 2^16`. -/
theorem memcpy_sub_ofNat (a : UInt16) (i : Nat) (hi : i < 65536) :
    (a + UInt16.ofNat i - a).toNat = i := by
  have e : ∀ x : UInt16, a + x - a = x := fun x => by bv_decide
  rw [e]
  simp
  omega

/-- The `i`-th address of a block of length `n` lies in its region. -/
theorem memcpy_in_region (a : UInt16) (i n : Nat) (hi : i < n) (hn : n ≤ 256) :
    region a n (a + UInt16.ofNat i) := by
  unfold region
  rw [memcpy_sub_ofNat a i (by omega)]
  exact hi

/-- Distinct offsets give distinct addresses. -/
theorem memcpy_ofNat_inj (a : UInt16) (i j : Nat) (hi : i < 65536) (hj : j < 65536)
    (h : a + UInt16.ofNat i = a + UInt16.ofNat j) : i = j := by
  have := congrArg (fun x => (x - a).toNat) h
  rwa [memcpy_sub_ofNat a i hi, memcpy_sub_ofNat a j hj] at this


/-- The code bytes, one literal address each. -/
theorem memcpy_code_bytes (m : Mem) (h : codeAt m 0x8000 memcpyCode) :
    m.read 0x8000 = 0xA0 ∧ m.read 0x8001 = 0x00 ∧ m.read 0x8002 = 0xB1 ∧
    m.read 0x8003 = 0x00 ∧ m.read 0x8004 = 0x91 ∧ m.read 0x8005 = 0x02 ∧
    m.read 0x8006 = 0xC8 ∧ m.read 0x8007 = 0xCA ∧ m.read 0x8008 = 0xD0 ∧
    m.read 0x8009 = 0xF8 := by
  simp only [memcpyCode, codeAt_cons, codeAt_nil] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Code and pointers in memory. -/
def memcpyMem (src dst : UInt16) (m : Mem) : Prop :=
  codeAt m 0x8000 memcpyCode ∧ m.read 0 = UInt16.lo src ∧ m.read 1 = UInt16.hi src ∧
    m.read 2 = UInt16.lo dst ∧ m.read 3 = UInt16.hi dst

/-- Precondition. -/
def memcpyPre (n : Nat) (src dst : UInt16) : Assn := fun s m =>
  s.halted = false ∧ s.x = UInt8.ofNat n ∧ memcpyMem src dst m

/-- Loop invariant at the head `$8002`. -/
def memcpyInv (n : Nat) (src dst : UInt16) (m0 : Mem) : Assn := fun s m =>
  s.halted = false ∧ ∃ j, j < n ∧ s.y.toNat = j ∧ s.x = UInt8.ofNat (n - j) ∧
    Agree (region dst n) m0 m ∧
    ∀ i, i < j → m.read (dst + UInt16.ofNat i) = m0.read (src + UInt16.ofNat i)

/-- After the body, at the `BNE` (`$8008`). -/
def memcpyBodyPost (n : Nat) (src dst : UInt16) (m0 : Mem) (k : Nat) : Assn := fun s m =>
  s.halted = false ∧ ∃ j, j < n ∧ n - j = k ∧ s.y.toNat = (j + 1) % 256 ∧
    s.x = UInt8.ofNat (n - j) - 1 ∧ s.z = (s.x == 0) ∧ Agree (region dst n) m0 m ∧
    ∀ i, i < j + 1 → m.read (dst + UInt16.ofNat i) = m0.read (src + UInt16.ofNat i)

/-- One iteration: `$8002 ⟶ $8008`, copying byte `j`. -/
theorem memcpy_body (n : Nat) (src dst : UInt16) (m0 : Mem) (hn : n ≤ 256)
    (hmem : memcpyMem src dst m0)
    (hsd : Region.Disjoint (region src n) (region dst n))
    (hdp : Region.Disjoint (region dst n) (region 0 4))
    (hdc : Region.Disjoint (region dst n) (region 0x8000 10)) (k : Nat) :
    Triple (fun s m => memcpyInv n src dst m0 s m ∧ n - s.y.toNat = k) 0x8002 0x8008
      (memcpyBodyPost n src dst m0 k) := by
  apply Triple.of_steps 4
  rintro s m ⟨⟨hh, j, hj, hy, hx, hag, hcp⟩, hk⟩ hpc
  have kp : ∀ a, region 0x8000 10 a → m.read a = m0.read a :=
    fun a ha => hag a (fun hd => hdc a hd ha)
  have kz : ∀ a, region 0 4 a → m.read a = m0.read a :=
    fun a ha => hag a (fun hd => hdp a hd ha)
  obtain ⟨hcode, p0, p1, p2, p3⟩ := hmem
  obtain ⟨-, -, c2, c3, c4, c5, c6, c7, -, -⟩ := memcpy_code_bytes m0 hcode
  have hs : zpPtr m 0 = src := by
    show UInt16.ofLoHi (m.read 0) (m.read 1) = src
    rw [kz 0 (by unfold region; decide), kz 1 (by unfold region; decide), p0, p1,
      UInt16.ofLoHi_lo_hi]
  have hd : zpPtr m 2 = dst := by
    show UInt16.ofLoHi (m.read 2) (m.read 3) = dst
    rw [kz 2 (by unfold region; decide), kz 3 (by unfold region; decide), p2, p3,
      UInt16.ofLoHi_lo_hi]
  have hwa : dst + s.y.toUInt16 = dst + UInt16.ofNat j := by rw [memcpy_toUInt16, hy]
  have hin : region dst n (dst + s.y.toUInt16) := hwa ▸ memcpy_in_region dst j n hj hn
  have nc : ∀ a : UInt16, region 0x8000 10 a → dst + s.y.toUInt16 ≠ a :=
    fun a ha e => hdc a (e ▸ hin) ha
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := memcpy_body_run s m src dst hh hpc
    ((kp _ (by unfold region; decide)).trans c2) ((kp _ (by unfold region; decide)).trans c3)
    ((kp _ (by unfold region; decide)).trans c4) ((kp _ (by unfold region; decide)).trans c5)
    ((kp _ (by unfold region; decide)).trans c6) ((kp _ (by unfold region; decide)).trans c7)
    hs hd (nc _ (by unfold region; decide)) (nc _ (by unfold region; decide))
  refine ⟨r1, r2, j, hj, by omega, ?_, by rw [r4, hx], by rw [r5, r4], ?_, ?_⟩
  · rw [r3]; simp [UInt8.toNat_add, hy]
  · rw [r6]; exact hag.write _ hin
  · intro i hi
    rw [r6, read_write, hwa]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [memcpy_toUInt16, hy]
      exact hag _ (fun hd => hsd _ (memcpy_in_region src i n hj hn) hd)
    · have : dst + UInt16.ofNat j ≠ dst + UInt16.ofNat i :=
        fun e => hij (memcpy_ofNat_inj dst j i (by omega) (by omega) e).symm
      simp only [this, ↓reduceIte]
      exact hcp i (by omega)


/-- The postcondition at the exit `$800A`. -/
def memcpyPost (n : Nat) (src dst : UInt16) (m0 : Mem) : Assn := fun s m =>
  s.halted = false ∧
    (∀ i, i < n → m.read (dst + UInt16.ofNat i) = m0.read (src + UInt16.ofNat i)) ∧
    Agree (region dst n) m0 m

/-- The loop `$8002 ⟶ $800A`, by `Triple.loop_branch` with measure `n - Y`. -/
theorem memcpy_loop (n : Nat) (src dst : UInt16) (m0 : Mem) (hn : n ≤ 256)
    (hmem : memcpyMem src dst m0)
    (hsd : Region.Disjoint (region src n) (region dst n))
    (hdp : Region.Disjoint (region dst n) (region 0 4))
    (hdc : Region.Disjoint (region dst n) (region 0x8000 10)) :
    Triple (memcpyInv n src dst m0) 0x8002 0x800A (memcpyPost n src dst m0) := by
  have hb := memcpy_code_bytes m0 hmem.1
  refine Triple.loop_branch (b := 0x8008) (off := 0xF8) (op := 0xD0) (instr := .BNE)
    (R := memcpyBodyPost n src dst m0) (fun s _ => n - s.y.toNat) .bne (by decide)
    (memcpy_body n src dst m0 hn hmem hsd hdp hdc) ?_ ?_ ?_
  · rintro k s m ⟨hh, j, -, -, -, -, -, hag, -⟩
    refine ⟨hh, ?_, ?_⟩
    · rw [hag _ (fun hd => hdc _ hd (by unfold region; decide))]; exact hb.2.2.2.2.2.2.2.2.1
    · rw [hag _ (fun hd => hdc _ hd (by unfold region; decide))]; exact hb.2.2.2.2.2.2.2.2.2
  · rintro k s m ⟨hh, j, hj, hk, hy, hx, hz, hag, hcp⟩ hc
    simp only [branchCond, hz, Bool.not_eq_true', beq_eq_false_iff_ne] at hc
    have e : n - j = (n - j - 1) + 1 := by omega
    rw [e, memcpy_ofNat_sub] at hx
    have hlt : j + 1 < n := by
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact h
      · exfalso; apply hc; rw [hx, show n - j - 1 = 0 by omega]; rfl
    have hy' : s.y.toNat = j + 1 := by rw [hy]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨hh, j + 1, hlt, hy', by rw [hx]; congr 1, hag, hcp⟩, ?_⟩
    show n - s.y.toNat < k
    omega
  · rintro k s m ⟨hh, j, hj, hk, hy, hx, hz, hag, hcp⟩ hc
    simp only [branchCond, hz, Bool.not_eq_false', beq_iff_eq] at hc
    have e : n - j = (n - j - 1) + 1 := by omega
    rw [e, memcpy_ofNat_sub] at hx
    have h0 := memcpy_ofNat_eq_zero _ (by omega) (hx ▸ hc)
    refine ⟨hh, fun i hi => hcp i (by omega), hag⟩


/-- `LDY #$00` establishes the invariant with `j = 0`. -/
theorem memcpy_init (n : Nat) (src dst : UInt16) (m0 : Mem) (hn1 : 1 ≤ n) :
    Triple (fun s m => memcpyPre n src dst s m ∧ m = m0) 0x8000 0x8002
      (memcpyInv n src dst m0) := by
  apply Triple.of_step
  rintro s m ⟨⟨hh, hx, hmem⟩, rfl⟩ hpc
  obtain ⟨c0, c1, -⟩ := memcpy_code_bytes m hmem.1
  simp only [step, exec, resolve, hh, hpc, c0, dec_A0, AddrMode.len]
  simp only [show (32768 : UInt16) + 1 = 0x8001 from rfl, show (32768 : UInt16) + 2 = 0x8002 from rfl,
    c1, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by first | trivial | rfl, ?_⟩
  exact ⟨rfl, 0, by omega, rfl, by rw [hx]; rfl, Agree.refl _ _, fun i hi => by omega⟩

/-- The whole routine, with the initial memory `m0` as a ghost. -/
theorem memcpy_spec (n : Nat) (src dst : UInt16) (hn1 : 1 ≤ n) (hn : n ≤ 256)
    (hsd : Region.Disjoint (region src n) (region dst n))
    (hdp : Region.Disjoint (region dst n) (region 0 4))
    (hdc : Region.Disjoint (region dst n) (region 0x8000 10)) (m0 : Mem) :
    Triple (fun s m => memcpyPre n src dst s m ∧ m = m0) 0x8000 0x800A
      (memcpyPost n src dst m0) := by
  rintro s m ⟨⟨hpre, hm⟩, hpc⟩
  subst hm
  exact ((memcpy_init n src dst m hn1).seq (memcpy_loop n src dst m hn hpre.2.2 hsd hdp hdc))
    s m ⟨⟨hpre, rfl⟩, hpc⟩


/-- **Correctness.** From `memcpyPre` with initial memory `m0`, the routine reaches `$800A` with
`dst[i] = m0[src + i]` for every `i < n`, and the source block still intact. -/
theorem memcpy_correct (n : Nat) (src dst : UInt16) (hn1 : 1 ≤ n) (hn : n ≤ 256)
    (hsd : Region.Disjoint (region src n) (region dst n))
    (hdp : Region.Disjoint (region dst n) (region 0 4))
    (hdc : Region.Disjoint (region dst n) (region 0x8000 10)) (m0 : Mem) :
    Triple (fun s m => memcpyPre n src dst s m ∧ m = m0) 0x8000 0x800A
      (fun _ m =>
        (∀ i, i < n → m.read (dst + UInt16.ofNat i) = m0.read (src + UInt16.ofNat i)) ∧
        (∀ i, i < n → m.read (src + UInt16.ofNat i) = m0.read (src + UInt16.ofNat i))) :=
  (memcpy_spec n src dst hn1 hn hsd hdp hdc m0).post fun _ _ ⟨_, hcp, hag⟩ =>
    ⟨hcp, fun i hi => hag _ (fun hd => hsd _ (memcpy_in_region src i n hi hn) hd)⟩

/-- **Footprint.** The run modifies only `[dst, dst + n)`: every other cell — the source block,
the zero-page pointers, the code, the stack — is unchanged at the exit. -/
theorem memcpy_footprint (n : Nat) (src dst : UInt16) (hn1 : 1 ≤ n) (hn : n ≤ 256)
    (hsd : Region.Disjoint (region src n) (region dst n))
    (hdp : Region.Disjoint (region dst n) (region 0 4))
    (hdc : Region.Disjoint (region dst n) (region 0x8000 10)) :
    TripleM (memcpyPre n src dst) 0x8000 0x800A (fun s _ => s.halted = false) (region dst n) :=
  TripleM.iff_ghost.mpr fun m0 =>
    (memcpy_spec n src dst hn1 hn hsd hdp hdc m0).post fun _ _ ⟨hh, _, hag⟩ => ⟨hh, hag⟩

end Nes.Hoare.Examples
