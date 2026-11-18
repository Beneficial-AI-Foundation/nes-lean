import Nes.Hoare.Tactics

/-!
# `Nes.Hoare.Examples.Homebrew` — a routine lifted from a homebrew NES program

`getTVSystem` from Damian Yerrick's *spritecans* demo (2011), verified against the
instruction-level semantics `Cpu.step` through the Hoare logic of `Nes.Hoare`.

## Spec

**Source.** `testdata/nes-test-roms/spritecans-2011/src/paldetect.s` of the `nes-test-roms`
repository at commit `95d8f621ae55cee0d09b91519a8989ae0e64753b` (pinned in
`scripts/fetch-testdata.sh`). Only this one file is used: the other sources in that directory
are GPL-3 and nothing from them is reproduced here. Its notice, preserved as it requires:

```
; NES TV system detection code
; Copyright 2011 Damian Yerrick
;
; Copying and distribution of this file, with or without
; modification, are permitted in any medium without royalty
; provided the copyright notice and this notice are preserved.
; This file is offered as-is, without any warranty.
```

The routine (ca65 source, abridged comments):

```
getTVSystem:            ; $C5A0  (.align 32)
  ldx #0                ; $C5A0  A2 00
  ldy #0                ; $C5A2  A0 00
  lda nmis              ; $C5A4  A5 13
nmiwait1:
  cmp nmis              ; $C5A6  C5 13
  beq nmiwait1          ; $C5A8  F0 FC
  lda nmis              ; $C5AA  A5 13
nmiwait2:               ; "Each iteration takes 11 cycles."
  inx                   ; $C5AC  E8
  bne :+                ; $C5AD  D0 01
  iny                   ; $C5AF  C8
: cmp nmis              ; $C5B0  C5 13
  beq nmiwait2          ; $C5B2  F0 F8
  tya                   ; $C5B4  98
  sec                   ; $C5B5  38
  sbc #10               ; $C5B6  E9 0A
  cmp #3                ; $C5B8  C9 03
  bcc notAbove3         ; $C5BA  90 02
  lda #3                ; $C5BC  A9 03
notAbove3:
  rts                   ; $C5BE  60
```

Result in `A`: 0 NTSC, 1 PAL, 2 Dendy, 3 unknown; `Y:X` is the 16-bit iteration count.

**Bytes and address.** Assembled by hand from the source above; `nmis` is zero-page `$13` and
the routine sits at `$C5A0`. Cross-check: the 31-byte sequence `hb_code` occurs exactly once in
the built `spritecans.nes` (iNES, one 16 KiB PRG bank, so PRG is mapped at `$C000`), at file
offset `$5B0` = 16-byte header + PRG offset `$5A0`, i.e. CPU address `$C5A0` (32-byte aligned as
`.align 32` demands), with operand `$13` for `nmis` in all four places.

**What is verified, and what is not.** `getTVSystem` measures the time between two NMIs by
counting iterations of `nmiwait2`; the NMI handler increments `nmis` asynchronously. The ISA-level
logic has no interrupts: within a run memory changes only through the program's own stores, and
this routine stores nothing. So the NMI is modelled honestly by its *effect at the comparison*:

* `hb_iter_cycles` / `hb_loop_cycles` (timing, `CTriple`): while `nmis` still equals `A` (no NMI
  yet), one `nmiwait2` iteration from `$C5AC` back to `$C5AC` bumps the 16-bit counter `Y:X` by
  one and takes **11 cycles, or 12 when `X` wraps** (the `bne` falls through and `iny` runs) —
  the source comment's "11 cycles" is exact for 255 of every 256 iterations. Hence `k`
  iterations from counter `c` take exactly `11·k + (⌊(c+k)/256⌋ - ⌊c/256⌋)` cycles. This is the
  property the routine's correctness rests on: the count is a clock.
* `hb_exit_cycles` (timing): when `nmis ≠ A` at the comparison (the NMI has happened), the
  final iteration bumps the counter and falls out to `$C5B4` in 10 cycles (11 on a wrap).
* `hb_classify_tail` (functional + timing): `$C5B4 → $C5BE` (just before `rts`) leaves
  `A = hb_classify Y` (`Y - 10` if that is `< 3`, else `3`) in 11 or 12 cycles.
* `hb_measure` (functional, `Triple`): from `nmiwait2` with counter `c` and `nmis ≠ A`, the
  routine reaches `$C5BE` with `A = hb_classify ⌊(c+1)/256⌋`. With the source's iteration counts
  (`$A93` NTSC, `$BCE` PAL, `$C98` Dendy) this is 0 / 1 / 2 (`hb_classify_ntsc` etc.).

Not covered: the `nmiwait1` synchronisation loop and the initial `ldx/ldy/lda` (their meaning
is "wait for an NMI", unexpressible without interrupts), the `rts` (the stack frame is the
caller's business, see `Triple.call`), and wrap-around of the 16-bit counter (hypothesis
`c + k < 65536`; real runs stay below `$0D00`). Common hypotheses: `halted = false` and the code
bytes at `$C5A0`.
-/

namespace Nes.Hoare.Examples

open Nes Nes.Cpu Nes.Cpu.Proofs Nes.Hoare

/-- `getTVSystem` (paldetect.s, © 2011 Damian Yerrick, all-permissive), assembled at `$C5A0`
with `nmis = $13`; byte-identical to `spritecans.nes` at file offset `$5B0`. -/
def hb_code : List UInt8 :=
  [0xA2, 0x00, 0xA0, 0x00, 0xA5, 0x13, 0xC5, 0x13, 0xF0, 0xFC, 0xA5, 0x13,
   0xE8, 0xD0, 0x01, 0xC8, 0xC5, 0x13, 0xF0, 0xF8,
   0x98, 0x38, 0xE9, 0x0A, 0xC9, 0x03, 0x90, 0x02, 0xA9, 0x03, 0x60]

/-- Running CPU with the routine in memory. -/
def hb_inv (s : State) (m : Mem) : Prop := s.halted = false ∧ codeAt m 0xC5A0 hb_code

/-- The 16-bit iteration counter `Y:X`. -/
def hb_cnt (s : State) : Nat := s.y.toNat * 256 + s.x.toNat

/-- The tail's classification of the counter's high byte. -/
def hb_classify (y : UInt8) : UInt8 := if y - 10 < 3 then y - 10 else 3

theorem hb_classify_ntsc : hb_classify (UInt8.ofNat (0xA93 / 256)) = 0 := by decide
theorem hb_classify_pal : hb_classify (UInt8.ofNat (0xBCE / 256)) = 1 := by decide
theorem hb_classify_dendy : hb_classify (UInt8.ofNat (0xC98 / 256)) = 2 := by decide

/-! ## The classification tail `$C5B4 → $C5BE` -/

private theorem hb_sbc10 : ∀ y : UInt8, (Alu.fast.sbc y 10 true).r = y - 10 := by decide

private theorem hb_tail_lt (x y : UInt8) (hy : y - 10 < 3) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y) 0xC5B4 0xC5BE
      (fun s m => hb_inv s m ∧ s.a = y - 10 ∧ s.x = x ∧ s.y = y) 11 := by
  have hs := hb_sbc10 y; unfold hb_inv hb_code; hoare_run 5

private theorem hb_tail_ge (x y : UInt8) (hy : ¬ y - 10 < 3) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y) 0xC5B4 0xC5BE
      (fun s m => hb_inv s m ∧ s.a = 3 ∧ s.x = x ∧ s.y = y) 12 := by
  have hs := hb_sbc10 y; unfold hb_inv hb_code; hoare_run 6

/-- `tya; sec; sbc #10; cmp #3; bcc +2; lda #3`: `A = hb_classify Y`, in 11 cycles when the
branch is taken (result 0–2) and 12 otherwise. -/
theorem hb_classify_tail (x y : UInt8) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y) 0xC5B4 0xC5BE
      (fun s m => hb_inv s m ∧ s.a = hb_classify y ∧ s.x = x ∧ s.y = y)
      (if y - 10 < 3 then 11 else 12) := by
  by_cases hy : y - 10 < 3
  · simp only [hy, ite_true]
    exact (hb_tail_lt x y hy).conseq (fun _ _ h => h)
      (fun _ _ ⟨h1, h2, h3⟩ => ⟨h1, by simp [hb_classify, hy, h2], h3⟩)
  · simp only [hy, ite_false]
    exact (hb_tail_ge x y hy).conseq (fun _ _ h => h)
      (fun _ _ ⟨h1, h2, h3⟩ => ⟨h1, by simp [hb_classify, hy, h2], h3⟩)

/-! ## The counting loop `nmiwait2` -/

private theorem hb_iter_nowrap (x y : UInt8) (hx : x + 1 ≠ 0) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y ∧ s.a = m.read 0x13) 0xC5AC 0xC5AC
      (fun s m => hb_inv s m ∧ s.x = x + 1 ∧ s.y = y ∧ s.a = m.read 0x13) 11 := by
  unfold hb_inv hb_code; hoare_run 4

private theorem hb_iter_wrap (x y : UInt8) (hx : x + 1 = 0) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y ∧ s.a = m.read 0x13) 0xC5AC 0xC5AC
      (fun s m => hb_inv s m ∧ s.x = x + 1 ∧ s.y = y + 1 ∧ s.a = m.read 0x13) 12 := by
  unfold hb_inv hb_code; hoare_run 5

private theorem hb_exit_nowrap (x y a v : UInt8) (hx : x + 1 ≠ 0) (hav : (a - v == 0) = false) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y ∧ s.a = a ∧ m.read 0x13 = v)
      0xC5AC 0xC5B4 (fun s m => hb_inv s m ∧ s.x = x + 1 ∧ s.y = y) 10 := by
  unfold hb_inv hb_code; hoare_run 4

private theorem hb_exit_wrap (x y a v : UInt8) (hx : x + 1 = 0) (hav : (a - v == 0) = false) :
    CTriple (fun s m => hb_inv s m ∧ s.x = x ∧ s.y = y ∧ s.a = a ∧ m.read 0x13 = v)
      0xC5AC 0xC5B4 (fun s m => hb_inv s m ∧ s.x = x + 1 ∧ s.y = y + 1) 11 := by
  unfold hb_inv hb_code; hoare_run 5

/-- Incrementing `Y:X` the way `inx; bne +1; iny` does is `+1` on the 16-bit counter. -/
private theorem hb_cnt_succ (x y : UInt8) (h : y.toNat * 256 + x.toNat + 1 < 65536) :
    (if x + 1 = 0 then y + 1 else y).toNat * 256 + (x + 1).toNat =
      y.toNat * 256 + x.toNat + 1 ∧
    (x + 1 = 0 ↔ (y.toNat * 256 + x.toNat + 1) % 256 = 0) := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have e : x + 1 = 0 ↔ x.toNat = 255 := by
    constructor
    · intro h0; have := congrArg UInt8.toNat h0; simp at this; omega
    · intro h0; apply UInt8.toNat_inj.mp; simp; omega
  by_cases h0 : x + 1 = 0
  · have h255 := e.mp h0
    simp only [h0, ite_true, UInt8.toNat_add, true_iff]
    simp; omega
  · have h255 : x.toNat ≠ 255 := fun h' => h0 (e.mpr h')
    simp only [h0, ite_false, UInt8.toNat_add, false_iff]
    simp; omega

/-- **One `nmiwait2` iteration, no NMI yet** (`nmis = A`): the counter `Y:X` goes from `c` to
`c + 1` in 11 cycles, or 12 when the low byte wraps. -/
theorem hb_iter_cycles (c : Nat) (hc : c + 1 < 65536) :
    CTriple (fun s m => hb_inv s m ∧ s.a = m.read 0x13 ∧ hb_cnt s = c) 0xC5AC 0xC5AC
      (fun s m => hb_inv s m ∧ s.a = m.read 0x13 ∧ hb_cnt s = c + 1)
      (11 + if (c + 1) % 256 = 0 then 1 else 0) := by
  intro s m ⟨hi, ha, hcnt⟩ hpc
  unfold hb_cnt at hcnt
  obtain ⟨hsum, hwrap⟩ := hb_cnt_succ s.x s.y (by omega)
  by_cases h0 : s.x + 1 = 0
  · obtain ⟨n, h1, ⟨hi', hx', hy', ha'⟩, h3⟩ :=
      hb_iter_wrap s.x s.y h0 s m ⟨hi, rfl, rfl, ha⟩ hpc
    refine ⟨n, h1, ⟨hi', ha', ?_⟩, ?_⟩
    · unfold hb_cnt; rw [hx', hy']; rw [ite_eq_left h0] at hsum; rw [hsum, hcnt]
    · have : (c + 1) % 256 = 0 := by rw [← hcnt]; exact hwrap.mp h0
      simp [h3, this]
  · obtain ⟨n, h1, ⟨hi', hx', hy', ha'⟩, h3⟩ :=
      hb_iter_nowrap s.x s.y h0 s m ⟨hi, rfl, rfl, ha⟩ hpc
    refine ⟨n, h1, ⟨hi', ha', ?_⟩, ?_⟩
    · unfold hb_cnt; rw [hx', hy']; rw [ite_eq_right h0] at hsum; rw [hsum, hcnt]
    · have : ¬ (c + 1) % 256 = 0 := by rw [← hcnt]; exact fun h' => h0 (hwrap.mpr h')
      simp [h3, this]

private theorem hb_ctriple_cyc {P Q : Assn} {e x : UInt16} {c c' : Nat} (h : CTriple P e x Q c)
    (hc : c = c') : CTriple P e x Q c' := hc ▸ h

/-- **`k` iterations, no NMI during them**: the counter advances by `k` and the time spent is
exactly `11·k` cycles plus one per wrap of `X` — the iteration count is a clock. -/
theorem hb_loop_cycles (c k : Nat) (hc : c + k < 65536) :
    CTriple (fun s m => hb_inv s m ∧ s.a = m.read 0x13 ∧ hb_cnt s = c) 0xC5AC 0xC5AC
      (fun s m => hb_inv s m ∧ s.a = m.read 0x13 ∧ hb_cnt s = c + k)
      (11 * k + ((c + k) / 256 - c / 256)) := by
  induction k with
  | zero => exact hb_ctriple_cyc (CTriple.skip fun _ _ h => h) (by omega)
  | succ k ih =>
    refine hb_ctriple_cyc (CTriple.seq (ih (by omega)) (hb_iter_cycles (c + k) (by omega))) ?_
    split <;> omega

/-- **The last iteration, after the NMI** (`nmis ≠ A`): the counter goes from `c` to `c + 1`
and control falls out of the loop to `$C5B4` in 10 cycles (11 on a wrap); `Y` is the high byte
of the new count. -/
theorem hb_exit_cycles (c : Nat) (hc : c + 1 < 65536) :
    CTriple (fun s m => hb_inv s m ∧ s.a ≠ m.read 0x13 ∧ hb_cnt s = c) 0xC5AC 0xC5B4
      (fun s m => hb_inv s m ∧ hb_cnt s = c + 1 ∧ s.y.toNat = (c + 1) / 256)
      (10 + if (c + 1) % 256 = 0 then 1 else 0) := by
  intro s m ⟨hi, ha, hcnt⟩ hpc
  unfold hb_cnt at hcnt
  obtain ⟨hsum, hwrap⟩ := hb_cnt_succ s.x s.y (by omega)
  have hav : (s.a - m.read 0x13 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; exact ha (by
      have := congrArg (· + m.read 0x13) h; simpa using this)
  have hxl := (s.x + 1).toNat_lt
  by_cases h0 : s.x + 1 = 0
  · obtain ⟨n, h1, ⟨hi', hx', hy'⟩, h3⟩ :=
      hb_exit_wrap s.x s.y s.a (m.read 0x13) h0 hav s m ⟨hi, rfl, rfl, rfl, rfl⟩ hpc
    rw [ite_eq_left h0] at hsum
    refine ⟨n, h1, ⟨hi', ?_, ?_⟩, ?_⟩
    · unfold hb_cnt; rw [hx', hy', hsum, hcnt]
    · rw [hy']
      generalize (s.x + 1).toNat = X at *
      generalize hY : (s.y + 1).toNat = Y at *
      omega
    · have : (c + 1) % 256 = 0 := by rw [← hcnt]; exact hwrap.mp h0
      simp [h3, this]
  · obtain ⟨n, h1, ⟨hi', hx', hy'⟩, h3⟩ :=
      hb_exit_nowrap s.x s.y s.a (m.read 0x13) h0 hav s m ⟨hi, rfl, rfl, rfl, rfl⟩ hpc
    rw [ite_eq_right h0] at hsum
    refine ⟨n, h1, ⟨hi', ?_, ?_⟩, ?_⟩
    · unfold hb_cnt; rw [hx', hy', hsum, hcnt]
    · rw [hy']
      generalize (s.x + 1).toNat = X at *
      generalize hY : s.y.toNat = Y at *
      omega
    · have : ¬ (c + 1) % 256 = 0 := by rw [← hcnt]; exact fun h' => h0 (hwrap.mpr h')
      simp [h3, this]

/-- **Functional spec of the measurement's end** (`Triple`): entering `nmiwait2` with counter
`c` once the NMI has bumped `nmis` (so `nmis ≠ A`), the routine reaches `$C5BE` (the `rts`)
with `A = hb_classify ⌊(c+1)/256⌋` and `Y:X = c + 1`. -/
theorem hb_measure (c : Nat) (hc : c + 1 < 65536) :
    Triple (fun s m => hb_inv s m ∧ s.a ≠ m.read 0x13 ∧ hb_cnt s = c) 0xC5AC 0xC5BE
      (fun s m => hb_inv s m ∧ s.a = hb_classify (UInt8.ofNat ((c + 1) / 256)) ∧
        hb_cnt s = c + 1) := by
  refine Triple.seq (hb_exit_cycles c hc).toTriple ?_
  intro s m ⟨⟨hi, hcnt, hyv⟩, hpc⟩
  have hyeq : s.y = UInt8.ofNat ((c + 1) / 256) := by
    rw [← hyv]; simp
  obtain ⟨n, h1, ⟨hi', ha', hx', hy'⟩, _⟩ := hb_classify_tail s.x s.y s m ⟨hi, rfl, rfl⟩ hpc
  refine ⟨n, h1, hi', by rw [ha', hyeq], ?_⟩
  unfold hb_cnt at hcnt ⊢; rw [hx', hy']; exact hcnt


end Nes.Hoare.Examples
