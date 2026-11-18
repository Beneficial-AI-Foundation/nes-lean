import Nes.Apu.FrameCounter

/-!
# `Nes.Apu.Proofs.FrameCounter` — T-APU-1 (frame counter)

## Spec

`ticks k s` is `FrameCounter.tick` applied `k` times (events discarded); the event byte of the
`k`-th tick from `s` is `(tick (ticks (k - 1) s)).2` (bit 0 quarter frame, bit 1 half frame). A
*fresh sequence* is a state with `cycle = 0` and no pending reset (`resetIn = 0`). Event
tables (NESdev "APU Frame Counter", NTSC, in CPU cycles): `ev4 k` / `ev5 k`.

* **T-APU-1 (4-step)** (`T_APU_1_four_step`): from a fresh 4-step sequence the `k`-th tick
  (`1 ≤ k ≤ 29830`) emits exactly `ev4 k` — quarter at 7457 and 22371, quarter+half at 14913
  and 29829, nothing else — the counter does not return to 0 before tick 29830, and after
  29830 ticks the state is the start state (with the IRQ flag possibly raised).
* **T-APU-1 (5-step)** (`T_APU_1_five_step`): likewise with `ev5` — quarter+half at 37281
  instead of 29829, nothing at 29829 — and after 37282 ticks the state is exactly the start.
* **T-APU-1 (IRQ)** (`T_APU_1_irq`): in a fresh 4-step sequence the flag after `k ≤ 29830`
  ticks is `irq₀ || (!inhibit && 29828 ≤ k)` (set on 29828–29830); in 5-step mode it is
  unchanged over the whole sequence; no tick sets it unless mode is 4-step and inhibit clear;
  a `$4017` write with bit 6 set and `clearIrq` clear it.
* **T-APU-1 (immediate)** (`T_APU_1_immediate`): after `write4017 fc v odd`, the reset happens
  on tick 3 (even write cycle) or 4 (odd); that tick emits quarter+half iff `v` bit 7 is set
  (nothing otherwise) and leaves a fresh sequence in the written mode.

Method: a one-step lemma (`tick_run`) translating the `UInt16` comparisons of `tick` into a
`Nat` table, lifted by induction on `k` to the closed form `ticks k s = runState s k`
(`ticks_run`), so no ~37 000-step evaluation is ever performed.
-/

namespace Nes.Apu.Proofs
open Nes.Apu Nes.Apu.FrameCounter

/-! ### `UInt16` bridging -/

theorem u16_beq (a b : UInt16) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (UInt16.toNat_inj.mp e)
    simp [h, this]

theorem u16_succ (x : UInt16) (h : x.toNat < 65535) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt16.toNat_add]; simp; omega

/-! ### Tables and the closed form -/

/-- 4-step event table (CPU cycle → event byte). -/
def ev4 (n : Nat) : UInt8 :=
  if n = 7457 ∨ n = 22371 then 1 else if n = 14913 ∨ n = 29829 then 3 else 0
/-- 5-step event table (CPU cycle → event byte). -/
def ev5 (n : Nat) : UInt8 :=
  if n = 7457 ∨ n = 22371 then 1 else if n = 14913 ∨ n = 37281 then 3 else 0
/-- Sequence length in CPU cycles. -/
def seqLen (m5 : Bool) : Nat := if m5 then 37282 else 29830

/-- One tick inside a sequence with no pending reset. -/
theorem tick_run (s : FrameCounter) (hr : s.resetIn = 0) (hc : s.cycle.toNat < seqLen s.mode5) :
    (tick s).1 = { s with
      cycle := if s.cycle.toNat + 1 = seqLen s.mode5 then 0 else s.cycle + 1,
      irq := s.irq || (!s.mode5 && !s.inhibit && decide (29828 ≤ s.cycle.toNat + 1)) } ∧
    (tick s).2 = (if s.mode5 then ev5 else ev4) (s.cycle.toNat + 1) := by
  obtain ⟨c, r, m, i, q⟩ := s
  simp only at hr hc ⊢
  subst hr
  have hs := u16_succ c (by cases m <;> simp [seqLen] at hc <;> omega)
  cases m <;> simp [seqLen] at hc <;>
    simp only [tick, eventsAt, u16_beq, UInt16.le_iff_toNat_le, hs, seqLen] <;>
    simp [ev4, ev5] <;> (generalize c.toNat = n at *) <;> (cases i <;> cases q) <;>
    (refine ⟨?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> (repeat' split) <;>
    first | rfl | omega | (simp; omega) | (exfalso; omega) | (rw [Bool.eq_iff_iff]; simp; omega) | simp

/-- `tick` iterated `k` times. -/
def ticks : Nat → FrameCounter → FrameCounter
  | 0, s => s
  | k + 1, s => (tick (ticks k s)).1

/-- The state `k` cycles into a fresh sequence started from `s`. -/
def runState (s : FrameCounter) (k : Nat) : FrameCounter :=
  { s with cycle := UInt16.ofNat k,
           irq := s.irq || (!s.mode5 && !s.inhibit && decide (29828 ≤ k)) }

theorem ticks_run (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0) (k : Nat) :
    k < seqLen s.mode5 → ticks k s = runState s k := by
  induction k with
  | zero => intro _; obtain ⟨c, r, m, i, q⟩ := s; simp only at h0; subst h0; simp [ticks, runState]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hlen : seqLen s.mode5 ≤ 37282 := by cases s.mode5 <;> simp [seqLen]
    have hlt : (UInt16.ofNat k).toNat = k := by simp; omega
    rw [show ticks (k + 1) s = (tick (ticks k s)).1 from rfl, ih]
    have := tick_run (runState s k) (by simp [runState, hr]) (by simp only [runState, hlt]; omega)
    rw [this.1]
    have hne : k + 1 ≠ seqLen s.mode5 := by omega
    have hc : UInt16.ofNat k + 1 = UInt16.ofNat (k + 1) := by
      apply UInt16.toNat_inj.mp; rw [u16_succ _ (by omega), hlt]; simp; omega
    simp only [runState, hlt, hne, ite_false, hc]
    cases s.mode5 <;> cases s.inhibit <;> cases s.irq <;> simp <;> omega

theorem tick_pending (s : FrameCounter) (h : s.resetIn ≠ 0) (h1 : s.resetIn ≠ 1) :
    (tick s).1.resetIn = s.resetIn - 1 ∧ (tick s).1.mode5 = s.mode5 := by
  simp [tick, h, h1]

theorem tick_reset (s : FrameCounter) (h : s.resetIn = 1) :
    tick s = ({ s with cycle := 0, resetIn := 0 }, if s.mode5 then 3 else 0) := by
  simp [tick, h]

theorem tick_irq_only (s : FrameCounter) (h : (tick s).1.irq = true) :
    s.irq = true ∨ (s.mode5 = false ∧ s.inhibit = false) := by
  by_cases hr1 : s.resetIn = 1
  · simp [tick, hr1] at h; exact Or.inl h
  · simp [tick, hr1] at h
    cases hm : s.mode5 <;> cases hi : s.inhibit <;> cases hq : s.irq <;> simp_all

theorem ticks_events (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0) (k : Nat)
    (hk : k < seqLen s.mode5) : (tick (ticks k s)).2 = (if s.mode5 then ev5 else ev4) (k + 1) := by
  have hlen : seqLen s.mode5 ≤ 37282 := by cases s.mode5 <;> simp [seqLen]
  have hlt : (UInt16.ofNat k).toNat = k := by simp; omega
  rw [ticks_run s h0 hr k hk]
  have := tick_run (runState s k) (by simp [runState, hr]) (by simp only [runState, hlt]; omega)
  rw [this.2]; cases hm : s.mode5 <;> simp [runState, hlt, hm]

theorem ticks_wrap (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0) :
    ticks (seqLen s.mode5) s = { s with irq := s.irq || (!s.mode5 && !s.inhibit) } := by
  have hlen : 29830 ≤ seqLen s.mode5 ∧ seqLen s.mode5 ≤ 37282 := by
    cases s.mode5 <;> simp [seqLen]
  obtain ⟨j, hj⟩ : ∃ j, seqLen s.mode5 = j + 1 := ⟨seqLen s.mode5 - 1, by omega⟩
  have hlt : (UInt16.ofNat j).toNat = j := by simp; omega
  rw [hj, show ticks (j + 1) s = (tick (ticks j s)).1 from rfl, ticks_run s h0 hr j (by omega)]
  have := tick_run (runState s j) (by simp [runState, hr]) (by simp only [runState, hlt]; omega)
  rw [this.1]
  simp only [runState, hlt, ← hj, ite_true]
  obtain ⟨c, r, m, i, q⟩ := s
  simp only at h0 ⊢; subst h0
  have : 29828 ≤ j := by omega
  have : 29828 ≤ j + 1 := by omega
  cases m <;> cases i <;> cases q <;> simp_all

theorem ticks_cycle_ne (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0) (k : Nat)
    (hk0 : 0 < k) (hk : k < seqLen s.mode5) : (ticks k s).cycle ≠ 0 := by
  have hlen : seqLen s.mode5 ≤ 37282 := by cases s.mode5 <;> simp [seqLen]
  rw [ticks_run s h0 hr k hk]; simp only [runState]
  intro h; have := congrArg UInt16.toNat h; simp at this; omega

theorem ticks_pending (s : FrameCounter) (j : Nat) (h : j < s.resetIn.toNat) :
    (ticks j s).resetIn.toNat = s.resetIn.toNat - j ∧ (ticks j s).mode5 = s.mode5 := by
  induction j with
  | zero => simp [ticks]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hn0 : (ticks j s).resetIn ≠ 0 := fun e => by rw [e] at h1; simp at h1; omega
    have hn1 : (ticks j s).resetIn ≠ 1 := fun e => by rw [e] at h1; simp at h1; omega
    obtain ⟨p1, p2⟩ := tick_pending _ hn0 hn1
    refine ⟨?_, ?_⟩
    · show (tick (ticks j s)).1.resetIn.toNat = _
      rw [p1, UInt8.toNat_sub_of_le _ _ (by
        rw [UInt8.le_iff_toNat_le]; simp; omega)]
      simp; omega
    · show (tick (ticks j s)).1.mode5 = _
      rw [p2, h2]

/-- The tick at which a `$4017` write's pending reset takes effect (`resetIn = d + 1`) is the
`d + 1`-st: it restarts the sequence and emits quarter+half iff the mode is 5-step. -/
theorem ticks_reset_point (s : FrameCounter) (d : Nat) (hd : s.resetIn.toNat = d + 1) :
    (tick (ticks d s)).1 = { ticks d s with cycle := 0, resetIn := 0 } ∧
    (tick (ticks d s)).2 = (if s.mode5 then 3 else 0) ∧ (ticks d s).mode5 = s.mode5 := by
  have := ticks_pending s d (by omega)
  have hr := tick_reset (ticks d s) (UInt8.toNat_inj.mp (by rw [this.1]; simp; omega))
  rw [hr]; exact ⟨rfl, by rw [this.2], this.2⟩

/-! ## T-APU-1 -/

/-- **T-APU-1 (4-step).** From a fresh 4-step sequence, the `k`-th tick (`1 ≤ k ≤ 29830`)
emits exactly `ev4 k` (quarter at 7457, 22371; quarter+half at 14913, 29829; nothing else),
the cycle counter is nonzero strictly inside the sequence, and after 29830 ticks the state is
the start state again (up to the IRQ flag). -/
theorem T_APU_1_four_step (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0)
    (hm : s.mode5 = false) :
    (∀ k, 1 ≤ k → k ≤ 29830 → (tick (ticks (k - 1) s)).2 = ev4 k) ∧
    (∀ k, 0 < k → k < 29830 → (ticks k s).cycle ≠ 0) ∧
    ticks 29830 s = { s with irq := s.irq || !s.inhibit } := by
  have hL : seqLen s.mode5 = 29830 := by simp [seqLen, hm]
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ticks_cycle_ne s h0 hr k h1 (by omega), ?_⟩
  · have := ticks_events s h0 hr (k - 1) (by omega)
    rw [this, hm, show k - 1 + 1 = k by omega]; rfl
  · have := ticks_wrap s h0 hr; rw [hL] at this; rw [this]
    obtain ⟨c, r, m, i, q⟩ := s; simp_all

/-- **T-APU-1 (5-step).** From a fresh 5-step sequence, the `k`-th tick (`1 ≤ k ≤ 37282`)
emits exactly `ev5 k` (quarter at 7457, 22371; quarter+half at 14913, 37281; in particular
nothing at 29829), and after 37282 ticks the state is exactly the start state. -/
theorem T_APU_1_five_step (s : FrameCounter) (h0 : s.cycle = 0) (hr : s.resetIn = 0)
    (hm : s.mode5 = true) :
    (∀ k, 1 ≤ k → k ≤ 37282 → (tick (ticks (k - 1) s)).2 = ev5 k) ∧
    (tick (ticks 29828 s)).2 = 0 ∧
    (∀ k, 0 < k → k < 37282 → (ticks k s).cycle ≠ 0) ∧
    ticks 37282 s = s := by
  have hL : seqLen s.mode5 = 37282 := by simp [seqLen, hm]
  have hev : ∀ k, 1 ≤ k → k ≤ 37282 → (tick (ticks (k - 1) s)).2 = ev5 k := by
    intro k h1 h2
    have := ticks_events s h0 hr (k - 1) (by omega)
    rw [this, hm, show k - 1 + 1 = k by omega]; rfl
  refine ⟨hev, hev 29829 (by omega) (by omega), fun k h1 h2 => ticks_cycle_ne s h0 hr k h1 (by omega), ?_⟩
  have := ticks_wrap s h0 hr; rw [hL] at this; rw [this]
  obtain ⟨c, r, m, i, q⟩ := s; simp_all

/-- **T-APU-1 (IRQ).** In a fresh 4-step sequence the flag becomes set exactly from the
29828th tick on, and only when inhibit is clear; in 5-step mode it never changes. In general a
tick can only set the flag in 4-step mode with inhibit clear; a `$4017` write with bit 6 set
and `clearIrq` (the `$4015` read) clear it. -/
theorem T_APU_1_irq :
    (∀ s : FrameCounter, s.cycle = 0 → s.resetIn = 0 → s.mode5 = false →
      ∀ k, k ≤ 29830 → (ticks k s).irq = (s.irq || (!s.inhibit && decide (29828 ≤ k)))) ∧
    (∀ s : FrameCounter, s.cycle = 0 → s.resetIn = 0 → s.mode5 = true →
      ∀ k, k ≤ 37282 → (ticks k s).irq = s.irq) ∧
    (∀ s : FrameCounter, (tick s).1.irq = true →
      s.irq = true ∨ (s.mode5 = false ∧ s.inhibit = false)) ∧
    (∀ (fc : FrameCounter) (v : UInt8) (odd : Bool), v &&& 0x40 ≠ 0 →
      (write4017 fc v odd).irq = false) ∧
    (∀ fc : FrameCounter, (clearIrq fc).irq = false ∧ (clearIrq fc).irqLine = false) := by
  refine ⟨fun s h0 hr hm k hk => ?_, fun s h0 hr hm k hk => ?_, tick_irq_only,
    fun fc v odd h => by simp [write4017, h], fun fc => by simp [clearIrq, irqLine]⟩
  · have hL : seqLen s.mode5 = 29830 := by simp [seqLen, hm]
    rcases Nat.lt_or_ge k 29830 with h | h
    · rw [ticks_run s h0 hr k (by omega)]; simp [runState, hm]
    · have := ticks_wrap s h0 hr; rw [hL] at this
      rw [show k = 29830 by omega, this]; simp [hm]
  · have hL : seqLen s.mode5 = 37282 := by simp [seqLen, hm]
    rcases Nat.lt_or_ge k 37282 with h | h
    · rw [ticks_run s h0 hr k (by omega)]; simp [runState, hm]
    · have := ticks_wrap s h0 hr; rw [hL] at this
      rw [show k = 37282 by omega, this]; simp [hm]

/-- **T-APU-1 (immediate clock).** After a `$4017` write the sequencer restarts on the 3rd
(even write cycle) or 4th (odd) tick; that tick emits quarter+half (`3`) iff bit 7 is set and
nothing otherwise, and leaves a fresh sequence (`cycle = 0`, no pending reset) in the written
mode — from which `T_APU_1_four_step` / `T_APU_1_five_step` apply. -/
theorem T_APU_1_immediate (fc : FrameCounter) (v : UInt8) (odd : Bool) :
    let w := write4017 fc v odd
    let d := if odd then 3 else 2
    (tick (ticks d w)).2 = (if v &&& 0x80 != 0 then 3 else 0) ∧
    (ticks (d + 1) w).cycle = 0 ∧ (ticks (d + 1) w).resetIn = 0 ∧
    (ticks (d + 1) w).mode5 = (v &&& 0x80 != 0) := by
  intro w d
  have hd : w.resetIn.toNat = d + 1 := by cases odd <;> simp [w, d, write4017]
  obtain ⟨h1, h2, h3⟩ := ticks_reset_point w d hd
  rw [show ticks (d + 1) w = (tick (ticks d w)).1 from rfl, h1]
  refine ⟨by rw [h2]; simp [w, write4017], rfl, rfl, ?_⟩
  simp only [h3]; simp [w, write4017]

end Nes.Apu.Proofs
