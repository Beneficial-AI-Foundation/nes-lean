import Nes.Ppu.Timing

/-!
# `Nes.Ppu.Proofs.Timing` — T-PPU-1 (timing constants)

## Spec

Positions are linearised as `lin s = scanline * 341 + dot` (0 … 89341); `Valid s` says
`dot ≤ 340 ∧ scanline ≤ 261`. `ticks n` is `tick` applied `n` times.

* **T-PPU-1 (frame).** From `(0, 0)` on an even frame or with rendering disabled, 89342 ticks
  return to `(0, 0)` with the frame parity flipped (`T_PPU_1_frame_dots`).
* **T-PPU-1 (odd frame).** From `(0, 0)` on an odd frame with rendering enabled, 89341 ticks
  return to `(0, 0)` with the parity flipped (`T_PPU_1_odd_frame`).
* **T-PPU-1 (vblank).** The tick from `(241, 0)` reaches `(241, 1)` and, unless suppressed by a
  `$2002` read, sets the vblank flag (`T_PPU_1_vblank_set`); the tick from `(261, 0)` reaches
  `(261, 1)` and clears vblank, sprite-0 hit and sprite overflow (`T_PPU_1_vblank_clear`).
* **T-PPU-1 (rates).** `cpuCyclesPerFrame = 89342 / 3 = 29780 + 2/3` as a `Rat` identity, and
  `3 * 29780 + 2 = dotsPerFrame` as a `Nat` identity (`T_PPU_1_cpu_cycles`); the NTSC frame
  rate with rendering on (alternating 89342/89341-dot frames, PPU clock 236.25 MHz / 44) lies
  in `(60.0988, 60.0989)` Hz (`T_PPU_1_frame_rate`). `Rat` is core Lean's; the identities are
  closed by kernel evaluation (`decide +kernel`, GMP-backed `Nat.gcd`).

Method: one-step lemmas on `lin` (`tick_step`, `tick_wrap`, `tick_skip`), lifted to `ticks k`
by induction on `k` (`ticks_lin`), so no 89342-step evaluation is ever performed.
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.State

/-- Linear position within a frame. -/
def lin (s : State) : Nat := s.scanline.toNat * 341 + s.dot.toNat

/-- The counters are in range. -/
def Valid (s : State) : Prop := s.dot.toNat ≤ 340 ∧ s.scanline.toNat ≤ 261

/-! ### Bit helpers (decided over the 256 bytes) -/

theorem u8_or80 : ∀ x : UInt8, ((x ||| 0x80) &&& 0x80 != 0) = true := by decide
theorem u8_and1F_80 : ∀ x : UInt8, ((x &&& 0x1F) &&& 0x80 != 0) = false := by decide
theorem u8_and1F_40 : ∀ x : UInt8, ((x &&& 0x1F) &&& 0x40 != 0) = false := by decide
theorem u8_and1F_20 : ∀ x : UInt8, ((x &&& 0x1F) &&& 0x20 != 0) = false := by decide
theorem u8_and7F_80 : ∀ x : UInt8, ((x &&& 0x7F) &&& 0x80 != 0) = false := by decide

/-! ### One-step lemmas -/

theorem dotEvents_pos (s : State) :
    (dotEvents s).dot = s.dot ∧ (dotEvents s).scanline = s.scanline ∧
      (dotEvents s).frameOdd = s.frameOdd ∧ (dotEvents s).mask = s.mask ∧
      (dotEvents s).ctrl = s.ctrl := by
  unfold dotEvents; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem advance_regs (s : State) :
    (advance s).status = s.status ∧ (advance s).nmiOut = s.nmiOut ∧
      (advance s).suppressVbl = s.suppressVbl ∧ (advance s).mask = s.mask ∧
      (advance s).ctrl = s.ctrl := by
  unfold advance; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem advance_step (s : State) (hv : Valid s) (h1 : lin s + 1 < 89342)
    (h2 : ¬ (lin s = 89340 ∧ s.frameOdd = true ∧ s.rendering = true)) :
    lin (advance s) = lin s + 1 ∧ Valid (advance s) ∧ (advance s).frameOdd = s.frameOdd := by
  unfold Valid lin at *
  unfold advance
  split
  · rename_i h
    simp [← UInt16.toNat_inj, State.rendering] at h
    simp [State.rendering] at h2
    exact absurd (h2 (by omega) h.1.2) h.2
  · split
    · rename_i _ h
      split
      · rename_i h'
        simp [← UInt16.toNat_inj] at h h'
        omega
      · rename_i h'
        simp [← UInt16.toNat_inj] at h h'
        simp [UInt16.toNat_add]
        omega
    · rename_i _ h
      simp [← UInt16.toNat_inj] at h
      simp [UInt16.toNat_add]
      omega

theorem advance_wrap (s : State) (hv : Valid s) (h : lin s = 89341) :
    lin (advance s) = 0 ∧ Valid (advance s) ∧ (advance s).frameOdd = !s.frameOdd := by
  unfold Valid lin at *
  have hd : s.dot = 340 := by rw [← UInt16.toNat_inj]; simp; omega
  have hl : s.scanline = 261 := by rw [← UInt16.toNat_inj]; simp; omega
  unfold advance
  simp [hd, hl]

theorem advance_skip (s : State) (hv : Valid s) (h : lin s = 89340) (ho : s.frameOdd = true)
    (hr : s.rendering = true) :
    lin (advance s) = 0 ∧ Valid (advance s) ∧ (advance s).frameOdd = !s.frameOdd := by
  unfold Valid lin at *
  have hd : s.dot = 339 := by rw [← UInt16.toNat_inj]; simp; omega
  have hl : s.scanline = 261 := by rw [← UInt16.toNat_inj]; simp; omega
  unfold advance
  simp [hd, hl, ho, hr]

/-- `tick` keeps `mask` and `ctrl`. -/
theorem tick_mask (s : State) : (tick s).mask = s.mask ∧ (tick s).ctrl = s.ctrl := by
  unfold tick
  rw [(dotEvents_pos _).2.2.2.1, (dotEvents_pos _).2.2.2.2, (advance_regs s).2.2.2.1,
    (advance_regs s).2.2.2.2]
  exact ⟨rfl, rfl⟩

theorem lin_tick (s : State) : lin (tick s) = lin (advance s) := by
  unfold lin tick; rw [(dotEvents_pos _).1, (dotEvents_pos _).2.1]

theorem valid_tick (s : State) : Valid (tick s) ↔ Valid (advance s) := by
  unfold Valid tick; rw [(dotEvents_pos _).1, (dotEvents_pos _).2.1]

theorem frameOdd_tick (s : State) : (tick s).frameOdd = (advance s).frameOdd := by
  unfold tick; rw [(dotEvents_pos _).2.2.1]

theorem tick_step (s : State) (hv : Valid s) (h1 : lin s + 1 < 89342)
    (h2 : ¬ (lin s = 89340 ∧ s.frameOdd = true ∧ s.rendering = true)) :
    lin (tick s) = lin s + 1 ∧ Valid (tick s) ∧ (tick s).frameOdd = s.frameOdd := by
  rw [lin_tick, valid_tick, frameOdd_tick]; exact advance_step s hv h1 h2

/-! ### Iteration -/

theorem ticks_succ (n : Nat) (s : State) : ticks (n + 1) s = ticks n (tick s) := rfl

theorem ticks_add (m n : Nat) (s : State) : ticks (m + n) s = ticks n (ticks m s) := by
  induction m generalizing s with
  | zero => simp [ticks]
  | succ m ih => rw [Nat.succ_add, ticks_succ, ticks_succ, ih]

theorem ticks_rendering (k : Nat) (s : State) :
    (ticks k s).mask = s.mask ∧ (ticks k s).ctrl = s.ctrl := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [ticks_succ, (ih _).1, (ih _).2]; exact tick_mask s

/-- `k` ticks that do not cross the frame end (nor the odd-frame skip point) advance `lin` by `k`. -/
theorem ticks_lin (k : Nat) (s : State) (hv : Valid s) (h1 : lin s + k < 89342)
    (h2 : lin s + k ≤ 89340 ∨ ¬ (s.frameOdd = true ∧ s.rendering = true)) :
    lin (ticks k s) = lin s + k ∧ Valid (ticks k s) ∧ (ticks k s).frameOdd = s.frameOdd := by
  induction k generalizing s with
  | zero => exact ⟨(Nat.add_zero _).symm, hv, rfl⟩
  | succ k ih =>
    have hs := tick_step s hv (by omega) (by
      intro ⟨hl, ho, hr⟩; rcases h2 with h2 | h2
      · omega
      · exact h2 ⟨ho, hr⟩)
    have hm : (tick s).rendering = s.rendering := by
      unfold State.rendering; rw [(tick_mask s).1]
    have := ih (tick s) hs.2.1 (by omega) (by
      rcases h2 with h2 | h2
      · left; omega
      · right; rw [hs.2.2, hm]; exact h2)
    rw [ticks_succ, this.1, hs.1, this.2.2, hs.2.2]
    exact ⟨by omega, this.2.1, rfl⟩

theorem pos_of_lin0 (s : State) (hv : Valid s) (h : lin s = 0) : s.dot = 0 ∧ s.scanline = 0 := by
  unfold Valid lin at *
  constructor <;> (rw [← UInt16.toNat_inj]; simp; omega)

/-! ### T-PPU-1 -/

/-- T-PPU-1: a frame from `(0, 0)` on an even frame (or with rendering off) is 89342 dots. -/
theorem T_PPU_1_frame_dots (s : State) (hd : s.dot = 0) (hl : s.scanline = 0)
    (h : s.frameOdd = false ∨ s.rendering = false) :
    (ticks 89342 s).dot = 0 ∧ (ticks 89342 s).scanline = 0 ∧
      (ticks 89342 s).frameOdd = !s.frameOdd := by
  have hv : Valid s := by unfold Valid; simp [hd, hl]
  have h0 : lin s = 0 := by unfold lin; simp [hd, hl]
  have hns : ¬ (s.frameOdd = true ∧ s.rendering = true) := by
    rcases h with h | h <;> simp [h]
  have r := ticks_lin 89341 s hv (by omega) (Or.inr hns)
  rw [show (89342 : Nat) = 89341 + 1 from rfl, ticks_add, ticks_succ, ticks]
  have w := advance_wrap _ r.2.1 (by omega)
  rw [← lin_tick, ← valid_tick, ← frameOdd_tick] at w
  obtain ⟨a, b⟩ := pos_of_lin0 _ w.2.1 w.1
  exact ⟨a, b, by rw [w.2.2, r.2.2]⟩

/-- T-PPU-1: an odd frame with rendering enabled is 89341 dots (the idle dot is skipped). -/
theorem T_PPU_1_odd_frame (s : State) (hd : s.dot = 0) (hl : s.scanline = 0)
    (ho : s.frameOdd = true) (hr : s.rendering = true) :
    (ticks 89341 s).dot = 0 ∧ (ticks 89341 s).scanline = 0 ∧ (ticks 89341 s).frameOdd = false := by
  have hv : Valid s := by unfold Valid; simp [hd, hl]
  have h0 : lin s = 0 := by unfold lin; simp [hd, hl]
  have r := ticks_lin 89340 s hv (by omega) (Or.inl (by omega))
  rw [show (89341 : Nat) = 89340 + 1 from rfl, ticks_add, ticks_succ, ticks]
  have hr' : (ticks 89340 s).rendering = true := by
    unfold State.rendering; rw [(ticks_rendering _ _).1]; exact hr
  have w := advance_skip _ r.2.1 (by omega) (by rw [r.2.2, ho]) hr'
  rw [← lin_tick, ← valid_tick, ← frameOdd_tick] at w
  obtain ⟨a, b⟩ := pos_of_lin0 _ w.2.1 w.1
  exact ⟨a, b, by rw [w.2.2, r.2.2, ho]; rfl⟩

/-- T-PPU-1: the tick from `(241, 0)` reaches `(241, 1)` and sets vblank (unless suppressed). -/
theorem T_PPU_1_vblank_set (s : State) (hd : s.dot = 0) (hl : s.scanline = 241)
    (hs : s.suppressVbl = false) :
    (tick s).scanline = 241 ∧ (tick s).dot = 1 ∧ (tick s).vblank = true ∧
      (tick s).frameReady = true := by
  simp [tick, advance, dotEvents, hd, hl, hs, State.vblank, u8_or80]

/-- T-PPU-1: the tick from `(261, 0)` reaches `(261, 1)` and clears vblank, sprite-0 hit and
sprite overflow. -/
theorem T_PPU_1_vblank_clear (s : State) (hd : s.dot = 0) (hl : s.scanline = 261) :
    (tick s).scanline = 261 ∧ (tick s).dot = 1 ∧ (tick s).vblank = false ∧
      (tick s).spr0Hit = false ∧ (tick s).sprOverflow = false := by
  simp [tick, advance, dotEvents, hd, hl, State.vblank, State.spr0Hit, State.sprOverflow,
    u8_and1F_80, u8_and1F_40, u8_and1F_20]

/-- T-PPU-1: CPU cycles per (89342-dot) frame are `29780 ⅔`. -/
theorem T_PPU_1_cpu_cycles :
    cpuCyclesPerFrame = 29780 + 2 / 3 ∧ 3 * 29780 + 2 = dotsPerFrame ∧ dotsPerFrame = 89342 := by
  refine ⟨by decide +kernel, by decide, by decide⟩

/-- T-PPU-1: NTSC frame rate with rendering on is ≈ 60.0988 Hz. -/
theorem T_PPU_1_frame_rate : (60.0988 : Rat) < frameRate ∧ frameRate < (60.0989 : Rat) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end Nes.Ppu.Proofs
