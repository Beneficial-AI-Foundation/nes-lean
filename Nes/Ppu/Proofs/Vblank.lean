import Nes.Ppu.Registers
import Nes.Ppu.Proofs.Timing

/-!
# `Nes.Ppu.Proofs.Vblank` — T-PPU-5 (NMI generation)

## Spec

* **T-PPU-5 (NMI at vblank).** The tick from `(241, 0)` (no pending `$2002` suppression) leaves
  `nmiLine = nmiEnable` (`T_PPU_5_nmi_at_vblank`).
* **T-PPU-5 (retrigger).** While vblank is set, a `$2000` write with bit 7 set raises
  `nmiLine` (`T_PPU_5_retrigger`); a write with bit 7 clear lowers it, so disabling then
  re-enabling NMI inside vblank produces a fresh rising edge (`T_PPU_5_toggle`). Also through
  the `cpuWrite` dispatcher at `$2000` (`T_PPU_5_retrigger_cpuWrite`).
* **T-PPU-5 (suppression).** If `$2002` is read on a state at `(241, 0)` (one PPU clock before
  the flag is set), then for every `k ≤ 6821` — every dot through `(261, 1)`, where the flags
  are cleared — the state after `k` ticks has vblank clear and `nmiLine` low: that frame's
  vblank flag is never set and no NMI is generated (`T_PPU_5_suppress`).

Method: simulation through the `lin` position lemmas of `Nes.Ppu.Proofs.Timing`; an invariant
(vblank clear ∧ NMI line low) is preserved by every tick that does not land on `(241, 1)`.
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.State

/-- T-PPU-5: at vblank start the NMI line follows `ctrl.7`. -/
theorem T_PPU_5_nmi_at_vblank (s : State) (hd : s.dot = 0) (hl : s.scanline = 241)
    (hs : s.suppressVbl = false) :
    (tick s).nmiLine = s.nmiEnable ∧ (tick s).vblank = true := by
  simp [tick, advance, dotEvents, hd, hl, hs, State.nmiLine, State.nmiEnable, State.vblank,
    u8_or80]

/-- T-PPU-5: enabling NMI while vblank is set raises the NMI line immediately. -/
theorem T_PPU_5_retrigger (s : State) (d : UInt8) (hv : s.vblank = true)
    (hd : (d &&& 0x80 != 0) = true) : (s.writeCtrl d).nmiLine = true := by
  simp only [State.writeCtrl, State.nmiLine, hd, hv, Bool.and_self]

/-- T-PPU-5: inside vblank, writing `$2000` with bit 7 clear then set gives a low → high edge. -/
theorem T_PPU_5_toggle (s : State) (d₀ d₁ : UInt8) (hv : s.vblank = true)
    (h₀ : (d₀ &&& 0x80 != 0) = false) (h₁ : (d₁ &&& 0x80 != 0) = true) :
    (s.writeCtrl d₀).nmiLine = false ∧ ((s.writeCtrl d₀).writeCtrl d₁).nmiLine = true := by
  refine ⟨?_, T_PPU_5_retrigger _ _ hv h₁⟩
  simp only [State.writeCtrl, State.nmiLine, h₀, Bool.false_and]

/-- T-PPU-5 through the register dispatcher: a CPU write of `$2000` enabling NMI in vblank. -/
theorem T_PPU_5_retrigger_cpuWrite (s : State) (d : UInt8) (hv : s.vblank = true)
    (hd : (d &&& 0x80 != 0) = true) : (s.cpuWrite 0x2000 d).1.nmiLine = true := by
  have : ((0x2000 : UInt16) &&& 7).toNat = 0 := by decide
  simp only [State.cpuWrite, this]
  exact T_PPU_5_retrigger _ _ (by simpa [State.vblank] using hv) hd

/-! ### Suppression -/

/-- A tick that does not land on `(241, 1)` keeps "vblank clear ∧ NMI line low". -/
theorem tick_noVbl (s : State) (hl : lin (tick s) ≠ 241 * 341 + 1)
    (h₁ : s.vblank = false) (h₂ : s.nmiOut = false) :
    (tick s).vblank = false ∧ (tick s).nmiOut = false := by
  have ha := advance_regs s
  rw [lin_tick] at hl
  unfold tick dotEvents
  split
  · rename_i hd
    split
    · rename_i hsl
      unfold lin at hl
      simp [← UInt16.toNat_inj] at hd hsl
      omega
    · split
      · simp [State.vblank, u8_and1F_80]
      · unfold State.vblank at *; rw [ha.1, ha.2.1]; exact ⟨h₁, h₂⟩
  · unfold State.vblank at *; rw [ha.1, ha.2.1]; exact ⟨h₁, h₂⟩

theorem ticks_noVbl (k : Nat) (s : State) (hv : Valid s) (hlo : 241 * 341 + 1 ≤ lin s)
    (hhi : lin s + k ≤ 89340) (h₁ : s.vblank = false) (h₂ : s.nmiOut = false) :
    (ticks k s).vblank = false ∧ (ticks k s).nmiOut = false := by
  induction k generalizing s with
  | zero => exact ⟨h₁, h₂⟩
  | succ k ih =>
    have hs := tick_step s hv (by omega) (by omega)
    have := tick_noVbl s (by omega) h₁ h₂
    rw [ticks_succ]
    exact ih (tick s) hs.2.1 (by omega) (by omega) this.1 this.2

/-- T-PPU-5: a `$2002` read one PPU clock before vblank (state at `(241, 0)`) suppresses that
frame's vblank flag and NMI, through the flag clear at `(261, 1)`. -/
theorem T_PPU_5_suppress (s : State) (hd : s.dot = 0) (hl : s.scanline = 241) :
    ∀ k, k ≤ 6821 →
      (ticks k (s.readStatus).1).vblank = false ∧ (ticks k (s.readStatus).1).nmiLine = false := by
  intro k hk
  -- the read: vblank clear, line low, suppression armed, position unchanged
  have hr1 : (s.readStatus).1.vblank = false := by
    simp [State.readStatus, State.vblank, u8_and7F_80]
  have hr2 : (s.readStatus).1.nmiOut = false := by simp [State.readStatus]
  have hr3 : (s.readStatus).1.suppressVbl = true := by simp [State.readStatus, hd, hl]
  have hrd : (s.readStatus).1.dot = 0 := by simp [State.readStatus, hd]
  have hrl : (s.readStatus).1.scanline = 241 := by simp [State.readStatus, hl]
  cases k with
  | zero => exact ⟨hr1, hr2⟩
  | succ k =>
    -- first tick: lands on (241, 1) with suppression armed
    have hrv : Valid (s.readStatus).1 := by unfold Valid; simp [hrd, hrl]
    have h0 : lin (s.readStatus).1 = 241 * 341 := by unfold lin; simp [hrd, hrl]
    have hs := tick_step _ hrv (by omega) (by omega)
    have e1 : (tick (s.readStatus).1).vblank = false ∧ (tick (s.readStatus).1).nmiOut = false := by
      have ha := advance_regs (s.readStatus).1
      have had : (advance (s.readStatus).1).dot = 1 := by simp [advance, hrd, hrl]
      have hal : (advance (s.readStatus).1).scanline = 241 := by simp [advance, hrd, hrl]
      unfold tick dotEvents
      simp only [had, hal, ha.2.2.1, hr3]
      simp only [State.vblank, beq_self_eq_true, ite_true]
      unfold State.vblank at hr1
      rw [ha.1, ha.2.1]
      exact ⟨hr1, hr2⟩
    rw [ticks_succ]
    have := ticks_noVbl k _ hs.2.1 (by omega) (by omega) e1.1 e1.2
    exact ⟨this.1, this.2⟩

end Nes.Ppu.Proofs
