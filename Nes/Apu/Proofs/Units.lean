import Nes.Apu.Pulse
import Nes.Apu.Noise

/-!
# `Nes.Apu.Proofs.Units` — facts about the APU length counter, envelope, sweep and noise LFSR

## Spec

* `lengthTable_values`: `lengthLoad i` for `i = 0..31` is the documented NESdev table.
* `length_halt`: with the halt flag set, a half-frame clock leaves the length counter alone;
  `length_dec`: without it, a nonzero counter decrements by one.
* Envelope (`envelope_*`): constant volume outputs V regardless of the decay level; a start
  flag sets the decay level to 15; with the divider at 0 a nonzero decay level steps down by
  one; at 0 it wraps to 15 when looping and holds 0 otherwise. `envelope_decay` bundles these.
* `sweep_mute`: muted iff `period < 8 ∨ target > $7FF` (regardless of `enabled`).
* `pulse1_negate_ones_complement` / `pulse2_negate_twos_complement`: when negating with
  `change < period`, pulse 1's target is `p - change - 1` and pulse 2's `p - change`.
* `noise_lfsr_period`: in long mode, the LFSR started from the power-up seed 1 first returns
  to 1 after exactly 32767 = 2^15 - 1 steps (maximal length; checked by kernel evaluation,
  `decide +kernel`, a few seconds).
-/

namespace Nes.Apu.Proofs

open Nes.Apu

/-- The NESdev "APU Length Counter" table, as documented. -/
def lengthTableDoc : List UInt8 :=
  [10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
   12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30]

theorem lengthTable_values :
    (List.range 32).map (fun i => lengthLoad i.toUInt8) = lengthTableDoc := by decide

theorem length_halt (l : Length) (h : l.halt = true) : l.halfFrame = l := by
  cases l; simp_all [Length.halfFrame]

theorem length_dec (l : Length) (h : l.halt = false) (hc : l.counter ≠ 0) :
    l.halfFrame.counter = l.counter - 1 := by
  simp [Length.halfFrame, h, hc]

theorem envelope_const (e : Envelope) (h : e.constVol = true) : e.output = e.volume := by
  simp [Envelope.output, h]

theorem envelope_start (e : Envelope) (h : e.start = true) :
    e.quarterFrame.decay = 15 ∧ e.quarterFrame.divider = e.volume ∧
      e.quarterFrame.start = false := by
  simp [Envelope.quarterFrame, h]

theorem envelope_step (e : Envelope) (hs : e.start = false) (hd : e.divider = 0)
    (hz : e.decay ≠ 0) : e.quarterFrame.decay = e.decay - 1 := by
  simp [Envelope.quarterFrame, Envelope.nextDecay, hs, hd, hz]

theorem envelope_loop (e : Envelope) (hs : e.start = false) (hd : e.divider = 0)
    (hz : e.decay = 0) (hl : e.loop = true) : e.quarterFrame.decay = 15 := by
  simp [Envelope.quarterFrame, Envelope.nextDecay, hs, hd, hz, hl]

theorem envelope_hold (e : Envelope) (hs : e.start = false) (hd : e.divider = 0)
    (hz : e.decay = 0) (hl : e.loop = false) : e.quarterFrame.decay = 0 := by
  simp [Envelope.quarterFrame, Envelope.nextDecay, hs, hd, hz, hl]

/-- Decay behaviour of the level counter itself: from 15 it reaches 0 in 15 clocks, and the
next clock wraps to 15 (loop) or holds 0. -/
theorem envelope_decay :
    (∀ l : Bool, Nat.repeat (Envelope.nextDecay · l) 15 15 = 0) ∧
    Envelope.nextDecay 0 true = 15 ∧ Envelope.nextDecay 0 false = 0 ∧
    (∀ d : Fin 16, d.val ≠ 0 → ∀ l, Envelope.nextDecay d.val.toUInt8 l = d.val.toUInt8 - 1) := by
  decide

theorem sweep_mute (s : Sweep) (ones : Bool) (p : UInt16) :
    s.muted ones p = true ↔ p < 8 ∨ s.target ones p > 0x7FF := by
  simp [Sweep.muted]

theorem pulse1_negate_ones_complement (s : Sweep) (p : UInt16) (hn : s.negate = true)
    (hc : (p >>> s.shift.toUInt16).toNat < p.toNat) :
    s.target true p = p - (p >>> s.shift.toUInt16) - 1 := by
  simp only [Sweep.target, hn, ite_true]
  generalize p >>> s.shift.toUInt16 = c at *
  have h1 : ¬ p < c + 1 := by rw [UInt16.lt_iff_toNat_lt, UInt16.toNat_add]; simp; omega
  simp only [h1, ite_false]
  apply UInt16.toBitVec_inj.mp; simp; bv_omega

theorem pulse2_negate_twos_complement (s : Sweep) (p : UInt16) (hn : s.negate = true)
    (hc : (p >>> s.shift.toUInt16).toNat < p.toNat) :
    s.target false p = p - (p >>> s.shift.toUInt16) := by
  simp only [Sweep.target, hn, ite_true]
  generalize p >>> s.shift.toUInt16 = c at *
  have h1 : ¬ p < c := by rw [UInt16.lt_iff_toNat_lt]; omega
  simp [h1]

/-- NESdev "APU Sweep" example: period $100 (256), shift 1 → change 128; pulse 1 negate
gives 127, pulse 2 negate 128, adding gives 384. -/
example : ({ negate := true, shift := 1 } : Sweep).target true 0x100 = 127 ∧
    ({ negate := true, shift := 1 } : Sweep).target false 0x100 = 128 ∧
    ({ shift := 1 } : Sweep).target true 0x100 = 384 := by decide

/-- First return of the long-mode LFSR to 1 within `fuel` steps: `k` such that
`lfsrStep^[k] 1 = 1`, or `0` if none. -/
def lfsrFirstReturn : Nat → Nat → UInt16 → Nat
  | 0, _, _ => 0
  | fuel + 1, k, x =>
    let y := lfsrStep false x
    if y == 1 then k + 1 else lfsrFirstReturn fuel (k + 1) y

theorem noise_lfsr_period : lfsrFirstReturn 40000 0 1 = 32767 := by decide +kernel

end Nes.Apu.Proofs

