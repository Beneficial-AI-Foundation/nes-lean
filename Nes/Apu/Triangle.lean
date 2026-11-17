import Nes.Apu.Units

/-!
# `Nes.Apu.Triangle` — triangle channel

NESdev "APU Triangle". Registers `$4008–$400B`.

## Spec

* State: 11-bit `period`, `timer`, sequencer position `seq` (0..31), `len : Length`, linear
  counter `linear`, its reload value `linReload` (7 bits), `linReloadFlag`, the
  `control` flag (= length halt), the `$4015` `enabled` bit.
* `write t r v` (`r` mod 4):
  * 0 (`$4008`): `control := v.7` (also `len.halt`), `linReload := v & $7F`.
  * 1 (`$4009`): unused.
  * 2 (`$400A`): `period` bits 0–7.
  * 3 (`$400B`): `period` bits 8–10; `Length.load` (only if enabled);
    `linReloadFlag := true`. The timer and sequencer are not reset.
* `tick` (once per CPU cycle): if `timer = 0` then `timer := period`, and the sequencer
  steps (`seq := (seq + 1) mod 32`) when both `len.counter ≠ 0` and `linear ≠ 0` and
  `period ≥ 2`; else `timer - 1`.
* Ultrasonic periods (`period < 2`, ~28–55 kHz): hardware keeps stepping and the DAC
  averages to ~7.5. We choose to *freeze* the sequencer instead, so the output holds its
  current value: stable (no aliasing hiss, no pop) — as several emulators do. Silencing is
  rejected because jumping to 0 would itself click.
* `quarterFrame` (linear counter): if `linReloadFlag` then `linear := linReload`, else if
  `linear ≠ 0` decrement; then if `control` is clear, `linReloadFlag := false`.
* `halfFrame`: length counter.
* `output` (0..15): the 32-step sequence `15, 14, …, 0, 0, 1, …, 15` at `seq`. Not gated by
  the counters: halting the sequencer holds the current level (as hardware).
-/

namespace Nes.Apu

/-- Triangle 32-step sequence value at step `seq` (mod 32): 15..0 then 0..15. -/
@[inline] def triangleLevel (seq : UInt8) : UInt8 :=
  let s := seq &&& 31
  if s < 16 then 15 - s else s - 16

/-- The triangle channel. -/
structure Triangle where
  timer : UInt16 := 0
  period : UInt16 := 0
  seq : UInt8 := 0
  len : Length := {}
  linear : UInt8 := 0
  linReload : UInt8 := 0
  linReloadFlag : Bool := false
  control : Bool := false
  enabled : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Triangle

/-- Register write; `r` is the register index (mod 4). -/
@[inline] def write (t : Triangle) (r : UInt8) (v : UInt8) : Triangle :=
  match r &&& 3 with
  | 0 => let c := v &&& 0x80 != 0
         { t with control := c, len := { t.len with halt := c }, linReload := v &&& 0x7F }
  | 1 => t
  | 2 => { t with period := (t.period &&& (0x700 : UInt16)) ||| v.toUInt16 }
  | _ => { t with period := (t.period &&& (0xFF : UInt16)) ||| ((v.toUInt16 &&& 7) <<< 8),
                  len := t.len.load t.enabled v, linReloadFlag := true }

/-- Timer step (once per CPU cycle). -/
@[inline] def tick (t : Triangle) : Triangle :=
  let z := t.timer == 0
  let step := z && t.len.counter != 0 && t.linear != 0 && t.period >= 2
  { t with timer := if z then t.period else t.timer - 1,
           seq := if step then (t.seq + 1) &&& 31 else t.seq }

/-- Quarter-frame clock: linear counter. -/
@[inline] def quarterFrame (t : Triangle) : Triangle :=
  { t with linear := if t.linReloadFlag then t.linReload
                     else if t.linear != 0 then t.linear - 1 else 0,
           linReloadFlag := t.linReloadFlag && t.control }

/-- Half-frame clock: length counter. -/
@[inline] def halfFrame (t : Triangle) : Triangle := { t with len := t.len.halfFrame }

/-- `$4015` enable bit. -/
@[inline] def setEnabled (t : Triangle) (b : Bool) : Triangle :=
  { t with enabled := b, len := t.len.setEnabled b }

/-- `$4015` status bit. -/
@[inline] def lengthNonzero (t : Triangle) : Bool := t.len.nonzero

/-- Channel output, 0..15. -/
@[inline] def output (t : Triangle) : UInt8 := triangleLevel t.seq

end Triangle

end Nes.Apu
