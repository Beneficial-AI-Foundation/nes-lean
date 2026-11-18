import Nes.Apu.Units

/-!
# `Nes.Apu.Pulse` — pulse (square) channels 1 and 2

NESdev "APU Pulse". Registers `$4000–$4003` (pulse 1) / `$4004–$4007` (pulse 2).

## Spec

* State: `duty` (0..3), sequencer position `seq` (0..7), 11-bit `period` and its countdown
  `timer`, `len : Length`, `env : Envelope`, `sweep : Sweep`, the `$4015` `enabled` bit, and
  `ones` (true for pulse 1: the sweep negates in ones' complement; see `Sweep.target`).
* `write p r v` (`r` taken mod 4):
  * 0: `duty := v >>> 6`, `len.halt := v.5`, `Envelope.write` (loop = v.5, const = v.4, V).
  * 1: `Sweep.write`.
  * 2: `period` bits 0–7 := `v`.
  * 3: `period` bits 8–10 := `v & 7`; `Length.load` (only if enabled); `seq := 0`;
    `env.start := true`. The timer is not reset.
* `tick` (once per APU cycle = every 2 CPU cycles): if `timer = 0` then `timer := period` and
  the sequencer steps `seq := (seq - 1) mod 8` (it counts 0, 7, 6, …, 1); else `timer - 1`.
  So one waveform step lasts `period + 1` APU cycles.
* Duty sequences (NESdev lookup table, bit `seq` of the row): 0 = `00000001`,
  1 = `00000011`, 2 = `00001111`, 3 = `11111100` (written seq 0..7 left to right); played
  from a reset (0, 7, 6, …) they give the waveforms `01000000`, `01100000`, `01111000`,
  `10011111`.
* `quarterFrame`: envelope. `halfFrame`: length counter and sweep (period update, then
  divider).
* `setEnabled`: `enabled := b`; `false` clears the length counter.
* `output` (0..15): 0 if the duty bit is 0, the length counter is 0, or the sweep mutes
  (`period < 8 ∨ target > $7FF`); else the envelope volume.
-/

namespace Nes.Apu

/-- Duty table packed as 4 bytes (row `d` is byte `d`, bit `seq` = output). -/
def dutyBits : UInt32 := 0x3FF0C080

/-- Duty-table lookup: `1` or `0` for duty `d` (mod 4) at sequencer step `seq` (mod 8). -/
@[inline] def dutyBit (d seq : UInt8) : UInt8 :=
  ((dutyBits >>> ((d &&& 3).toUInt32 * 8 + (seq &&& 7).toUInt32)) &&& 1).toUInt8

/-- A pulse channel. -/
structure Pulse where
  duty : UInt8 := 0
  seq : UInt8 := 0
  timer : UInt16 := 0
  period : UInt16 := 0
  len : Length := {}
  env : Envelope := {}
  sweep : Sweep := {}
  enabled : Bool := false
  /-- Pulse 1 (`true`): ones' complement sweep negate. Pulse 2: two's complement. -/
  ones : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Pulse

/-- Power-up pulse 1. -/
def init1 : Pulse := { ones := true }
/-- Power-up pulse 2. -/
def init2 : Pulse := { ones := false }

/-- Register write; `r` is the register index (mod 4). -/
@[inline] def write (p : Pulse) (r : UInt8) (v : UInt8) : Pulse :=
  match r &&& 3 with
  | 0 => { p with duty := v >>> 6, len := { p.len with halt := v &&& 0x20 != 0 },
                  env := p.env.write v }
  | 1 => { p with sweep := p.sweep.write v }
  | 2 => { p with period := (p.period &&& (0x700 : UInt16)) ||| v.toUInt16 }
  | _ => { p with period := (p.period &&& (0xFF : UInt16)) ||| ((v.toUInt16 &&& 7) <<< 8),
                  len := p.len.load p.enabled v, seq := 0,
                  env := { p.env with start := true } }

/-- Timer step (once per APU cycle). -/
@[inline] def tick (p : Pulse) : Pulse :=
  let z := p.timer == 0
  { p with timer := if z then p.period else p.timer - 1,
           seq := if z then (p.seq - 1) &&& 7 else p.seq }

/-- Quarter-frame clock: envelope. -/
@[inline] def quarterFrame (p : Pulse) : Pulse := { p with env := p.env.quarterFrame }

/-- Half-frame clock: length counter and sweep. -/
@[inline] def halfFrame (p : Pulse) : Pulse :=
  { p with period := p.sweep.newPeriod p.ones p.period, sweep := p.sweep.clockDivider,
           len := p.len.halfFrame }

/-- `$4015` enable bit. -/
@[inline] def setEnabled (p : Pulse) (b : Bool) : Pulse :=
  { p with enabled := b, len := p.len.setEnabled b }

/-- `$4015` status bit. -/
@[inline] def lengthNonzero (p : Pulse) : Bool := p.len.nonzero

/-- Channel output, 0..15. -/
@[inline] def output (p : Pulse) : UInt8 :=
  if dutyBit p.duty p.seq == 0 || p.len.counter == 0 || p.sweep.muted p.ones p.period then 0
  else p.env.output

end Pulse

end Nes.Apu
