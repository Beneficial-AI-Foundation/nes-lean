/-!
# `Nes.Apu.FrameCounter` — the APU frame counter (4/5-step sequencer, frame IRQ)

The frame counter is a divider/sequencer, clocked once per CPU cycle here, that produces the
*quarter-frame* clock (envelopes, triangle linear counter) and the *half-frame* clock (length
counters, sweep units), and in 4-step mode raises the frame interrupt.

Source: NESdev wiki, "APU Frame Counter" (NTSC). Step times in APU cycles are 3728.5, 7456.5,
11185.5, 14914 / 14914.5 / 0 (4-step) and 3728.5, 7456.5, 11185.5, 14914.5, 18640.5 / 0
(5-step). Counted in CPU cycles since the sequence (re)start this is:

| CPU cycle | 4-step (`$4017` bit 7 = 0)         | 5-step (`$4017` bit 7 = 1) |
|-----------|------------------------------------|----------------------------|
| 7457      | quarter                            | quarter                    |
| 14913     | quarter + half                     | quarter + half             |
| 22371     | quarter                            | quarter                    |
| 29828     | IRQ flag set                       | —                          |
| 29829     | quarter + half, IRQ flag set       | nothing                    |
| 29830     | IRQ flag set; sequence wraps to 0  | —                          |
| 37281     | —                                  | quarter + half             |
| 37282     | —                                  | sequence wraps to 0        |

The IRQ flag is only set while the interrupt-inhibit flag (`$4017` bit 6) is clear; setting
inhibit clears the flag. Reading `$4015` clears the flag (done by the APU register file through
`clearIrq`).

`$4017` write: the mode and inhibit bits take effect at once; the sequencer is reset "3 CPU
cycles after the write cycle if the write occurs during an APU cycle, 4 if between APU cycles"
(wiki). The caller passes the parity of the write cycle (`cpuOdd`): even → 3, odd → 4, the
same convention as the blargg-validated M2 scaffolding (`Test/Blargg.lean`): the reset is
performed by the 3rd/4th `tick` called *after* the write (the write cycle's own tick runs
before its bus access). At the reset, in
5-step mode, a quarter and a half frame clock are generated immediately; in 4-step mode no
clock is generated.

Power-up (wiki, "APU power up and reset"): as if `$00` had been written to `$4017` (`powerOn`).
Reset: as if the last value were written again (mode and inhibit kept, `reset`).

Representation (hot path, PLAN §4): all fields are scalars; `tick` returns the new state and a
packed event byte, `bit 0` = quarter-frame clock, `bit 1` = half-frame clock (`evQuarter`,
`evHalf`), so the composer clocks the channels without allocation.

Convention: `cycle` is the number of CPU cycles since the sequence start. `tick` increments it
and then performs the events of the new value (so from `cycle = 0`, the `k`-th tick performs
the events of cycle `k`); the tick reaching the wrap value leaves `cycle = 0`.
-/

namespace Nes.Apu

/-- Event bit: quarter-frame clock. -/
@[inline] def evQuarter : UInt8 := 1
/-- Event bit: half-frame clock. -/
@[inline] def evHalf : UInt8 := 2

/-- APU frame counter state. -/
structure FrameCounter where
  /-- CPU cycles since the start of the current sequence. -/
  cycle : UInt16 := 0
  /-- Pending sequencer reset: ticks until it happens (0 = none; the reset happens on the
  tick that sees `1`). -/
  resetIn : UInt8 := 0
  /-- `$4017` bit 7: 5-step mode. -/
  mode5 : Bool := false
  /-- `$4017` bit 6: IRQ inhibit. -/
  inhibit : Bool := false
  /-- Frame interrupt flag (read in `$4015` bit 6). -/
  irq : Bool := false
  deriving Repr, Inhabited, DecidableEq

namespace FrameCounter

/-- Quarter/half events performed when the sequencer reaches CPU cycle `c`. -/
@[inline] def eventsAt (m5 : Bool) (c : UInt16) : UInt8 :=
  if c == 7457 || c == 22371 then 1
  else if c == 14913 then 3
  else if m5 then (if c == 37281 then 3 else 0)
  else if c == 29829 then 3 else 0

/-- One CPU cycle of the frame counter: new state and the packed event byte. -/
@[inline] def tick (fc : FrameCounter) : FrameCounter × UInt8 :=
  let r := fc.resetIn
  if r == 1 then
    ({ fc with cycle := 0, resetIn := 0 }, if fc.mode5 then 3 else 0)
  else
    let m5 := fc.mode5
    let c := fc.cycle + 1
    let irqStep := !m5 && (c == 29828 || c == 29829 || c == 29830)
    let wrap := if m5 then c ≥ 37282 else c ≥ 29830
    ({ fc with cycle := if wrap then 0 else c,
               resetIn := if r == 0 then 0 else r - 1,
               irq := fc.irq || (irqStep && !fc.inhibit) },
     eventsAt m5 c)

/-- CPU write to `$4017`. `cpuOdd` is the parity of the write cycle (even → reset after 3
cycles, odd → after 4). -/
@[inline] def write4017 (fc : FrameCounter) (v : UInt8) (cpuOdd : Bool) : FrameCounter :=
  let inh := v &&& 0x40 != 0
  { fc with mode5 := v &&& 0x80 != 0, inhibit := inh,
            irq := fc.irq && !inh,
            resetIn := if cpuOdd then 4 else 3 }

/-- Acknowledge the frame interrupt (the `$4015` read side effect). -/
@[inline] def clearIrq (fc : FrameCounter) : FrameCounter := { fc with irq := false }

/-- The frame counter's contribution to the CPU IRQ line. -/
@[inline] def irqLine (fc : FrameCounter) : Bool := fc.irq

/-- Power-up state: as if `$00` were written to `$4017`. -/
def powerOn : FrameCounter := write4017 {} 0 false

/-- Reset: as if the last `$4017` value were written again. -/
def reset (fc : FrameCounter) : FrameCounter :=
  write4017 fc ((if fc.mode5 then 0x80 else 0) ||| (if fc.inhibit then 0x40 else 0)) false

end FrameCounter

end Nes.Apu
