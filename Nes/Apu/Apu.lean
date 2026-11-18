import Nes.Apu.FrameCounter
import Nes.Apu.Pulse
import Nes.Apu.Triangle
import Nes.Apu.Noise
import Nes.Apu.Dmc
import Nes.Apu.Mixer

/-!
# `Nes.Apu.Apu` — the composed APU (2A03 sound part)

Bundles the frame counter (`Nes.Apu.FrameCounter`), the two pulse channels, the triangle, the
noise channel and the DMC, and implements the CPU-visible register file `$4000–$4013`, `$4015`,
`$4017` (NESdev "APU registers"). The system (`Nes.System.Nes`) owns the DMC's DMA: it watches
`dmc.dmaRequest`, steals CPU cycles and calls `dmcDmaComplete` with the fetched byte.

## Clocking (`tick`, once per CPU cycle, *before* the cycle's bus access)

1. the frame counter ticks (`FrameCounter.tick`; its `$4017` reset delay convention requires the
   write cycle's own tick to run before the write — hence before the bus access);
2. on the "odd" APU phase (every other CPU cycle = once per APU cycle) the pulse and noise timers
   step; the triangle and DMC timers step every CPU cycle;
3. quarter-frame events clock the envelopes and the triangle's linear counter; half-frame events
   the length counters and sweeps.

Pending length writes (`haltMask`/`haltVal`, `loadMask`/`loadVal`) are applied after the
next tick (`applyPending`, see the quirks below).

## Registers

* `$4000–$4003` pulse 1, `$4004–$4007` pulse 2, `$4008–$400B` triangle, `$400C–$400F` noise,
  `$4010–$4013` DMC (each channel's `write`).
  Quirks (blargg 2005 `len_halt_timing`, `len_reload_timing`; `setLen`): relative to the
  half-frame clock of the *next* tick (`halfNext`), a halt-flag write is deferred past the clock,
  and a length reload is ignored if the counter is nonzero, else deferred past the clock.
* `$4015` write: enable bits 0–4 (`setEnabled`; the DMC's clears the DMC IRQ flag).
* `$4015` read (`read4015`): bits 0–3 length counters `≠ 0`, bit 4 DMC bytes remaining `≠ 0`,
  bit 6 frame IRQ, bit 7 DMC IRQ (bit 5 is open bus, merged by the system). The read clears the
  frame IRQ flag. (NESdev's "not when it coincides with setting it" refinement was tried and
  fails `apu_test/6-irq_flag_timing`; not modelled.)
* `$4017` write: `FrameCounter.write4017` with the write cycle's parity.

## Output

`sample a` = `mixSample` of the five channel outputs (`[0, 65535]`): the mixer output of the
current state, i.e. the sample of the last ticked cycle (a function of the state rather than a
stored field: nothing is computed per cycle unless audio is collected — `runFrameAudio`).

`irq a` = frame IRQ ∨ DMC IRQ (wired into the CPU's IRQ line).

## Power-up / reset (NESdev "APU power up and reset")

`powerOn`: frame counter as if `$4017 ← $00` one cycle before the CPU's first cycle (one
`FrameCounter.tick` applied: the sequencer restarts 10–11 cycles before the first instruction —
`apu_reset/4017_timing` prints 11, `09.reset_timing` needs ≥ 10), all channels silent, noise
LFSR = 1, DMC timer phase 426 (so the DMC's reload fetches halt the CPU on a put cycle and steal
4 cycles, as `dmc_dma_during_read4`'s `sync_dmc` assumes).
`reset`: `$4015 ← $00` (length counters cleared, DMC stopped, DMC IRQ cleared), `$4017`
rewritten with its last value (and one tick, as at power-up), the frame IRQ cleared, triangle unaffected, DMC level `&= 1`.
-/

namespace Nes.Apu

/-- The APU. -/
structure Apu where
  fc : FrameCounter := FrameCounter.powerOn.tick.1
  p1 : Pulse := Pulse.init1
  p2 : Pulse := Pulse.init2
  tri : Triangle := {}
  noise : Noise := {}
  dmc : Dmc := { timer := 426 }
  /-- APU phase: pulse/noise timers step on ticks where this is `true` (then it flips). -/
  odd : Bool := false
  /-- Length-halt writes waiting for the next tick (bit 0 pulse 1, 1 pulse 2, 2 triangle,
  3 noise): a halt write made just before a half-frame clock takes effect after it. -/
  haltMask : UInt8 := 0
  /-- The pending halt values (same bits). -/
  haltVal : UInt8 := 0
  /-- Length reloads waiting for the next tick (same bits): a reload made just before a
  half-frame clock while the counter is 0 lands after the clock (not decremented by it). -/
  loadMask : UInt8 := 0
  /-- The pending reload values, byte `k` for channel bit `k`. -/
  loadVal : UInt32 := 0
  deriving Repr, DecidableEq, Inhabited

namespace Apu

/-- Power-up state. -/
def powerOn : Apu := {}

/-- A length counter with the pending writes of channel bit `b` (index `k`) applied. -/
@[inline] def pendLen (a : Apu) (b : UInt8) (k : UInt32) (l : Length) : Length :=
  { counter := if a.loadMask &&& b != 0 then (a.loadVal >>> (8 * k)).toUInt8 else l.counter,
    halt := if a.haltMask &&& b != 0 then a.haltVal &&& b != 0 else l.halt }

/-- Apply the pending length writes (rare path, out of the per-cycle straight line). -/
@[noinline] def applyPending (a : Apu) : Apu :=
  { a with p1 := { a.p1 with len := a.pendLen 1 0 a.p1.len },
           p2 := { a.p2 with len := a.pendLen 2 1 a.p2.len },
           tri := { a.tri with len := a.pendLen 4 2 a.tri.len },
           noise := { a.noise with len := a.pendLen 8 3 a.noise.len },
           haltMask := 0, loadMask := 0 }

/-- One CPU cycle. -/
@[inline] def tick (a : Apu) : Apu :=
  let (fc, ev) := a.fc.tick
  let q := ev &&& evQuarter != 0
  let h := ev &&& evHalf != 0
  let step := a.odd
  let p1 := a.p1
  let p1 := if step then p1.tick else p1
  let p1 := if q then p1.quarterFrame else p1
  let p1 := if h then p1.halfFrame else p1
  let p2 := a.p2
  let p2 := if step then p2.tick else p2
  let p2 := if q then p2.quarterFrame else p2
  let p2 := if h then p2.halfFrame else p2
  let tri := a.tri.tick
  let tri := if q then tri.quarterFrame else tri
  let tri := if h then tri.halfFrame else tri
  let nz := a.noise
  let nz := if step then nz.tick else nz
  let nz := if q then nz.quarterFrame else nz
  let nz := if h then nz.halfFrame else nz
  let a' := { a with fc, p1, p2, tri, noise := nz, dmc := a.dmc.tick, odd := !a.odd }
  if a.haltMask ||| a.loadMask != 0 then a'.applyPending else a'

/-- Will the next tick clock the length counters (a half-frame event)? -/
@[inline] def halfNext (a : Apu) : Bool := a.fc.tick.2 &&& evHalf != 0

/-- A channel register write made just before a half-frame clock (`a.halfNext`): given the
channel's length counter before (`old`) and after (`new`) its own `write`, store `old` now and
record what the clock must not see (blargg `len_halt_timing`, `len_reload_timing`):
* a halt-flag change is deferred past the clock (the clock uses the old flag);
* a reload is ignored if the counter is nonzero, else deferred past the clock (so it is not
  decremented by it).
Channel bit `b`, index `k`. Without a clock next, `new` is stored. -/
@[inline] def setLen (a : Apu) (b : UInt8) (k : UInt32) (old new : Length) : Apu × Length :=
  if !a.halfNext then (a, new)
  else
    let dh := new.halt != old.halt
    let dl := new.counter != old.counter && old.counter == 0
    ({ a with haltMask := if dh then a.haltMask ||| b else a.haltMask,
              haltVal := if dh then (if new.halt then a.haltVal ||| b else a.haltVal &&& ~~~b)
                         else a.haltVal,
              loadMask := if dl then a.loadMask ||| b else a.loadMask,
              loadVal := if dl then (a.loadVal &&& ~~~((0xFF : UInt32) <<< (8 * k))) |||
                           (new.counter.toUInt32 <<< (8 * k)) else a.loadVal },
     old)

/-- `$4015` write. -/
@[inline] def write4015 (a : Apu) (v : UInt8) : Apu :=
  { a with p1 := a.p1.setEnabled (v &&& 1 != 0), p2 := a.p2.setEnabled (v &&& 2 != 0),
           tri := a.tri.setEnabled (v &&& 4 != 0), noise := a.noise.setEnabled (v &&& 8 != 0),
           dmc := a.dmc.setEnabled (v &&& 0x10 != 0) }

/-- CPU write to `addr ∈ $4000–$4017` (other addresses — `$4014`, `$4016` — are ignored).
`cpuOdd`: parity of the write cycle (for `$4017`). -/
@[inline] def write (a : Apu) (addr : UInt16) (v : UInt8) (cpuOdd : Bool) : Apu :=
  let r := (addr &&& 0x1F).toUInt8
  let i := r &&& 3
  if r < 4 then
    let p := a.p1.write i v
    let (a, len) := a.setLen 1 0 a.p1.len p.len
    { a with p1 := { p with len } }
  else if r < 8 then
    let p := a.p2.write i v
    let (a, len) := a.setLen 2 1 a.p2.len p.len
    { a with p2 := { p with len } }
  else if r < 0x0C then
    let t := a.tri.write i v
    let (a, len) := a.setLen 4 2 a.tri.len t.len
    { a with tri := { t with len } }
  else if r < 0x10 then
    let n := a.noise.write i v
    let (a, len) := a.setLen 8 3 a.noise.len n.len
    { a with noise := { n with len } }
  else if r < 0x14 then { a with dmc := a.dmc.write i v }
  else if r == 0x15 then a.write4015 v
  else if r == 0x17 then { a with fc := a.fc.write4017 v cpuOdd }
  else a

/-- `$4015` status byte (bit 5 = 0; the system merges open bus). -/
@[inline] def status (a : Apu) : UInt8 :=
  (if a.p1.lengthNonzero then 1 else 0) ||| (if a.p2.lengthNonzero then 2 else 0) |||
  (if a.tri.lengthNonzero then 4 else 0) ||| (if a.noise.lengthNonzero then 8 else 0) |||
  (if a.dmc.active then 0x10 else 0) ||| (if a.fc.irq then 0x40 else 0) |||
  (if a.dmc.irq then 0x80 else 0)

/-- `$4015` read: the status byte, and the frame IRQ flag cleared (unless set this cycle). -/
@[inline] def read4015 (a : Apu) : Apu × UInt8 :=
  ({ a with fc := a.fc.clearIrq }, a.status)

/-- The APU's IRQ output (frame counter or DMC). -/
@[inline] def irq (a : Apu) : Bool := a.fc.irq || a.dmc.irq

/-- The mixer output of the current state, `[0, 65535]`. -/
@[inline] def sample (a : Apu) : UInt16 :=
  mixSample a.p1.output a.p2.output a.tri.output a.noise.output a.dmc.output

/-- Deliver a DMC DMA byte. -/
@[inline] def dmcDmaComplete (a : Apu) (b : UInt8) : Apu := { a with dmc := a.dmc.dmaComplete b }

/-- Reset button (see the module doc). -/
def reset (a : Apu) : Apu :=
  let a := a.write4015 0
  { a with fc := a.fc.reset.tick.1.clearIrq, dmc := { a.dmc with level := a.dmc.level &&& 1 } }

end Apu

end Nes.Apu
