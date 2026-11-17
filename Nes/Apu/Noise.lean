import Nes.Apu.Units

/-!
# `Nes.Apu.Noise` — noise channel

NESdev "APU Noise". Registers `$400C–$400F`.

## Spec

* State: `timer` and its reload `reload` (APU cycles), `mode` flag, 15-bit `lfsr` (power-up
  value 1), `len : Length`, `env : Envelope`, the `$4015` `enabled` bit.
* `noisePeriodTable` (NTSC, NESdev): 4, 8, 16, 32, 64, 96, 128, 160, 202, 254, 380, 508,
  762, 1016, 2034, 4068 — CPU cycles per LFSR clock. The timer runs on APU cycles
  (= 2 CPU cycles) and counts `reload, …, 0`, so `reload := entry / 2 - 1`.
* `write n r v` (`r` mod 4):
  * 0 (`$400C`): `len.halt := v.5`, `Envelope.write`.
  * 1 (`$400D`): unused.
  * 2 (`$400E`): `mode := v.7`, `reload := noisePeriodTable[v & 15] / 2 - 1`.
  * 3 (`$400F`): `Length.load` (only if enabled); `env.start := true`.
* `lfsrStep mode x`: `fb := x.0 xor (mode ? x.6 : x.1)`; `x := (x >>> 1) | (fb <<< 14)`.
* `tick` (once per APU cycle): if `timer = 0` then `timer := reload`, `lfsr := lfsrStep`;
  else `timer - 1`.
* `quarterFrame`: envelope. `halfFrame`: length counter.
* `output` (0..15): 0 if `lfsr.0 = 1` or the length counter is 0, else the envelope volume.
-/

namespace Nes.Apu

/-- NTSC noise periods in CPU cycles (NESdev "APU Noise"). -/
def noisePeriodTable : Array UInt16 :=
  #[4, 8, 16, 32, 64, 96, 128, 160, 202, 254, 380, 508, 762, 1016, 2034, 4068]

theorem noisePeriodTable_size : noisePeriodTable.size = 16 := rfl

/-- Timer reload (APU cycles) for period index `i` (mod 16). -/
@[inline] def noiseReload (i : UInt8) : UInt16 :=
  (noisePeriodTable[i.toNat % 16]'(by rw [noisePeriodTable_size]; exact Nat.mod_lt _ (by decide)))
    / 2 - 1

/-- One LFSR clock. `mode = true`: feedback from bit 6 (short, 93-step loops); else bit 1. -/
@[inline] def lfsrStep (mode : Bool) (x : UInt16) : UInt16 :=
  let fb := (x ^^^ (x >>> (if mode then 6 else 1))) &&& 1
  (x >>> 1) ||| (fb <<< 14)

/-- The noise channel. -/
structure Noise where
  timer : UInt16 := 0
  reload : UInt16 := noiseReload 0
  mode : Bool := false
  lfsr : UInt16 := 1
  len : Length := {}
  env : Envelope := {}
  enabled : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Noise

/-- Register write; `r` is the register index (mod 4). -/
@[inline] def write (n : Noise) (r : UInt8) (v : UInt8) : Noise :=
  match r &&& 3 with
  | 0 => { n with len := { n.len with halt := v &&& 0x20 != 0 }, env := n.env.write v }
  | 1 => n
  | 2 => { n with mode := v &&& 0x80 != 0, reload := noiseReload (v &&& 0x0F) }
  | _ => { n with len := n.len.load n.enabled v, env := { n.env with start := true } }

/-- Timer step (once per APU cycle). -/
@[inline] def tick (n : Noise) : Noise :=
  let z := n.timer == 0
  { n with timer := if z then n.reload else n.timer - 1,
           lfsr := if z then lfsrStep n.mode n.lfsr else n.lfsr }

/-- Quarter-frame clock: envelope. -/
@[inline] def quarterFrame (n : Noise) : Noise := { n with env := n.env.quarterFrame }

/-- Half-frame clock: length counter. -/
@[inline] def halfFrame (n : Noise) : Noise := { n with len := n.len.halfFrame }

/-- `$4015` enable bit. -/
@[inline] def setEnabled (n : Noise) (b : Bool) : Noise :=
  { n with enabled := b, len := n.len.setEnabled b }

/-- `$4015` status bit. -/
@[inline] def lengthNonzero (n : Noise) : Bool := n.len.nonzero

/-- Channel output, 0..15. -/
@[inline] def output (n : Noise) : UInt8 :=
  if n.lfsr &&& 1 != 0 || n.len.counter == 0 then 0 else n.env.output

end Noise

end Nes.Apu
