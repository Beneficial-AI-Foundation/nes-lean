/-!
# `Nes.Apu.Units` — length counter, envelope, sweep

The small building blocks shared by the APU tone channels. Each is a plain structure of
`UInt8`/`Bool` scalars with `@[inline]` clock functions, so a channel's hot path stays
allocation free.

## Spec

* `lengthTable` (NESdev "APU Length Counter"): the 32-entry load table, indexed by bits 7–3 of
  the channel's 4th register. `lengthLoad i = lengthTable[i mod 32]`.
* `Length`: `counter` and `halt`.
  * `load l en v`: if the channel is enabled (`$4015`), `counter := lengthLoad (v >>> 3)`;
    otherwise the write is ignored.
  * `halfFrame`: if `halt` is clear and `counter ≠ 0`, decrement; else unchanged.
  * `setEnabled l false` clears `counter`; `setEnabled l true` changes nothing.
  * `nonzero` (the `$4015` status bit): `counter ≠ 0`.
* `Envelope` (NESdev "APU Envelope"): `start` flag, `loop`, `constVol`, `volume` (V, also
  the divider period), `divider`, `decay`.
  * `write e v`: `loop := v.5`, `constVol := v.4`, `volume := v & 15`.
  * `quarterFrame`: if `start`: clear it, `decay := 15`, `divider := V`. Otherwise, when the
    divider is 0 it reloads with V and clocks the decay level (`decay - 1` if nonzero, else
    15 if `loop`, else stays 0); when nonzero the divider is decremented.
  * `output`: `V` if `constVol`, else `decay`.
* `Sweep` (NESdev "APU Sweep"): `enabled`, `divPeriod` (P), `negate`, `shift`, `reload`,
  `divider`.
  * `write s v`: `enabled := v.7`, `P := (v >>> 4) & 7`, `negate := v.3`, `shift := v & 7`,
    `reload := true`.
  * `target s ones p`: `change := p >>> shift`; not negating: `p + change`; negating:
    `p - change - 1` (pulse 1, `ones = true`, ones' complement) or `p - change` (pulse 2,
    two's complement), clamped at 0 (only reachable for pulse 1 with `shift = 0`; the
    resulting target is then irrelevant because the period is never updated with `shift = 0`
    and the clamp keeps `target ≤ p`, so it cannot mute).
  * `muted s ones p`: `p < 8 ∨ target > $7FF` — computed continuously, even when the sweep
    is disabled.
  * `newPeriod s ones p` (the half-frame period update): if `divider = 0 ∧ enabled ∧
    shift ≠ 0 ∧ ¬muted` then `target` else `p`.
  * `clockDivider` (the half-frame divider update): if `divider = 0 ∨ reload` then
    `divider := P, reload := false`, else `divider - 1`.
-/

namespace Nes.Apu

/-- NESdev "APU Length Counter" load table, indexed by bits 7–3 of `$4003/$4007/$400B/$400F`. -/
def lengthTable : Array UInt8 :=
  #[10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30]

theorem lengthTable_size : lengthTable.size = 32 := rfl

/-- Length-counter load value for table index `i` (taken mod 32). -/
@[inline] def lengthLoad (i : UInt8) : UInt8 :=
  lengthTable[i.toNat % 32]'(by rw [lengthTable_size]; exact Nat.mod_lt _ (by decide))

/-! ## Length counter -/

/-- Length counter (NESdev "APU Length Counter"). -/
structure Length where
  counter : UInt8 := 0
  halt : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Length

/-- 4th-register write: reload from the table (bits 7–3 of `v`) if the channel is enabled. -/
@[inline] def load (l : Length) (enabled : Bool) (v : UInt8) : Length :=
  { l with counter := if enabled then lengthLoad (v >>> 3) else l.counter }

/-- Half-frame clock: decrement unless halted or already 0. -/
@[inline] def halfFrame (l : Length) : Length :=
  { l with counter := if l.halt || l.counter == 0 then l.counter else l.counter - 1 }

/-- `$4015` enable bit: clearing it forces the counter to 0. -/
@[inline] def setEnabled (l : Length) (en : Bool) : Length :=
  { l with counter := if en then l.counter else 0 }

/-- `$4015` status bit: the counter is nonzero. -/
@[inline] def nonzero (l : Length) : Bool := l.counter != 0

end Length

/-! ## Envelope -/

/-- Envelope generator (NESdev "APU Envelope"). -/
structure Envelope where
  start : Bool := false
  loop : Bool := false
  constVol : Bool := false
  /-- V: constant volume, and the divider's reload value. -/
  volume : UInt8 := 0
  divider : UInt8 := 0
  decay : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

namespace Envelope

/-- 1st-register write (`$4000/$4004/$400C`): loop (bit 5), constant volume (bit 4), V. -/
@[inline] def write (e : Envelope) (v : UInt8) : Envelope :=
  { e with loop := v &&& 0x20 != 0, constVol := v &&& 0x10 != 0, volume := v &&& 0x0F }

/-- Decay-level clock: count down to 0, then wrap to 15 if looping, else hold 0. -/
@[inline] def nextDecay (decay : UInt8) (loop : Bool) : UInt8 :=
  if decay != 0 then decay - 1 else if loop then 15 else 0

/-- Quarter-frame clock. -/
@[inline] def quarterFrame (e : Envelope) : Envelope :=
  let z := e.divider == 0
  { e with start := false,
           divider := if e.start || z then e.volume else e.divider - 1,
           decay := if e.start then 15 else if z then nextDecay e.decay e.loop else e.decay }

/-- Envelope volume (0..15). -/
@[inline] def output (e : Envelope) : UInt8 := if e.constVol then e.volume else e.decay

end Envelope

/-! ## Sweep -/

/-- Sweep unit (NESdev "APU Sweep"). -/
structure Sweep where
  enabled : Bool := false
  /-- P: divider reload value. -/
  divPeriod : UInt8 := 0
  negate : Bool := false
  shift : UInt8 := 0
  reload : Bool := false
  divider : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

namespace Sweep

/-- 2nd-register write (`$4001/$4005`): `EPPP NSSS`, sets the reload flag. -/
@[inline] def write (s : Sweep) (v : UInt8) : Sweep :=
  { s with enabled := v &&& 0x80 != 0, divPeriod := (v >>> 4) &&& 7, negate := v &&& 0x08 != 0,
           shift := v &&& 7, reload := true }

/-- Target period. `ones = true` for pulse 1 (ones' complement negate: `p - change - 1`),
`false` for pulse 2 (two's complement: `p - change`). Negative results clamp to 0. -/
@[inline] def target (s : Sweep) (ones : Bool) (p : UInt16) : UInt16 :=
  let change := p >>> s.shift.toUInt16
  if s.negate then
    let sub := change + (if ones then 1 else 0)
    if p < sub then 0 else p - sub
  else p + change

/-- Muting (independent of `enabled`): period below 8 or target above `$7FF`. -/
@[inline] def muted (s : Sweep) (ones : Bool) (p : UInt16) : Bool :=
  p < 8 || s.target ones p > 0x7FF

/-- Half-frame period update. -/
@[inline] def newPeriod (s : Sweep) (ones : Bool) (p : UInt16) : UInt16 :=
  if s.divider == 0 && s.enabled && s.shift != 0 && !s.muted ones p then s.target ones p else p

/-- Half-frame divider update. -/
@[inline] def clockDivider (s : Sweep) : Sweep :=
  let r := s.divider == 0 || s.reload
  { s with divider := if r then s.divPeriod else s.divider - 1, reload := false }

end Sweep

end Nes.Apu
