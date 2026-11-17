/-!
# `Nes.Apu.Mixer` — 2A03 output mixer

PLAN §5.4 / §6.5 (T-APU-2). Two representations, deliberately separate:

**Spec (exact `Rat`).** NESdev "APU Mixer", nonlinear formulas, with the decimal constants as exact
rationals and rewritten into a division-friendly closed form (one fraction of naturals each):

* `pulse_out = 95.88 / (8128 / (p1 + p2) + 100)` (0 when `p1 + p2 = 0`)
  `= 95.88·p / (8128 + 100·p)` with `p = p1 + p2` → `pulseOut p = 9588·p / (812800 + 10000·p)`.
* `tnd_out = 159.79 / (1 / (t/8227 + n/12241 + d/22638) + 100)` (0 when all are 0)
  `= 159.79·x / (1 + 100·x)`, `x = N / D`, `D = 8227·12241·22638`,
  `N = 12241·22638·t + 8227·22638·n + 8227·12241·d` → `tndOut t n d = 15979·N / (100·D + 10000·N)`.
* `mix p1 p2 t n d = pulseOut (p1 + p2) + tndOut t n d`; ranges `p1 p2 t n ∈ [0,15]`, `d ∈ [0,127]`.
  The exact maximum `mix 15 15 15 15 127 ≈ 0.99999935` is `< 1`.

**Runtime (hot path, one sample per CPU cycle: no `Rat`, no `Nat` arithmetic, no allocation).**
Two top-level `UInt16` lookup tables, fixed point scaled by 65535 (round half up):
* `pulseTable[i] = round(65535 · pulseOut i)`, `i = p1 + p2 ∈ [0,30]` (31 entries; exact formula,
  rounding error ≤ ½ LSB — `Nes.Apu.Proofs.T_APU_2_pulseTable`).
* `tndTable[k] = round(65535 · 163.67 / (24329 / k + 100))`, `k = 3t + 2n + d ∈ [0,202]`
  (203 entries). **This is NESdev's documented lookup *approximation*, not the exact formula**: it
  collapses three inputs into one index. Proved error vs the exact `tndOut`, for all 32768 in-range
  inputs, including table rounding: `≤ 0.013` of full scale (≈ 850 LSB; worst case `t = n = 0`,
  `d = 118`) — `Nes.Apu.Proofs.T_APU_2_tndTable_err`.
* `mixSample = min 65535 (pulseTable[p1+p2] + tndTable[3t+2n+d])`: the approximate tnd table
  overshoots the exact maximum slightly (`16940 + 48658 = 65598`), so the sum saturates.
  Inputs are masked to their hardware widths (4 / 4 / 4 / 4 / 7 bits), so lookups are total.

The tables were generated offline from the formulas above (exact rational arithmetic); the proof
file re-checks every entry against the spec by kernel evaluation.
-/

namespace Nes.Apu

/-- `a / b` in `Rat` for naturals (the shape every spec quantity is put in). -/
def frac (a b : Nat) : Rat := (a : Rat) / (b : Rat)

/-! ### Spec -/

/-- Pulse group output for `p = p1 + p2` (NESdev formula, closed form). -/
def pulseOut (p : Nat) : Rat := frac (9588 * p) (812800 + 10000 * p)

/-- `D = 8227 · 12241 · 22638`, common denominator of the tnd weights. -/
def tndDen : Nat := 8227 * 12241 * 22638

/-- `N` with `t/8227 + n/12241 + d/22638 = N / tndDen`. -/
def tndNum (t n d : Nat) : Nat := 12241 * 22638 * t + 8227 * 22638 * n + 8227 * 12241 * d

/-- Triangle/noise/DMC group output (NESdev formula, closed form). -/
def tndOut (t n d : Nat) : Rat := frac (15979 * tndNum t n d) (100 * tndDen + 10000 * tndNum t n d)

/-- Mixer output in `[0, 1]` (T-APU-2). -/
def mix (p1 p2 t n d : Nat) : Rat := pulseOut (p1 + p2) + tndOut t n d

/-- The NESdev tnd lookup approximation `163.67 / (24329 / k + 100)` (0 at `k = 0`), closed form. -/
def tndApprox (k : Nat) : Rat := frac (16367 * k) (2432900 + 10000 * k)

/-! ### Runtime tables -/

/-- `round(65535 · pulseOut i)`, `i ∈ [0,30]`. -/
def pulseLevels : List Nat := [
    0, 764, 1509, 2237, 2947, 3641, 4320, 4982, 5630, 6264, 6884, 7490,
    8083, 8664, 9233, 9789, 10335, 10869, 11392, 11905, 12408, 12901, 13385, 13859,
    14324, 14781, 15228, 15668, 16100, 16524, 16940]

/-- `round(65535 · tndApprox k)`, `k ∈ [0,202]`. -/
def tndLevels : List Nat := [
    0, 439, 875, 1307, 1735, 2160, 2582, 3000, 3415, 3826, 4235, 4640,
    5042, 5441, 5836, 6229, 6619, 7005, 7389, 7770, 8148, 8523, 8895, 9264,
    9631, 9995, 10356, 10715, 11070, 11424, 11774, 12123, 12468, 12811, 13152, 13490,
    13826, 14159, 14490, 14819, 15145, 15469, 15791, 16110, 16428, 16743, 17056, 17366,
    17675, 17981, 18286, 18588, 18888, 19187, 19483, 19777, 20070, 20360, 20648, 20935,
    21220, 21502, 21783, 22062, 22340, 22615, 22889, 23161, 23431, 23699, 23966, 24231,
    24494, 24756, 25016, 25274, 25531, 25786, 26040, 26292, 26542, 26791, 27039, 27285,
    27529, 27772, 28013, 28253, 28492, 28729, 28964, 29198, 29431, 29663, 29893, 30122,
    30349, 30575, 30800, 31023, 31245, 31466, 31685, 31904, 32121, 32336, 32551, 32764,
    32976, 33187, 33397, 33605, 33813, 34019, 34224, 34428, 34630, 34832, 35032, 35232,
    35430, 35627, 35823, 36018, 36212, 36405, 36597, 36788, 36978, 37166, 37354, 37541,
    37727, 37912, 38095, 38278, 38460, 38641, 38821, 39000, 39178, 39355, 39531, 39707,
    39881, 40055, 40227, 40399, 40570, 40740, 40909, 41077, 41245, 41411, 41577, 41742,
    41906, 42069, 42232, 42394, 42554, 42714, 42874, 43032, 43190, 43347, 43503, 43658,
    43813, 43967, 44120, 44272, 44424, 44575, 44725, 44875, 45024, 45172, 45319, 45466,
    45612, 45757, 45902, 46046, 46189, 46331, 46473, 46615, 46755, 46895, 47035, 47173,
    47311, 47449, 47585, 47722, 47857, 47992, 48126, 48260, 48393, 48526, 48658]

/-- Pulse lookup table (31 × `UInt16`). -/
def pulseTable : Array UInt16 := (pulseLevels.map Nat.toUInt16).toArray

/-- Tnd lookup table (203 × `UInt16`). -/
def tndTable : Array UInt16 := (tndLevels.map Nat.toUInt16).toArray

/-- Total table read (0 out of range; never happens for masked indices). -/
@[inline] def tableAt (a : Array UInt16) (i : USize) : UInt16 :=
  if h : i.toNat < a.size then a.uget i h else 0

/-- One mixer sample, fixed point `[0, 65535]` ≈ `65535 · mix`. Masks inputs to hardware widths. -/
@[inline] def mixSample (p1 p2 t n d : UInt8) : UInt16 :=
  let i := ((p1 &&& 15) + (p2 &&& 15)).toUSize
  let k := (3 * (t &&& 15) + 2 * (n &&& 15) + (d &&& 127)).toUSize
  let s := (tableAt pulseTable i).toUInt32 + (tableAt tndTable k).toUInt32
  if s > 65535 then 65535 else s.toUInt16

end Nes.Apu
