import Nes.Cart.Mirroring

/-!
# `Nes.Bus.Map` — CPU and PPU address decode

Address decode is a pure function from an address to a `Target`. Mirroring is a *theorem about
this function* (`Nes.Bus.Proofs.Mirroring`), not a set of masks scattered through the bus.

## Spec

**CPU space** (`decode : UInt16 → Target`):

| range           | target                     | index                         |
|-----------------|----------------------------|-------------------------------|
| `$0000–$1FFF`   | `ram i`                    | `i = a mod $800` (2 KiB, ×4)  |
| `$2000–$3FFF`   | `ppuReg r`                 | `r = a mod 8` (×1024)         |
| `$4000–$4017`   | `apuIo r`                  | `r = a − $4000`               |
| `$4018–$FFFF`   | `cart a`                   | the full address              |

`$4018–$401F` are the 2A03's CPU test registers, disabled on retail consoles: the CPU itself
does not drive the data bus there. The cartridge edge sees every address, so we route them to
the cartridge (`cart`); a mapper that does not decode them returns open bus — exactly the
hardware behaviour, and it keeps `Target` at four constructors.

**Fast path.** `decode` allocates a `Target` (a constructor with a field is a heap object
unless inlined away), so the system bus dispatches on the `@[inline]` scalar helpers instead:
the predicates `isRam`/`isPpuReg`/`isApuIo`/`isCart` and the raw `UInt16` offsets
`ramOffset`/`ppuRegOffset`/`apuIoOffset` (`Fin`-typed views: `ramIndex`, `ppuRegIndex`).
`decode` is *defined* from those helpers in the same `if` order the bus uses, so the
agreement lemmas in the proofs file are definitional.

**PPU space** (`ppuDecode : UInt16 → PpuTarget`), on the 14-bit PPU address `a mod $4000`:

| range           | target                                                         |
|-----------------|----------------------------------------------------------------|
| `$0000–$1FFF`   | `chr a` — pattern tables, to the cartridge                     |
| `$2000–$3EFF`   | `nametable a'` — `$3000–$3EFF` folded onto `$2000–$2EFF`       |
| `$3F00–$3FFF`   | `palette i` — `i = a mod 32`, with `$10/$14/$18/$1C ↦ $00/$04/$08/$0C` |

**Nametable mirroring.** A nametable address `a` splits into the logical table
`ntTable a = (a / $400) mod 4` and the in-table offset `ntOffset a = a mod $400`.
`ciramIndex m a : Fin 2048` is the CIRAM cell the four non-four-screen modes select:
horizontal → page `table / 2`, vertical → page `table mod 2`, singleLow → page 0,
singleHigh → page 1 (`index = page·$400 + offset`). `ntCanonical m a` is the address of the
*lowest* logical table that shares `a`'s CIRAM page; it is idempotent and `ciramIndex`
factors through it.

`fourScreen`: CIRAM holds only 2 KiB; four-screen boards supply 2 KiB of extra cartridge VRAM,
so the bus must route four-screen nametable accesses to the cartridge using `fourScreenIndex
a : Fin 4096` (`a mod $1000`). `ciramIndex .fourScreen` is total but **not meaningful**
(it returns the vertical-mirroring cell); the CIRAM theorems exclude it.
-/

namespace Nes.Bus

/-! ### Mask helpers -/

/-- `(a &&& m).toNat < n` whenever `m.toNat < n`. -/
theorem and_toNat_lt (a m : UInt16) {n : Nat} (h : m.toNat < n) : (a &&& m).toNat < n := by
  rw [UInt16.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right h

/-! ### CPU address space -/

/-- What a CPU address selects. -/
inductive Target where
  /-- Internal 2 KiB work RAM, index into it. -/
  | ram (i : Fin 2048)
  /-- PPU register `$2000 + r`. -/
  | ppuReg (r : Fin 8)
  /-- APU / I/O register `$4000 + r` (`$4000–$4017`). -/
  | apuIo (r : Fin 24)
  /-- Cartridge space (`$4018–$FFFF`), full address. -/
  | cart (a : UInt16)
  deriving DecidableEq, Repr

/-- `$0000–$1FFF`. -/
@[inline] def isRam (a : UInt16) : Bool := a < 0x2000
/-- `$2000–$3FFF`. -/
@[inline] def isPpuReg (a : UInt16) : Bool := 0x2000 ≤ a && a < 0x4000
/-- `$4000–$4017`. -/
@[inline] def isApuIo (a : UInt16) : Bool := 0x4000 ≤ a && a < 0x4018
/-- `$4018–$FFFF`. -/
@[inline] def isCart (a : UInt16) : Bool := 0x4018 ≤ a

/-- RAM cell of a RAM-range address (raw). -/
@[inline] def ramOffset (a : UInt16) : UInt16 := a &&& 0x7FF
/-- PPU register number of a PPU-register-range address (raw). -/
@[inline] def ppuRegOffset (a : UInt16) : UInt16 := a &&& 0x7
/-- APU/IO register number of an APU/IO-range address (raw). -/
@[inline] def apuIoOffset (a : UInt16) : UInt16 := a - 0x4000

/-- `ramOffset` as a `Fin 2048`. -/
@[inline] def ramIndex (a : UInt16) : Fin 2048 :=
  ⟨(ramOffset a).toNat, and_toNat_lt a 0x7FF (by decide)⟩
/-- `ppuRegOffset` as a `Fin 8`. -/
@[inline] def ppuRegIndex (a : UInt16) : Fin 8 :=
  ⟨(ppuRegOffset a).toNat, and_toNat_lt a 0x7 (by decide)⟩

/-- The CPU address decoder. Defined in the bus's dispatch order from the fast helpers. -/
@[inline] def decode (a : UInt16) : Target :=
  if a < 0x2000 then .ram (ramIndex a)
  else if h2 : a < 0x4000 then .ppuReg (ppuRegIndex a)
  else if h : a < 0x4018 then
    .apuIo ⟨(apuIoOffset a).toNat, by
      simp only [apuIoOffset]
      rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; rw [UInt16.lt_iff_toNat_lt] at h2; omega)]
      rw [UInt16.lt_iff_toNat_lt] at h h2; simp at h h2 ⊢; omega⟩
  else .cart a

/-! ### PPU address space -/

/-- What a PPU address selects. -/
inductive PpuTarget where
  /-- Pattern tables `$0000–$1FFF` (cartridge CHR). -/
  | chr (a : UInt16)
  /-- Nametables, canonical address in `$2000–$2EFF`... `$2FFF`; the mirroring maps it. -/
  | nametable (a : UInt16)
  /-- Palette RAM cell (after the `$3F1x` alias). -/
  | palette (i : Fin 32)
  deriving DecidableEq, Repr

/-- Palette RAM cell of a palette-range address: `a mod 32`, with the sprite-backdrop
entries `$10/$14/$18/$1C` aliased to `$00/$04/$08/$0C`. -/
@[inline] def paletteIndex (a : UInt16) : Fin 32 :=
  let i := a &&& 0x1F
  if h : i &&& 0x3 == 0 && 0x10 ≤ i then
    ⟨(i - 0x10).toNat, by
      have : i.toNat < 32 := and_toNat_lt a 0x1F (by decide)
      have h' : (0x10 : UInt16) ≤ i := by simp at h; exact h.2
      rw [UInt16.toNat_sub_of_le _ _ h']; omega⟩
  else ⟨i.toNat, and_toNat_lt a 0x1F (by decide)⟩

/-- The PPU address decoder (14-bit address bus: `a mod $4000`). -/
@[inline] def ppuDecode (a : UInt16) : PpuTarget :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then .chr a
  else if a < 0x3F00 then .nametable (if 0x3000 ≤ a then a - 0x1000 else a)
  else .palette (paletteIndex a)

/-! ### Nametable mirroring -/

/-- Offset inside a 1 KiB nametable (`a mod $400`). -/
@[inline] def ntOffset (a : UInt16) : UInt16 := a &&& 0x3FF
/-- Logical nametable number 0–3 (`(a / $400) mod 4`). -/
@[inline] def ntTable (a : UInt16) : UInt16 := (a >>> 10) &&& 0x3

/-- The lowest logical table sharing table `t`'s CIRAM page under mirroring `m`. -/
@[inline] def canonTable : Mirroring → UInt16 → UInt16
  | .horizontal, t => t &&& 0x2
  | .vertical, t => t &&& 0x1
  | .singleLow, _ => 0
  | .singleHigh, _ => 0
  | .fourScreen, t => t

/-- Canonical nametable address: same offset, lowest logical table on the same CIRAM page.
Always lands in `$2000–$2FFF`. -/
@[inline] def ntCanonical (m : Mirroring) (a : UInt16) : UInt16 :=
  0x2000 + canonTable m (ntTable a) * 0x400 + ntOffset a

/-- CIRAM page (0 or 1) that table `t` selects under `m` (`fourScreen`: not meaningful). -/
@[inline] def ciramPage : Mirroring → UInt16 → UInt16
  | .horizontal, t => t >>> 1
  | .vertical, t => t &&& 0x1
  | .singleLow, _ => 0
  | .singleHigh, _ => 1
  | .fourScreen, t => t &&& 0x1

/-- Raw CIRAM cell (`< $800`) for nametable address `a` under `m`. -/
@[inline] def ciramOffset (m : Mirroring) (a : UInt16) : UInt16 :=
  ciramPage m (ntTable a) * 0x400 + ntOffset a

theorem ciramOffset_lt (m : Mirroring) (a : UInt16) : (ciramOffset m a).toNat < 2048 := by
  have ho : (ntOffset a).toNat < 1024 := and_toNat_lt a 0x3FF (by decide)
  have ht : (ntTable a).toNat < 4 := and_toNat_lt _ 0x3 (by decide)
  have hp : (ciramPage m (ntTable a)).toNat < 2 := by
    cases m <;> simp only [ciramPage]
    · rw [UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
    all_goals first | exact and_toNat_lt _ 0x1 (by decide) | decide
  simp only [ciramOffset, UInt16.toNat_add, UInt16.toNat_mul]
  simp; omega

/-- CIRAM cell for nametable address `a` under `m` (`fourScreen`: not meaningful — use
`fourScreenIndex` into cartridge VRAM). -/
@[inline] def ciramIndex (m : Mirroring) (a : UInt16) : Fin 2048 :=
  ⟨(ciramOffset m a).toNat, ciramOffset_lt m a⟩

/-- Four-screen nametable cell (4 KiB: CIRAM + cartridge VRAM), `a mod $1000`. -/
@[inline] def fourScreenIndex (a : UInt16) : Fin 4096 :=
  ⟨(a &&& 0xFFF).toNat, and_toNat_lt a 0xFFF (by decide)⟩

end Nes.Bus
