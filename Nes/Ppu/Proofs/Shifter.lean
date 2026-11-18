import Nes.Ppu.Step
import Nes.Ppu.Proofs.Loopy

/-!
# `Nes.Ppu.Proofs.Shifter` — background shifter invariant (T-PPU-6 building block)

## Spec

Throughout, `rd : UInt16 → UInt8` is a fixed (static) PPU-bus reader, `c` the `ctrl` byte, and
rendering is enabled (`mask & $18 ≠ 0`). "One dot" is `fun s => bgDot rd s.advance`, or any `f`
with `BgEq (bgDot rd s.advance) (f s)` whenever rendering is on — in particular the full PPU dot
`Nes.Ppu.dot rd pr` (`bgEq_ppuDot`). `run f n` is `f` applied `n` times.

* `tileBits rd c v` — the tile addressed by loopy `v`: NT byte `rd (ntAddr v)`; pattern bytes
  `rd (ptAddrOf c nt v false/true)` (table `c.4`, tile·16, `+8` for the high plane, fine Y of
  `v`); 2-bit palette `atSelect v (rd (atAddr v))`. `tilePx T col` is its 4-bit pixel at column
  `col` (bit `7 - col`; 0 when the pattern bits are 0, else `attr·4 + pattern`).
* `Holds s A B j` — the 16-bit shifters are `(A ‖ B) <<< j`: `bgPatLo = (A.lo·256 + B.lo) <<< j`,
  likewise `bgPatHi`, and the attribute shifters with `$FF`/`$00` per palette bit.
* **Per-phase invariant** `PInv rd c u s` (dots 1–256 of a visible line, after `bgDot`; phase
  `ph s = (dot - 1) & 7`): `Holds s (tile u) (tile (incX u)) (ph s)` — the drawn tile `u` in the
  high byte, the next in the low byte, shifted by the phase — and the latches hold the fetches
  so far of tile `incX (incX u)` (NT always, AT from phase 2, PT low from 4, PT high from 6),
  with `v = incX (incX u)` (one more `incX` after phase 7, except at dot 256). So `v` points
  two tiles ahead of the tile being drawn ("pattern bits of the tile at v + 2"). At the dot of
  each reload (phase 0, dots 9, 17, …) the shift count is 0.
* `PInv.step`: one dot from `PInv u` at dot < 256 gives `PInv u'` with `u' = incX u` after phase
  7 (the reload dot) and `u' = u` otherwise. `Start.step`: dot 0 → dot 1.
* `pixel_holds`: under `Holds s A B j` (`j < 8`), `bgPixelRaw s` is `tilePx A (j + fx)` if
  `j + fx < 8`, else `tilePx B (j + fx - 8)`, where `fx = x & 7`.
* **Scanline** (`bg_scanline`, `_bgRun`, `_ppuDot`): from `Start rd c u0` at dot 0 of a visible
  line (shifters `= tile u0 ‖ tile (incX u0)` unshifted, `v = incX (incX u0)`), after `n ∈ 1..256`
  dots, `bgPixelRaw = tilePx (tileBits rd c (incX^[P / 8] u0)) (P % 8)` with
  `P = n - 1 + (x & 7)`: screen column `n - 1` shows pixel `P` of the line counted from the
  tile `u0` (`incX^[k]` is `Nat.repeat incX k`).
* **Prefetch** (`prefetch`): from dot 320 of an active line (0–239 or 261) with `v = V`,
  17 dots reach dot 337 with `Ready rd c V`: `Holds (tile V) (tile (incX V)) 0` and
  `v = incX (incX V)` (reloads at 329 and 337). `Ready.idle`: the idle dots 338–340 and 0 keep
  `Ready`; `Ready.start`: `Ready` at dot 0 of a visible line is `Start`.

Method: per-field lemmas (`fetch_*`, `holds_*`, `low_*`) unfold `Bg.shifters`/`Bg.fetchV` once,
name the bus reads as opaque bytes, and close by `bv_decide`; the invariants are then pure
rewriting, and the iteration is an induction on the dot count.
-/

namespace Nes.Ppu.Proofs
open Nes.Ppu Nes.Ppu.Bg Nes.Ppu.Loopy

/-- Pattern bytes and 2-bit palette of one background tile. -/
structure Tile where
  lo : UInt8
  hi : UInt8
  attr : UInt8

/-- Pattern address of plane `hi` of tile `tile` at fine Y of `v` (ctrl bit 4 = table). -/
@[inline] def ptAddrOf (ctrl tile : UInt8) (v : UInt16) (hi : Bool) : UInt16 :=
  let tbl : UInt16 := if ctrl &&& 0x10 != 0 then 0x1000 else 0
  tbl ||| (tile.toUInt16 <<< 4) ||| (if hi then (0x08 : UInt16) else 0) ||| ((v >>> 12) &&& 0x07)

/-- The tile addressed by loopy `v` (NT byte at `ntAddr v`, pattern planes at fine Y of `v`,
palette quadrant of `v`), read through `rd` with background table `ctrl.4`. -/
def tileBits (rd : UInt16 → UInt8) (ctrl : UInt8) (v : UInt16) : Tile :=
  let nt := rd (ntAddr v)
  { lo := rd (ptAddrOf ctrl nt v false), hi := rd (ptAddrOf ctrl nt v true),
    attr := atSelect v (rd (atAddr v)) }

theorem ptAddr_eq (s : State) (hi : Bool) : ptAddr s hi = ptAddrOf s.ctrl s.bgNextTile s.v hi := rfl

/-- 16-bit shifter word: `a` in the high byte, `b` in the low byte. -/
def word (a b : UInt8) : UInt16 := (a.toUInt16 <<< 8) ||| b.toUInt16
/-- Attribute-shifter byte for palette bit `m` of `a`, as `bgReload` fills it. -/
def attrFill (a m : UInt8) : UInt16 := if a &&& m != 0 then 0xFF else 0
def attrWord (a b m : UInt8) : UInt16 := (attrFill a m <<< 8) ||| attrFill b m

/-- The four shifters hold tiles `A` (high byte) and `B` (low byte), shifted left by `j`. -/
structure Holds (s : State) (A B : Tile) (j : UInt16) : Prop where
  lo : s.bgPatLo = word A.lo B.lo <<< j
  hi : s.bgPatHi = word A.hi B.hi <<< j
  alo : s.bgAttrLo = attrWord A.attr B.attr 1 <<< j
  ahi : s.bgAttrHi = attrWord A.attr B.attr 2 <<< j

theorem act_of_lt {sl : UInt16} (h : sl < 240) : activeLine sl = true := by simp [activeLine, h]

theorem bgDot_active (rd) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true) :
    bgDot rd s =
    { s with bgPatLo := (Bg.shifters s).toUInt16, bgPatHi := (Bg.shifters s >>> 16).toUInt16,
             bgAttrLo := (Bg.shifters s >>> 32).toUInt16, bgAttrHi := (Bg.shifters s >>> 48).toUInt16,
             bgNextTile := (Bg.fetchV rd s).toUInt8, bgNextAttr := (Bg.fetchV rd s >>> 8).toUInt8,
             bgNextLo := (Bg.fetchV rd s >>> 16).toUInt8, bgNextHi := (Bg.fetchV rd s >>> 24).toUInt8,
             v := (Bg.fetchV rd s >>> 32).toUInt16 } := by
  simp [bgDot, hr, hl]

theorem holds_mid (rd) (s : State) (A B : Tile) (j : UInt16) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true)
    (hd : (2 ≤ s.dot ∧ s.dot ≤ 256) ∨ (322 ≤ s.dot ∧ s.dot ≤ 337)) (hp : (s.dot - 1) &&& 7 ≠ 0)
    (hj : j < 7) (h : Holds s A B j) : Holds (bgDot rd s) A B (j + 1) := by
  obtain ⟨h1', h2', h3', h4'⟩ := h
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, word, attrWord, attrFill] at * <;> bv_decide

theorem holds_reload (rd) (s : State) (A B C : Tile) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true)
    (hd : (9 ≤ s.dot ∧ s.dot ≤ 257) ∨ s.dot = 329 ∨ s.dot = 337) (hp : (s.dot - 1) &&& 7 = 0)
    (hlo : s.bgNextLo = C.lo) (hhi : s.bgNextHi = C.hi) (ha : s.bgNextAttr = C.attr)
    (h : Holds s A B 7) : Holds (bgDot rd s) B C 0 := by
  obtain ⟨h1', h2', h3', h4'⟩ := h
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, word, attrWord, attrFill, hlo, hhi, ha] at * <;> bv_decide

theorem holds_one (rd) (s : State) (A B : Tile) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true) (h1 : s.dot = 1 ∨ s.dot = 321) (h : Holds s A B 0) : Holds (bgDot rd s) A B 0 := by
  obtain ⟨h1', h2', h3', h4'⟩ := h
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, word, attrWord, attrFill] at * <;> bv_decide

theorem ptAddr_bool (s : State) (b : Bool) :
    ptAddr s b = if b then ptAddr s true else ptAddr s false := by cases b <;> rfl

/-- Unfold `fetchV` on a fetch dot, name the four possible reads, bit-blast. -/
local macro "fetch_tac" rd:term : tactic => `(tactic| (
  simp only [Bg.fetchV, ppuAddrBg]
  rw [ptAddr_bool]
  simp only [apply_ite $rd]
  generalize $rd (ntAddr _) = rN
  generalize $rd (atAddr _) = rA
  generalize $rd (ptAddr _ true) = rH
  generalize $rd (ptAddr _ false) = rL
  simp only [fetchDot, atSelect, incX, incY, activeLine, Bool.decide_eq_true] at *
  bv_decide))

section fetch
variable (rd : UInt16 → UInt8) (s : State) (hr : s.rendering = true)
  (hl : activeLine s.scanline = true) (hd : (1 ≤ s.dot ∧ s.dot ≤ 256) ∨ (321 ≤ s.dot ∧ s.dot ≤ 336))
include hr hl hd

theorem fetch_tile : (bgDot rd s).bgNextTile =
    if (s.dot - 1) &&& 7 = 0 then rd (ntAddr s.v) else s.bgNextTile := by
  rw [bgDot_active rd s hr hl]; dsimp only
  split
  · fetch_tac rd
  · fetch_tac rd

theorem fetch_attr : (bgDot rd s).bgNextAttr =
    if (s.dot - 1) &&& 7 = 2 then atSelect s.v (rd (atAddr s.v)) else s.bgNextAttr := by
  rw [bgDot_active rd s hr hl]; dsimp only
  split <;> fetch_tac rd

theorem fetch_lo : (bgDot rd s).bgNextLo =
    if (s.dot - 1) &&& 7 = 4 then rd (ptAddr s false) else s.bgNextLo := by
  rw [bgDot_active rd s hr hl]; dsimp only
  split <;> fetch_tac rd

theorem fetch_hi : (bgDot rd s).bgNextHi =
    if (s.dot - 1) &&& 7 = 6 then rd (ptAddr s true) else s.bgNextHi := by
  rw [bgDot_active rd s hr hl]; dsimp only
  split <;> fetch_tac rd

theorem fetch_v : (bgDot rd s).v =
    if (s.dot - 1) &&& 7 = 7 then (if s.dot = 256 then incY (incX s.v) else incX s.v)
    else s.v := by
  rw [bgDot_active rd s hr hl]; dsimp only
  repeat' split
  all_goals fetch_tac rd

end fetch

theorem advance_vis (s : State) (hl : s.scanline < 240) (hd : s.dot < 340) :
    s.advance = { s with dot := s.dot + 1 } := by
  have h1 : s.scanline ≠ 261 := by bv_decide
  have h2 : s.dot ≠ 340 := by bv_decide
  simp [State.advance, h1, h2]

theorem bgDot_keeps (rd) (s : State) :
    (bgDot rd s).dot = s.dot ∧ (bgDot rd s).scanline = s.scanline ∧ (bgDot rd s).ctrl = s.ctrl ∧
    (bgDot rd s).mask = s.mask ∧ (bgDot rd s).x = s.x := by
  simp only [bgDot]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Phase of the 8-dot fetch cycle of the dot `s` is at: `(dot - 1) mod 8`. -/
abbrev ph (s : State) : UInt16 := (s.dot - 1) &&& 7

/-- Shifter invariant on dot `s.dot ∈ 1..256` of a visible line, after `bgDot`: with `u` the loopy
address of the tile being drawn, the shifters hold tile `u` (high byte) and tile `incX u` (low
byte) shifted left by the phase, the latches hold what the fetches of this cycle (of tile
`incX (incX u)`, the address in `v`) have read so far, and `v` is still that address (one more
`incX` after phase 7, except at dot 256 where `incY` also runs). -/
structure PInv (rd : UInt16 → UInt8) (c : UInt8) (u : UInt16) (s : State) : Prop where
  ren : s.rendering = true
  line : s.scanline < 240
  ctrl : s.ctrl = c
  d1 : 1 ≤ s.dot
  d2 : s.dot ≤ 256
  hold : Holds s (tileBits rd c u) (tileBits rd c (incX u)) (ph s)
  nt : s.bgNextTile = rd (ntAddr (incX (incX u)))
  attr : 2 ≤ ph s → s.bgNextAttr = (tileBits rd c (incX (incX u))).attr
  lo : 4 ≤ ph s → s.bgNextLo = (tileBits rd c (incX (incX u))).lo
  hi : 6 ≤ ph s → s.bgNextHi = (tileBits rd c (incX (incX u))).hi
  v : ph s < 7 → s.v = incX (incX u)
  v7 : ph s = 7 → s.dot ≠ 256 → s.v = incX (incX (incX u))

/-- One PPU dot (`advance`, then `bgDot`) preserves the invariant; the drawn tile moves on by
one coarse-X step after phase 7. -/
theorem PInv.step (rd c u) (s : State) (h : PInv rd c u s) (hd : s.dot < 256) :
    PInv rd c (if ph s = 7 then incX u else u) (bgDot rd s.advance) := by
  have ha := advance_vis s h.line (by bv_decide)
  obtain ⟨k1, k2, k3, k4, k5⟩ := bgDot_keeps rd s.advance
  rw [ha] at k1 k2 k3 k4 k5 ⊢
  dsimp only at k1 k2 k3 k4 k5
  have hr : ({ s with dot := s.dot + 1 } : State).rendering = true := h.ren
  have hl : activeLine ({ s with dot := s.dot + 1 } : State).scanline = true := act_of_lt h.line
  have e1 : 1 ≤ s.dot + 1 := by have := h.d1; bv_decide
  have e2 : s.dot + 1 ≤ 256 := by bv_decide
  have ft := fetch_tile rd _ hr hl (Or.inl ⟨e1, e2⟩)
  have fa := fetch_attr rd _ hr hl (Or.inl ⟨e1, e2⟩)
  have fl := fetch_lo rd _ hr hl (Or.inl ⟨e1, e2⟩)
  have fh := fetch_hi rd _ hr hl (Or.inl ⟨e1, e2⟩)
  have fv := fetch_v rd _ hr hl (Or.inl ⟨e1, e2⟩)
  simp only [ptAddr_eq] at fl fh
  dsimp only at ft fa fl fh fv
  have hold0 : Holds ({ s with dot := s.dot + 1 } : State) _ _ (ph s) :=
    ⟨h.hold.lo, h.hold.hi, h.hold.alo, h.hold.ahi⟩
  have ren : (bgDot rd { s with dot := s.dot + 1 }).rendering = true := by
    simp only [State.rendering, k4]; exact h.ren
  have hd1 := h.d1
  by_cases h7 : ph s = 7
  · simp only [h7, ite_true]
    have hq : ((s.dot + 1) - 1) &&& 7 = 0 := by simp only [ph] at h7; bv_decide
    have hv := h.v7 h7 (by bv_decide)
    have hA := h.attr (by rw [h7]; decide)
    have hL := h.lo (by rw [h7]; decide)
    have hH := h.hi (by rw [h7]; decide)
    refine ⟨ren, (by rw [k2]; exact h.line), (by rw [k3]; exact h.ctrl), (by rw [k1]; exact e1),
      (by rw [k1]; exact e2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ph, k1, hq]
      exact holds_reload rd _ _ _ _ hr hl (Or.inl ⟨by simp only [ph] at h7; bv_decide, by dsimp only; bv_decide⟩) hq hL hH hA
        (h7 ▸ hold0)
    · rw [ft]; simp only [hq, ↓reduceIte]; rw [hv]
    all_goals simp only [ph, k1, hq]
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro _; rw [fv]; simp only [hq]; exact hv
    · intro h; exact absurd h (by decide)
  · simp only [h7, ite_false]
    have hq : ((s.dot + 1) - 1) &&& 7 = ph s + 1 := by simp only [ph] at h7 ⊢; bv_decide
    have hlt : ph s < 7 := by simp only [ph] at h7 ⊢; bv_decide
    have hv := h.v hlt
    refine ⟨ren, (by rw [k2]; exact h.line), (by rw [k3]; exact h.ctrl), (by rw [k1]; exact e1),
      (by rw [k1]; exact e2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ph, k1, hq]
      exact holds_mid rd _ _ _ (ph s) hr hl (Or.inl ⟨by simp only [ph] at hlt; bv_decide, e2⟩)
        (by rw [hq]; simp only [ph] at hlt ⊢; bv_decide) hlt hold0
    · have : ¬ (((s.dot + 1) - 1) &&& 7 = 0) := by rw [hq]; simp only [ph] at hlt ⊢; bv_decide
      rw [ft]; simp only [this, ↓reduceIte]; exact h.nt
    all_goals simp only [ph, k1, hq]
    · intro h2
      rw [fa]; split
      · rw [hv]; rfl
      · exact h.attr (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      rw [fl]; split
      · rw [hv, h.nt, h.ctrl]; rfl
      · exact h.lo (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      rw [fh]; split
      · rw [hv, h.nt, h.ctrl]; rfl
      · exact h.hi (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      have : ¬ (((s.dot + 1) - 1) &&& 7 = 7) := by simp only [ph] at hlt h2 ⊢; bv_decide
      rw [fv]; simp only [this, ↓reduceIte]; exact hv
    · intro h2 h3
      have : ((s.dot + 1) - 1) &&& 7 = 7 := by simp only [ph] at hlt h2 ⊢; bv_decide
      rw [fv]; simp only [this, h3, hv, ↓reduceIte]

/-- State at dot 0 of a visible line (after the dot-337 reload and the idle dots), about to draw
tile `u`: shifters hold tiles `u`, `incX u` unshifted, `v` points two tiles ahead. -/
structure Start (rd : UInt16 → UInt8) (c : UInt8) (u : UInt16) (s : State) : Prop where
  ren : s.rendering = true
  line : s.scanline < 240
  ctrl : s.ctrl = c
  dot : s.dot = 0
  hold : Holds s (tileBits rd c u) (tileBits rd c (incX u)) 0
  v : s.v = incX (incX u)

theorem Start.step (rd c u) (s : State) (h : Start rd c u s) : PInv rd c u (bgDot rd s.advance) := by
  have ha := advance_vis s h.line (by rw [h.dot]; decide)
  obtain ⟨k1, k2, k3, k4, k5⟩ := bgDot_keeps rd s.advance
  rw [ha] at k1 k2 k3 k4 k5 ⊢
  dsimp only at k1 k2 k3 k4 k5
  have hr : ({ s with dot := s.dot + 1 } : State).rendering = true := h.ren
  have hl : activeLine ({ s with dot := s.dot + 1 } : State).scanline = true := act_of_lt h.line
  have e1 : 1 ≤ s.dot + 1 := by rw [h.dot]; decide
  have e2 : s.dot + 1 ≤ 256 := by rw [h.dot]; decide
  have hq : ((s.dot + 1) - 1) &&& 7 = 0 := by rw [h.dot]; decide
  have ft := fetch_tile rd _ hr hl (Or.inl ⟨e1, e2⟩)
  have fv := fetch_v rd _ hr hl (Or.inl ⟨e1, e2⟩)
  dsimp only at ft fv
  have ren : (bgDot rd { s with dot := s.dot + 1 }).rendering = true := by
    simp only [State.rendering, k4]; exact h.ren
  refine ⟨ren, (by rw [k2]; exact h.line), (by rw [k3]; exact h.ctrl), (by rw [k1]; exact e1),
      (by rw [k1]; exact e2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ph, k1, hq]
    exact holds_one rd _ _ _ hr hl (Or.inl (by dsimp only; rw [h.dot]; decide))
      ⟨h.hold.lo, h.hold.hi, h.hold.alo, h.hold.ahi⟩
  · rw [ft]; simp only [hq, ↓reduceIte]; rw [h.v]
  all_goals simp only [ph, k1, hq]
  · intro h; exact absurd h (by decide)
  · intro h; exact absurd h (by decide)
  · intro h; exact absurd h (by decide)
  · intro _; rw [fv]; simp only [hq]; exact h.v
  · intro h; exact absurd h (by decide)

/-- Pixel (4-bit `attr·4 + pattern`, 0 if transparent) of tile `T` at column `col` (0–7). -/
def tilePx (T : Tile) (col : UInt16) : UInt8 :=
  let sh : UInt16 := 7 - col
  let p0 := ((T.lo.toUInt16 >>> sh) &&& 1).toUInt8
  let p1 := ((T.hi.toUInt16 >>> sh) &&& 1).toUInt8
  let pat := (p1 <<< 1) ||| p0
  if pat == 0 then 0 else ((T.attr &&& 3) <<< 2) ||| pat

theorem pixel_holds (s : State) (A B : Tile) (j : UInt16) (h : Holds s A B j) (hj : j < 8) :
    bgPixelRaw s =
      if j + (s.x &&& 7).toUInt16 < 8 then tilePx A (j + (s.x &&& 7).toUInt16)
      else tilePx B (j + (s.x &&& 7).toUInt16 - 8) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bgPixelRaw, tilePx, h1, h2, h3, h4, word, attrWord, attrFill, bne_iff_ne, ne_eq,
    beq_iff_eq]
  bv_decide

/-! ### Transport to `Ppu.dot` -/

/-- Two states agree on everything the background pipeline reads or writes. -/
structure BgEq (a b : State) : Prop where
  patLo : b.bgPatLo = a.bgPatLo
  patHi : b.bgPatHi = a.bgPatHi
  attrLo : b.bgAttrLo = a.bgAttrLo
  attrHi : b.bgAttrHi = a.bgAttrHi
  tile : b.bgNextTile = a.bgNextTile
  nattr : b.bgNextAttr = a.bgNextAttr
  nlo : b.bgNextLo = a.bgNextLo
  nhi : b.bgNextHi = a.bgNextHi
  v : b.v = a.v
  t : b.t = a.t
  x : b.x = a.x
  ctrl : b.ctrl = a.ctrl
  mask : b.mask = a.mask
  dot : b.dot = a.dot
  scanline : b.scanline = a.scanline

theorem BgEq.refl (s : State) : BgEq s s := by constructor <;> rfl
theorem BgEq.trans {a b c : State} (h1 : BgEq a b) (h2 : BgEq b c) : BgEq a c := by
  cases h1; cases h2; constructor <;> simp_all
theorem BgEq.ite {p : Prop} [Decidable p] {s a b : State} (ha : BgEq s a) (hb : BgEq s b) :
    BgEq s (if p then a else b) := by split <;> assumption

local macro "bgeq_tac" : tactic => `(tactic| (constructor <;>
  simp only [apply_ite State.bgPatLo, apply_ite State.bgPatHi, apply_ite State.bgAttrLo,
    apply_ite State.bgAttrHi, apply_ite State.bgNextTile, apply_ite State.bgNextAttr,
    apply_ite State.bgNextLo, apply_ite State.bgNextHi, apply_ite State.v, apply_ite State.t,
    apply_ite State.x, apply_ite State.ctrl, apply_ite State.mask, apply_ite State.dot,
    apply_ite State.scanline, ite_self]))

theorem bgEq_evalDot (s : State) : BgEq s (Sprites.evalDot s) := by
  simp only [Sprites.evalDot]; bgeq_tac
theorem bgEq_fetchDot (rd) (s : State) : BgEq s (Sprites.fetchDot rd s) := by
  simp only [Sprites.fetchDot]; bgeq_tac
theorem bgEq_pixel (pr) (b) (s : State) : BgEq s (Render.pixel pr b s) := by
  simp only [Render.pixel]; bgeq_tac
theorem bgEq_dotEvents (s : State) : BgEq s (State.dotEvents s) := by
  simp only [State.dotEvents]; bgeq_tac

theorem bgEq_a12 (rd) (s : State) (b : Bool) :
    BgEq (bgDot rd s) (bgDot rd { s with a12 := b }) := by
  unfold bgDot
  have e : (({ s with a12 := b } : State).rendering && activeLine ({ s with a12 := b } : State).scanline)
      = (s.rendering && activeLine s.scanline) := rfl
  rw [e]
  split <;> constructor <;> rfl

/-- With rendering enabled, a full PPU dot agrees with `advance` then `bgDot` on every
background field. -/
theorem bgEq_ppuDot (rd pr) (s : State) (hr : s.rendering = true) :
    BgEq (bgDot rd s.advance) (Nes.Ppu.dot rd pr s) := by
  have hra : s.advance.rendering = true := by
    simp only [State.advance]; repeat' split
    all_goals exact hr
  have h0 : BgEq (bgDot rd s.advance) (bgDot rd { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 }) := by
    exact bgEq_a12 rd _ _
  have c2 : ∀ t, BgEq (bgDot rd s.advance) t → BgEq (bgDot rd s.advance) (Sprites.evalDot t) :=
    fun t h => h.trans (bgEq_evalDot t)
  have c3 : ∀ t, BgEq (bgDot rd s.advance) t → BgEq (bgDot rd s.advance) (Sprites.fetchDot rd t) :=
    fun t h => h.trans (bgEq_fetchDot rd t)
  have c4 : ∀ b t, BgEq (bgDot rd s.advance) t → BgEq (bgDot rd s.advance) (Render.pixel pr b t) :=
    fun b t h => h.trans (bgEq_pixel pr b t)
  have hrend : BgEq (bgDot rd s.advance) (render rd pr s.advance) := by
    unfold render
    dsimp only
    have hra' : ({ s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } : State).rendering
        = true := hra
    simp only [hra', ↓reduceIte]
    exact c4 _ _ (BgEq.ite (c3 _ (BgEq.ite (c2 _ h0) h0)) (BgEq.ite (c2 _ h0) h0))
  unfold Nes.Ppu.dot
  dsimp only
  have h1 := hrend.trans (bgEq_dotEvents _)
  refine BgEq.ite ?_ h1
  exact h1.trans (by constructor <;> rfl)

/-- `f` applied `n` times. -/
def run (f : State → State) : Nat → State → State
  | 0, s => s
  | n + 1, s => f (run f n s)

/-- `n` background dots (`advance` then `bgDot`), the background part of `Ppu.dot`. -/
abbrev bgRun (rd : UInt16 → UInt8) : Nat → State → State := run (fun s => bgDot rd s.advance)

theorem PInv.transport {rd c u} {a b : State} (e : BgEq a b) (h : PInv rd c u a) : PInv rd c u b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, -, -, e12, e13, e14, e15⟩ := e
  obtain ⟨h1, h2, h3, h4, h5, ⟨g1, g2, g3, g4⟩, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [ph] at *
  refine ⟨by simp only [State.rendering, e13]; exact h1, e15 ▸ h2, e12 ▸ h3, e14 ▸ h4, e14 ▸ h5,
    ⟨?_, ?_, ?_, ?_⟩, e5 ▸ h7, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ph, e1, e2, e3, e4, e6, e7, e8, e9, e14]
  all_goals assumption

theorem ph_nat (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 340) :
    (n.toUInt16 - 1) &&& 7 = ((n - 1) % 8).toUInt16 := by
  have e : n.toUInt16 - 1 = (n - 1).toUInt16 := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_sub_of_le]
    · simp; omega
    · rw [UInt16.le_iff_toNat_le]; simp; omega
  rw [e]
  apply UInt16.toNat_inj.mp
  rw [UInt16.toNat_and, show (7 : UInt16).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem small_toUInt16_eq (a b : Nat) (ha : a < 65536) (hb : b < 65536) :
    a.toUInt16 = b.toUInt16 ↔ a = b := by
  constructor
  · intro h; have := congrArg UInt16.toNat h; simp at this; omega
  · intro h; rw [h]

/-- One step of `f` from a visible-line state at dot `d < 340`: `dot + 1`, `x` unchanged. -/
theorem step_pos (rd) (f : State → State) (s : State) (e : BgEq (bgDot rd s.advance) (f s))
    (hl : s.scanline < 240) (hd : s.dot < 340) : (f s).dot = s.dot + 1 ∧ (f s).x = s.x := by
  obtain ⟨k1, -, -, -, k5⟩ := bgDot_keeps rd s.advance
  rw [advance_vis s hl hd] at k1 k5
  rw [e.dot, e.x, advance_vis s hl hd]
  exact ⟨k1, k5⟩

/-- **Single-scanline invariant.** From `Start` at dot 0, after `n ∈ 1..256` background dots
the invariant holds with the drawn tile `Nat.repeat incX ((n-1)/8) u0`, at dot `n`, fine X unchanged. -/
theorem scan (rd c u0) (f : State → State)
    (hf : ∀ s, s.rendering = true → BgEq (bgDot rd s.advance) (f s))
    (s0 : State) (h : Start rd c u0 s0) : ∀ n, 1 ≤ n → n ≤ 256 →
    PInv rd c (Nat.repeat incX ((n - 1) / 8) u0) (run f n s0) ∧ (run f n s0).dot = n.toUInt16 ∧
    (run f n s0).x = s0.x
  | 0, h1, _ => absurd h1 (by decide)
  | 1, _, _ => by
      have := step_pos rd f s0 (hf s0 h.ren) h.line (by rw [h.dot]; decide)
      refine ⟨(Start.step rd c u0 s0 h).transport (hf s0 h.ren), ?_, this.2⟩
      simp only [run]; rw [this.1, h.dot]; decide
  | n + 2, _, h2 => by
      obtain ⟨ih, hd, hx⟩ := scan rd c u0 f hf s0 h (n + 1) (by omega) (by omega)
      have hlt : (run f (n + 1) s0).dot < 256 := by
        rw [hd, UInt16.lt_iff_toNat_lt]; simp; omega
      have he := hf _ ih.ren
      have hst := (ih.step rd c _ _ hlt).transport he
      have hpos := step_pos rd f _ he ih.line (by have := hlt; bv_decide)
      have hph : ph (run f (n + 1) s0) = (n % 8).toUInt16 := by
        simp only [ph, hd]; rw [ph_nat (n + 1) (by omega) (by omega)]; simp
      refine ⟨?_, ?_, ?_⟩
      · rw [show run f (n + 2) s0 = f (run f (n + 1) s0) from rfl]
        rw [hph] at hst
        have e7 : (n % 8).toUInt16 = 7 ↔ n % 8 = 7 :=
          small_toUInt16_eq _ 7 (by omega) (by decide)
        by_cases h7 : n % 8 = 7
        · simp only [e7.mpr h7, ↓reduceIte] at hst
          rwa [show (n + 2 - 1) / 8 = (n + 1 - 1) / 8 + 1 by omega]
        · simp only [show ¬ (n % 8).toUInt16 = 7 from fun h => h7 (e7.mp h), ↓reduceIte] at hst
          rwa [show (n + 2 - 1) / 8 = (n + 1 - 1) / 8 by omega]
      · rw [show run f (n + 2) s0 = f (run f (n + 1) s0) from rfl, hpos.1, hd]
        apply UInt16.toNat_inj.mp; simp
      · rw [show run f (n + 2) s0 = f (run f (n + 1) s0) from rfl, hpos.2, hx]

/-- **Single-scanline background statement.** From `Start rd c u0` at dot 0 of a visible line,
the unmasked background pixel at dot `n ∈ 1..256` (screen column `n - 1`) is pixel
`P mod 8` of the tile `P / 8` coarse-X steps after `u0`, where `P = n - 1 + fine x`. -/
theorem bg_scanline (rd c u0) (f : State → State)
    (hf : ∀ s, s.rendering = true → BgEq (bgDot rd s.advance) (f s))
    (s0 : State) (h : Start rd c u0 s0) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 256) :
    bgPixelRaw (run f n s0) =
      tilePx (tileBits rd c (Nat.repeat incX ((n - 1 + (s0.x &&& 7).toNat) / 8) u0))
        ((n - 1 + (s0.x &&& 7).toNat) % 8).toUInt16 := by
  obtain ⟨hi, hd, hx⟩ := scan rd c u0 f hf s0 h n h1 h2
  have hph : ph (run f n s0) = ((n - 1) % 8).toUInt16 := by
    simp only [ph, hd]; exact ph_nat n h1 (by omega)
  have hj : ((n - 1) % 8).toUInt16 < 8 := by
    rw [UInt16.lt_iff_toNat_lt]; simp; omega
  have hp := pixel_holds _ _ _ _ hi.hold (by rw [hph]; exact hj)
  rw [hp, hph, hx]
  have hxf : (s0.x &&& 7).toNat < 8 := by
    rw [UInt8.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hxu : (s0.x &&& 7).toUInt16 = ((s0.x &&& 7).toNat).toUInt16 := by
    apply UInt16.toNat_inj.mp; simp
  rw [hxu]
  generalize (s0.x &&& 7).toNat = xf at hxf ⊢
  have hc : ((n - 1) % 8).toUInt16 + xf.toUInt16 = ((n - 1) % 8 + xf).toUInt16 := by
    apply UInt16.toNat_inj.mp; simp
  rw [hc]
  by_cases hlt : (n - 1) % 8 + xf < 8
  · have : ((n - 1) % 8 + xf).toUInt16 < 8 := by
      rw [UInt16.lt_iff_toNat_lt]; simp; omega
    simp only [this, ↓reduceIte]
    rw [show (n - 1 + xf) / 8 = (n - 1) / 8 by omega,
      show (n - 1 + xf) % 8 = (n - 1) % 8 + xf by omega]
  · have : ¬ ((n - 1) % 8 + xf).toUInt16 < 8 := by
      rw [UInt16.lt_iff_toNat_lt]; simp; omega
    simp only [this, ↓reduceIte]
    rw [show (n - 1 + xf) / 8 = (n - 1) / 8 + 1 by omega]
    congr 1
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]
    simp; omega

/-- `bg_scanline` for the background pipeline alone. -/
theorem bg_scanline_bgRun (rd c u0) (s0 : State) (h : Start rd c u0 s0) (n : Nat) (h1 : 1 ≤ n)
    (h2 : n ≤ 256) :
    bgPixelRaw (bgRun rd n s0) =
      tilePx (tileBits rd c (Nat.repeat incX ((n - 1 + (s0.x &&& 7).toNat) / 8) u0))
        ((n - 1 + (s0.x &&& 7).toNat) % 8).toUInt16 :=
  bg_scanline rd c u0 _ (fun _ _ => BgEq.refl _) s0 h n h1 h2

/-- `bg_scanline` for the full PPU dot `Nes.Ppu.dot rd pr` (sprites, mux, timing events
included). -/
theorem bg_scanline_ppuDot (rd pr c u0) (s0 : State) (h : Start rd c u0 s0) (n : Nat)
    (h1 : 1 ≤ n) (h2 : n ≤ 256) :
    bgPixelRaw (run (Nes.Ppu.dot rd pr) n s0) =
      tilePx (tileBits rd c (Nat.repeat incX ((n - 1 + (s0.x &&& 7).toNat) / 8) u0))
        ((n - 1 + (s0.x &&& 7).toNat) % 8).toUInt16 :=
  bg_scanline rd c u0 _ (fun s hr => bgEq_ppuDot rd pr s hr) s0 h n h1 h2

/-! ### Prefetch (dots 321–337) and the idle dots (338–340, 0) -/

/-- The low byte of the shifters, shifted left by `j`, holds tile `B` (the high byte is not
constrained: during the prefetch it is left over from the previous line). -/
structure LowHolds (s : State) (B : Tile) (j : UInt16) : Prop where
  lo : (s.bgPatLo >>> j) &&& 0xFF = B.lo.toUInt16
  hi : (s.bgPatHi >>> j) &&& 0xFF = B.hi.toUInt16
  alo : (s.bgAttrLo >>> j) &&& 0xFF = attrFill B.attr 1
  ahi : (s.bgAttrHi >>> j) &&& 0xFF = attrFill B.attr 2

theorem low_reload (rd) (s : State) (C : Tile) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true) (hd : s.dot = 329)
    (hlo : s.bgNextLo = C.lo) (hhi : s.bgNextHi = C.hi) (ha : s.bgNextAttr = C.attr) :
    LowHolds (bgDot rd s) C 0 := by
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, attrFill, hlo, hhi, ha] at * <;> bv_decide

theorem low_mid (rd) (s : State) (B : Tile) (j : UInt16) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true) (hd : 330 ≤ s.dot ∧ s.dot ≤ 336) (hj : j < 7)
    (h : LowHolds s B j) : LowHolds (bgDot rd s) B (j + 1) := by
  obtain ⟨h1', h2', h3', h4'⟩ := h
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, attrFill] at * <;> bv_decide

theorem holds_reload_low (rd) (s : State) (A C : Tile) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true) (hd : s.dot = 337)
    (hlo : s.bgNextLo = C.lo) (hhi : s.bgNextHi = C.hi) (ha : s.bgNextAttr = C.attr)
    (h : LowHolds s A 7) : Holds (bgDot rd s) A C 0 := by
  obtain ⟨h1', h2', h3', h4'⟩ := h
  rw [bgDot_active rd s hr hl]
  constructor <;> simp only [Bg.shifters, word, attrWord, attrFill, hlo, hhi, ha] at * <;> bv_decide

theorem advance_lt (s : State) (hd : s.dot < 339) : s.advance = { s with dot := s.dot + 1 } := by
  have h1 : s.dot ≠ 339 := by bv_decide
  have h2 : s.dot ≠ 340 := by bv_decide
  simp [State.advance, h1, h2]

/-- Prefetch invariant on dots 321–336 of an active line (after `bgDot`): `V` is `v` at dot 320
(the first tile of the next line), `W` the tile being fetched this cycle (`V` on 321–328,
`incX V` on 329–336, when the low byte already holds tile `V`). -/
structure PreInv (rd : UInt16 → UInt8) (c : UInt8) (V W : UInt16) (s : State) : Prop where
  ren : s.rendering = true
  act : activeLine s.scanline = true
  ctrl : s.ctrl = c
  d1 : 321 ≤ s.dot
  d2 : s.dot ≤ 336
  cyc : (s.dot ≤ 328 ∧ W = V) ∨ (329 ≤ s.dot ∧ W = incX V ∧ LowHolds s (tileBits rd c V) (ph s))
  nt : s.bgNextTile = rd (ntAddr W)
  attr : 2 ≤ ph s → s.bgNextAttr = (tileBits rd c W).attr
  lo : 4 ≤ ph s → s.bgNextLo = (tileBits rd c W).lo
  hi : 6 ≤ ph s → s.bgNextHi = (tileBits rd c W).hi
  v : ph s < 7 → s.v = W
  v7 : ph s = 7 → s.v = incX W

/-- After the dot-337 reload (and through the idle dots): shifters hold tiles `V`, `incX V`
unshifted and `v` points two tiles ahead — `Start` minus the position. -/
structure Ready (rd : UInt16 → UInt8) (c : UInt8) (V : UInt16) (s : State) : Prop where
  ren : s.rendering = true
  ctrl : s.ctrl = c
  hold : Holds s (tileBits rd c V) (tileBits rd c (incX V)) 0
  v : s.v = incX (incX V)

theorem Ready.start {rd c V} {s : State} (h : Ready rd c V s) (hd : s.dot = 0)
    (hl : s.scanline < 240) : Start rd c V s := ⟨h.ren, hl, h.ctrl, hd, h.hold, h.v⟩

/-- Shared setup for one prefetch dot `s → bgDot rd s.advance` with `s.dot < 336`. -/
theorem pre_fields (rd) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true)
    (h1 : 320 ≤ s.dot) (h2 : s.dot < 336) :
    let t : State := { s with dot := s.dot + 1 }
    bgDot rd s.advance = bgDot rd t ∧
    (bgDot rd t).bgNextTile = (if ((s.dot + 1) - 1) &&& 7 = 0 then rd (ntAddr s.v) else s.bgNextTile) ∧
    (bgDot rd t).bgNextAttr = (if ((s.dot + 1) - 1) &&& 7 = 2 then atSelect s.v (rd (atAddr s.v))
      else s.bgNextAttr) ∧
    (bgDot rd t).bgNextLo = (if ((s.dot + 1) - 1) &&& 7 = 4 then
      rd (ptAddrOf s.ctrl s.bgNextTile s.v false) else s.bgNextLo) ∧
    (bgDot rd t).bgNextHi = (if ((s.dot + 1) - 1) &&& 7 = 6 then
      rd (ptAddrOf s.ctrl s.bgNextTile s.v true) else s.bgNextHi) ∧
    (bgDot rd t).v = (if ((s.dot + 1) - 1) &&& 7 = 7 then incX s.v else s.v) ∧
    (bgDot rd t).dot = s.dot + 1 ∧ (bgDot rd t).scanline = s.scanline ∧
    (bgDot rd t).ctrl = s.ctrl ∧ (bgDot rd t).mask = s.mask := by
  intro t
  have hr' : t.rendering = true := hr
  have hl' : activeLine t.scanline = true := hl
  have hd : (1 ≤ t.dot ∧ t.dot ≤ 256) ∨ (321 ≤ t.dot ∧ t.dot ≤ 336) := by
    right; dsimp only [t]; constructor <;> bv_decide
  obtain ⟨k1, k2, k3, k4, -⟩ := bgDot_keeps rd t
  have fv := fetch_v rd t hr' hl' hd
  have n256 : ¬ (t.dot = 256) := by dsimp only [t]; bv_decide
  simp only [n256, ↓reduceIte] at fv
  refine ⟨by rw [advance_lt s (by bv_decide)], fetch_tile rd t hr' hl' hd, fetch_attr rd t hr' hl' hd,
    fetch_lo rd t hr' hl' hd, fetch_hi rd t hr' hl' hd, fv, k1, k2, k3, k4⟩

theorem PreInv.step (rd c V W) (s : State) (h : PreInv rd c V W s) (hd : s.dot < 336) :
    PreInv rd c V (if ph s = 7 then incX W else W) (bgDot rd s.advance) := by
  obtain ⟨ea, ft, fa, fl, fh, fv, k1, k2, k3, k4⟩ :=
    pre_fields rd s h.ren h.act (by have := h.d1; bv_decide) hd
  rw [ea]
  have hr : ({ s with dot := s.dot + 1 } : State).rendering = true := h.ren
  have hl : activeLine ({ s with dot := s.dot + 1 } : State).scanline = true := h.act
  have ren : (bgDot rd { s with dot := s.dot + 1 }).rendering = true := by
    simp only [State.rendering, k4]; exact h.ren
  have hd1 := h.d1
  by_cases h7 : ph s = 7
  · simp only [h7, ↓reduceIte]
    have hq : ((s.dot + 1) - 1) &&& 7 = 0 := by simp only [ph] at h7; bv_decide
    have hv := h.v7 h7
    have hA := h.attr (by rw [h7]; decide)
    have hL := h.lo (by rw [h7]; decide)
    have hH := h.hi (by rw [h7]; decide)
    have h328 : s.dot = 328 := by
      have := h.d2; simp only [ph] at h7; bv_decide
    have hW : W = V := by
      rcases h.cyc with ⟨-, e⟩ | ⟨e, -⟩
      · exact e
      · rw [h328] at e; exact absurd e (by decide)
    refine ⟨ren, (by rw [k2]; exact h.act), (by rw [k3]; exact h.ctrl),
      (by rw [k1]; bv_decide), (by rw [k1]; bv_decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · right
      refine ⟨by rw [k1]; bv_decide, by rw [hW], ?_⟩
      simp only [ph, k1, hq]
      rw [← hW]
      exact low_reload rd _ _ hr hl (by dsimp only; rw [h328]; decide) hL hH hA
    · rw [ft]; simp only [hq, ↓reduceIte]; rw [hv]
    all_goals simp only [ph, k1, hq]
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro _; rw [fv]; simp only [hq]; exact hv
    · intro h; exact absurd h (by decide)
  · simp only [h7, ↓reduceIte]
    have hq : ((s.dot + 1) - 1) &&& 7 = ph s + 1 := by simp only [ph] at h7 ⊢; bv_decide
    have hlt : ph s < 7 := by simp only [ph] at h7 ⊢; bv_decide
    have hv := h.v hlt
    refine ⟨ren, (by rw [k2]; exact h.act), (by rw [k3]; exact h.ctrl),
      (by rw [k1]; bv_decide), (by rw [k1]; bv_decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases h.cyc with ⟨e1, e⟩ | ⟨e1, e, hlow⟩
      · left; refine ⟨?_, e⟩; rw [k1]; simp only [ph] at hlt; bv_decide
      · right; refine ⟨by rw [k1]; bv_decide, e, ?_⟩
        simp only [ph, k1, hq]
        exact low_mid rd _ _ _ hr hl (by dsimp only; simp only [ph] at hlt; constructor <;> bv_decide)
          hlt ⟨hlow.lo, hlow.hi, hlow.alo, hlow.ahi⟩
    · have : ¬ (((s.dot + 1) - 1) &&& 7 = 0) := by rw [hq]; simp only [ph] at hlt ⊢; bv_decide
      rw [ft]; simp only [this, ↓reduceIte]; exact h.nt
    all_goals simp only [ph, k1, hq]
    · intro h2
      rw [fa]; split
      · rw [hv]; rfl
      · exact h.attr (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      rw [fl]; split
      · rw [hv, h.nt, h.ctrl]; rfl
      · exact h.lo (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      rw [fh]; split
      · rw [hv, h.nt, h.ctrl]; rfl
      · exact h.hi (by simp only [ph] at hlt h2 ⊢; bv_decide)
    · intro h2
      have : ¬ (((s.dot + 1) - 1) &&& 7 = 7) := by simp only [ph] at hlt h2 ⊢; bv_decide
      rw [fv]; simp only [this, ↓reduceIte]; exact hv
    · intro h2
      have : ((s.dot + 1) - 1) &&& 7 = 7 := by simp only [ph] at hlt h2 ⊢; bv_decide
      rw [fv]; simp only [this, hv, ↓reduceIte]

theorem PreInv.start (rd c V) (s : State) (hr : s.rendering = true)
    (hl : activeLine s.scanline = true) (hc : s.ctrl = c) (hd : s.dot = 320) (hv : s.v = V) :
    PreInv rd c V V (bgDot rd s.advance) := by
  obtain ⟨ea, ft, -, -, -, fv, k1, k2, k3, k4⟩ :=
    pre_fields rd s hr hl (by rw [hd]; decide) (by rw [hd]; decide)
  rw [ea]
  have hq : ((s.dot + 1) - 1) &&& 7 = 0 := by rw [hd]; decide
  have ren : (bgDot rd { s with dot := s.dot + 1 }).rendering = true := by
    simp only [State.rendering, k4]; exact hr
  refine ⟨ren, (by rw [k2]; exact hl), (by rw [k3]; exact hc),
    (by rw [k1, hd]; decide), (by rw [k1, hd]; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · left; exact ⟨by rw [k1, hd]; decide, rfl⟩
  · rw [ft]; simp only [hq, ↓reduceIte]; rw [hv]
  all_goals simp only [ph, k1, hq]
  · intro h; exact absurd h (by decide)
  · intro h; exact absurd h (by decide)
  · intro h; exact absurd h (by decide)
  · intro _; rw [fv]; simp only [hq]; exact hv
  · intro h; exact absurd h (by decide)

/-- `bgDot` on dots 337 and 0, 338–340 leaves the shifters' fields named here and `v` alone
(only the shifters at 337 and `bgNextTile` at 337/339 move). -/
theorem idle_bgDot (rd) (s : State) (hd : s.dot = 0 ∨ (338 ≤ s.dot ∧ s.dot ≤ 340)) :
    (bgDot rd s).bgPatLo = s.bgPatLo ∧ (bgDot rd s).bgPatHi = s.bgPatHi ∧
    (bgDot rd s).bgAttrLo = s.bgAttrLo ∧ (bgDot rd s).bgAttrHi = s.bgAttrHi ∧
    (bgDot rd s).v = s.v := by
  by_cases hc : (s.rendering && activeLine s.scanline) = true
  · simp only [Bool.and_eq_true] at hc
    rw [bgDot_active rd s hc.1 hc.2]; dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Bg.shifters] at *; bv_decide
    · simp only [Bg.shifters] at *; bv_decide
    · simp only [Bg.shifters] at *; bv_decide
    · simp only [Bg.shifters] at *; bv_decide
    · have := hc.2; fetch_tac rd
  · simp [bgDot, hc]

theorem v_337 (rd) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true)
    (hd : s.dot = 337) : (bgDot rd s).v = s.v := by
  rw [bgDot_active rd s hr hl]; dsimp only; fetch_tac rd

theorem advance_keep (s : State) :
    s.advance.bgPatLo = s.bgPatLo ∧ s.advance.bgPatHi = s.bgPatHi ∧
    s.advance.bgAttrLo = s.bgAttrLo ∧ s.advance.bgAttrHi = s.bgAttrHi ∧ s.advance.v = s.v ∧
    s.advance.ctrl = s.ctrl ∧ s.advance.mask = s.mask := by
  simp only [State.advance]; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Dot 337: the second prefetch reload completes the shifters for the next line. -/
theorem PreInv.finish (rd c V W) (s : State) (h : PreInv rd c V W s) (hd : s.dot = 336) :
    Ready rd c V (bgDot rd s.advance) ∧ (bgDot rd s.advance).dot = 337 ∧
    (bgDot rd s.advance).scanline = s.scanline := by
  have h7 : ph s = 7 := by simp only [ph, hd]; decide
  have hW : W = incX V := by
    rcases h.cyc with ⟨e, -⟩ | ⟨-, e, -⟩
    · rw [hd] at e; exact absurd e (by decide)
    · exact e
  have hlow : LowHolds s (tileBits rd c V) 7 := by
    rcases h.cyc with ⟨e, -⟩ | ⟨-, -, e⟩
    · rw [hd] at e; exact absurd e (by decide)
    · rw [h7] at e; exact e
  rw [advance_lt s (by rw [hd]; decide)]
  have hr : ({ s with dot := s.dot + 1 } : State).rendering = true := h.ren
  have hl : activeLine ({ s with dot := s.dot + 1 } : State).scanline = true := h.act
  have e337 : ({ s with dot := s.dot + 1 } : State).dot = 337 := by dsimp only; rw [hd]; decide
  obtain ⟨k1, k2, k3, k4, -⟩ := bgDot_keeps rd { s with dot := s.dot + 1 }
  refine ⟨⟨by simp only [State.rendering, k4]; exact h.ren, by rw [k3]; exact h.ctrl, ?_, ?_⟩,
    by rw [k1, e337], k2⟩
  · have := holds_reload_low rd _ (tileBits rd c V) (tileBits rd c W) hr hl e337
      (h.lo (by rw [h7]; decide)) (h.hi (by rw [h7]; decide)) (h.attr (by rw [h7]; decide))
      ⟨hlow.lo, hlow.hi, hlow.alo, hlow.ahi⟩
    rwa [hW] at this
  · rw [v_337 rd _ hr hl e337]; dsimp only; rw [h.v7 h7, hW]

/-- An idle dot (the target dot is 0 or 338–340) keeps `Ready`, for any per-dot function that
agrees with `advance`-then-`bgDot` on the background fields. -/
theorem Ready.idle (rd c V) (f : State → State)
    (hf : ∀ s, s.rendering = true → BgEq (bgDot rd s.advance) (f s))
    (s : State) (h : Ready rd c V s) (hd : (f s).dot = 0 ∨ (338 ≤ (f s).dot ∧ (f s).dot ≤ 340)) :
    Ready rd c V (f s) := by
  have e := hf s h.ren
  rw [e.dot, (bgDot_keeps rd _).1] at hd
  obtain ⟨i1, i2, i3, i4, i5⟩ := idle_bgDot rd s.advance hd
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := advance_keep s
  obtain ⟨k1, k2, k3, k4, -⟩ := bgDot_keeps rd s.advance
  obtain ⟨h1, h2, ⟨g1, g2, g3, g4⟩, h4⟩ := h
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.rendering, e.mask, k4, a7]; exact h1
  · rw [e.ctrl, k3, a6, h2]
  · rw [e.patLo, i1, a1, g1]
  · rw [e.patHi, i2, a2, g2]
  · rw [e.attrLo, i3, a3, g3]
  · rw [e.attrHi, i4, a4, g4]
  · rw [e.v, i5, a5, h4]

theorem PreInv.transport {rd c V W} {a b : State} (e : BgEq a b) (h : PreInv rd c V W a) :
    PreInv rd c V W b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, -, -, e12, e13, e14, e15⟩ := e
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨by simp only [State.rendering, e13]; exact h1, e15 ▸ h2, e12 ▸ h3, e14 ▸ h4, e14 ▸ h5,
    ?_, e5 ▸ h7, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h6 with ⟨x1, x2⟩ | ⟨x1, x2, ⟨l1, l2, l3, l4⟩⟩
    · exact Or.inl ⟨e14 ▸ x1, x2⟩
    · refine Or.inr ⟨e14 ▸ x1, x2, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp only [ph, e1, e2, e3, e4, e14] <;>
        assumption
  all_goals simp only [ph, e6, e7, e8, e9, e14]
  all_goals assumption

/-- **Prefetch.** From dot 320 of an active line with `v = V` (rendering on, `ctrl = c`),
seventeen dots of `f` reach dot 337 with `Ready rd c V`: the shifters hold tiles `V` and
`incX V` (the first two tiles of the next line) and `v = incX (incX V)`. -/
theorem prefetch (rd c V) (f : State → State)
    (hf : ∀ s, s.rendering = true → BgEq (bgDot rd s.advance) (f s))
    (s0 : State) (hr : s0.rendering = true) (hl : activeLine s0.scanline = true) (hc : s0.ctrl = c)
    (hd : s0.dot = 320) (hv : s0.v = V) :
    Ready rd c V (run f 17 s0) ∧ (run f 17 s0).dot = 337 ∧ (run f 17 s0).scanline = s0.scanline := by
  have loop : ∀ n, 1 ≤ n → n ≤ 16 →
      PreInv rd c V (Nat.repeat incX ((n - 1) / 8) V) (run f n s0) ∧
      (run f n s0).dot = (320 + n).toUInt16 ∧ (run f n s0).scanline = s0.scanline := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (by decide)
    | succ m ih =>
      intro _ h2
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have e := hf s0 hr
        refine ⟨(PreInv.start rd c V s0 hr hl hc hd hv).transport e, ?_, ?_⟩
        · show (f s0).dot = _
          rw [e.dot, (bgDot_keeps rd _).1, advance_lt s0 (by rw [hd]; decide)]; dsimp only; rw [hd]; decide
        · show (f s0).scanline = _
          rw [e.scanline, (bgDot_keeps rd _).2.1, advance_lt s0 (by rw [hd]; decide)]
      · obtain ⟨ip, idot, isl⟩ := ih hm (by omega)
        have e := hf _ ip.ren
        have hlt : (run f m s0).dot < 336 := by
          rw [idot, UInt16.lt_iff_toNat_lt]; simp; omega
        have hst := (ip.step rd c V _ _ hlt).transport e
        have hph : ph (run f m s0) = ((m - 1) % 8).toUInt16 := by
          simp only [ph, idot]; rw [ph_nat (320 + m) (by omega) (by omega)]
          congr 1; omega
        have hadv := advance_lt (run f m s0) (by have := hlt; bv_decide)
        refine ⟨?_, ?_, ?_⟩
        · show PreInv _ _ _ _ (f (run f m s0))
          rw [hph] at hst
          have e7 : ((m - 1) % 8).toUInt16 = 7 ↔ (m - 1) % 8 = 7 :=
            small_toUInt16_eq _ 7 (by omega) (by decide)
          by_cases h7 : (m - 1) % 8 = 7
          · simp only [e7.mpr h7, ↓reduceIte] at hst
            rwa [show (m + 1 - 1) / 8 = (m - 1) / 8 + 1 by omega]
          · simp only [show ¬ ((m - 1) % 8).toUInt16 = 7 from fun h => h7 (e7.mp h),
              ↓reduceIte] at hst
            rwa [show (m + 1 - 1) / 8 = (m - 1) / 8 by omega]
        · show (f (run f m s0)).dot = _
          rw [e.dot, (bgDot_keeps rd _).1, hadv]; dsimp only; rw [idot]
          apply UInt16.toNat_inj.mp; simp; omega
        · show (f (run f m s0)).scanline = _
          rw [e.scanline, (bgDot_keeps rd _).2.1, hadv]; exact isl
  obtain ⟨ip, idot, isl⟩ := loop 16 (by decide) (by decide)
  have e := hf _ ip.ren
  obtain ⟨r, rd', rs⟩ := ip.finish rd c V _ _ (by rw [idot]; decide)
  refine ⟨?_, ?_, ?_⟩
  · show Ready _ _ _ (f (run f 16 s0))
    obtain ⟨r1, r2, ⟨g1, g2, g3, g4⟩, r4⟩ := r
    exact ⟨by simp only [State.rendering, e.mask]; exact r1, by rw [e.ctrl]; exact r2,
      ⟨by rw [e.patLo]; exact g1, by rw [e.patHi]; exact g2, by rw [e.attrLo]; exact g3,
       by rw [e.attrHi]; exact g4⟩, by rw [e.v]; exact r4⟩
  · show (f (run f 16 s0)).dot = 337
    rw [e.dot, rd']
  · show (f (run f 16 s0)).scanline = _
    rw [e.scanline, rs, isl]

end Nes.Ppu.Proofs
