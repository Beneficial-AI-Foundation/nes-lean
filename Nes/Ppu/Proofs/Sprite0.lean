import Nes.Ppu.Step
import Nes.Ppu.Registers
import Nes.Ppu.Proofs.Timing

/-!
# `Nes.Ppu.Proofs.Sprite0` — T-PPU-4 (sprite-0 hit)

## Spec

Positions follow `Nes.Ppu.Timing`: the `(scanline, dot)` of a state is the dot *just executed*,
and visible pixel `x` (0–255) of line `y` (0–239) is output on dot `x + 1` (`Render.pixel`).

* **Sprite-0 opacity.** `spr0Opaque s x` (bit 7 of `Render.spritePixel s x`): sprite 0 is on the
  line (`spr0Line`), slot 0 is loaded (`0 < min sprCount 8`), `sprX[0] ≤ x < sprX[0] + 8`, and
  the slot-0 pattern bit at column `x - sprX[0]` is non-zero (`spritePixel_bit7`). Slot 0 is first
  in slot order, so it wins whenever it is opaque.
* **`hitCond bgPx s x`** := `x ≠ 255 ∧ showBg ∧ showSpr ∧ (x ≥ 8 ∨ (bgLeft ∧ sprLeft)) ∧
  spr0Opaque s x ∧ bgPx & 3 ≠ 0` (`bgPx` is the 4-bit background index: bits 0–1 pattern, so
  opaque iff `bgPx & 3 ≠ 0`).
* **T-PPU-4 (hit iff, one pixel).** For `s` at visible line `y < 240`, dot `x + 1`:
  `(pixel palRd bgPx s).spr0Hit = s.spr0Hit ∨ hitCond bgPx s x` (`T_PPU_4_hit_iff`).
* **T-PPU-4 (hit iff, one PPU dot).** For `Ppu.dot rd palRd s` landing on `(y, x + 1)` with
  `y < 240`: `spr0Hit` after = before ∨ `hitCond` of the background pixel and the pre-pixel state
  computed by the dot (`prePixel`, whose `mask` is `s.mask`) (`T_PPU_4_dot_hit_iff`).
* **T-PPU-4 (never outside).** If `Ppu.dot` lands on a line ≥ 240, on dot 0 or on a dot > 256, it
  never sets `spr0Hit` (`T_PPU_4_never_outside`); at `(261, 1)` it clears it
  (`T_PPU_4_clear`).
* **T-PPU-4 (priority independent).** `spr0Opaque` and `hitCond` do not read the sprite's
  priority bit (`sprAttr[0]` bit 5): changing `sprAttr` leaves `hitCond` unchanged
  (`T_PPU_4_priority_independent`).
* **T-PPU-4 (visible at x + 2).** If a `Ppu.dot` step sets the flag, the dot it executed is a
  visible pixel dot `x + 1` (1–256) of a line < 240; a `$2002` read on the state before the step
  (i.e. between dots `x` and `x + 1`) returns bit 6 clear, and a read on the state after it
  (between dots `x + 1` and `x + 2`, i.e. during dot `x + 2`) returns bit 6 set
  (`T_PPU_4_visible_at`).

Method: unfolding and case splits on the straight-line code; small `UInt8`/`UInt64` bit facts by
`decide` / `bv_decide`.
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.State Nes.Ppu.Render Nes.Ppu.Sprites Nes.Ppu.Bg

/-! ### Definitions -/

/-- Slot-0 pattern value (2 bits) at column `x` (the expression `spritePixelAux` tests). -/
def spr0Pat (s : State) (x : UInt8) : UInt8 :=
  let sh : UInt8 := 7 - (x - getByte s.sprX 0)
  ((getByte s.sprPatLo 0 >>> sh) &&& (1 : UInt8)) |||
    (((getByte s.sprPatHi 0 >>> sh) &&& (1 : UInt8)) <<< (1 : UInt8))

/-- Sprite 0 has an opaque pixel at column `x` on the current line. -/
def spr0Opaque (s : State) (x : UInt8) : Bool :=
  s.spr0Line && decide (0 < min s.sprCount 8) && x ≥ getByte s.sprX 0 &&
    decide (x - getByte s.sprX 0 < 8) && spr0Pat s x != 0

/-- Sprite-0 hit condition of pixel `x` with background index `bgPx`. -/
def hitCond (bgPx : UInt8) (s : State) (x : UInt8) : Bool :=
  x != 255 && s.showBg && s.showSpr && (x ≥ 8 || (s.bgLeft && s.sprLeft)) && spr0Opaque s x &&
    (bgPx &&& 3 != 0)

/-! ### Bit facts -/

theorem pack_bit7 (a b c : UInt8) :
    ((a &&& (1 : UInt8)) ||| ((b &&& (1 : UInt8)) <<< (1 : UInt8)) |||
      ((c &&& (3 : UInt8)) <<< (2 : UInt8)) ||| ((c &&& (0x20 : UInt8)) >>> (1 : UInt8)) |||
      (0 : UInt8)) &&& 0x80 = 0 := by
  bv_decide

theorem or80_bit7 (a : UInt8) : (a ||| 0x80) &&& 0x80 = 0x80 := by bv_decide

/-! ### Sprite pixel: bit 7 = sprite 0 opaque -/

/-- Slots other than 0 never carry the sprite-0 bit. -/
theorem aux_bit7 (s : State) (x n : UInt8) :
    ∀ (fuel : Nat) (i : UInt8), i ≠ 0 → i.toNat + fuel ≤ 255 →
      spritePixelAux s x n fuel i &&& 0x80 = 0 := by
  intro fuel
  induction fuel with
  | zero => intro i _ _; rw [spritePixelAux]; rfl
  | succ k ih =>
    intro i hi hb
    have hi' : i + 1 ≠ 0 := by
      intro h
      have := congrArg UInt8.toNat h
      simp [UInt8.toNat_add] at this
      omega
    have hb' : (i + 1).toNat + k ≤ 255 := by
      rw [UInt8.toNat_add]; simp; omega
    have hz : (i == 0 && s.spr0Line) = false := by simp [hi]
    rw [spritePixelAux]
    simp only [hz, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · split
        · exact pack_bit7 _ _ _
        · exact ih _ hi' hb'
      · exact ih _ hi' hb'

/-- Bit 7 of the packed sprite pixel is exactly "sprite 0 opaque at `x`". -/
theorem spritePixel_bit7 (s : State) (x : UInt8) :
    (spritePixel s x &&& 0x80 != 0) = spr0Opaque s x := by
  unfold spritePixel spr0Opaque spr0Pat
  rw [spritePixelAux]
  have h1 := aux_bit7 s x (min s.sprCount 8) 7 1 (by decide) (by decide)
  simp only [UInt8.zero_add, beq_self_eq_true, Bool.true_and, UInt8.toNat_zero]
  split
  · rename_i h
    have : ¬ (0 < min s.sprCount 8) := UInt8.not_lt.mpr h
    simp [this]
  · rename_i h
    have h0 : 0 < min s.sprCount 8 := UInt8.not_le.mp h
    split
    · rename_i hr
      split
      · rename_i hp
        cases hs : s.spr0Line
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
          rw [pack_bit7]; rfl
        · simp only [↓reduceIte]
          rw [or80_bit7]
          simp only [hp, hr, decide_eq_true h0, Bool.true_and]
          decide
      · rename_i hp
        rw [h1]
        simp at hp
        simp [hp]
    · rename_i hr
      rw [h1]
      revert hr
      generalize decide (x ≥ getByte s.sprX 0) = a
      generalize decide (x - getByte s.sprX 0 < 8) = b
      cases a <;> cases b <;> simp

/-! ### One pixel -/

theorem dot_vis : ∀ x : UInt8, (x.toUInt16 + 1 == 0 || x.toUInt16 + 1 > 256) = false := by
  decide

theorem dot_x : ∀ x : UInt8, (x.toUInt16 + 1 - 1).toUInt8 = x := by decide

theorem hi_none : ∀ c : UInt8, (c.toUInt16 >>> 8).toUInt8 = 0 := by decide

theorem hi_hit : ∀ c : UInt8, ((c.toUInt16 ||| 0x4000) >>> 8).toUInt8 = 0x40 := by decide

theorem hi_nohit : ∀ c : UInt8, ((c.toUInt16 ||| 0) >>> 8).toUInt8 = 0 := by decide

theorem hi_if (c : UInt8) (b : Bool) :
    (((c.toUInt16 ||| if b then 0x4000 else 0) >>> 8).toUInt8 &&& 0x40 != 0) = b := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, hi_nohit]; decide
  · simp only [↓reduceIte, hi_hit]; decide

theorem or_bit6 (a b : UInt8) :
    ((a ||| b) &&& 0x40 != 0) = ((a &&& 0x40 != 0) || (b &&& 0x40 != 0)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, ← Classical.not_and_iff_not_or_not]
  bv_decide

theorem or_zero_bit6 (a : UInt8) : ((a ||| 0) &&& 0x40 != 0) = (a &&& 0x40 != 0) := by
  simp

theorem or_40_bit6 (a : UInt8) : ((a ||| 0x40) &&& 0x40 != 0) = true := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, iff_true]
  bv_decide

theorem showBg_of_rendering : ∀ m : UInt8, (m &&& 0x18 != 0) = false → (m &&& 0x08 != 0) = false := by
  decide

theorem bg_and3 : ∀ b : UInt8, (b &&& 0x0F) &&& 3 = b &&& 3 := by decide

theorem ge8 (x : UInt8) : decide (x ≥ 8) = !decide (x < 8) := by
  by_cases h : x < 8
  · simp [h, UInt8.not_le.mpr h]
  · simp [h, UInt8.not_lt.mp h]

/-- **T-PPU-4 (hit iff).** One pixel step at visible line `y < 240`, dot `x + 1`: the sprite-0
flag after is the flag before, or the hit condition. -/
theorem T_PPU_4_hit_iff (palRd : UInt8 → UInt8) (bgPx : UInt8) (s : State) (x : UInt8)
    (hd : s.dot = x.toUInt16 + 1) (hy : s.scanline < 240) :
    (pixel palRd bgPx s).spr0Hit = (s.spr0Hit || hitCond bgPx s x) := by
  have hy' : ¬ s.scanline ≥ 240 := UInt16.not_le.mpr hy
  unfold pixel
  simp only [hd, dot_vis, hy', decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    dot_x]
  simp only [State.spr0Hit, or_bit6]
  congr 1
  unfold pixelOut
  cases hr : s.rendering
  · simp only [Bool.not_false, ↓reduceIte, hi_none]
    have : s.showBg = false := showBg_of_rendering _ hr
    simp [hitCond, this]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi_if]
    unfold hitCond
    rw [ge8, ← spritePixel_bit7]
    cases s.showBg <;> cases s.showSpr <;> cases decide (x < 8) <;> cases s.bgLeft <;>
      cases s.sprLeft <;> simp [bg_and3, Bool.and_comm, Bool.and_left_comm]


/-! ### Field preservation of the other per-dot functions -/

theorem bgDot_fields (rd : UInt16 → UInt8) (s : State) :
    (bgDot rd s).status = s.status ∧ (bgDot rd s).mask = s.mask ∧
      (bgDot rd s).dot = s.dot ∧ (bgDot rd s).scanline = s.scanline := by
  unfold bgDot; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem fetchDot_fields (rd : UInt16 → UInt8) (s : State) :
    (Sprites.fetchDot rd s).status = s.status ∧ (Sprites.fetchDot rd s).mask = s.mask ∧
      (Sprites.fetchDot rd s).dot = s.dot ∧ (Sprites.fetchDot rd s).scanline = s.scanline := by
  simp only [Sprites.fetchDot]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem packEval_status (n m sec latch st : UInt8) (spr0 : Bool) (i b : UInt8) :
    (packEval n m sec latch st spr0 i b >>> 32).toUInt8 = st := by
  unfold packEval
  cases spr0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide

theorem or20_bit6 : ∀ a : UInt8, (a ||| 0x20) &&& 0x40 = a &&& 0x40 := by decide

theorem evalStep_bit6 (s : State) :
    (evalStep s >>> 32).toUInt8 &&& 0x40 = s.status &&& 0x40 := by
  simp only [evalStep, evalAct]
  repeat' split
  all_goals simp only [packEval_status, or20_bit6]

theorem evalDot_fields (s : State) :
    (evalDot s).status &&& 0x40 = s.status &&& 0x40 ∧ (evalDot s).mask = s.mask ∧
      (evalDot s).dot = s.dot ∧ (evalDot s).scanline = s.scanline := by
  simp only [evalDot]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨evalStep_bit6 s, rfl, rfl, rfl⟩


/-! ### One PPU dot -/

/-- The state and background index `Render.pixel` receives inside `render` (steps 2–5 of
`Nes.Ppu.Step`). -/
def prePixel (rd : UInt16 → UInt8) (s : State) : State × UInt8 :=
  let s := { s with a12 := busAddr s &&& 0x1000 != 0 }
  if s.rendering then
    let s1 := bgDot rd s
    let b := bgPixel s1
    let s2 := if s1.scanline < 240 then evalDot s1 else s1
    let s3 := if activeLine s2.scanline then Sprites.fetchDot rd s2 else s2
    (s3, b)
  else (s, 0)

theorem render_eq (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    render rd palRd s = pixel palRd (prePixel rd s).2 (prePixel rd s).1 := by
  simp only [render, prePixel]
  split <;> rfl

theorem prePixel_fields (rd : UInt16 → UInt8) (s : State) :
    (prePixel rd s).1.spr0Hit = s.spr0Hit ∧ (prePixel rd s).1.mask = s.mask ∧
      (prePixel rd s).1.dot = s.dot ∧ (prePixel rd s).1.scanline = s.scanline := by
  simp only [prePixel]
  split
  · obtain ⟨b1, b2, b3, b4⟩ := bgDot_fields rd { s with a12 := busAddr s &&& 0x1000 != 0 }
    generalize bgDot rd { s with a12 := busAddr s &&& 0x1000 != 0 } = s1 at *
    have h2 : ∃ s2 : State, (if s1.scanline < 240 then evalDot s1 else s1) = s2 ∧
        s2.status &&& 0x40 = s1.status &&& 0x40 ∧ s2.mask = s1.mask ∧ s2.dot = s1.dot ∧
        s2.scanline = s1.scanline := by
      split
      · exact ⟨_, rfl, evalDot_fields s1⟩
      · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨s2, e2, c1, c2, c3, c4⟩ := h2
    rw [e2]
    have h3 : ∃ s3 : State, (if activeLine s2.scanline then Sprites.fetchDot rd s2 else s2) = s3 ∧
        s3.status = s2.status ∧ s3.mask = s2.mask ∧ s3.dot = s2.dot ∧
        s3.scanline = s2.scanline := by
      split
      · exact ⟨_, rfl, fetchDot_fields rd s2⟩
      · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨s3, e3, d1, d2, d3, d4⟩ := h3
    rw [e3]
    simp only [State.spr0Hit, d1, c1, b1, d2, c2, b2, d3, c3, b3, d4, c4, b4]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem pixel_fields (palRd : UInt8 → UInt8) (b : UInt8) (s : State) :
    (pixel palRd b s).mask = s.mask ∧ (pixel palRd b s).dot = s.dot ∧
      (pixel palRd b s).scanline = s.scanline := by
  simp only [pixel]; split <;> exact ⟨rfl, rfl, rfl⟩

theorem pixel_outside (palRd : UInt8 → UInt8) (b : UInt8) (s : State)
    (h : s.scanline ≥ 240 ∨ s.dot = 0 ∨ s.dot > 256) : pixel palRd b s = s := by
  simp only [pixel]
  split
  · rfl
  · rename_i h'
    exfalso; apply h'
    rcases h with h | h | h <;> simp [h]

theorem or80_bit6 : ∀ a : UInt8, ((a ||| 128) &&& 64 != 0) = (a &&& 64 != 0) := by decide

theorem and1F_bit6 : ∀ a : UInt8, a &&& 31 &&& 64 = 0 := by decide

theorem dotEvents_spr0Hit (s : State) :
    (dotEvents s).spr0Hit = (s.spr0Hit && !(s.dot == 1 && s.scanline == 261)) := by
  simp only [dotEvents]
  repeat' split
  all_goals simp_all [State.spr0Hit, or80_bit6, and1F_bit6]

theorem render_fields (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    (render rd palRd s).dot = s.dot ∧ (render rd palRd s).scanline = s.scanline ∧
      (render rd palRd s).mask = s.mask := by
  rw [render_eq]
  obtain ⟨p1, p2, p3⟩ := pixel_fields palRd (prePixel rd s).2 (prePixel rd s).1
  obtain ⟨_, q2, q3, q4⟩ := prePixel_fields rd s
  exact ⟨p2.trans q3, p3.trans q4, p1.trans q2⟩

/-- `Ppu.dot` is `dotEvents ∘ render ∘ advance` up to `renderLatch`. -/
theorem dot_eq_latch (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    let t := dotEvents (render rd palRd (advance s))
    (Ppu.dot rd palRd s).dot = t.dot ∧ (Ppu.dot rd palRd s).scanline = t.scanline ∧
      (Ppu.dot rd palRd s).mask = t.mask ∧ (Ppu.dot rd palRd s).status = t.status := by
  simp only [Ppu.dot]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Position and mask after one PPU dot. -/
theorem dot_fields (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    (Ppu.dot rd palRd s).dot = (advance s).dot ∧
      (Ppu.dot rd palRd s).scanline = (advance s).scanline ∧
      (Ppu.dot rd palRd s).mask = s.mask := by
  obtain ⟨e1, e2, e3, _⟩ := dot_eq_latch rd palRd s
  obtain ⟨d1, d2, _, d4, _⟩ := dotEvents_pos (render rd palRd (advance s))
  obtain ⟨r1, r2, r3⟩ := render_fields rd palRd (advance s)
  exact ⟨e1.trans (d1.trans r1), e2.trans (d2.trans r2),
    e3.trans (d4.trans (r3.trans (advance_regs s).2.2.2.1))⟩

theorem dot_spr0Hit (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    (Ppu.dot rd palRd s).spr0Hit =
      ((render rd palRd (advance s)).spr0Hit &&
        !((Ppu.dot rd palRd s).dot == 1 && (Ppu.dot rd palRd s).scanline == 261)) := by
  obtain ⟨e1, e2, _, e4⟩ := dot_eq_latch rd palRd s
  obtain ⟨d1, d2, _⟩ := dotEvents_pos (render rd palRd (advance s))
  simp only [State.spr0Hit] at *
  rw [e4, e1, e2, d1, d2]
  exact dotEvents_spr0Hit _


/-! ### T-PPU-4 at the level of `Ppu.dot` -/

/-- **T-PPU-4 (hit iff, one PPU dot).** A dot landing on `(y, x + 1)`, `y < 240`: the flag after
is the flag before, or the hit condition of the pixel `render` outputs (background index and
pre-pixel state `prePixel rd (advance s)`, whose `mask` is `s.mask`). -/
theorem T_PPU_4_dot_hit_iff (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (x : UInt8) (hd : (Ppu.dot rd palRd s).dot = x.toUInt16 + 1)
    (hy : (Ppu.dot rd palRd s).scanline < 240) :
    (Ppu.dot rd palRd s).spr0Hit =
      (s.spr0Hit || hitCond (prePixel rd (advance s)).2 (prePixel rd (advance s)).1 x) := by
  have h261 : ((Ppu.dot rd palRd s).scanline == 261) = false := by
    simp only [beq_eq_false_iff_ne]; intro h; rw [h] at hy; exact absurd hy (by decide)
  rw [dot_spr0Hit, h261, Bool.and_false, Bool.not_false, Bool.and_true, render_eq]
  obtain ⟨f1, f2, _⟩ := dot_fields rd palRd s
  obtain ⟨q1, _, q3, q4⟩ := prePixel_fields rd (advance s)
  rw [T_PPU_4_hit_iff _ _ _ x (q3.trans (f1.symm.trans hd)) (by rw [q4, ← f2]; exact hy), q1]
  simp only [State.spr0Hit, (advance_regs s).1]

/-- **T-PPU-4 (never outside).** A dot landing on a line ≥ 240, on dot 0 or on a dot > 256 never
sets the sprite-0 flag. -/
theorem T_PPU_4_never_outside (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (h : (Ppu.dot rd palRd s).scanline ≥ 240 ∨ (Ppu.dot rd palRd s).dot = 0 ∨
      (Ppu.dot rd palRd s).dot > 256)
    (hs : (Ppu.dot rd palRd s).spr0Hit = true) : s.spr0Hit = true := by
  rw [dot_spr0Hit, render_eq, Bool.and_eq_true] at hs
  obtain ⟨f1, f2, _⟩ := dot_fields rd palRd s
  obtain ⟨q1, _, q3, q4⟩ := prePixel_fields rd (advance s)
  rw [pixel_outside _ _ _ (by rw [q3, q4, ← f1, ← f2]; exact h), q1] at hs
  simpa [State.spr0Hit, (advance_regs s).1] using hs.1

/-- **T-PPU-4 (clear).** The dot landing on `(261, 1)` clears the sprite-0 flag. -/
theorem T_PPU_4_clear (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (hd : (Ppu.dot rd palRd s).dot = 1) (hy : (Ppu.dot rd palRd s).scanline = 261) :
    (Ppu.dot rd palRd s).spr0Hit = false := by
  rw [dot_spr0Hit, hd, hy]; simp

/-- **T-PPU-4 (priority independent).** The sprite-0 bit of the sprite pixel, and hence the hit
condition, do not depend on the sprite attributes (in particular the priority bit 5). -/
theorem T_PPU_4_priority_independent (s : State) (a : ByteArray) (bgPx x : UInt8) :
    (spritePixel { s with sprAttr := a } x &&& 0x80 != 0) = (spritePixel s x &&& 0x80 != 0) ∧
      hitCond bgPx { s with sprAttr := a } x = hitCond bgPx s x := by
  rw [spritePixel_bit7, spritePixel_bit7]
  exact ⟨rfl, rfl⟩

theorem readStatus_bit6 (s : State) : ((readStatus s).2 &&& 0x40 != 0) = s.spr0Hit := by
  simp only [readStatus, State.spr0Hit]
  generalize s.status = a; generalize s.ioLatch = b
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq]
  bv_decide

theorem dot_vis_inv (d : UInt16) (h1 : ¬ d = 0) (h2 : ¬ d > 256) :
    d = ((d - 1).toUInt8).toUInt16 + 1 := by
  bv_decide

/-- **T-PPU-4 (visible at `x + 2`).** If a PPU dot sets the sprite-0 flag, the dot it executed is a
visible pixel dot `x + 1` (`1 ≤ dot ≤ 256`) of a line `< 240` where the hit condition held; a
`$2002` read on the state before the dot (between dots `x` and `x + 1`) returns bit 6 clear, and a
read on the state after it (between dots `x + 1` and `x + 2`, i.e. during dot `x + 2`) returns
bit 6 set. -/
theorem T_PPU_4_visible_at (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (h0 : s.spr0Hit = false) (h1 : (Ppu.dot rd palRd s).spr0Hit = true) :
    let s' := Ppu.dot rd palRd s
    let x := (s'.dot - 1).toUInt8
    s'.scanline < 240 ∧ s'.dot = x.toUInt16 + 1 ∧
      hitCond (prePixel rd (advance s)).2 (prePixel rd (advance s)).1 x = true ∧
      ((readStatus s).2 &&& 0x40 != 0) = false ∧ ((readStatus s').2 &&& 0x40 != 0) = true := by
  intro s' x
  have hin : ¬ (s'.scanline ≥ 240 ∨ s'.dot = 0 ∨ s'.dot > 256) := fun h =>
    absurd (T_PPU_4_never_outside rd palRd s h h1) (by simp [h0])
  simp only [not_or] at hin
  obtain ⟨hy, hd0, hd256⟩ := hin
  have hy' : s'.scanline < 240 := UInt16.not_le.mp hy
  have hd : s'.dot = x.toUInt16 + 1 := dot_vis_inv _ hd0 hd256
  have hh := T_PPU_4_dot_hit_iff rd palRd s x hd hy'
  rw [h1, h0, Bool.false_or] at hh
  exact ⟨hy', hd, hh.symm, by rw [readStatus_bit6, h0], by rw [readStatus_bit6]; exact h1⟩

end Nes.Ppu.Proofs
