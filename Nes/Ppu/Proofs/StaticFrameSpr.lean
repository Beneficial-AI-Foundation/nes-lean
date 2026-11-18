import Nes.Ppu.Step
import Nes.Ppu.Declarative
import Nes.Ppu.Proofs.Sprites
import Nes.Ppu.Proofs.Sprite0
import Nes.Ppu.Proofs.Shifter

/-!
# `Nes.Ppu.Proofs.StaticFrameSpr` — sprite half and priority mux of T-PPU-6

## Spec

Throughout, `rd`/`pr` are fixed pure readers (CHR/VRAM, palette), the run is the real pipeline
`run (Ppu.dot rd pr) n` (so OAM, `ctrl`, `mask` cannot change), rendering is enabled, `L` is a
visible line, the start state `s` is at dot 0 of `L`, and the slot arrays / secondary OAM / frame
have their power-up sizes (8 / 32 / 61440 bytes).

* **Evaluation in the pipeline (`T_PPU_3_ppuDot`).** After the 256 real dots of dots 1–256 the
  evaluation fields equal those of `evalLine` (`evEq_run`: on a visible line `bgDot`, the A12
  update, `fetchDot`, `Render.pixel`, `dotEvents` keep `secOam evalN evalM evalSec evalLatch
  spr0Next oam ctrl` and status bit 5; `evalDot` respects that relation), so T-PPU-3 holds for
  the real pipeline: secondary OAM = OAM bytes of `sel = (evalSpec oam L h).1`, `evalSec = 4·|sel|`,
  `spr0Next = (0 ∈ sel)`, overflow flag `old ∨ ovf`.
* **Fetch (`T_PPU_6_fetch`).** After 320 real dots: `sprCount = |sel|`, `spr0Line = (0 ∈ sel)`;
  slot `i < |sel|` holds `sel[i]`'s attribute and X and the two pattern planes
  `sprPlane rd ctrl L Y tile attr` (address `sprAddr`: row `L − Y`, vertical flip, 8×16 bank /
  top-bottom tile; byte bit-reversed for horizontal flip); slots `|sel| ≤ i < 8` have zero
  patterns. `fstep`: one real dot of fetch phase `p` of slot `j` (phases 0, 5, 7 write; others
  idle); `fblock`: 8 dots fill slot `j`.
* **Slots persist (`slots_ppuDot`).** A dot whose new position is not 257–320 keeps the slots;
  dots 321–340, the wrap to `(L+1, 0)` and dots 1–256 of `L + 1` qualify (`to_next_line`,
  `slots_run_vis`).
* **Sprite pixel (`spritePixel_decl`, `T_PPU_6_spr`).** With `decodeSpr p = none` if `p & 3 = 0`
  else `some ($10 | p & $0F, p & $10 ≠ 0)`: at dot `x` of line `L + 1` (after `341 + x` dots),
  `decodeSpr (Render.spritePixel t x) = Declarative.spritePixel s rd x (L + 1)`. Per slot,
  `slot_bits`: the 2-bit pattern the scan reads equals `Declarative.spriteBits` (UInt16 address
  arithmetic = the `Nat` formula, `sprAddr_nat`; flip bits, `plane_bit`); the slot scan is the
  declarative `find?` (`aux_find`).
* **Mux and frame byte (`pixelOut_decl`, `frame_byte`, `T_PPU_6_spr_pixel`).** Rendering on: the
  colour `pixelOut` writes is `Declarative.pixel`'s formula (masks, priority `declIdx`, backdrop,
  greyscale) of the background index `B` (well-formed, `bgPixel_wf`) and the decoded sprite
  pixel. Composed: if `bgPixelRaw` after the dot drawing `(x, L+1)` is
  `Declarative.bgPixel s0 rd x (L+1)` (the shape of `T_PPU_6_bg`) and `s0` has `s`'s OAM, `ctrl`,
  mask, then `frame[256·(L+1) + x] = Declarative.pixel s0 rd pr x (L+1)`.

Line 0 (sprites come from the pre-render line's fetch, `sprCount := 0`) is not covered here.
-/

namespace Nes.Ppu.Proofs.StaticSpr

open Nes.Ppu Nes.Ppu.Sprites Nes.Ppu.Proofs Nes.Ppu.Proofs.SpriteEval

/-! ### Pushing projections through `if` -/

theorem ite_toUInt8 (c : Prop) [Decidable c] (x y : UInt64) :
    (if c then x else y).toUInt8 = if c then x.toUInt8 else y.toUInt8 := by split <;> rfl
theorem ite_shr (c : Prop) [Decidable c] (x y k : UInt64) :
    (if c then x else y) >>> k = if c then x >>> k else y >>> k := by split <;> rfl
theorem ite_and64 (c : Prop) [Decidable c] (x y k : UInt64) :
    (if c then x else y) &&& k = if c then x &&& k else y &&& k := by split <;> rfl
theorem ite_toNat64 (c : Prop) [Decidable c] (x y : UInt64) :
    (if c then x else y).toNat = if c then x.toNat else y.toNat := by split <;> rfl
theorem ite_bne64 (c : Prop) [Decidable c] (x y k : UInt64) :
    ((if c then x else y) != k) = if c then x != k else y != k := by split <;> rfl
theorem ite_and8 (c : Prop) [Decidable c] (x y k : UInt8) :
    (if c then x else y) &&& k = if c then x &&& k else y &&& k := by split <;> rfl

theorem and20_and20 : ∀ a : UInt8, a &&& 0x20 &&& 0x20 = a &&& 0x20 := by decide
theorem or20_and20 : ∀ a : UInt8, (a ||| 0x20) &&& 0x20 = 0x20 := by decide

/-! ### `evalDot` reads only the evaluation fields (and status bit 5 only through bit 5) -/

/-- The fields sprite evaluation reads and writes; `status` only through bit 5. -/
structure EvEq (a b : State) : Prop where
  dot : b.dot = a.dot
  scanline : b.scanline = a.scanline
  ctrl : b.ctrl = a.ctrl
  oam : b.oam = a.oam
  secOam : b.secOam = a.secOam
  evalN : b.evalN = a.evalN
  evalM : b.evalM = a.evalM
  evalSec : b.evalSec = a.evalSec
  evalLatch : b.evalLatch = a.evalLatch
  spr0Next : b.spr0Next = a.spr0Next
  st5 : b.status &&& 0x20 = a.status &&& 0x20

theorem EvEq.refl (s : State) : EvEq s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem EvEq.trans {a b c : State} (h1 : EvEq a b) (h2 : EvEq b c) : EvEq a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6, h2.7.trans h1.7, h2.8.trans h1.8, h2.9.trans h1.9, h2.10.trans h1.10,
   h2.11.trans h1.11⟩

/-- `evalStep` of `b` is `evalStep` of `a` with `b`'s status. -/
theorem evalStep_congr {a b : State} (h : EvEq a b) :
    evalStep b = evalStep { a with status := b.status } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h
  simp only [evalStep, evalAct, height, State.sprTall, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  rfl

theorem height_st (a : State) (st : UInt8) : height { a with status := st } = height a := rfl

local macro "evst_tac" : tactic => `(tactic| (
  unfold evalStep evalAct height State.sprTall
  dsimp only
  repeat' (split <;> try simp only [*, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false])
  all_goals try simp only [pack_n, pack_m, pack_sec, pack_latch, pack_st, pack_b, pack_i, pack_spr0,
    and20_and20, or20_and20, ite_and8]))

theorem evalStep_st_n (a : State) (st : UInt8) :
    (evalStep { a with status := st }).toUInt8 = (evalStep a).toUInt8 := by evst_tac
theorem evalStep_st_m (a : State) (st : UInt8) :
    (evalStep { a with status := st } >>> 8).toUInt8 = (evalStep a >>> 8).toUInt8 := by evst_tac
theorem evalStep_st_sec (a : State) (st : UInt8) :
    (evalStep { a with status := st } >>> 16).toUInt8 = (evalStep a >>> 16).toUInt8 := by evst_tac
theorem evalStep_st_latch (a : State) (st : UInt8) :
    (evalStep { a with status := st } >>> 24).toUInt8 = (evalStep a >>> 24).toUInt8 := by evst_tac
theorem evalStep_st_b (a : State) (st : UInt8) :
    (evalStep { a with status := st } >>> 48).toUInt8 = (evalStep a >>> 48).toUInt8 := by evst_tac
theorem evalStep_st_i (a : State) (st : UInt8) :
    ((evalStep { a with status := st } >>> 40) &&& 0x1F).toNat =
      ((evalStep a >>> 40) &&& 0x1F).toNat := by evst_tac
theorem evalStep_st_spr0 (a : State) (st : UInt8) :
    ((evalStep { a with status := st } >>> 56) &&& 1 != 0) = ((evalStep a >>> 56) &&& 1 != 0) := by
  evst_tac
theorem evalStep_st_5 (a : State) (st : UInt8) (h : st &&& (0x20 : UInt8) = a.status &&& 0x20) :
    (evalStep { a with status := st } >>> 32).toUInt8 &&& (0x20 : UInt8) =
      (evalStep a >>> 32).toUInt8 &&& (0x20 : UInt8) := by
  evst_tac
  all_goals exact h

theorem evalDot_congr {a b : State} (h : EvEq a b) : EvEq (evalDot a) (evalDot b) := by
  have hs := evalStep_congr h
  unfold evalDot
  dsimp only
  rw [h.dot]
  by_cases hc : (a.dot == 0 || decide (a.dot > 256)) = true
  · simp only [hc, ↓reduceIte]; exact h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rw [hs]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    constructor <;> dsimp only
    all_goals simp only [h2, h3, h4, h5, evalStep_st_i, evalStep_st_b, evalStep_st_n,
      evalStep_st_m, evalStep_st_sec, evalStep_st_latch, evalStep_st_spr0, evalStep_st_5 a _ h11]

/-! ### The other per-dot functions leave the evaluation fields alone -/

theorem evEq_bgDot (rd : UInt16 → UInt8) (s : State) : EvEq s (bgDot rd s) := by
  unfold bgDot; split
  · exact EvEq.refl s
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem evEq_fetchDot (rd : UInt16 → UInt8) (s : State) : EvEq s (fetchDot rd s) := by
  simp only [fetchDot]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hi5_none : ∀ c : UInt8, (c.toUInt16 >>> 8).toUInt8 &&& 0x20 = 0 := by decide
theorem hi5_if : ∀ (c : UInt8) (b : Bool),
    ((c.toUInt16 ||| if b then 0x4000 else 0) >>> 8).toUInt8 &&& 0x20 = 0 := by decide

theorem pixelOut_hi5 (palRd : UInt8 → UInt8) (b : UInt8) (s : State) (x : UInt8) :
    (Render.pixelOut palRd b s x >>> 8).toUInt8 &&& 0x20 = 0 := by
  unfold Render.pixelOut; dsimp only
  split
  · exact hi5_none _
  · exact hi5_if _ _

theorem or_hi5 (a c : UInt8) (h : c &&& 0x20 = 0) : (a ||| c) &&& 0x20 = a &&& 0x20 := by
  bv_decide

theorem evEq_pixel (palRd : UInt8 → UInt8) (b : UInt8) (s : State) :
    EvEq s (Render.pixel palRd b s) := by
  unfold Render.pixel; dsimp only; split
  · exact EvEq.refl s
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, or_hi5 _ _ (pixelOut_hi5 _ _ _ _)⟩

/-- On a visible line the timing events of a dot do nothing. -/
theorem dotEvents_vis (s : State) (hl : s.scanline < 240) : State.dotEvents s = s := by
  have h1 : (s.scanline == 241) = false := by
    simp only [beq_eq_false_iff_ne]; intro h; rw [h] at hl; exact absurd hl (by decide)
  have h2 : (s.scanline == 261) = false := by
    simp only [beq_eq_false_iff_ne]; intro h; rw [h] at hl; exact absurd hl (by decide)
  unfold State.dotEvents
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, ite_self]

/-- The state after `advance` and the A12 update of a dot on a visible line, before `bgDot`. -/
def preBg (s : State) : State :=
  { s with dot := s.dot + 1, a12 := busAddr { s with dot := s.dot + 1 } &&& 0x1000 != 0 }

/-- **One PPU dot on a visible line** (dots 1–338 reached, rendering enabled): background work,
evaluation, fetch, pixel; the timing events and the render-latch sample do nothing. -/
theorem ppuDot_vis (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hr : s.rendering = true) (hl : s.scanline < 240) (hd : s.dot < 339) :
    Ppu.dot rd pr s =
      Render.pixel pr (bgPixel (bgDot rd (preBg s)))
        (fetchDot rd (evalDot (bgDot rd (preBg s)))) := by
  have ha : s.advance = { s with dot := s.dot + 1 } := advance_lt s hd
  obtain ⟨k1, k2, -, k4, -⟩ := bgDot_keeps rd (preBg s)
  have hsl : (bgDot rd (preBg s)).scanline < 240 := by rw [k2]; exact hl
  obtain ⟨-, -, -, e4⟩ := evalDot_fields (bgDot rd (preBg s))
  have hact : Bg.activeLine (evalDot (bgDot rd (preBg s))).scanline = true := by
    rw [e4]; exact act_of_lt hsl
  have hren : (preBg s).rendering = true := hr
  have hfin := (pixel_fields pr (bgPixel (bgDot rd (preBg s)))
    (fetchDot rd (evalDot (bgDot rd (preBg s))))).2.2
  obtain ⟨-, -, -, f4⟩ := fetchDot_fields rd (evalDot (bgDot rd (preBg s)))
  have hpre : ({ s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } : State) = preBg s := by
    rw [ha]; rfl
  simp only [Ppu.dot, render, hpre]
  simp only [hren, hsl, ↓reduceIte, hact]
  have hsl2 : (Render.pixel pr (bgPixel (bgDot rd (preBg s)))
      (fetchDot rd (evalDot (bgDot rd (preBg s))))).scanline < 240 := by
    rw [hfin, f4, e4]; exact hsl
  rw [dotEvents_vis _ hsl2]
  have : ((Render.pixel pr (bgPixel (bgDot rd (preBg s)))
      (fetchDot rd (evalDot (bgDot rd (preBg s))))).scanline == 261) = false := by
    simp only [beq_eq_false_iff_ne]; intro h; rw [h] at hsl2; exact absurd hsl2 (by decide)
  simp only [this, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ### Evaluation inside the real pipeline -/

/-- One real PPU dot on a visible line (dot `d < 256` → `d + 1`) does to the evaluation fields
what the evaluation-only step `evalDot { · with dot := d + 1 }` does. -/
theorem evEq_ppuDot (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) {a b : State} (h : EvEq a b)
    (hr : b.rendering = true) (hl : b.scanline < 240) (hd : b.dot < 256) :
    EvEq (evalDot { a with dot := a.dot + 1 }) (Ppu.dot rd pr b) := by
  rw [ppuDot_vis rd pr b hr hl (by bv_decide)]
  have h0 : EvEq { a with dot := a.dot + 1 } (preBg b) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    exact ⟨by simp only [preBg, h1], h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact (evalDot_congr (h0.trans (evEq_bgDot rd _))).trans
    ((evEq_fetchDot rd _).trans (evEq_pixel _ _ _))

theorem evalFrom_fields (s : State) : ∀ k, (evalFrom 0 k s).scanline = s.scanline ∧
    (k = 0 ∨ (evalFrom 0 k s).dot = k.toUInt16)
  | 0 => ⟨rfl, Or.inl rfl⟩
  | k + 1 => by
    rw [evalFrom_add]
    obtain ⟨-, -, e3, e4⟩ := evalDot_fields { evalFrom 0 k s with dot := (0 + k + 1).toUInt16 }
    refine ⟨e4.trans (evalFrom_fields s k).1, Or.inr ?_⟩
    show (evalDot { evalFrom 0 k s with dot := (0 + k + 1).toUInt16 }).dot = _
    rw [e3, Nat.zero_add]

/-- **The real pipeline runs the evaluation machine.** From dot 0 of a visible line with
rendering enabled, after `k ≤ 256` real PPU dots the evaluation fields (`secOam evalN evalM
evalSec evalLatch spr0Next`, OAM, `ctrl`, status bit 5, position) are those of `k` steps of the
evaluation-only run (`evalFrom`, of which `evalLine` is the 256-step case). -/
theorem evEq_run (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s0 : State)
    (hr : s0.rendering = true) (hl : s0.scanline < 240) (hd : s0.dot = 0) :
    ∀ k ≤ 256, EvEq (evalFrom 0 k s0) (run (Ppu.dot rd pr) k s0) ∧
      (run (Ppu.dot rd pr) k s0).mask = s0.mask
  | 0, _ => ⟨EvEq.refl _, rfl⟩
  | k + 1, hk => by
    obtain ⟨ih, hm⟩ := evEq_run rd pr s0 hr hl hd k (by omega)
    obtain ⟨fs, fd⟩ := evalFrom_fields s0 k
    have hdk : (evalFrom 0 k s0).dot = k.toUInt16 := by
      rcases fd with fd | fd
      · subst fd; exact hd
      · exact fd
    have hdk' : (run (Ppu.dot rd pr) k s0).dot < 256 := by
      rw [ih.dot, hdk, UInt16.lt_iff_toNat_lt]; simp; omega
    have hrr : (run (Ppu.dot rd pr) k s0).rendering = true := by
      simp only [State.rendering, hm]; exact hr
    have hll : (run (Ppu.dot rd pr) k s0).scanline < 240 := by rw [ih.scanline, fs]; exact hl
    refine ⟨?_, ?_⟩
    · rw [evalFrom_add]
      show EvEq (evalDot { evalFrom 0 k s0 with dot := (0 + k + 1).toUInt16 }) _
      have e : (0 + k + 1).toUInt16 = (evalFrom 0 k s0).dot + 1 := by
        rw [hdk]; apply UInt16.toNat_inj.mp; simp
      rw [e]
      exact evEq_ppuDot rd pr ih hrr hll hdk'
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k s0)).mask = _
      rw [(dot_fields rd pr _).2.2, hm]

theorem evalLine_eq (s : State) : evalLine s = evalFrom 0 256 s := by
  unfold evalLine; rw [List.range_eq_range', foldl_evalFrom]

/-! ### Sprite fetches (dots 257–320) -/

theorem fetch_idx : ∀ i, i < 8 → ∀ p, p < 8 →
    ((((257 + 8 * i + p : Nat).toUInt16 < 257) || ((257 + 8 * i + p : Nat).toUInt16 > 320)) = false) ∧
    ((((257 + 8 * i + p : Nat).toUInt16 - 257) >>> 3).toNat = i) ∧
    ((((257 + 8 * i + p : Nat).toUInt16 - 257) &&& 7 == 0) = decide (p = 0)) ∧
    ((((257 + 8 * i + p : Nat).toUInt16 - 257) &&& 7 == 5) = decide (p = 5)) ∧
    ((((257 + 8 * i + p : Nat).toUInt16 - 257) &&& 7 == 7) = decide (p = 7)) := by decide

/-- The pattern byte slot `i` latches at phase 5 (`hi = false`) or 7 (`hi = true`). -/
def sprByte (rd : UInt16 → UInt8) (t : State) (i : Nat) (hi : Bool) : UInt8 :=
  let a := patAddr t i
  let b := rd (if hi then a + 8 else a)
  if i < t.sprCount.toNat then (if getByte t.sprAttr i &&& 0x40 != 0 then rev8 b else b) else 0

local macro "fetch_tac" hd:term "," j:term "," hj:term "," p:term : tactic => `(tactic| (
  obtain ⟨h1, h2, h3, h4, h5⟩ := fetch_idx $j $hj $p (by decide)
  unfold fetchDot
  rw [$hd:term]
  generalize ((257 + 8 * $j + $p : Nat).toUInt16) = D at h1 h2 h3 h4 h5 $hd:term
  simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, decide_true, decide_false,
    Bool.or_false, Bool.false_or, Bool.or_true]))

theorem fetch_p0 (rd : UInt16 → UInt8) (t : State) (j : Nat) (hj : j < 8)
    (hd : t.dot = (257 + 8 * j + 0 : Nat).toUInt16) (hl : t.scanline < 240) :
    fetchDot rd t =
      { t with sprCount := if j = 0 then t.evalSec >>> 2 else t.sprCount,
               spr0Line := if j = 0 then t.spr0Next else t.spr0Line,
               sprAttr := t.sprAttr.set! j (getByte t.secOam (4 * j + 2)),
               sprX := t.sprX.set! j (getByte t.secOam (4 * j + 3)) } := by
  fetch_tac hd, j, hj, 0
  by_cases h0 : j = 0
  · subst h0; simp only [hl, ↓reduceIte, beq_self_eq_true]
  · have : (j == 0) = false := by simp [h0]
    simp only [h0, this, Bool.false_eq_true, ↓reduceIte]
    rw [hd]

theorem fetch_p5 (rd : UInt16 → UInt8) (t : State) (j : Nat) (hj : j < 8)
    (hd : t.dot = (257 + 8 * j + 5 : Nat).toUInt16) :
    fetchDot rd t = { t with sprPatLo := t.sprPatLo.set! j (sprByte rd t j false) } := by
  fetch_tac hd, j, hj, 5
  rfl

theorem fetch_p7 (rd : UInt16 → UInt8) (t : State) (j : Nat) (hj : j < 8)
    (hd : t.dot = (257 + 8 * j + 7 : Nat).toUInt16) :
    fetchDot rd t = { t with sprPatHi := t.sprPatHi.set! j (sprByte rd t j true) } := by
  fetch_tac hd, j, hj, 7
  rfl

theorem fetch_idle (rd : UInt16 → UInt8) (t : State) (j p : Nat) (hj : j < 8) (hp : p < 8)
    (h0 : p ≠ 0) (h5 : p ≠ 5) (h7 : p ≠ 7) (hd : t.dot = (257 + 8 * j + p : Nat).toUInt16) :
    fetchDot rd t = t := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := fetch_idx j hj p hp
  unfold fetchDot
  rw [hd]
  generalize ((257 + 8 * j + p : Nat).toUInt16) = D at h1 h2 h3 h4 h6
  simp only [h1, h3, h4, h6, h0, h5, h7, Bool.false_eq_true, ↓reduceIte, decide_false, Bool.or_false]

/-- `bgDot` after `preBg` touches only the background fields, `v`, `a12` and `dot`. -/
theorem bgPre_fields (rd : UInt16 → UInt8) (s : State) :
    let t := bgDot rd (preBg s)
    t.dot = s.dot + 1 ∧ t.scanline = s.scanline ∧ t.ctrl = s.ctrl ∧ t.secOam = s.secOam ∧
    t.evalSec = s.evalSec ∧ t.spr0Next = s.spr0Next ∧ t.mask = s.mask ∧ t.oam = s.oam ∧
    t.sprCount = s.sprCount ∧ t.spr0Line = s.spr0Line ∧ t.sprAttr = s.sprAttr ∧
    t.sprX = s.sprX ∧ t.sprPatLo = s.sprPatLo ∧ t.sprPatHi = s.sprPatHi := by
  unfold bgDot preBg; split <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem patAddr_congr {a b : State} (h1 : b.secOam = a.secOam) (h2 : b.scanline = a.scanline)
    (h3 : b.ctrl = a.ctrl) (i : Nat) : patAddr b i = patAddr a i := by
  unfold patAddr height State.sprTall State.sprTable; rw [h1, h2, h3]

theorem sprByte_congr (rd : UInt16 → UInt8) {a b : State} (h1 : b.secOam = a.secOam)
    (h2 : b.scanline = a.scanline) (h3 : b.ctrl = a.ctrl) (h4 : b.sprCount = a.sprCount)
    (h5 : b.sprAttr = a.sprAttr) (i : Nat) (hi : Bool) : sprByte rd b i hi = sprByte rd a i hi := by
  unfold sprByte; rw [patAddr_congr h1 h2 h3, h4, h5]

/-- A real PPU dot that reaches a sprite-fetch dot (257–320) of a visible line is
`fetchDot` after the background work: evaluation and pixel output are idle there. -/
theorem ppuDot_fetch (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hr : s.rendering = true) (hl : s.scanline < 240) (hd1 : 256 ≤ s.dot) (hd2 : s.dot < 320) :
    Ppu.dot rd pr s = fetchDot rd (bgDot rd (preBg s)) := by
  rw [ppuDot_vis rd pr s hr hl (by bv_decide)]
  obtain ⟨k1, -⟩ := bgPre_fields rd s
  have hd : (bgDot rd (preBg s)).dot = s.dot + 1 := k1
  have he : evalDot (bgDot rd (preBg s)) = bgDot rd (preBg s) := by
    unfold evalDot
    have : ((bgDot rd (preBg s)).dot == 0 || decide ((bgDot rd (preBg s)).dot > 256)) = true := by
      rw [hd]; bv_decide
    simp only [this, ↓reduceIte]
  rw [he]
  obtain ⟨-, -, f3, -⟩ := fetchDot_fields rd (bgDot rd (preBg s))
  apply pixel_outside
  right; right; rw [f3, hd]; bv_decide

/-- One real PPU dot at fetch phase `p` of slot `j` (it reaches dot `257 + 8j + p`). -/
theorem fstep (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State) (j p : Nat) (hj : j < 8)
    (hp : p < 8) (hr : s.rendering = true) (hl : s.scanline < 240)
    (hd : s.dot = (256 + 8 * j + p : Nat).toUInt16) :
    (Ppu.dot rd pr s).dot = (256 + 8 * j + p + 1 : Nat).toUInt16 ∧ (Ppu.dot rd pr s).scanline = s.scanline ∧ (Ppu.dot rd pr s).ctrl = s.ctrl ∧
    (Ppu.dot rd pr s).secOam = s.secOam ∧ (Ppu.dot rd pr s).evalSec = s.evalSec ∧ (Ppu.dot rd pr s).spr0Next = s.spr0Next ∧ (Ppu.dot rd pr s).mask = s.mask ∧
    (Ppu.dot rd pr s).oam = s.oam ∧
    (Ppu.dot rd pr s).sprCount = (if p = 0 ∧ j = 0 then s.evalSec >>> 2 else s.sprCount) ∧
    (Ppu.dot rd pr s).spr0Line = (if p = 0 ∧ j = 0 then s.spr0Next else s.spr0Line) ∧
    (Ppu.dot rd pr s).sprAttr = (if p = 0 then s.sprAttr.set! j (getByte s.secOam (4 * j + 2)) else s.sprAttr) ∧
    (Ppu.dot rd pr s).sprX = (if p = 0 then s.sprX.set! j (getByte s.secOam (4 * j + 3)) else s.sprX) ∧
    (Ppu.dot rd pr s).sprPatLo = (if p = 5 then s.sprPatLo.set! j (sprByte rd s j false) else s.sprPatLo) ∧
    (Ppu.dot rd pr s).sprPatHi = (if p = 7 then s.sprPatHi.set! j (sprByte rd s j true) else s.sprPatHi) := by
  have hd1 : 256 ≤ s.dot := by rw [hd, UInt16.le_iff_toNat_le]; simp; omega
  have hd2 : s.dot < 320 := by rw [hd, UInt16.lt_iff_toNat_lt]; simp; omega
  rw [ppuDot_fetch rd pr s hr hl hd1 hd2]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ := bgPre_fields rd s
  generalize bgDot rd (preBg s) = u at k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 ⊢
  have hdu : u.dot = (257 + 8 * j + p : Nat).toUInt16 := by
    rw [k1, hd]; apply UInt16.toNat_inj.mp; simp; omega
  have hdt : u.dot = (256 + 8 * j + p + 1 : Nat).toUInt16 := by
    rw [hdu]; congr 1; omega
  have hsb : ∀ hi, sprByte rd u j hi = sprByte rd s j hi :=
    sprByte_congr rd k4 k2 k3 k9 k11 j
  by_cases h0 : p = 0
  · subst h0
    rw [fetch_p0 rd u j hj hdu (by rw [k2]; exact hl)]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [and_self, ↓reduceIte, Nat.reduceMul, Nat.zero_add]
      exact ⟨by rw [hdu], k2, k3, k4, k5, k6, k7, k8, by rw [k5], by rw [k6], by rw [k11, k4],
        by rw [k12, k4], k13, k14⟩
    · simp only [hj0, and_false, ↓reduceIte]
      exact ⟨hdt, k2, k3, k4, k5, k6, k7, k8, k9, k10, by rw [k11, k4],
        by rw [k12, k4], k13, k14⟩
  · by_cases h5 : p = 5
    · subst h5
      rw [fetch_p5 rd u j hj hdu]
      simp only [h0, false_and, ↓reduceIte, hsb]
      exact ⟨hdt, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, by rw [k13], k14⟩
    · by_cases h7 : p = 7
      · subst h7
        rw [fetch_p7 rd u j hj hdu]
        simp only [h0, false_and, ↓reduceIte, hsb]
        exact ⟨hdt, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, by rw [k14]⟩
      · rw [fetch_idle rd u j p hj hp h0 h5 h7 hdu]
        simp only [h0, h5, h7, false_and, ↓reduceIte]
        exact ⟨hdt, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩

/-- The fields the sprite fetch reads or writes, other than `dot`. -/
structure SprEq (a b : State) : Prop where
  scanline : b.scanline = a.scanline
  ctrl : b.ctrl = a.ctrl
  secOam : b.secOam = a.secOam
  evalSec : b.evalSec = a.evalSec
  spr0Next : b.spr0Next = a.spr0Next
  mask : b.mask = a.mask
  oam : b.oam = a.oam
  sprCount : b.sprCount = a.sprCount
  spr0Line : b.spr0Line = a.spr0Line
  sprAttr : b.sprAttr = a.sprAttr
  sprX : b.sprX = a.sprX
  sprPatLo : b.sprPatLo = a.sprPatLo
  sprPatHi : b.sprPatHi = a.sprPatHi

theorem SprEq.refl (s : State) : SprEq s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SprEq.trans {a b c : State} (h1 : SprEq a b) (h2 : SprEq b c) : SprEq a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6, h2.7.trans h1.7, h2.8.trans h1.8, h2.9.trans h1.9, h2.10.trans h1.10,
   h2.11.trans h1.11, h2.12.trans h1.12, h2.13.trans h1.13⟩

/-- An idle fetch phase (1–4, 6) changes no sprite field. -/
theorem fstep_idle (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State) (j p : Nat) (hj : j < 8)
    (hp : p < 8) (h0 : p ≠ 0) (h5 : p ≠ 5) (h7 : p ≠ 7) (hr : s.rendering = true)
    (hl : s.scanline < 240) (hd : s.dot = (256 + 8 * j + p : Nat).toUInt16) :
    SprEq s (Ppu.dot rd pr s) ∧ (Ppu.dot rd pr s).dot = (256 + 8 * j + (p + 1) : Nat).toUInt16 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ :=
    fstep rd pr s j p hj hp hr hl hd
  simp only [h0, h5, h7, false_and, ↓reduceIte] at a9 a10 a11 a12 a13 a14
  exact ⟨⟨a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩, by rw [a1]; rfl⟩

/-- The pattern byte that slot `i` should hold for the line after `u`'s (spec of `sprByte` in
terms of the inputs at dot 256: secondary OAM, line, `ctrl`, the count `evalSec / 4`). -/
def slotByte (rd : UInt16 → UInt8) (u : State) (i : Nat) (hi : Bool) : UInt8 :=
  let a := patAddr u i
  let b := rd (if hi then a + 8 else a)
  if i < (u.evalSec >>> 2).toNat then
    (if getByte u.secOam (4 * i + 2) &&& 0x40 != 0 then rev8 b else b) else 0

/-- Slot `i` of `t` holds sprite `i` of `u`'s secondary OAM. -/
def SlotOK (rd : UInt16 → UInt8) (u t : State) (i : Nat) : Prop :=
  getByte t.sprAttr i = getByte u.secOam (4 * i + 2) ∧ getByte t.sprX i = getByte u.secOam (4 * i + 3) ∧
  getByte t.sprPatLo i = slotByte rd u i false ∧ getByte t.sprPatHi i = slotByte rd u i true

/-- Fetch invariant at dot `256 + 8j` of the line of `u` (the state at dot 256). -/
structure FInv (rd : UInt16 → UInt8) (u : State) (j : Nat) (t : State) : Prop where
  dot : t.dot = (256 + 8 * j : Nat).toUInt16
  scanline : t.scanline = u.scanline
  ctrl : t.ctrl = u.ctrl
  secOam : t.secOam = u.secOam
  evalSec : t.evalSec = u.evalSec
  spr0Next : t.spr0Next = u.spr0Next
  mask : t.mask = u.mask
  oam : t.oam = u.oam
  szA : t.sprAttr.size = 8
  szX : t.sprX.size = 8
  szL : t.sprPatLo.size = 8
  szH : t.sprPatHi.size = 8
  cnt : 0 < j → t.sprCount = u.evalSec >>> 2 ∧ t.spr0Line = u.spr0Next
  slots : ∀ i < j, SlotOK rd u t i

theorem getByte_set8 (a : ByteArray) (ha : a.size = 8) (j i : Nat) (hj : j < 8) (v : UInt8) :
    getByte (a.set! j v) i = if j = i then v else getByte a i := by
  rw [getByte_set]
  by_cases h : j = i
  · simp [h, ha] at hj ⊢; omega
  · simp [h]

theorem sfs_run_add (f : State → State) (a b : Nat) (s : State) :
    run f (a + b) s = run f b (run f a s) := by
  induction b with
  | zero => rfl
  | succ b ih => show f (run f (a + b) s) = f (run f b (run f a s)); rw [ih]

theorem sprByte_slot (rd : UInt16 → UInt8) {t u : State} (j : Nat) (hi : Bool)
    (h1 : t.secOam = u.secOam) (h2 : t.scanline = u.scanline) (h3 : t.ctrl = u.ctrl)
    (hc : t.sprCount = u.evalSec >>> 2) (ha : getByte t.sprAttr j = getByte u.secOam (4 * j + 2)) :
    sprByte rd t j hi = slotByte rd u j hi := by
  unfold sprByte slotByte; rw [patAddr_congr h1 h2 h3, hc, ha]

theorem SprEq.ren {a b : State} (h : SprEq a b) (hr : a.rendering = true) : b.rendering = true := by
  simp only [State.rendering, h.mask]; exact hr
theorem SprEq.vis {a b : State} (h : SprEq a b) (hl : a.scanline < 240) : b.scanline < 240 := by
  rw [h.scanline]; exact hl

theorem n05 : (0 : Nat) ≠ 5 := by decide
theorem n07 : (0 : Nat) ≠ 7 := by decide
theorem n50 : (5 : Nat) ≠ 0 := by decide
theorem n57 : (5 : Nat) ≠ 7 := by decide
theorem n70 : (7 : Nat) ≠ 0 := by decide
theorem n75 : (7 : Nat) ≠ 5 := by decide

/-- One slot: the 8 real PPU dots `257 + 8j … 264 + 8j`. -/
theorem fblock (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (u : State) (j : Nat) (t : State)
    (hj : j < 8) (hr : u.rendering = true) (hl : u.scanline < 240) (h : FInv rd u j t) :
    FInv rd u (j + 1) (run (Ppu.dot rd pr) 8 t) := by
  obtain ⟨hd, e1, e2, e3, e4, e5, e6, e7, szA, szX, szL, szH, hc, hs⟩ := h
  have hrt : t.rendering = true := by simp only [State.rendering, e6]; exact hr
  have hlt : t.scanline < 240 := by rw [e1]; exact hl
  -- phase 0: attribute, X (and the count at slot 0)
  rw [show (8 : Nat) = 1 + 7 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 7 (Ppu.dot rd pr t))
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ :=
    fstep rd pr t j 0 hj (by decide) hrt hlt (by rw [hd]; rfl)
  simp only [true_and, ↓reduceIte, n05, n07] at a9 a10 a11 a12 a13 a14
  generalize Ppu.dot rd pr t = t1 at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 ⊢
  have hr1 : t1.rendering = true := by simp only [State.rendering, a7]; exact hrt
  have hl1 : t1.scanline < 240 := by rw [a2]; exact hlt
  -- phases 1–4: idle
  rw [show (7 : Nat) = 1 + 6 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 6 (Ppu.dot rd pr t1))
  obtain ⟨q2, d2⟩ := fstep_idle rd pr t1 j 1 hj (by decide) (by decide) (by decide) (by decide)
    hr1 hl1 (by rw [a1])
  generalize Ppu.dot rd pr t1 = t2 at q2 d2 ⊢
  rw [show (6 : Nat) = 1 + 5 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 5 (Ppu.dot rd pr t2))
  obtain ⟨q3, d3⟩ := fstep_idle rd pr t2 j 2 hj (by decide) (by decide) (by decide) (by decide)
    (q2.ren hr1) (q2.vis hl1) (by rw [d2])
  generalize Ppu.dot rd pr t2 = t3 at q3 d3 ⊢
  have q13 := q2.trans q3
  rw [show (5 : Nat) = 1 + 4 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 4 (Ppu.dot rd pr t3))
  obtain ⟨q4, d4⟩ := fstep_idle rd pr t3 j 3 hj (by decide) (by decide) (by decide) (by decide)
    (q13.ren hr1) (q13.vis hl1) (by rw [d3])
  generalize Ppu.dot rd pr t3 = t4 at q4 d4 ⊢
  have q14 := q13.trans q4
  rw [show (4 : Nat) = 1 + 3 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 3 (Ppu.dot rd pr t4))
  obtain ⟨q5, d5⟩ := fstep_idle rd pr t4 j 4 hj (by decide) (by decide) (by decide) (by decide)
    (q14.ren hr1) (q14.vis hl1) (by rw [d4])
  generalize Ppu.dot rd pr t4 = t5 at q5 d5 ⊢
  have q15 := q14.trans q5
  -- phase 5: pattern low plane
  rw [show (3 : Nat) = 1 + 2 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (run (Ppu.dot rd pr) 2 (Ppu.dot rd pr t5))
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ :=
    fstep rd pr t5 j 5 hj (by decide) (q15.ren hr1) (q15.vis hl1) (by rw [d5])
  simp only [↓reduceIte, n50, n57, false_and] at b9 b10 b11 b12 b13 b14
  have hb := sprByte_slot rd (t := t5) (u := u) j false
    (by rw [q15.secOam, a4, e3]) (by rw [q15.scanline, a2, e1]) (by rw [q15.ctrl, a3, e2])
    (by
      rw [q15.sprCount, a9]
      by_cases h0 : j = 0
      · simp only [h0, ↓reduceIte]; rw [e4]
      · simp only [h0, ↓reduceIte]; exact (hc (by omega)).1)
    (by rw [q15.sprAttr, a11, getByte_set8 _ szA j j hj, e3]; simp only [↓reduceIte])
  generalize Ppu.dot rd pr t5 = t6 at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ⊢
  -- phase 6: idle
  rw [show (2 : Nat) = 1 + 1 from rfl, sfs_run_add]
  change FInv rd u (j + 1) (Ppu.dot rd pr (Ppu.dot rd pr t6))
  have hr6 : t6.rendering = true := by simp only [State.rendering, b7]; exact q15.ren hr1
  have hl6 : t6.scanline < 240 := by rw [b2]; exact q15.vis hl1
  obtain ⟨q7, d7⟩ := fstep_idle rd pr t6 j 6 hj (by decide) (by decide) (by decide) (by decide)
    hr6 hl6 (by rw [b1])
  generalize Ppu.dot rd pr t6 = t7 at q7 d7 ⊢
  -- phase 7: pattern high plane
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ :=
    fstep rd pr t7 j 7 hj (by decide) (q7.ren hr6) (q7.vis hl6) (by rw [d7])
  simp only [↓reduceIte, n70, n75, false_and] at c9 c10 c11 c12 c13 c14
  have hc' := sprByte_slot rd (t := t7) (u := u) j true
    (by rw [q7.secOam, b4, q15.secOam, a4, e3]) (by rw [q7.scanline, b2, q15.scanline, a2, e1])
    (by rw [q7.ctrl, b3, q15.ctrl, a3, e2])
    (by
      rw [q7.sprCount, b9, q15.sprCount, a9]
      by_cases h0 : j = 0
      · simp only [h0, ↓reduceIte]; rw [e4]
      · simp only [h0, ↓reduceIte]; exact (hc (by omega)).1)
    (by rw [q7.sprAttr, b11, q15.sprAttr, a11, getByte_set8 _ szA j j hj, e3]; simp only [↓reduceIte])
  generalize Ppu.dot rd pr t7 = t8 at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 ⊢
  -- assemble
  have hA : t8.sprAttr = t.sprAttr.set! j (getByte t.secOam (4 * j + 2)) := by
    rw [c11, q7.sprAttr, b11, q15.sprAttr, a11]
  have hX : t8.sprX = t.sprX.set! j (getByte t.secOam (4 * j + 3)) := by
    rw [c12, q7.sprX, b12, q15.sprX, a12]
  have hL : t8.sprPatLo = t.sprPatLo.set! j (sprByte rd t5 j false) := by
    rw [c13, q7.sprPatLo, b13, q15.sprPatLo, a13]
  have hH : t8.sprPatHi = t.sprPatHi.set! j (sprByte rd t7 j true) := by
    rw [c14, q7.sprPatHi, b14, q15.sprPatHi, a14]
  refine ⟨?_, by rw [c2, q7.scanline, b2, q15.scanline, a2, e1], by rw [c3, q7.ctrl, b3, q15.ctrl, a3, e2],
    by rw [c4, q7.secOam, b4, q15.secOam, a4, e3], by rw [c5, q7.evalSec, b5, q15.evalSec, a5, e4],
    by rw [c6, q7.spr0Next, b6, q15.spr0Next, a6, e5], by rw [c7, q7.mask, b7, q15.mask, a7, e6],
    by rw [c8, q7.oam, b8, q15.oam, a8, e7],
    by rw [hA, ByteArray.size_set!, szA], by rw [hX, ByteArray.size_set!, szX],
    by rw [hL, ByteArray.size_set!, szL], by rw [hH, ByteArray.size_set!, szH], ?_, ?_⟩
  · rw [c1]; congr 1
  · intro _
    rw [c9, q7.sprCount, b9, q15.sprCount, a9, c10, q7.spr0Line, b10, q15.spr0Line, a10]
    by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte]; rw [e4, e5]; exact ⟨rfl, rfl⟩
    · simp only [h0, ↓reduceIte]; exact hc (by omega)
  · intro i hi
    rw [SlotOK, hA, hX, hL, hH, getByte_set8 _ szA j i hj, getByte_set8 _ szX j i hj,
      getByte_set8 _ szL j i hj, getByte_set8 _ szH j i hj]
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte, hb, hc', e3, and_self]
    · simp only [hij, ↓reduceIte]
      exact hs i (by omega)

theorem fetch_all (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (u : State)
    (hr : u.rendering = true) (hl : u.scanline < 240) (hd : u.dot = 256)
    (szA : u.sprAttr.size = 8) (szX : u.sprX.size = 8) (szL : u.sprPatLo.size = 8)
    (szH : u.sprPatHi.size = 8) : ∀ j ≤ 8, FInv rd u j (run (Ppu.dot rd pr) (8 * j) u)
  | 0, _ => ⟨by show u.dot = _; rw [hd]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, szA, szX, szL, szH,
      fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    rw [show 8 * (j + 1) = 8 * j + 8 by omega, sfs_run_add]
    exact fblock rd pr u j _ (by omega) hr hl (fetch_all rd pr u hr hl hd szA szX szL szH j (by omega))

/-- Low-plane pattern address of a sprite with top byte `y`, tile `tile`, attribute `attr` for
the line after `L` (`ctrl` gives the height and the 8×8 table): the body of `patAddr`. -/
def sprAddr (c : UInt8) (L : UInt16) (y tile attr : UInt8) : UInt16 :=
  let tile := tile.toUInt16
  let h : UInt16 := if c &&& 0x20 != 0 then 16 else 8
  let row : UInt16 := (L - y.toUInt16) &&& (h - 1)
  let row : UInt16 := if attr &&& 0x80 != 0 then h - 1 - row else row
  if c &&& 0x20 != 0 then
    let bank : UInt16 := (tile &&& (1 : UInt16)) <<< (12 : UInt16)
    let t2 : UInt16 := (tile &&& (0xFE : UInt16)) + (row >>> (3 : UInt16))
    bank + (t2 <<< 4) + (row &&& 7)
  else
    (if c &&& 0x08 != 0 then (0x1000 : UInt16) else 0) + (tile <<< 4) + row

theorem patAddr_eq (s : State) (i : Nat) :
    patAddr s i = sprAddr s.ctrl s.scanline (getByte s.secOam (4 * i)) (getByte s.secOam (4 * i + 1))
      (getByte s.secOam (4 * i + 2)) := rfl

/-- The pattern byte (plane `hi`) of a sprite fetched for the line after `L`, horizontal flip
applied (bit 7 = leftmost pixel). -/
def sprPlane (rd : UInt16 → UInt8) (c : UInt8) (L : UInt16) (y tile attr : UInt8) (hi : Bool) :
    UInt8 :=
  let a := sprAddr c L y tile attr
  let b := rd (if hi then a + 8 else a)
  if attr &&& 0x40 != 0 then rev8 b else b

/-! ### Outside dots 257–320 the sprite slots do not move -/

/-- The sprite slots (what the pixel output reads) and the dot. -/
structure SlotEq (a b : State) : Prop where
  dot : b.dot = a.dot
  sprCount : b.sprCount = a.sprCount
  spr0Line : b.spr0Line = a.spr0Line
  sprAttr : b.sprAttr = a.sprAttr
  sprX : b.sprX = a.sprX
  sprPatLo : b.sprPatLo = a.sprPatLo
  sprPatHi : b.sprPatHi = a.sprPatHi

theorem SlotEq.trans {a b c : State} (h1 : SlotEq a b) (h2 : SlotEq b c) : SlotEq a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6, h2.7.trans h1.7⟩
theorem SlotEq.ite {c : Prop} [Decidable c] {s a b : State} (ha : SlotEq s a) (hb : SlotEq s b) :
    SlotEq s (if c then a else b) := by split <;> assumption

local macro "sloteq_tac" : tactic => `(tactic| (constructor <;>
  simp only [apply_ite State.dot, apply_ite State.sprCount, apply_ite State.spr0Line,
    apply_ite State.sprAttr, apply_ite State.sprX, apply_ite State.sprPatLo,
    apply_ite State.sprPatHi, ite_self]))

theorem slotEq_bgDot (rd : UInt16 → UInt8) (s : State) : SlotEq s (bgDot rd s) := by
  simp only [bgDot]; sloteq_tac
theorem slotEq_evalDot (s : State) : SlotEq s (evalDot s) := by
  simp only [evalDot]; sloteq_tac
theorem slotEq_pixel (pr : UInt8 → UInt8) (b : UInt8) (s : State) :
    SlotEq s (Render.pixel pr b s) := by
  simp only [Render.pixel]; sloteq_tac
theorem slotEq_dotEvents (s : State) : SlotEq s (State.dotEvents s) := by
  simp only [State.dotEvents]; sloteq_tac

theorem fetchDot_idle (rd : UInt16 → UInt8) (t : State) (h : t.dot < 257 ∨ t.dot > 320) :
    fetchDot rd t = t := by
  unfold fetchDot
  have : (t.dot < 257 || t.dot > 320) = true := by
    rcases h with h | h <;> simp [h]
  simp only [this, ↓reduceIte]

/-- A real PPU dot whose new position is not a sprite-fetch dot (257–320) keeps the slots. -/
theorem slotEq_ppuDot (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (h : s.advance.dot < 257 ∨ s.advance.dot > 320) :
    SlotEq s.advance (Ppu.dot rd pr s) := by
  have h1 : SlotEq s.advance { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have c1 : ∀ t, SlotEq s.advance t → SlotEq s.advance (bgDot rd t) :=
    fun t h => h.trans (slotEq_bgDot rd t)
  have c2 : ∀ t, SlotEq s.advance t → SlotEq s.advance (evalDot t) :=
    fun t h => h.trans (slotEq_evalDot t)
  have c3 : ∀ t, SlotEq s.advance t → SlotEq s.advance (fetchDot rd t) := by
    intro t ht
    rw [fetchDot_idle rd t (by rw [ht.dot]; exact h)]; exact ht
  have c4 : ∀ b t, SlotEq s.advance t → SlotEq s.advance (Render.pixel pr b t) :=
    fun b t h => h.trans (slotEq_pixel pr b t)
  have hr : SlotEq s.advance (render rd pr s.advance) := by
    unfold render
    dsimp only
    exact SlotEq.ite (c4 _ _ (SlotEq.ite (c3 _ (SlotEq.ite (c2 _ (c1 _ h1)) (c1 _ h1)))
      (SlotEq.ite (c2 _ (c1 _ h1)) (c1 _ h1)))) (c4 _ _ h1)
  have he := hr.trans (slotEq_dotEvents _)
  unfold Ppu.dot
  dsimp only
  exact SlotEq.ite (he.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) he

theorem slotEq_advance (s : State) :
    s.advance.sprCount = s.sprCount ∧ s.advance.spr0Line = s.spr0Line ∧
    s.advance.sprAttr = s.sprAttr ∧ s.advance.sprX = s.sprX ∧ s.advance.sprPatLo = s.sprPatLo ∧
    s.advance.sprPatHi = s.sprPatHi := by
  unfold State.advance; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The slots, ignoring the dot. -/
structure Slots (a b : State) : Prop where
  sprCount : b.sprCount = a.sprCount
  spr0Line : b.spr0Line = a.spr0Line
  sprAttr : b.sprAttr = a.sprAttr
  sprX : b.sprX = a.sprX
  sprPatLo : b.sprPatLo = a.sprPatLo
  sprPatHi : b.sprPatHi = a.sprPatHi

theorem Slots.refl (s : State) : Slots s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Slots.trans {a b c : State} (h1 : Slots a b) (h2 : Slots b c) : Slots a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6⟩

theorem slots_ppuDot (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (h : s.advance.dot < 257 ∨ s.advance.dot > 320) : Slots s (Ppu.dot rd pr s) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := slotEq_advance s
  obtain ⟨-, b2, b3, b4, b5, b6, b7⟩ := slotEq_ppuDot rd pr s h
  exact ⟨b2.trans a1, b3.trans a2, b4.trans a3, b5.trans a4, b6.trans a5, b7.trans a6⟩

/-- Dots 1–256 of a visible line keep the slots (from dot 0). -/
theorem slots_run_vis (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hl : s.scanline < 240) (hd : s.dot = 0) :
    ∀ k ≤ 256, Slots s (run (Ppu.dot rd pr) k s) ∧ (run (Ppu.dot rd pr) k s).dot = k.toUInt16 ∧
      (run (Ppu.dot rd pr) k s).scanline = s.scanline
  | 0, _ => ⟨Slots.refl s, hd, rfl⟩
  | k + 1, hk => by
    obtain ⟨ih, hdk, hsk⟩ := slots_run_vis rd pr s hl hd k (by omega)
    have hlt : (run (Ppu.dot rd pr) k s).dot < 340 := by
      rw [hdk, UInt16.lt_iff_toNat_lt]; simp; omega
    have ha := advance_vis _ (by rw [hsk]; exact hl) hlt
    have had : (run (Ppu.dot rd pr) k s).advance.dot = (k + 1).toUInt16 := by
      rw [ha, hdk]; apply UInt16.toNat_inj.mp; simp
    obtain ⟨f1, f2, -⟩ := dot_fields rd pr (run (Ppu.dot rd pr) k s)
    refine ⟨ih.trans (slots_ppuDot rd pr _ (Or.inl ?_)), ?_, ?_⟩
    · rw [had, UInt16.lt_iff_toNat_lt]; simp; omega
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k s)).dot = _
      rw [f1, had]
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k s)).scanline = _
      rw [f2, ha, hsk]

theorem and_FE : ∀ t : UInt8, (t.toUInt16 &&& 0xFE).toNat = t.toNat - t.toNat % 2 := by decide
theorem bank_nat : ∀ t : UInt8, ((t.toUInt16 &&& 1) <<< 12).toNat = 4096 * (t.toNat % 2) := by decide

theorem tall_nat (t : UInt8) (r : UInt16) (hr : r.toNat < 16) :
    (((t.toUInt16 &&& 1) <<< (12 : UInt16)) + (((t.toUInt16 &&& (0xFE : UInt16)) + (r >>> (3 : UInt16))) <<< 4) + (r &&& 7)).toNat =
      4096 * (t.toNat % 2) + 16 * (t.toNat - t.toNat % 2 + r.toNat / 8) + r.toNat % 8 := by
  have h1 := bank_nat t
  have h2 := and_FE t
  have ht := t.toNat_lt
  have e3 : (r >>> (3 : UInt16)).toNat = r.toNat / 8 := by
    rw [UInt16.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have e4 : (r &&& 7).toNat = r.toNat % 8 := by
    rw [UInt16.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 3
  generalize (t.toUInt16 &&& (0xFE : UInt16)) = A at h2
  generalize ((t.toUInt16 &&& 1) <<< (12 : UInt16)) = B at h1
  have e5 : (A + (r >>> (3 : UInt16))).toNat = A.toNat + r.toNat / 8 := by
    rw [UInt16.toNat_add, e3]; omega
  have e6 : ((A + (r >>> (3 : UInt16))) <<< 4).toNat = 16 * (A.toNat + r.toNat / 8) := by
    rw [UInt16.toNat_shiftLeft, e5]; simp [Nat.shiftLeft_eq]; omega
  rw [UInt16.toNat_add, UInt16.toNat_add, e6, e4, h1, h2]; omega

theorem short_nat (c : UInt8) (t : UInt8) (r : UInt16) (hr : r.toNat < 8) :
    ((if c &&& 0x08 != 0 then (0x1000 : UInt16) else 0) + (t.toUInt16 <<< 4) + r).toNat =
      (if c &&& 0x08 != 0 then 0x1000 else 0) + 16 * t.toNat + r.toNat := by
  have ht := t.toNat_lt
  have e : (t.toUInt16 <<< 4).toNat = 16 * t.toNat := by
    rw [UInt16.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  split <;> rw [UInt16.toNat_add, UInt16.toNat_add, e] <;> simp <;> omega

theorem rev_shr (b k : UInt8) (hk : k < 8) : (rev8 b >>> (7 - k)) &&& 1 = (b >>> k) &&& 1 := by
  unfold rev8; bv_decide

theorem shr_toNat (b j : UInt8) (hj : j < 8) : ((b >>> j) &&& 1).toNat = b.toNat / 2 ^ j.toNat % 2 := by
  have hj' : j.toNat < 8 := hj
  rw [UInt8.toNat_and, UInt8.toNat_shiftRight, show UInt8.toNat 1 = 1 from rfl, Nat.and_one_is_mod,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hj']

theorem sub7 (k : UInt8) (hk : k < 8) : (7 - k).toNat = 7 - k.toNat := by
  have hk' : k.toNat < 8 := hk
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; simp; omega)]; rfl

theorem pack2 (a b : UInt8) : ((a &&& (1 : UInt8)) ||| ((b &&& (1 : UInt8)) <<< (1 : UInt8))).toNat =
    (a &&& (1 : UInt8)).toNat + 2 * (b &&& (1 : UInt8)).toNat := by
  have e : ((a &&& (1 : UInt8)) ||| ((b &&& (1 : UInt8)) <<< (1 : UInt8))) =
      (a &&& (1 : UInt8)) + 2 * (b &&& (1 : UInt8)) := by bv_decide
  have h1 : (a &&& (1 : UInt8)).toNat ≤ 1 := by rw [UInt8.toNat_and]; exact Nat.and_le_right
  have h2 : (b &&& (1 : UInt8)).toNat ≤ 1 := by rw [UInt8.toNat_and]; exact Nat.and_le_right
  rw [e, UInt8.toNat_add, UInt8.toNat_mul]; simp; omega

theorem bit7_iff : ∀ a : UInt8, (a &&& 0x80 != 0) = decide (Declarative.bit a 7 = 1) := by decide
theorem bit6_iff : ∀ a : UInt8, (a &&& 0x40 != 0) = decide (Declarative.bit a 6 = 1) := by decide
theorem bit5_iff : ∀ a : UInt8, (a &&& 0x20 != 0) = decide (Declarative.bit a 5 = 1) := by decide

/-- Sprite height in rows for `ctrl` byte `c`. -/
def hgtC (c : UInt8) : Nat := if c &&& 0x20 != 0 then 16 else 8

/-- The pattern-table address `Declarative.spriteBits` computes, for sprite row `r0` (counted from
the sprite top, before the vertical flip). -/
def addrSpec (c tile attr : UInt8) (r0 : Nat) : Nat :=
  let row := if Declarative.bit attr 7 = 1 then hgtC c - 1 - r0 else r0
  if c &&& 0x20 != 0 then 0x1000 * (tile.toNat % 2) + 16 * (tile.toNat - tile.toNat % 2 + row / 8) + row % 8
  else (if c &&& 0x08 != 0 then 0x1000 else 0) + 16 * tile.toNat + row

theorem and15 (r : UInt16) (h : r.toNat < 16) : (r &&& 15).toNat = r.toNat := by
  rw [UInt16.toNat_and]
  rw [show UInt16.toNat 15 = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
theorem and7 (r : UInt16) (h : r.toNat < 8) : (r &&& 7).toNat = r.toNat := by
  rw [UInt16.toNat_and]
  rw [show UInt16.toNat 7 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem sprAddr_nat (c : UInt8) (L : UInt16) (top tile attr : UInt8) (h1 : top.toNat ≤ L.toNat)
    (h2 : L.toNat < top.toNat + hgtC c) :
    (sprAddr c L top tile attr).toNat = addrSpec c tile attr (L.toNat - top.toNat) := by
  have hsub : (L - top.toUInt16).toNat = L.toNat - top.toNat := by
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simpa using h1)]; simp
  unfold sprAddr addrSpec
  rw [bit7_iff attr]
  unfold hgtC at h2 ⊢
  by_cases ht : (c &&& 0x20 != 0) = true
  · simp only [ht, ↓reduceIte] at h2 ⊢
    have hr : ((L - top.toUInt16) &&& (16 - 1)).toNat = L.toNat - top.toNat := by
      rw [show (16 : UInt16) - 1 = 15 from rfl, and15 _ (by rw [hsub]; omega), hsub]
    generalize (L - top.toUInt16) &&& (16 - 1) = r at hr
    by_cases hf : Declarative.bit attr 7 = 1
    · simp only [hf, decide_true, ↓reduceIte]
      have hr' : (16 - 1 - r).toNat = 16 - 1 - (L.toNat - top.toNat) := by
        rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le, hr]; simp; omega), hr]; rfl
      rw [tall_nat tile _ (by rw [hr']; omega), hr']
    · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [tall_nat tile _ (by rw [hr]; omega), hr]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    have hr : ((L - top.toUInt16) &&& (8 - 1)).toNat = L.toNat - top.toNat := by
      rw [show (8 : UInt16) - 1 = 7 from rfl, and7 _ (by rw [hsub]; omega), hsub]
    generalize (L - top.toUInt16) &&& (8 - 1) = r at hr
    by_cases hf : Declarative.bit attr 7 = 1
    · simp only [hf, decide_true, ↓reduceIte]
      have hr' : (8 - 1 - r).toNat = 8 - 1 - (L.toNat - top.toNat) := by
        rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le, hr]; simp; omega), hr]; rfl
      rw [short_nat c tile _ (by rw [hr']; omega), hr']
    · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [short_nat c tile _ (by rw [hr]; omega), hr]

/-- The 2-bit pattern of slot `i` at screen column `x` as `Render.spritePixelAux` computes it
(0 outside the sprite's 8 columns). -/
def implPat (t : State) (x : UInt8) (i : Nat) : UInt8 :=
  let sx := getByte t.sprX i
  if x ≥ sx && x - sx < 8 then
    let sh : UInt8 := 7 - (x - sx)
    ((getByte t.sprPatLo i >>> sh) &&& (1 : UInt8)) ||| (((getByte t.sprPatHi i >>> sh) &&& (1 : UInt8)) <<< (1 : UInt8))
  else 0

theorem plane_bit (rd : UInt16 → UInt8) (c : UInt8) (L : UInt16) (top tile attr : UInt8) (hi : Bool)
    (k : UInt8) (hk : k < 8) :
    ((sprPlane rd c L top tile attr hi >>> (7 - k)) &&& 1).toNat =
      Declarative.bit (rd (if hi then sprAddr c L top tile attr + 8 else sprAddr c L top tile attr))
        (if Declarative.bit attr 6 = 1 then k.toNat else 7 - k.toNat) := by
  unfold sprPlane
  dsimp only
  rw [bit6_iff attr]
  generalize rd (if hi then sprAddr c L top tile attr + 8 else sprAddr c L top tile attr) = b
  have hk' : k.toNat < 8 := hk
  by_cases hf : Declarative.bit attr 6 = 1
  · simp only [hf, decide_true, ↓reduceIte]
    rw [rev_shr b k hk, shr_toNat b k hk]; rfl
  · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [shr_toNat b _ (by rw [UInt8.lt_iff_toNat_lt, sub7 k hk]; simp; omega), sub7 k hk]; rfl

theorem height_eq (s0 : State) : Declarative.height s0 = hgtC s0.ctrl := rfl

theorem addrSpec_lt (c tile attr : UInt8) (r0 : Nat) (h : r0 < 16) :
    addrSpec c tile attr r0 < 0x3000 := by
  have ht := tile.toNat_lt
  unfold addrSpec hgtC
  dsimp only
  repeat' split
  all_goals omega

/-- **One slot against the declarative lookup.** A slot fetched for sprite `n` (in range of line
`L`) shows, at column `x`, exactly the pattern bits `Declarative.spriteBits` gives for `n` at
`(x, L + 1)`. -/
theorem slot_bits (rd : UInt16 → UInt8) (s0 t : State) (L : UInt16) (x : UInt8) (i n : Nat)
    (hX : getByte t.sprX i = getByte s0.oam (4 * n + 3))
    (hP : ∀ hi : Bool, getByte (if hi then t.sprPatHi else t.sprPatLo) i =
      sprPlane rd s0.ctrl L (getByte s0.oam (4 * n)) (getByte s0.oam (4 * n + 1))
        (getByte s0.oam (4 * n + 2)) hi)
    (hin : inRangeSpec (getByte s0.oam (4 * n)) L.toNat (Declarative.height s0) = true) :
    (implPat t x i).toNat = Declarative.spriteBits s0 rd n x.toNat (L.toNat + 1) := by
  have hLo := hP false
  have hHi := hP true
  simp only [Bool.false_eq_true, ↓reduceIte] at hLo hHi
  unfold implPat Declarative.spriteBits
  rw [hX, hLo, hHi, height_eq]
  rw [height_eq] at hin
  unfold inRangeSpec at hin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  generalize getByte s0.oam (4 * n) = top at hin ⊢
  generalize getByte s0.oam (4 * n + 1) = tile
  generalize getByte s0.oam (4 * n + 2) = attr
  generalize getByte s0.oam (4 * n + 3) = sx
  have hy : L.toNat + 1 - 1 - top.toNat = L.toNat - top.toNat := by omega
  simp only [hy]
  have hA := sprAddr_nat s0.ctrl L top tile attr hin.1 hin.2
  have hlt := addrSpec_lt s0.ctrl tile attr (L.toNat - top.toNat) (by unfold hgtC at hin; split at hin <;> omega)
  have hA16 : sprAddr s0.ctrl L top tile attr = (addrSpec s0.ctrl tile attr (L.toNat - top.toNat)).toUInt16 := by
    apply UInt16.toNat_inj.mp; rw [hA, u16 _ (by omega)]
  have hA8 : sprAddr s0.ctrl L top tile attr + 8 =
      (addrSpec s0.ctrl tile attr (L.toNat - top.toNat) + 8).toUInt16 := by
    apply UInt16.toNat_inj.mp
    rw [UInt16.toNat_add, hA, u16 _ (by omega)]; simp; omega
  by_cases hr : sx.toNat ≤ x.toNat ∧ x.toNat < sx.toNat + 8
  · have hk : x - sx < 8 := by
      rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact hr.1)]
      simp; omega
    have hc : (x ≥ sx && x - sx < 8) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [ge_iff_le, UInt8.le_iff_toNat_le]; exact hr.1, hk⟩
    have hkn : (x - sx).toNat = x.toNat - sx.toNat :=
      UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact hr.1)
    simp only [hc, ↓reduceIte, hr, and_self]
    rw [pack2, plane_bit _ _ _ _ _ _ _ _ hk, plane_bit _ _ _ _ _ _ _ _ hk]
    simp only [Bool.false_eq_true, ↓reduceIte, hkn]
    rw [hA8, hA16]
    rfl
  · have hc : (x ≥ sx && x - sx < 8) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h1 : sx.toNat ≤ x.toNat
      · right
        rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact h1)]
        simp; omega
      · left; rw [ge_iff_le, UInt8.le_iff_toNat_le]; exact h1
    simp only [hc, Bool.false_eq_true, ↓reduceIte, hr]
    rfl

/-- Decode a packed `Render.spritePixel` value into the declarative form: `none` if transparent,
else the palette index `$10 | palette·4 | pattern` and the behind-background bit. -/
def decodeSpr (p : UInt8) : Option (UInt8 × Bool) :=
  if p &&& 3 = 0 then none else some (0x10 ||| (p &&& 0x0F), p &&& 0x10 != 0)

/-- The packed value `spritePixelAux` returns for an opaque slot. -/
def packSpr (pat a : UInt8) (z : UInt8) : UInt8 :=
  pat ||| ((a &&& (3 : UInt8)) <<< (2 : UInt8)) ||| ((a &&& (0x20 : UInt8)) >>> (1 : UInt8)) ||| z

theorem implPat_lt4 (t : State) (x : UInt8) (i : Nat) : implPat t x i < 4 := by
  unfold implPat; dsimp only; split
  · generalize getByte t.sprPatLo i >>> (7 - (x - getByte t.sprX i)) = a
    generalize getByte t.sprPatHi i >>> (7 - (x - getByte t.sprX i)) = b
    bv_decide
  · decide

theorem aux_step (t : State) (x n : UInt8) (fuel : Nat) (i : UInt8) :
    Render.spritePixelAux t x n (fuel + 1) i =
      if i ≥ n then 0
      else if implPat t x i.toNat != 0 then
        packSpr (implPat t x i.toNat) (getByte t.sprAttr i.toNat) (if i == 0 && t.spr0Line then 0x80 else 0)
      else Render.spritePixelAux t x n fuel (i + 1) := by
  rw [Render.spritePixelAux]
  unfold implPat packSpr
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]

theorem decode_zero : decodeSpr 0 = none := rfl

theorem pack_low (pat a z : UInt8) (hp : pat < 4) (hz : z = 0 ∨ z = 0x80) :
    packSpr pat a z &&& 3 = pat ∧ 0x10 ||| (packSpr pat a z &&& 0x0F) = 0x10 + 4 * (a &&& 3) + pat ∧
      (packSpr pat a z &&& 0x10 != 0) = (a &&& 0x20 != 0) := by
  unfold packSpr
  rcases hz with hz | hz <;> subst hz <;> refine ⟨by bv_decide, by bv_decide, ?_⟩ <;>
    (apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne, ne_eq]; bv_decide)

theorem idx_nat (a pat : UInt8) (hp : pat < 4) :
    (0x10 + 4 * (a.toNat % 4) + pat.toNat).toUInt8 = 0x10 + 4 * (a &&& 3) + pat := by
  have hp' : pat.toNat < 4 := hp
  have ha : (a &&& 3).toNat = a.toNat % 4 := by
    rw [UInt8.toNat_and, show UInt8.toNat 3 = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, UInt8.toNat_add, UInt8.toNat_mul, ha]
  have : a.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  simp

/-- The declarative sprite lookup over a list of OAM indices (first opaque one wins). -/
def declFind (s0 : State) (rd : UInt16 → UInt8) (x y : Nat) (l : List Nat) : Option (UInt8 × Bool) :=
  match l.find? (Declarative.spriteBits s0 rd · x y ≠ 0) with
  | none => none
  | some n =>
    let attr := getByte s0.oam (4 * n + 2)
    some ((0x10 + 4 * (attr.toNat % 4) + Declarative.spriteBits s0 rd n x y).toUInt8,
      Declarative.bit attr 5 = 1)

theorem u8n (k : Nat) (hk : k < 256) : k.toUInt8.toNat = k := by simp; omega

/-- The slot `k` of `t` holds sprite `sel[k]` as the fetch leaves it. -/
def SlotsHold (rd : UInt16 → UInt8) (s0 t : State) (L : UInt16) (sel : List Nat) : Prop :=
  ∀ i (hi : i < sel.length), getByte t.sprAttr i = getByte s0.oam (4 * sel[i] + 2) ∧
    getByte t.sprX i = getByte s0.oam (4 * sel[i] + 3) ∧
    ∀ hi' : Bool, getByte (if hi' then t.sprPatHi else t.sprPatLo) i =
      sprPlane rd s0.ctrl L (getByte s0.oam (4 * sel[i])) (getByte s0.oam (4 * sel[i] + 1))
        (getByte s0.oam (4 * sel[i] + 2)) hi'

/-- **The slot scan is the declarative `find?`.** Scanning slots `k …` of `t` (`spritePixelAux`)
decodes to the declarative first-opaque lookup over `sel.drop k`. -/
theorem aux_find (rd : UInt16 → UInt8) (s0 t : State) (L : UInt16) (x : UInt8) (sel : List Nat)
    (hcnt : t.sprCount.toNat = sel.length) (h8 : sel.length ≤ 8) (hs : SlotsHold rd s0 t L sel)
    (hin : ∀ n ∈ sel, inRangeSpec (getByte s0.oam (4 * n)) L.toNat (Declarative.height s0) = true) :
    ∀ m k fuel, k + m = sel.length → m ≤ fuel →
      decodeSpr (Render.spritePixelAux t x t.sprCount fuel k.toUInt8) =
        declFind s0 rd x.toNat (L.toNat + 1) (sel.drop k)
  | 0, k, fuel, hk, _ => by
    have hd : sel.drop k = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd]
    cases fuel with
    | zero => rw [Render.spritePixelAux]; rfl
    | succ f =>
      rw [aux_step]
      have : (k.toUInt8 ≥ t.sprCount) := by
        rw [ge_iff_le, UInt8.le_iff_toNat_le, u8n k (by omega)]; omega
      simp only [this, ↓reduceIte]; rfl
  | m + 1, k, fuel, hk, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hkl : k < sel.length := by omega
    rw [aux_step, List.drop_eq_getElem_cons hkl]
    have hge : ¬ (k.toUInt8 ≥ t.sprCount) := by
      rw [ge_iff_le, UInt8.le_iff_toNat_le, u8n k (by omega)]; omega
    simp only [hge, ↓reduceIte, u8n k (by omega)]
    obtain ⟨hA, hX, hP⟩ := hs k hkl
    have hb := slot_bits rd s0 t L x k sel[k] hX hP (hin _ (List.getElem_mem hkl))
    unfold declFind
    rw [List.find?_cons]
    by_cases h0 : Declarative.spriteBits s0 rd sel[k] x.toNat (L.toNat + 1) = 0
    · have hz : implPat t x k = 0 := by
        apply UInt8.toNat_inj.mp; rw [hb, h0]; rfl
      simp only [hz, h0, ne_eq, not_true_eq_false, decide_false, show ((0 : UInt8) != 0) = false from rfl,
        Bool.false_eq_true, ↓reduceIte]
      have ih := aux_find rd s0 t L x sel hcnt h8 hs hin m (k + 1) f (by omega) (by omega)
      rw [show k.toUInt8 + 1 = (k + 1).toUInt8 by
        apply UInt8.toNat_inj.mp; rw [UInt8.toNat_add, u8n k (by omega), u8n (k + 1) (by omega)]; simp; omega]
      rw [ih]
      unfold declFind; rfl
    · have hnz : (implPat t x k != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro h; apply h0; rw [← hb, h]; rfl
      simp only [hnz, ↓reduceIte, h0, ne_eq, not_false_eq_true, decide_true]
      have hz : (if k.toUInt8 == 0 && t.spr0Line then (0x80 : UInt8) else 0) = 0 ∨
          (if k.toUInt8 == 0 && t.spr0Line then (0x80 : UInt8) else 0) = 0x80 := by
        split
        · right; rfl
        · left; rfl
      obtain ⟨p1, p2, p3⟩ := pack_low (implPat t x k) (getByte t.sprAttr k) _ (implPat_lt4 t x k) hz
      unfold decodeSpr
      have hpz : ¬ (implPat t x k = 0) := by simpa using hnz
      rw [p1, p2, p3, hA]
      simp only [hpz, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hb, idx_nat _ _ (implPat_lt4 t x k)]
      · rw [bit5_iff]

/-- The sprites selected for the line after `L` (first ≤ 8 in range of `L`, OAM order). -/
def selL (s0 : State) (L : UInt16) : List Nat :=
  (evalSpec s0.oam L.toNat (Declarative.height s0)).1

theorem selL_inRange (s0 : State) (L : UInt16) :
    ∀ n ∈ selL s0 L, inRangeSpec (getByte s0.oam (4 * n)) L.toNat (Declarative.height s0) = true := by
  intro n hn
  unfold selL evalSpec at hn
  have := List.mem_of_mem_take hn
  exact (List.mem_filter.mp this).2

theorem selL_len (s0 : State) (L : UInt16) : (selL s0 L).length ≤ 8 := by
  unfold selL evalSpec; exact List.length_take_le _ _

/-- **Sprite pixel = declarative sprite lookup.** If the slots of `t` hold the sprites evaluation
selected on line `L` (count and slot contents as `T_PPU_6_fetch` leaves them), the packed
`Render.spritePixel t x` decodes to `Declarative.spritePixel s0 rd x (L + 1)`: same palette
index (`$10–$1F`), same behind-background bit, transparent iff no selected sprite is opaque at
`x`. -/
theorem spritePixel_decl (rd : UInt16 → UInt8) (s0 t : State) (L : UInt16) (x : UInt8)
    (hcnt : t.sprCount.toNat = (selL s0 L).length) (hs : SlotsHold rd s0 t L (selL s0 L)) :
    decodeSpr (Render.spritePixel t x) = Declarative.spritePixel s0 rd x.toNat (L.toNat + 1) := by
  have h8 := selL_len s0 L
  have hmin : min t.sprCount 8 = t.sprCount := by
    have : t.sprCount ≤ 8 := by rw [UInt8.le_iff_toNat_le]; show t.sprCount.toNat ≤ 8; omega
    simp only [Min.min, this, ↓reduceIte]
  unfold Render.spritePixel
  rw [hmin]
  have := aux_find rd s0 t L x (selL s0 L) hcnt h8 hs (selL_inRange s0 L) (selL s0 L).length 0 8
    (by omega) h8
  rw [show (0 : Nat).toUInt8 = 0 from rfl] at this
  rw [this]
  unfold Declarative.spritePixel declFind
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.drop_zero]
  rfl

/-! ### The priority mux, masks, greyscale and the frame write -/

theorem bg_wf_fin : ∀ pal, pal < 4 → ∀ pat, pat < 4 → pat ≠ 0 →
    (4 * pal + pat).toUInt8 &&& 0x0F = (4 * pal + pat).toUInt8 ∧
      ((4 * pal + pat).toUInt8 &&& 3 = 0 → (4 * pal + pat).toUInt8 = 0) := by decide

theorem bg_wf_of (P pal : Nat) (hP : P < 4) (hpal : pal < 4) :
    (if P = 0 then (0 : UInt8) else (4 * pal + P).toUInt8) &&& 0x0F =
        (if P = 0 then (0 : UInt8) else (4 * pal + P).toUInt8) ∧
      ((if P = 0 then (0 : UInt8) else (4 * pal + P).toUInt8) &&& 3 = 0 →
        (if P = 0 then (0 : UInt8) else (4 * pal + P).toUInt8) = 0) := by
  split
  · exact ⟨rfl, fun _ => rfl⟩
  · rename_i hp; exact bg_wf_fin pal hpal P hP hp

theorem pat_lt (a b : UInt8) (c : Nat) : Declarative.bit a c + 2 * Declarative.bit b c < 4 := by
  unfold Declarative.bit
  have := Nat.mod_lt (a.toNat / 2 ^ c) (show 2 > 0 by decide)
  have := Nat.mod_lt (b.toNat / 2 ^ c) (show 2 > 0 by decide)
  omega

/-- `Declarative.bgPixel` is a 4-bit index that is 0 exactly when its pattern bits are 0. -/
theorem bgPixel_wf (s0 : State) (rd : UInt16 → UInt8) (x y : Nat) :
    Declarative.bgPixel s0 rd x y &&& 0x0F = Declarative.bgPixel s0 rd x y ∧
      (Declarative.bgPixel s0 rd x y &&& 3 = 0 → Declarative.bgPixel s0 rd x y = 0) := by
  unfold Declarative.bgPixel
  dsimp only
  exact bg_wf_of _ _ (pat_lt _ _ _) (Nat.mod_lt _ (by decide))

/-- The declarative priority rule on a decoded sprite pixel. -/
def declIdx (bg : UInt8) (spr : Option (UInt8 × Bool)) : UInt8 :=
  match spr with
  | some (i, behind) => if behind = true ∧ bg ≠ 0 then bg else i
  | none => bg

theorem mux_decode (bg P : UInt8) (hB : bg &&& 0x0F = bg) (hB3 : bg &&& 3 = 0 → bg = 0) :
    Render.muxIndex bg P = declIdx bg (decodeSpr P) := by
  unfold Render.muxIndex decodeSpr declIdx
  by_cases hb : bg = 0
  · subst hb
    by_cases hp : P &&& 3 = 0
    · simp only [hp, ↓reduceIte]; rfl
    · simp only [hp, ↓reduceIte]
      have : (P &&& 3 != 0) = true := by simpa using hp
      simp only [this, Bool.true_and, show ((0 : UInt8) &&& 3 != 0) = false from rfl, Bool.not_false,
        Bool.true_or, ↓reduceIte, ne_eq, not_true_eq_false, and_false]
  · have hb3 : (bg &&& 3 != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; exact hb (hB3 h)
    by_cases hp : P &&& 3 = 0
    · simp only [hp, ↓reduceIte, show ((0 : UInt8) != 0) = false from rfl, Bool.false_and,
        Bool.false_eq_true, hb3, hB]
    · have : (P &&& 3 != 0) = true := by simpa using hp
      simp only [hp, ↓reduceIte, this, Bool.true_and, hb3, Bool.not_true, Bool.false_or, hb,
        ne_eq, not_false_eq_true, and_true, hB]
      by_cases hq : P &&& 0x10 = 0
      · simp [hq]
      · simp [hq]

theorem grey_and (v : UInt8) (b : Bool) :
    v &&& 0x3F &&& (if b then 0x30 else 0x3F) = v &&& (if b then 0x30 else 0x3F) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide

theorem lo8 : ∀ (c : UInt8) (b : Bool), (c.toUInt16 ||| if b then 0x4000 else 0).toUInt8 = c := by
  decide

theorem lt8_iff (x : UInt8) : decide (x < 8) = !decide (8 ≤ x.toNat) := by
  by_cases h : x < 8
  · have : ¬ 8 ≤ x.toNat := by rw [UInt8.lt_iff_toNat_lt] at h; exact Nat.not_le.mpr h
    simp [h, this]
  · have : 8 ≤ x.toNat := by rw [UInt8.lt_iff_toNat_lt] at h; exact Nat.le_of_not_lt h
    simp [h, this]

/-- **Priority mux, masks, backdrop, greyscale.** With rendering enabled, the colour
`Render.pixelOut` produces at column `x` is the declarative colour (`Declarative.pixel`'s
formula on the masks of `p`) of the 4-bit background index `B` (well-formed: 0 iff transparent)
and the decoded sprite pixel, when the background pixel handed in is `Nes.Ppu.bgPixel`'s masked `B`
(`bgPx = 0` when the background is hidden at `x`, else `B`). -/
theorem pixelOut_decl (palRd : UInt8 → UInt8) (bgPx : UInt8) (p : State) (x : UInt8) (B : UInt8)
    (hr : p.rendering = true) (hB : B &&& 0x0F = B) (hB3 : B &&& 3 = 0 → B = 0)
    (hbg : bgPx = if !p.showBg || (!p.bgLeft && decide (x < 8)) then 0 else B) :
    (Render.pixelOut palRd bgPx p x).toUInt8 =
      palRd (declIdx (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0)
          (if p.showSpr = true ∧ (8 ≤ x.toNat ∨ p.sprLeft = true) then decodeSpr (Render.spritePixel p x)
            else none)) &&& (if p.mask &&& 1 != 0 then 0x30 else 0x3F) := by
  unfold Render.pixelOut
  simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lo8, grey_and]
  congr 2
  have e1 : (if (p.showBg && (!decide (x < 8) || p.bgLeft)) = true then bgPx &&& 0x0F else 0) =
      (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0) := by
    rw [hbg, lt8_iff]
    cases p.showBg <;> cases p.bgLeft <;> by_cases h8 : 8 ≤ x.toNat <;> simp [h8, hB]
  have e2 : (if (p.showSpr && (!decide (x < 8) || p.sprLeft)) = true then Render.spritePixel p x else 0) =
      (if p.showSpr = true ∧ (8 ≤ x.toNat ∨ p.sprLeft = true) then Render.spritePixel p x else 0) := by
    rw [lt8_iff]
    cases p.showSpr <;> cases p.sprLeft <;> by_cases h8 : 8 ≤ x.toNat <;> simp [h8]
  rw [e1, e2]
  have hwf : (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0) &&& 0x0F =
      (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0) := by
    split
    · exact hB
    · rfl
  have hwf3 : (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0) &&& 3 = 0 →
      (if p.showBg = true ∧ (8 ≤ x.toNat ∨ p.bgLeft = true) then B else 0) = 0 := by
    split
    · exact hB3
    · intro _; rfl
  rw [mux_decode _ _ hwf hwf3]
  by_cases hs : p.showSpr = true ∧ (8 ≤ x.toNat ∨ p.sprLeft = true)
  · rw [ite_eq_left hs, ite_eq_left hs]
  · rw [ite_eq_right hs, ite_eq_right hs, decode_zero]

theorem evalDot_frame (u : State) : (evalDot u).frame = u.frame := by
  unfold evalDot; dsimp only; split <;> rfl
theorem bgDot_frame (rd : UInt16 → UInt8) (u : State) : (bgDot rd u).frame = u.frame := by
  unfold bgDot; split <;> rfl

theorem bgPixelRaw_congr {a b : State} (h : BgEq a b) : bgPixelRaw b = bgPixelRaw a := by
  unfold bgPixelRaw; rw [h.patLo, h.patHi, h.attrLo, h.attrHi, h.x]

theorem spritePixelAux_congr {a b : State} (h : Slots a b) (x n : UInt8) :
    ∀ fuel i, Render.spritePixelAux b x n fuel i = Render.spritePixelAux a x n fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [Render.spritePixelAux, h.sprX, h.sprPatLo, h.sprPatHi, h.sprAttr, h.spr0Line,
      spritePixelAux_congr h x n fuel (i + 1)]

theorem spritePixel_congr {a b : State} (h : Slots a b) (x : UInt8) :
    Render.spritePixel b x = Render.spritePixel a x := by
  unfold Render.spritePixel; rw [h.sprCount]; exact spritePixelAux_congr h x _ 8 0

theorem dot_lt8 (x : Nat) (hx : x < 256) : decide ((x.toUInt16 + 1) ≤ 8) = decide (x.toUInt8 < 8) := by
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
  rw [UInt16.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt16.toNat_add]
  simp; omega

/-- **Frame byte at visible pixel `(x, y)`.** One real PPU dot from a state at dot `x` of visible
line `y` (rendering enabled, 61440-byte frame) writes `frame[256·y + x] =
Declarative.pixel s0 rd pr x y`, provided the masks are `s0`'s, the unmasked background index the
dot's background pipeline shows (`bgPixelRaw` after the dot — the shape of `T_PPU_6_bg`) is
`Declarative.bgPixel s0 rd x y`, and the slots decode to `Declarative.spritePixel s0 rd x y`
(`spritePixel_decl`). -/
theorem frame_byte (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s0 t : State) (x y : Nat)
    (hr : t.rendering = true) (hy : t.scanline.toNat = y) (hy240 : y < 240)
    (hx : t.dot.toNat = x) (hx256 : x < 256) (hm : t.mask = s0.mask)
    (hfs : t.frame.size = 61440)
    (hbg : bgPixelRaw (Ppu.dot rd pr t) = Declarative.bgPixel s0 rd x y)
    (hspr : decodeSpr (Render.spritePixel t x.toUInt8) = Declarative.spritePixel s0 rd x y) :
    getByte (Ppu.dot rd pr t).frame (256 * y + x) = Declarative.pixel s0 rd pr x y := by
  have hl : t.scanline < 240 := by rw [UInt16.lt_iff_toNat_lt, hy]; simpa using hy240
  have hd : t.dot < 339 := by rw [UInt16.lt_iff_toNat_lt, hx]; simp; omega
  have hdot : t.dot = x.toUInt16 := by apply UInt16.toNat_inj.mp; rw [hx]; simp; omega
  -- the background pixel handed to the mux
  have ha := advance_lt t hd
  have hB1 : bgPixelRaw (bgDot rd (preBg t)) = Declarative.bgPixel s0 rd x y := by
    have e1 := bgEq_ppuDot rd pr t hr
    have e2 : BgEq (bgDot rd t.advance) (bgDot rd (preBg t)) := by
      have := bgEq_a12 rd t.advance (busAddr { t with dot := t.dot + 1 } &&& 0x1000 != 0)
      rw [ha] at this ⊢; exact this
    rw [bgPixelRaw_congr e2, ← bgPixelRaw_congr e1, hbg]
  rw [ppuDot_vis rd pr t hr hl hd]
  obtain ⟨k1, k2, -, k4, -⟩ := bgDot_keeps rd (preBg t)
  obtain ⟨-, e2, e3, e4⟩ := evalDot_fields (bgDot rd (preBg t))
  have hpd : (evalDot (bgDot rd (preBg t))).dot = x.toUInt16 + 1 := by
    rw [e3, k1]; show t.dot + 1 = _; rw [hdot]
  rw [fetchDot_idle rd _ (Or.inl (by rw [hpd, UInt16.lt_iff_toNat_lt, UInt16.toNat_add]; simp; omega))]
  have hfr : (evalDot (bgDot rd (preBg t))).frame = t.frame := by
    rw [evalDot_frame, bgDot_frame]; rfl
  have hsl : Slots t (evalDot (bgDot rd (preBg t))) := by
    have a1 := slotEq_bgDot rd (preBg t)
    have a2 := slotEq_evalDot (bgDot rd (preBg t))
    exact ⟨a2.2.trans a1.2, a2.3.trans a1.3, a2.4.trans a1.4, a2.5.trans a1.5, a2.6.trans a1.6,
      a2.7.trans a1.7⟩
  have hpm : (evalDot (bgDot rd (preBg t))).mask = t.mask := by rw [e2, k4]; rfl
  have hps : (evalDot (bgDot rd (preBg t))).scanline = t.scanline := by rw [e4, k2]; rfl
  generalize hp : evalDot (bgDot rd (preBg t)) = p at hpd hfr hsl hpm hps
  have hpr : p.rendering = true := by simp only [State.rendering, hpm]; exact hr
  have hbgPx : Nes.Ppu.bgPixel (bgDot rd (preBg t)) =
      if !p.showBg || (!p.bgLeft && decide (x.toUInt8 < 8)) then 0 else Declarative.bgPixel s0 rd x y := by
    unfold Nes.Ppu.bgPixel
    rw [hB1, k1]
    simp only [State.showBg, State.bgLeft, hpm, k4]
    rw [show (preBg t).mask = t.mask from rfl, show (preBg t).dot = t.dot + 1 from rfl, hdot,
      dot_lt8 x hx256]
  obtain ⟨w1, w2⟩ := bgPixel_wf s0 rd x y
  have hout := pixelOut_decl pr (Nes.Ppu.bgPixel (bgDot rd (preBg t))) p x.toUInt8 _ hpr w1 w2 hbgPx
  rw [spritePixel_congr hsl, hspr] at hout
  unfold Render.pixel
  have hc : (p.dot == 0 || decide (p.dot > 256) || decide (p.scanline ≥ 240)) = false := by
    rw [hpd, hps]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h; have := congrArg UInt16.toNat h; rw [UInt16.toNat_add] at this; simp at this; omega
    · rw [gt_iff_lt, UInt16.lt_iff_toNat_lt, UInt16.toNat_add]; simp; omega
    · rw [ge_iff_le, UInt16.le_iff_toNat_le, hy]; simp; omega
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  have hidx : (p.scanline.toUInt32 * 256 + (p.dot - 1).toUInt8.toUInt32).toNat = 256 * y + x := by
    rw [hps, hpd]
    have : (x.toUInt16 + 1 - 1).toUInt8 = x.toUInt8 := by simp
    rw [this]
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp [hy]; omega
  rw [hidx, getByte_set, hfr, hfs, ite_eq_left ⟨rfl, by omega⟩]
  have hx8 : (p.dot - 1).toUInt8 = x.toUInt8 := by rw [hpd]; simp
  rw [hx8, hout]
  unfold Declarative.pixel declIdx
  have hxn : x.toUInt8.toNat = x := u8n x hx256
  simp only [hxn, State.showBg, State.bgLeft, State.showSpr, State.sprLeft, hpm, hm]
  rfl

/-! ### From the fetch to the next line's pixels -/

theorem advance_340 (s : State) (hl : s.scanline < 240) (hd : s.dot = 340) :
    s.advance = { s with dot := 0, scanline := s.scanline + 1 } := by
  have h1 : s.scanline ≠ 261 := by bv_decide
  simp [State.advance, hd, h1]

/-- Dots 321–340 of a visible line keep the slots (from dot 320). -/
theorem slots_tail (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (r : State) (hl : r.scanline < 240)
    (hd : r.dot = 320) :
    ∀ k ≤ 20, Slots r (run (Ppu.dot rd pr) k r) ∧ (run (Ppu.dot rd pr) k r).dot = (320 + k).toUInt16 ∧
      (run (Ppu.dot rd pr) k r).scanline = r.scanline ∧ (run (Ppu.dot rd pr) k r).mask = r.mask
  | 0, _ => ⟨Slots.refl r, hd, rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨ih, hdk, hsk, hmk⟩ := slots_tail rd pr r hl hd k (by omega)
    have hlt : (run (Ppu.dot rd pr) k r).dot < 340 := by
      rw [hdk, UInt16.lt_iff_toNat_lt]; simp; omega
    have ha := advance_vis _ (by rw [hsk]; exact hl) hlt
    have had : (run (Ppu.dot rd pr) k r).advance.dot = (320 + (k + 1)).toUInt16 := by
      rw [ha, hdk]; apply UInt16.toNat_inj.mp; simp; omega
    obtain ⟨f1, f2, f3⟩ := dot_fields rd pr (run (Ppu.dot rd pr) k r)
    refine ⟨ih.trans (slots_ppuDot rd pr _ (Or.inr ?_)), ?_, ?_, ?_⟩
    · rw [had, gt_iff_lt, UInt16.lt_iff_toNat_lt]; simp; omega
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k r)).dot = _
      rw [f1, had]
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k r)).scanline = _
      rw [f2, ha, hsk]
    · show (Ppu.dot rd pr (run (Ppu.dot rd pr) k r)).mask = _
      rw [f3, hmk]

/-- From dot 320 of visible line `L < 239`, 21 real dots reach dot 0 of line `L + 1` with the
slots and mask unchanged. -/
theorem to_next_line (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (r : State) (hl : r.scanline < 240)
    (hd : r.dot = 320) :
    Slots r (run (Ppu.dot rd pr) 21 r) ∧ (run (Ppu.dot rd pr) 21 r).dot = 0 ∧
      (run (Ppu.dot rd pr) 21 r).scanline = r.scanline + 1 ∧
      (run (Ppu.dot rd pr) 21 r).mask = r.mask := by
  obtain ⟨h1, h2, h3, h4⟩ := slots_tail rd pr r hl hd 20 (Nat.le_refl _)
  have ha := advance_340 (run (Ppu.dot rd pr) 20 r) (by rw [h3]; exact hl) h2
  obtain ⟨f1, f2, f3⟩ := dot_fields rd pr (run (Ppu.dot rd pr) 20 r)
  have hs := slots_ppuDot rd pr (run (Ppu.dot rd pr) 20 r) (Or.inl (by rw [ha]; show (0 : UInt16) < 257; decide))
  refine ⟨h1.trans hs, ?_, ?_, ?_⟩
  · show (Ppu.dot rd pr (run (Ppu.dot rd pr) 20 r)).dot = _; rw [f1, ha]
  · show (Ppu.dot rd pr (run (Ppu.dot rd pr) 20 r)).scanline = _; rw [f2, ha, h3]
  · show (Ppu.dot rd pr (run (Ppu.dot rd pr) 20 r)).mask = _; rw [f3, h4]

theorem slotsHold_congr {rd s0 a b L sel} (h : Slots a b) (hs : SlotsHold rd s0 a L sel) :
    SlotsHold rd s0 b L sel := by
  intro i hi
  obtain ⟨h1, h2, h3⟩ := hs i hi
  refine ⟨by rw [h.sprAttr]; exact h1, by rw [h.sprX]; exact h2, fun hi' => ?_⟩
  rw [h.sprPatHi, h.sprPatLo]; exact h3 hi'

/-! ### Frame size, declarative congruence -/

theorem frameSize_ppuDot (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State) :
    (Ppu.dot rd pr s).frame.size = s.frame.size := by
  have ha : s.advance.frame = s.frame := by
    unfold State.advance; repeat' split
    all_goals rfl
  have hp : ∀ b (u : State), (Render.pixel pr b u).frame.size = u.frame.size := by
    intro b u; unfold Render.pixel; dsimp only; split
    · rfl
    · exact ByteArray.size_set! ..
  have hf : ∀ u : State, (fetchDot rd u).frame = u.frame := by
    intro u; simp only [fetchDot]; repeat' split
    all_goals rfl
  have he : ∀ u : State, (State.dotEvents u).frame = u.frame := by
    intro u; unfold State.dotEvents; repeat' split
    all_goals rfl
  have fi : ∀ {c : Prop} [Decidable c] {u v : State}, u.frame.size = s.frame.size →
      v.frame.size = s.frame.size → (if c then u else v).frame.size = s.frame.size := by
    intro c _ u v hu hv; split <;> assumption
  have k1 : ∀ u : State, u.frame.size = s.frame.size → (bgDot rd u).frame.size = s.frame.size :=
    fun u h => by rw [bgDot_frame]; exact h
  have k2 : ∀ u : State, u.frame.size = s.frame.size → (evalDot u).frame.size = s.frame.size :=
    fun u h => by rw [evalDot_frame]; exact h
  have k3 : ∀ u : State, u.frame.size = s.frame.size → (fetchDot rd u).frame.size = s.frame.size :=
    fun u h => by rw [hf]; exact h
  have k4 : ∀ b (u : State), u.frame.size = s.frame.size →
      (Render.pixel pr b u).frame.size = s.frame.size := fun b u h => by rw [hp]; exact h
  have h1 : ({ s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } : State).frame.size =
      s.frame.size := by show s.advance.frame.size = _; rw [ha]
  have hr : (render rd pr s.advance).frame.size = s.frame.size := by
    unfold render; dsimp only
    exact fi (k4 _ _ (fi (k3 _ (fi (k2 _ (k1 _ h1)) (k1 _ h1))) (fi (k2 _ (k1 _ h1)) (k1 _ h1))))
      (k4 _ _ h1)
  unfold Ppu.dot; dsimp only
  split
  · show (State.dotEvents (render rd pr s.advance)).frame.size = _; rw [he, hr]
  · rw [he, hr]

theorem frameSize_run (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State) :
    ∀ k, (run (Ppu.dot rd pr) k s).frame.size = s.frame.size
  | 0 => rfl
  | k + 1 => (frameSize_ppuDot rd pr _).trans (frameSize_run rd pr s k)

theorem declSprite_congr (rd : UInt16 → UInt8) {a b : State} (h1 : b.oam = a.oam)
    (h2 : b.ctrl = a.ctrl) (x y : Nat) :
    Declarative.spritePixel b rd x y = Declarative.spritePixel a rd x y := by
  unfold Declarative.spritePixel Declarative.spriteBits Declarative.height State.sprTall
    State.sprTable
  rw [h1, h2]

theorem mask_run (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State) :
    ∀ k, (run (Ppu.dot rd pr) k s).mask = s.mask
  | 0 => rfl
  | k + 1 => ((dot_fields rd pr _).2.2).trans (mask_run rd pr s k)

end Nes.Ppu.Proofs.StaticSpr

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.Sprites Nes.Ppu.Proofs.SpriteEval Nes.Ppu.Proofs.StaticSpr

/-- **T-PPU-3 on the real pipeline.** From dot 0 of a visible line `L` with rendering enabled
and a 32-byte secondary OAM, after the 256 real PPU dots `Ppu.dot rd pr` of dots 1–256:
secondary OAM starts with the four OAM bytes of each sprite of `(evalSpec oam L h).1`,
`evalSec = 4·|sel|`, `spr0Next = (0 ∈ sel)`, the overflow flag is `old ∨ ovf`; OAM, `ctrl`,
line unchanged and the dot is 256. -/
theorem T_PPU_3_ppuDot (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hr : s.rendering = true) (hl : s.scanline < 240) (hdot : s.dot = 0)
    (hsz : s.secOam.size = 32) :
    let spec := evalSpec s.oam s.scanline.toNat (if s.sprTall then 16 else 8)
    spec.1.length ≤ 8 ∧
    (∀ k (hk : k < spec.1.length), ∀ b < 4,
      getByte (run (Ppu.dot rd pr) 256 s).secOam (4 * k + b) = getByte s.oam (4 * spec.1[k] + b)) ∧
    (run (Ppu.dot rd pr) 256 s).evalSec.toNat = 4 * spec.1.length ∧
    ((run (Ppu.dot rd pr) 256 s).evalSec >>> 2).toNat = spec.1.length ∧
    (run (Ppu.dot rd pr) 256 s).spr0Next = decide (0 ∈ spec.1) ∧
    (run (Ppu.dot rd pr) 256 s).sprOverflow = (s.sprOverflow || spec.2) ∧
    (run (Ppu.dot rd pr) 256 s).oam = s.oam ∧ (run (Ppu.dot rd pr) 256 s).scanline = s.scanline ∧
    (run (Ppu.dot rd pr) 256 s).ctrl = s.ctrl ∧ (run (Ppu.dot rd pr) 256 s).dot = 256 ∧
    (run (Ppu.dot rd pr) 256 s).mask = s.mask := by
  intro spec
  have E : EvEq (evalLine s) (run (Ppu.dot rd pr) 256 s) := by
    rw [evalLine_eq]; exact (evEq_run rd pr s hr hl hdot 256 (Nat.le_refl _)).1
  have hm : (run (Ppu.dot rd pr) 256 s).mask = s.mask := (evEq_run rd pr s hr hl hdot 256 (Nat.le_refl _)).2
  have hd : (evalLine s).dot = 256 := by
    rw [evalLine_eq]
    rcases (evalFrom_fields s 256).2 with h | h
    · exact absurd h (by decide)
    · rw [h]; rfl
  obtain ⟨t1, t2, t3, t4, t5, -, t7, t8, t9, t10⟩ := T_PPU_3_eval s hdot hsz
  refine ⟨t1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
  · intro k hk b hb; rw [E.secOam]; exact t2 k hk b hb
  · rw [E.evalSec]; exact t3
  · rw [E.evalSec]; exact t4
  · rw [E.spr0Next]; exact t5
  · unfold State.sprOverflow at t7 ⊢; rw [E.st5]; exact t7
  · rw [E.oam]; exact t8
  · rw [E.scanline]; exact t9
  · rw [E.ctrl]; exact t10
  · rw [E.dot]; exact hd

/-- The sprites evaluation on the line of `s` selects (first ≤ 8 in range, OAM order). -/
def selOf (s : State) : List Nat := (evalSpec s.oam s.scanline.toNat (if s.sprTall then 16 else 8)).1

/-- **Sprite fetch (dots 257–320) on the real pipeline.** From dot 0 of a visible line `L` with
rendering enabled (32-byte secondary OAM, 8-byte slot arrays), after the 320 real PPU dots of
dots 1–320: the slot count is `|sel|` and `spr0Line = (0 ∈ sel)` for `sel = (evalSpec oam L h).1`;
slot `i < |sel|` holds sprite `sel[i]`'s attribute, X and its two pattern planes for row
`L + 1 − Y` (vertical flip / 8×16 rules in `sprAddr`, horizontal flip applied); slots
`|sel| ≤ i < 8` have transparent (zero) patterns. Line, `ctrl`, OAM and mask are unchanged. -/
theorem T_PPU_6_fetch (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hr : s.rendering = true) (hl : s.scanline < 240) (hdot : s.dot = 0)
    (hsz : s.secOam.size = 32) (szA : s.sprAttr.size = 8) (szX : s.sprX.size = 8)
    (szL : s.sprPatLo.size = 8) (szH : s.sprPatHi.size = 8) :
    (run (Ppu.dot rd pr) 320 s).sprCount.toNat = (selOf s).length ∧
    (run (Ppu.dot rd pr) 320 s).spr0Line = decide (0 ∈ (selOf s)) ∧
    (∀ i (hi : i < (selOf s).length),
      getByte (run (Ppu.dot rd pr) 320 s).sprAttr i = getByte s.oam (4 * (selOf s)[i] + 2) ∧
      getByte (run (Ppu.dot rd pr) 320 s).sprX i = getByte s.oam (4 * (selOf s)[i] + 3) ∧
      ∀ hi' : Bool, getByte (if hi' then (run (Ppu.dot rd pr) 320 s).sprPatHi
          else (run (Ppu.dot rd pr) 320 s).sprPatLo) i =
        sprPlane rd s.ctrl s.scanline (getByte s.oam (4 * (selOf s)[i])) (getByte s.oam (4 * (selOf s)[i] + 1))
          (getByte s.oam (4 * (selOf s)[i] + 2)) hi') ∧
    (∀ i, (selOf s).length ≤ i → i < 8 → getByte (run (Ppu.dot rd pr) 320 s).sprPatLo i = 0 ∧
      getByte (run (Ppu.dot rd pr) 320 s).sprPatHi i = 0) ∧
    (run (Ppu.dot rd pr) 320 s).dot = 320 ∧ (run (Ppu.dot rd pr) 320 s).scanline = s.scanline ∧
    (run (Ppu.dot rd pr) 320 s).ctrl = s.ctrl ∧ (run (Ppu.dot rd pr) 320 s).oam = s.oam ∧
    (run (Ppu.dot rd pr) 320 s).mask = s.mask := by
  obtain ⟨t1, t2, -, t4, t5, -, t7, t8, t9, t10, t11⟩ := T_PPU_3_ppuDot rd pr s hr hl hdot hsz
  change (selOf s).length ≤ 8 at t1
  change ∀ k (hk : k < (selOf s).length), ∀ b < 4,
    getByte (run (Ppu.dot rd pr) 256 s).secOam (4 * k + b) = getByte s.oam (4 * (selOf s)[k] + b) at t2
  change ((run (Ppu.dot rd pr) 256 s).evalSec >>> 2).toNat = (selOf s).length at t4
  change (run (Ppu.dot rd pr) 256 s).spr0Next = decide (0 ∈ selOf s) at t5
  obtain ⟨hS, -, -⟩ := slots_run_vis rd pr s hl hdot 256 (Nat.le_refl _)
  rw [show (320 : Nat) = 256 + 8 * 8 from rfl, sfs_run_add]
  generalize run (Ppu.dot rd pr) 256 s = u at t1 t2 t4 t5 t7 t8 t9 t10 t11 hS ⊢
  have hru : u.rendering = true := by simp only [State.rendering, t11]; exact hr
  have hlu : u.scanline < 240 := by rw [t8]; exact hl
  obtain ⟨f1, f2, f3, f4, -, f6, f7, f8, -, -, -, -, fc, fs⟩ :=
    fetch_all rd pr u hru hlu t10 (by rw [hS.sprAttr, szA]) (by rw [hS.sprX, szX])
      (by rw [hS.sprPatLo, szL]) (by rw [hS.sprPatHi, szH]) 8 (Nat.le_refl _)
  generalize run (Ppu.dot rd pr) (8 * 8) u = r at f1 f2 f3 f4 f6 f7 f8 fc fs ⊢
  obtain ⟨c1, c2⟩ := fc (by decide)
  have hsec : ∀ i (hi : i < (selOf s).length) (b : Nat), b < 4 →
      getByte u.secOam (4 * i + b) = getByte s.oam (4 * (selOf s)[i] + b) :=
    fun i hi b hb => t2 i hi b hb
  refine ⟨by rw [c1]; exact t4, by rw [c2]; exact t5, ?_, ?_, by rw [f1]; rfl, by rw [f2, t8],
    by rw [f3, t9], by rw [f8, t7], by rw [f7, t11]⟩
  · intro i hi
    obtain ⟨g1, g2, g3, g4⟩ := fs i (by have := t1; omega)
    refine ⟨by rw [g1, hsec i hi 2 (by decide)], by rw [g2, hsec i hi 3 (by decide)], ?_⟩
    intro hi'
    have hlt : i < (u.evalSec >>> 2).toNat := by rw [t4]; exact hi
    have e : slotByte rd u i hi' = sprPlane rd s.ctrl s.scanline (getByte s.oam (4 * (selOf s)[i]))
        (getByte s.oam (4 * (selOf s)[i] + 1)) (getByte s.oam (4 * (selOf s)[i] + 2)) hi' := by
      unfold slotByte sprPlane
      simp only [hlt, ↓reduceIte, patAddr_eq, t9, t8]
      rw [← hsec i hi 1 (by decide), ← hsec i hi 2 (by decide)]
      have h0 := hsec i hi 0 (by decide)
      simp only [Nat.add_zero] at h0
      rw [← h0]
    cases hi'
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [g3, e]
    · simp only [↓reduceIte]; rw [g4, e]
  · intro i hi h8
    obtain ⟨-, -, g3, g4⟩ := fs i h8
    have hlt : ¬ i < (u.evalSec >>> 2).toNat := by rw [t4]; omega
    refine ⟨by rw [g3]; unfold slotByte; simp only [hlt, ↓reduceIte],
      by rw [g4]; unfold slotByte; simp only [hlt, ↓reduceIte]⟩

/-- **Sprite half of T-PPU-6, one line.** From dot 0 of visible line `L` (`L + 1 < 240`, rendering
enabled, 32-byte secondary OAM, 8-byte slot arrays), `341 + x` real PPU dots later (`x < 256`)
the PPU is at dot `x` of line `L + 1` and the packed sprite pixel of column `x`
(`Render.spritePixel`, what dot `x + 1` muxes) decodes to the declarative lookup
`Declarative.spritePixel s rd x (L + 1)` over the sprites `evalSpec` selects on line `L`. -/
theorem T_PPU_6_spr (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s : State)
    (hr : s.rendering = true) (hl : s.scanline.toNat + 1 < 240) (hdot : s.dot = 0)
    (hsz : s.secOam.size = 32) (szA : s.sprAttr.size = 8) (szX : s.sprX.size = 8)
    (szL : s.sprPatLo.size = 8) (szH : s.sprPatHi.size = 8) (x : Nat) (hx : x < 256) :
    (run (Ppu.dot rd pr) (341 + x) s).scanline.toNat = s.scanline.toNat + 1 ∧
    (run (Ppu.dot rd pr) (341 + x) s).dot.toNat = x ∧
    (run (Ppu.dot rd pr) (341 + x) s).mask = s.mask ∧
    decodeSpr (Render.spritePixel (run (Ppu.dot rd pr) (341 + x) s) x.toUInt8) =
      Declarative.spritePixel s rd x (s.scanline.toNat + 1) := by
  have hl' : s.scanline < 240 := by rw [UInt16.lt_iff_toNat_lt]; simp; omega
  obtain ⟨F1, -, F3, -, F5, F6, -, -, F9⟩ := T_PPU_6_fetch rd pr s hr hl' hdot hsz szA szX szL szH
  rw [show 341 + x = 320 + 21 + x by omega, sfs_run_add, sfs_run_add]
  generalize run (Ppu.dot rd pr) 320 s = r at F1 F3 F5 F6 F9
  obtain ⟨N1, N2, N3, N4⟩ := to_next_line rd pr r (by rw [F6]; exact hl') F5
  generalize run (Ppu.dot rd pr) 21 r = u at N1 N2 N3 N4
  have hu : u.scanline.toNat = s.scanline.toNat + 1 := by
    rw [N3, F6, UInt16.toNat_add]; simp; omega
  obtain ⟨V1, V2, V3⟩ := slots_run_vis rd pr u (by rw [UInt16.lt_iff_toNat_lt, hu]; simp; omega)
    N2 x (by omega)
  have hmt := mask_run rd pr u x
  generalize run (Ppu.dot rd pr) x u = t at V1 V2 V3 hmt
  have hS := N1.trans V1
  have hcnt : t.sprCount.toNat = (selL s s.scanline).length := by rw [hS.sprCount]; exact F1
  have hold : SlotsHold rd s r s.scanline (selL s s.scanline) := by
    intro i hi
    obtain ⟨a1, a2, a3⟩ := F3 i hi
    exact ⟨a1, a2, a3⟩
  refine ⟨by rw [V3, hu], by rw [V2]; simp; omega, ?_, ?_⟩
  · rw [hmt, N4, F9]
  · rw [spritePixel_decl rd s t s.scanline x.toUInt8 hcnt (slotsHold_congr hS hold), u8n x hx]

/-- **Frame byte on lines 1–239 (sprite half + mux of T-PPU-6).** From dot 0 of visible line
`L` (`L + 1 < 240`; rendering on; 32-byte secondary OAM, 8-byte slots, 61440-byte frame) and a
snapshot `s0` with the same OAM, `ctrl` and mask: if the unmasked background index after the dot
that draws `(x, L + 1)` is `Declarative.bgPixel s0 rd x (L + 1)` (what `T_PPU_6_bg` gives), then
the frame byte written for `(x, L + 1)` is `Declarative.pixel s0 rd pr x (L + 1)`. -/
theorem T_PPU_6_spr_pixel (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s s0 : State)
    (hr : s.rendering = true) (hl : s.scanline.toNat + 1 < 240) (hdot : s.dot = 0)
    (hsz : s.secOam.size = 32) (szA : s.sprAttr.size = 8) (szX : s.sprX.size = 8)
    (szL : s.sprPatLo.size = 8) (szH : s.sprPatHi.size = 8) (hfs : s.frame.size = 61440)
    (ho : s.oam = s0.oam) (hc : s.ctrl = s0.ctrl) (hm : s.mask = s0.mask) (x : Nat) (hx : x < 256)
    (hbg : bgPixelRaw (run (Ppu.dot rd pr) (341 + x + 1) s) =
      Declarative.bgPixel s0 rd x (s.scanline.toNat + 1)) :
    getByte (run (Ppu.dot rd pr) (341 + x + 1) s).frame (256 * (s.scanline.toNat + 1) + x) =
      Declarative.pixel s0 rd pr x (s.scanline.toNat + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := T_PPU_6_spr rd pr s hr hl hdot hsz szA szX szL szH x hx
  have hrt : (run (Ppu.dot rd pr) (341 + x) s).rendering = true := by
    simp only [State.rendering, h3]; exact hr
  exact frame_byte rd pr s0 _ x _ hrt h1 hl h2 hx (h3.trans hm)
    ((frameSize_run rd pr s _).trans hfs) hbg (h4.trans (declSprite_congr rd ho.symm hc.symm _ _).symm)

end Nes.Ppu.Proofs
