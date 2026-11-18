import Nes.Ppu.Declarative
import Nes.Ppu.Proofs.Shifter

/-!
# `Nes.Ppu.Proofs.StaticFrameBg` — T-PPU-6, background half

## Spec

Throughout, `f = Nes.Ppu.dot rd pr` (the full PPU dot with fixed readers: a PPU-only run, so no
register, VRAM, palette or OAM write can occur), `run f n` is `f` applied `n` times, `c` the
`ctrl` byte, `t` the loopy `t`, and rendering is enabled (`mask & $18 ≠ 0`).

* **Registers** (`step_info`, `Cfg`): one `f` dot keeps `t`, `x`, `ctrl`, `mask`, moves
  `(scanline, dot, frameOdd)` exactly as `State.advance`, and sets `renderLatch` on reaching
  pre-render dot 338. `walk`: `k` dots within a line move the dot by `k`.
* **Late dots** (`late`): from dot 256 of an active line with `v = w`, after dot `257 + n`
  (`n < 64`) `v = copyX w t`, then `copyY (copyX w t) t` from dot 280 on the pre-render line
  (`lateV`; copy Y is idempotent over 280–304).
* **Line to line** (`line_step`): `Start rd c u` at dot 0 of visible line `y < 239` gives, 341
  dots later, `Start rd c (nextU t u)` at dot 0 of line `y + 1`, where
  `nextU t u = copyX (incY (incX^[34] u)) t` (34 coarse-X steps, `incY` at 256, `copyX` at 257).
  In positions (`hx w` = coarse X + 32·NT bit 0 ∈ 0..63, `vy w` = fine Y + 8·coarse Y +
  256·NT bit 1 ∈ 0..511): `hx (nextU t u) = hx t` (horizontal restarts from `t`) and
  `vy (nextU t u) = vstep (vy u)`, where `vstep` advances the row by one: rows `< 240` count
  modulo 240 toggling the vertical nametable on the 239 → 0 wrap (coarse Y 29), rows 240–255
  (coarse Y 30/31) count to 255 and wrap to 0 without toggling (`vy_incY`).
* **Pre-render line** (`prerender`): from dot 0 of line 261, `341 - [frameOdd]` dots reach dot 0
  of line 0 in `Start rd c (copyY (copyX w t) t)` (`w` = `v` at dot 256, irrelevant: `hx` and
  `vy` of the start tile are those of `t`); the odd-frame skip is taken iff `frameOdd`, since
  `renderLatch` is set at dot 338. `to_prerender`: from `(L, d)`, `241 ≤ L ≤ 260`,
  `341·(261 - L) - d` dots reach `(261, 0)`.
* **Closed forms**: `hx (incX^[k] w) = (hx w + k) mod 64`, `vy (incX^[k] w) = vy w`;
  `vstep^[y] b = vclosed b y` for `b < 512`, `y < 240`, with `vclosed b y` = row
  `(b mod 256 + y) mod 240`, nametable `b / 256 + (b mod 256 + y) / 240` (mod 2) when
  `b mod 256 < 240`, else row `(b mod 256 + y) mod 256`, nametable `b / 256`.
* **Arithmetic link** (`tile_pixN`, `scrollX_eq`, `scrollY_eq`, `tile_eq_declarative`): the
  tile pixel `tilePx (tileBits rd c w) col` is the declarative lookup `pixN` at column
  `8·(hx w mod 32) + col`, row `vy w mod 256`, nametable `(vy w / 256, hx w / 32)`; and
  `Declarative.scrollX/scrollY` are exactly these with `hx w = (hx t + (x + fine x)/8) mod 64`,
  `vy w = vclosed (vy t) y`.
* **T-PPU-6, background half** (`T_PPU_6_bg`): if `Static s0` (rendering on, `s0` in lines
  241–260, dot ≤ 340), then for all `y < 240`, `x < 256`, the state
  `run f (frameStart s0 + 341·y + x + 1) s0` is at line `y`, dot `x + 1`, and its unmasked
  background pixel `bgPixelRaw` equals `Declarative.bgPixel s0 rd x y`, where
  `frameStart s0 = 341·(261 - line) - dot + 341 - [frameOdd]` (dot 0 of line 0).

Method: compose `Shifter`'s `scan`/`prefetch`/`Ready.idle` with per-segment walks (`run_add`),
induction over lines; no symbolic iteration of `Ppu.dot` beyond one dot. Loopy word facts are
`UInt16` identities with `/`, `%` by constants closed by `bv_decide`, then moved to `Nat` with
`toNat` and `omega`.
-/

namespace Nes.Ppu.Proofs
open Nes.Ppu Nes.Ppu.Bg Nes.Ppu.Loopy

/-! ### Per-dot bookkeeping of `Ppu.dot` -/

/-- Fields of `Ppu.dot` that only the timing part moves. -/
structure TEq (a b : State) : Prop where
  frameOdd : b.frameOdd = a.frameOdd
  renderLatch : b.renderLatch = a.renderLatch

theorem TEq.trans {a b c : State} (h1 : TEq a b) (h2 : TEq b c) : TEq a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
theorem TEq.ite {p : Prop} [Decidable p] {s a b : State} (ha : TEq s a) (hb : TEq s b) :
    TEq s (if p then a else b) := by split <;> assumption

local macro "teq_tac" : tactic => `(tactic| (constructor <;>
  simp only [apply_ite State.frameOdd, apply_ite State.renderLatch, ite_self]))

theorem teq_evalDot (s : State) : TEq s (Sprites.evalDot s) := by
  simp only [Sprites.evalDot]; teq_tac
theorem teq_fetchDot (rd) (s : State) : TEq s (Sprites.fetchDot rd s) := by
  simp only [Sprites.fetchDot]; teq_tac
theorem teq_pixel (pr) (b) (s : State) : TEq s (Render.pixel pr b s) := by
  simp only [Render.pixel]; teq_tac
theorem teq_dotEvents (s : State) : TEq s (State.dotEvents s) := by
  simp only [State.dotEvents]; teq_tac
theorem teq_bgDot (rd) (s : State) : TEq s (bgDot rd s) := by
  simp only [bgDot]; teq_tac

theorem teq_render (rd pr) (s : State) : TEq s (render rd pr s) := by
  unfold render
  dsimp only
  have h0 : TEq s { s with a12 := busAddr s &&& 0x1000 != 0 } := ⟨rfl, rfl⟩
  split
  · refine h0.trans ?_
    refine (teq_bgDot rd _).trans ?_
    refine TEq.trans (b := _) ?_ (teq_pixel pr _ _)
    refine TEq.ite ?_ (TEq.ite (teq_evalDot _) ⟨rfl, rfl⟩)
    exact (TEq.ite (teq_evalDot _) ⟨rfl, rfl⟩).trans (teq_fetchDot rd _)
  · exact h0.trans (teq_pixel pr _ _)

theorem bgDot_t (rd) (s : State) : (bgDot rd s).t = s.t := by
  simp only [bgDot]; split <;> rfl

theorem advance_tx (s : State) : s.advance.t = s.t ∧ s.advance.x = s.x ∧
    s.advance.renderLatch = s.renderLatch := by
  simp only [State.advance]; repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- The registers a PPU-only run never changes. -/
structure Cfg (a b : State) : Prop where
  t : b.t = a.t
  x : b.x = a.x
  ctrl : b.ctrl = a.ctrl
  mask : b.mask = a.mask

theorem Cfg.refl (s : State) : Cfg s s := ⟨rfl, rfl, rfl, rfl⟩
theorem Cfg.trans {a b c : State} (h1 : Cfg a b) (h2 : Cfg b c) : Cfg a c :=
  ⟨h2.t.trans h1.t, h2.x.trans h1.x, h2.ctrl.trans h1.ctrl, h2.mask.trans h1.mask⟩
theorem Cfg.ren {a b : State} (h : Cfg a b) (hr : a.rendering = true) : b.rendering = true := by
  simp only [State.rendering, h.mask]; exact hr

/-- One `Ppu.dot` with rendering on: registers kept, position / parity as `advance`, and the
odd-frame latch set on reaching pre-render dot 338. -/
theorem step_info (rd pr) (s : State) (hr : s.rendering = true) :
    Cfg s (Nes.Ppu.dot rd pr s) ∧ (Nes.Ppu.dot rd pr s).dot = s.advance.dot ∧
    (Nes.Ppu.dot rd pr s).scanline = s.advance.scanline ∧
    (Nes.Ppu.dot rd pr s).frameOdd = s.advance.frameOdd ∧
    (Nes.Ppu.dot rd pr s).renderLatch =
      (if (Nes.Ppu.dot rd pr s).scanline = 261 ∧ (Nes.Ppu.dot rd pr s).dot = 338 then true
       else s.renderLatch) := by
  have e := bgEq_ppuDot rd pr s hr
  obtain ⟨k1, k2, k3, k4, k5⟩ := bgDot_keeps rd s.advance
  obtain ⟨-, -, -, -, -, a6, a7⟩ := advance_keep s
  obtain ⟨b1, b2, b3⟩ := advance_tx s
  have cfg : Cfg s (Nes.Ppu.dot rd pr s) :=
    ⟨by rw [e.t, bgDot_t, b1], by rw [e.x, k5, b2], by rw [e.ctrl, k3, a6], by rw [e.mask, k4, a7]⟩
  have ht : TEq s.advance (State.dotEvents (render rd pr s.advance)) :=
    (teq_render rd pr _).trans (teq_dotEvents _)
  have hdef : Nes.Ppu.dot rd pr s =
      if (State.dotEvents (render rd pr s.advance)).scanline == 261 &&
        (State.dotEvents (render rd pr s.advance)).dot == 338 then
        { State.dotEvents (render rd pr s.advance) with
          renderLatch := (State.dotEvents (render rd pr s.advance)).rendering }
      else State.dotEvents (render rd pr s.advance) := rfl
  refine ⟨cfg, by rw [e.dot, k1], by rw [e.scanline, k2], ?_, ?_⟩
  · rw [hdef]; split <;> exact ht.1
  · have hren := cfg.ren hr
    revert hren
    rw [hdef]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [hc, and_self, ↓reduceIte]
      intro h; exact h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [hc, ↓reduceIte]
      intro _; rw [ht.2, b3]

/-! ### Positions along a run -/

theorem run_add (f : State → State) (m n : Nat) (s : State) :
    run f (m + n) s = run f n (run f m s) := by
  induction n with
  | zero => rfl
  | succ n ih => show f (run f (m + n) s) = f (run f n (run f m s)); rw [ih]

theorem run_succ1 (f : State → State) (n : Nat) (s : State) : run f (n + 1) s = f (run f n s) := rfl

theorem run_succ' (f : State → State) (n : Nat) (s : State) : run f (n + 1) s = run f n (f s) := by
  rw [Nat.add_comm, run_add]; rfl

theorem u16_eq_iff (a : UInt16) (n : Nat) (hn : n < 65536) : a = n.toUInt16 ↔ a.toNat = n := by
  constructor
  · intro h; subst h; simp; omega
  · intro h; apply UInt16.toNat_inj.mp; simp; omega

theorem advance_mid (s : State) (hd : s.dot.toNat < 340)
    (h : s.scanline ≠ 261 ∨ s.dot.toNat ≠ 339) :
    s.advance.dot.toNat = s.dot.toNat + 1 ∧ s.advance.scanline = s.scanline ∧
    s.advance.frameOdd = s.frameOdd := by
  have h340 : s.dot ≠ 340 := fun e => by rw [e] at hd; simp at hd
  have hsk : ¬ (s.dot = 339 ∧ s.scanline = 261) := by
    rintro ⟨e1, e2⟩; rcases h with h | h
    · exact h e2
    · exact h (by rw [e1]; rfl)
  simp only [State.advance]
  split
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact absurd ⟨hc.1.1.1, hc.1.1.2⟩ hsk
  · simp only [beq_iff_eq, h340, ↓reduceIte, and_true]
    rw [UInt16.toNat_add]; simp; omega

theorem sfb_advance_wrap (s : State) (hd : s.dot.toNat = 340) (h : s.scanline ≠ 261) :
    s.advance.dot = 0 ∧ s.advance.scanline = s.scanline + 1 := by
  have hd' : s.dot = 340 := (u16_eq_iff _ 340 (by decide)).mpr hd
  simp [State.advance, hd', h]

theorem sfb_advance_wrap261 (s : State) (hd : s.dot.toNat = 340) (h : s.scanline = 261) :
    s.advance.dot = 0 ∧ s.advance.scanline = 0 := by
  have hd' : s.dot = 340 := (u16_eq_iff _ 340 (by decide)).mpr hd
  simp [State.advance, hd', h]

theorem advance_339 (s : State) (hd : s.dot.toNat = 339) (h : s.scanline = 261) :
    (s.frameOdd = true → s.renderLatch = true → s.advance.dot = 0 ∧ s.advance.scanline = 0) ∧
    (s.frameOdd = false → s.advance.dot.toNat = 340 ∧ s.advance.scanline = 261 ∧
      s.advance.frameOdd = false) := by
  have hd' : s.dot = 339 := (u16_eq_iff _ 339 (by decide)).mpr hd
  constructor
  · intro ho hl; simp [State.advance, hd', h, ho, hl]
  · intro ho; simp [State.advance, hd', h, ho]

/-- Within a line (not crossing dot 340, nor the odd-frame skip point), `k` dots of `Ppu.dot`
move the dot by `k` and keep the registers and the frame parity. -/
theorem walk (rd pr) (s : State) (hr : s.rendering = true) (k : Nat)
    (hk : s.dot.toNat + k ≤ 340) (h261 : s.scanline ≠ 261 ∨ s.dot.toNat + k ≤ 339) :
    Cfg s (run (Nes.Ppu.dot rd pr) k s) ∧
    (run (Nes.Ppu.dot rd pr) k s).dot.toNat = s.dot.toNat + k ∧
    (run (Nes.Ppu.dot rd pr) k s).scanline = s.scanline ∧
    (run (Nes.Ppu.dot rd pr) k s).frameOdd = s.frameOdd := by
  induction k with
  | zero => exact ⟨Cfg.refl _, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨c, d, l, o⟩ := ih (by omega) (by omega)
    obtain ⟨c', d', l', o', -⟩ := step_info rd pr _ (c.ren hr)
    obtain ⟨a1, a2, a3⟩ := advance_mid (run (Nes.Ppu.dot rd pr) k s) (by omega)
      (by rcases h261 with h | h
          · left; rw [l]; exact h
          · right; omega)
    show Cfg s (Nes.Ppu.dot rd pr _) ∧ (Nes.Ppu.dot rd pr _).dot.toNat = _ ∧
      (Nes.Ppu.dot rd pr _).scanline = _ ∧ (Nes.Ppu.dot rd pr _).frameOdd = _
    rw [d', l', o', a1, a2, a3, d, l, o]
    exact ⟨c.trans c', by omega, rfl, rfl⟩

/-! ### `v` on dots 257–320 (copy X at 257, copy Y on pre-render 280–304) -/

/-- Unfold `fetchV`, name the bus reads, bit-blast (as `Shifter`'s `fetch_tac`). -/
local macro "late_tac" rd:term : tactic => `(tactic| (
  simp only [Bg.fetchV, ppuAddrBg]
  rw [ptAddr_bool]
  simp only [apply_ite $rd]
  generalize $rd (ntAddr _) = rN
  generalize $rd (atAddr _) = rA
  generalize $rd (ptAddr _ true) = rH
  generalize $rd (ptAddr _ false) = rL
  simp only [fetchDot, atSelect, incX, incY, copyX, copyY, maskX, maskY, activeLine,
    Bool.decide_eq_true] at *
  bv_decide))

theorem le_u16 {a : UInt16} {n : Nat} (hn : n < 65536) : n.toUInt16 ≤ a ↔ n ≤ a.toNat := by
  rw [UInt16.le_iff_toNat_le]; simp; omega
theorem u16_le {a : UInt16} {n : Nat} (hn : n < 65536) : a ≤ n.toUInt16 ↔ a.toNat ≤ n := by
  rw [UInt16.le_iff_toNat_le]; simp; omega

theorem v_257 (rd) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true)
    (hd : s.dot.toNat = 257) : (bgDot rd s).v = copyX s.v s.t := by
  have hd' : s.dot = 257 := (u16_eq_iff _ 257 (by decide)).mpr hd
  rw [bgDot_active rd s hr hl]; dsimp only
  late_tac rd

theorem v_258 (rd) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true)
    (h1 : 258 ≤ s.dot.toNat) (h2 : s.dot.toNat ≤ 320) :
    (bgDot rd s).v =
      if s.scanline = 261 ∧ 280 ≤ s.dot.toNat ∧ s.dot.toNat ≤ 304 then copyY s.v s.t else s.v := by
  have e1 : (258 : UInt16) ≤ s.dot := (le_u16 (n := 258) (by decide)).mpr h1
  have e2 : s.dot ≤ (320 : UInt16) := (u16_le (n := 320) (by decide)).mpr h2
  rw [bgDot_active rd s hr hl]; dsimp only
  by_cases hc : s.scanline = 261 ∧ 280 ≤ s.dot.toNat ∧ s.dot.toNat ≤ 304
  · have c2 : (280 : UInt16) ≤ s.dot := (le_u16 (n := 280) (by decide)).mpr hc.2.1
    have c3 : s.dot ≤ (304 : UInt16) := (u16_le (n := 304) (by decide)).mpr hc.2.2
    have c1 := hc.1
    simp only [hc, and_self, ↓reduceIte]
    late_tac rd
  · have hc' : ¬ (s.scanline = 261 ∧ (280 : UInt16) ≤ s.dot ∧ s.dot ≤ (304 : UInt16)) := by
      rintro ⟨a, b, c⟩
      exact hc ⟨a, (le_u16 (n := 280) (by decide)).mp b, (u16_le (n := 304) (by decide)).mp c⟩
    simp only [hc, ↓reduceIte]
    late_tac rd

theorem copyY_idem (v t : UInt16) : copyY (copyY v t) t = copyY v t := by
  simp only [copyY, maskY]; bv_decide

/-- `v` after the dot `d ∈ 257..320` of an active line from `v = w` at dot 256: `copyX w t`,
then (pre-render line only, from dot 280) `copyY · t`. -/
def lateV (pre : Prop) [Decidable pre] (w t : UInt16) (d : Nat) : UInt16 :=
  if pre ∧ 280 ≤ d then copyY (copyX w t) t else copyX w t

theorem late (rd pr) (s : State) (hr : s.rendering = true) (hl : activeLine s.scanline = true)
    (hd : s.dot.toNat = 256) (n : Nat) (h2 : n + 1 ≤ 64) :
    (run (Nes.Ppu.dot rd pr) (n + 1) s).v = lateV (s.scanline = 261) s.v s.t (257 + n) ∧
    Cfg s (run (Nes.Ppu.dot rd pr) (n + 1) s) ∧
    (run (Nes.Ppu.dot rd pr) (n + 1) s).dot.toNat = 257 + n ∧
    (run (Nes.Ppu.dot rd pr) (n + 1) s).scanline = s.scanline := by
  obtain ⟨c, d, l, -⟩ := walk rd pr s hr (n + 1) (by omega) (Or.inr (by omega))
  refine ⟨?_, c, by omega, l⟩
  induction n with
  | zero =>
    have e := bgEq_ppuDot rd pr s hr
    obtain ⟨a1, a2, -⟩ := advance_mid s (by omega) (Or.inr (by omega))
    obtain ⟨-, -, -, -, -, -, -⟩ := advance_keep s
    show (Nes.Ppu.dot rd pr s).v = _
    rw [e.v, v_257 rd _ (by simp only [State.rendering, (advance_keep s).2.2.2.2.2.2]; exact hr)
      (by rw [a2]; exact hl) (by omega), (advance_keep s).2.2.2.2.1, (advance_tx s).1]
    simp [lateV]
  | succ n ih =>
    obtain ⟨c0, d0, l0, -⟩ := walk rd pr s hr (n + 1) (by omega) (Or.inr (by omega))
    have ihv := ih (by omega) c0 d0 l0
    obtain ⟨c1, d1, l1, -⟩ := walk rd pr s hr (n + 1) (by omega) (Or.inr (by omega))
    show (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) (n + 1) s)).v = _
    generalize run (Nes.Ppu.dot rd pr) (n + 1) s = r at c1 d1 l1 ihv
    have rr : r.rendering = true := c1.ren hr
    have e := bgEq_ppuDot rd pr r rr
    obtain ⟨a1, a2, -⟩ := advance_mid r (by omega) (Or.inr (by omega))
    rw [e.v, v_258 rd _ (by simp only [State.rendering, (advance_keep r).2.2.2.2.2.2]; exact rr)
      (by rw [a2, l1]; exact hl) (by omega) (by omega), (advance_keep r).2.2.2.2.1,
      (advance_tx r).1, a1, a2, ihv, c1.t, l1]
    simp only [lateV]
    by_cases hp : s.scanline = 261
    · simp only [hp, true_and]
      by_cases h3 : 280 ≤ 257 + (n + 1)
      · by_cases h4 : 280 ≤ 257 + n
        · simp only [h3, h4, ↓reduceIte]
          split
          · exact copyY_idem _ _
          · rfl
        · have h5 : 280 ≤ r.dot.toNat + 1 ∧ r.dot.toNat + 1 ≤ 304 := by omega
          simp only [h3, h4, h5, and_self, ↓reduceIte]
      · have h4 : ¬ 280 ≤ 257 + n := by omega
        have h5 : ¬ (280 ≤ r.dot.toNat + 1 ∧ r.dot.toNat + 1 ≤ 304) := by omega
        simp only [h3, h4, h5, ↓reduceIte]
    · simp [hp]

/-! ### Idle dots 338–340 / 0 -/

theorem idle_one (rd pr c V) (s : State) (h : Ready rd c V s) (h1 : 337 ≤ s.dot.toNat)
    (h2 : s.dot.toNat ≤ 339) (h261 : s.scanline ≠ 261 ∨ s.dot.toNat ≠ 339) :
    Ready rd c V (Nes.Ppu.dot rd pr s) ∧ (Nes.Ppu.dot rd pr s).dot.toNat = s.dot.toNat + 1 ∧
    (Nes.Ppu.dot rd pr s).scanline = s.scanline ∧ Cfg s (Nes.Ppu.dot rd pr s) ∧
    (Nes.Ppu.dot rd pr s).frameOdd = s.frameOdd := by
  obtain ⟨c', d', l', o', -⟩ := step_info rd pr s h.ren
  obtain ⟨a1, a2, a3⟩ := advance_mid s (by omega) h261
  refine ⟨Ready.idle rd c V _ (fun s hr => bgEq_ppuDot rd pr s hr) s h (Or.inr ?_), by rw [d', a1],
    by rw [l', a2], c', by rw [o', a3]⟩
  rw [d']
  exact ⟨(le_u16 (n := 338) (by decide)).mpr (by omega), (u16_le (n := 340) (by decide)).mpr (by omega)⟩

theorem idle_wrap (rd pr c V) (s : State) (h : Ready rd c V s) (hd : s.dot.toNat = 340)
    (hl : s.scanline ≠ 261) :
    Ready rd c V (Nes.Ppu.dot rd pr s) ∧ (Nes.Ppu.dot rd pr s).dot = 0 ∧
    (Nes.Ppu.dot rd pr s).scanline = s.scanline + 1 ∧ Cfg s (Nes.Ppu.dot rd pr s) := by
  obtain ⟨c', d', l', -, -⟩ := step_info rd pr s h.ren
  obtain ⟨a1, a2⟩ := sfb_advance_wrap s hd hl
  refine ⟨Ready.idle rd c V _ (fun s hr => bgEq_ppuDot rd pr s hr) s h (Or.inl ?_), by rw [d', a1],
    by rw [l', a2], c'⟩
  rw [d', a1]

/-- From `Ready` at dot 337 of a line other than the pre-render line, four dots reach dot 0 of
the next line, still `Ready`. -/
theorem idle4 (rd pr c V) (s : State) (h : Ready rd c V s) (hd : s.dot.toNat = 337)
    (hl : s.scanline ≠ 261) :
    Ready rd c V (run (Nes.Ppu.dot rd pr) 4 s) ∧ (run (Nes.Ppu.dot rd pr) 4 s).dot = 0 ∧
    (run (Nes.Ppu.dot rd pr) 4 s).scanline = s.scanline + 1 ∧ Cfg s (run (Nes.Ppu.dot rd pr) 4 s) := by
  show Ready rd c V (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr s)))) ∧
    (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr s)))).dot = 0 ∧
    (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr s)))).scanline =
      s.scanline + 1 ∧
    Cfg s (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr s))))
  obtain ⟨r1, d1, l1, c1, -⟩ := idle_one rd pr c V s h (by omega) (by omega) (Or.inl hl)
  obtain ⟨r2, d2, l2, c2, -⟩ := idle_one rd pr c V _ r1 (by omega) (by omega) (Or.inl (by rw [l1]; exact hl))
  obtain ⟨r3, d3, l3, c3, -⟩ := idle_one rd pr c V _ r2 (by omega) (by omega) (Or.inl (by rw [l2, l1]; exact hl))
  obtain ⟨r4, d4, l4, c4⟩ := idle_wrap rd pr c V _ r3 (by omega) (by rw [l3, l2, l1]; exact hl)
  exact ⟨r4, d4, by rw [l4, l3, l2, l1], c1.trans (c2.trans (c3.trans c4))⟩

/-! ### One visible line -/

/-- First tile of the next line, from the first tile `u` of this one: 34 coarse-X steps (two
prefetched + 32 drawn), `incY` at dot 256, horizontal reload from `t` at dot 257. -/
def nextU (t u : UInt16) : UInt16 := copyX (incY (Nat.repeat incX 34 u)) t

theorem pos_dot (s : State) (n : Nat) (hn : n < 65536) (h : s.dot.toNat = n) : s.dot = n.toUInt16 :=
  (u16_eq_iff _ n hn).mpr h

theorem step_256 (rd pr) (r : State) (hr : r.rendering = true) (hl : r.scanline < 240)
    (hd : r.dot = 255) : (Nes.Ppu.dot rd pr r).v = incY (incX r.v) := by
  have e := bgEq_ppuDot rd pr r hr
  rw [e.v, advance_vis r hl (by rw [hd]; decide)]
  have := fetch_v rd { r with dot := r.dot + 1 } hr (act_of_lt hl)
    (Or.inl (by dsimp only; rw [hd]; decide))
  rw [this]; simp [hd]

theorem repeat_succ (f : UInt16 → UInt16) (n : Nat) (a : UInt16) :
    Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := rfl

theorem ne261_of_lt {sl : UInt16} (h : sl < 240) : sl ≠ 261 := by
  intro e; rw [e] at h; exact absurd h (by decide)

/-- **Line to line.** From `Start rd c u` at dot 0 of visible line `y < 239`, 341 dots of
`Ppu.dot` reach dot 0 of line `y + 1` in `Start rd c (nextU t u)`. -/
theorem line_step (rd pr c u) (s : State) (h : Start rd c u s) (hy : s.scanline.toNat + 1 < 240) :
    Start rd c (nextU s.t u) (run (Nes.Ppu.dot rd pr) 341 s) ∧
    (run (Nes.Ppu.dot rd pr) 341 s).scanline = s.scanline + 1 ∧
    Cfg s (run (Nes.Ppu.dot rd pr) 341 s) := by
  have hf : ∀ s : State, s.rendering = true → BgEq (bgDot rd s.advance) (Nes.Ppu.dot rd pr s) :=
    fun s hr => bgEq_ppuDot rd pr s hr
  have hd0 : s.dot.toNat = 0 := by rw [h.dot]; rfl
  have n261 := ne261_of_lt h.line
  -- dots 1–255 (shifter invariant), 256
  obtain ⟨pi, -, -⟩ := scan rd c u _ hf s h 255 (by decide) (by decide)
  obtain ⟨c255, d255, l255, -⟩ := walk rd pr s h.ren 255 (by omega) (Or.inl n261)
  have p255 : (run (Nes.Ppu.dot rd pr) 255 s).dot = 255 := pos_dot _ 255 (by decide) (by omega)
  have v255 : (run (Nes.Ppu.dot rd pr) 255 s).v = incX (incX (Nat.repeat incX 31 u)) :=
    pi.v (by simp only [ph, p255]; decide)
  have v256 : (run (Nes.Ppu.dot rd pr) 256 s).v = incY (Nat.repeat incX 34 u) := by
    rw [run_succ1 _ 255 s,
      step_256 rd pr _ (c255.ren h.ren) (by rw [l255]; exact h.line) p255, v255]
    rfl
  obtain ⟨c256, d256, l256, -⟩ := walk rd pr s h.ren 256 (by omega) (Or.inl n261)
  have hact : activeLine (run (Nes.Ppu.dot rd pr) 256 s).scanline = true := by
    rw [l256]; exact act_of_lt h.line
  -- dots 257–320
  obtain ⟨v320, c320, d320, l320⟩ := late rd pr _ (c256.ren h.ren) hact (by omega) 63 (by decide)
  simp only [lateV, l256, n261, false_and, ↓reduceIte, v256, c256.t] at v320
  rw [← run_add] at v320 c320 d320 l320
  simp only [Nat.reduceAdd] at v320 c320 d320 l320
  -- dots 321–337
  obtain ⟨rdy, d337, l337⟩ := prefetch rd c _ _ hf _ (c320.ren (c256.ren h.ren))
    (by rw [l320, l256]; exact act_of_lt h.line) (by rw [c320.ctrl, c256.ctrl, h.ctrl])
    (pos_dot _ 320 (by decide) (by omega)) v320
  obtain ⟨c337, -, -, -⟩ := walk rd pr _ (c320.ren (c256.ren h.ren)) 17 (by omega)
    (Or.inl (by rw [l320, l256]; exact n261))
  rw [← run_add] at rdy d337 l337 c337
  simp only [Nat.reduceAdd] at rdy d337 l337 c337
  -- dots 338–340, 0
  obtain ⟨rdy', d0, l0, c4⟩ := idle4 rd pr c _ _ rdy (by rw [d337]; rfl)
    (by rw [l337, l320, l256]; exact n261)
  rw [← run_add] at rdy' d0 l0 c4
  simp only [Nat.reduceAdd] at rdy' d0 l0 c4
  have hl1 : (run (Nes.Ppu.dot rd pr) 341 s).scanline = s.scanline + 1 := by
    rw [l0, l337, l320, l256]
  refine ⟨?_, hl1, c256.trans (c320.trans (c337.trans c4))⟩
  have := rdy'.start d0 (by
    rw [hl1, UInt16.lt_iff_toNat_lt, UInt16.toNat_add]; simp; omega)
  rw [show nextU s.t u = copyX (incY (Nat.repeat incX 34 u)) s.t from rfl]
  exact this

/-- `Start` at dot 0 of line 0, after `y` lines: `Start` at dot 0 of line `y`. -/
theorem lines (rd pr c u) (s : State) (h : Start rd c u s) (h0 : s.scanline = 0) :
    ∀ y, y < 240 → Start rd c (Nat.repeat (nextU s.t) y u) (run (Nes.Ppu.dot rd pr) (341 * y) s) ∧
      (run (Nes.Ppu.dot rd pr) (341 * y) s).scanline.toNat = y ∧
      Cfg s (run (Nes.Ppu.dot rd pr) (341 * y) s)
  | 0, _ => ⟨h, by rw [show 341 * 0 = 0 from rfl]; simp [run, h0], Cfg.refl _⟩
  | y + 1, hy => by
    obtain ⟨st, l, cf⟩ := lines rd pr c u s h h0 y (by omega)
    obtain ⟨st', l', cf'⟩ := line_step rd pr c _ _ st (by omega)
    rw [← run_add, show 341 * y + 341 = 341 * (y + 1) by omega, cf.t] at st'
    rw [← run_add, show 341 * y + 341 = 341 * (y + 1) by omega] at l' cf'
    refine ⟨st', ?_, cf.trans cf'⟩
    rw [l', UInt16.toNat_add]; simp; omega

/-! ### The pre-render line -/

/-- **Pre-render line.** From dot 0 of line 261 (rendering on), `341 - [odd frame]` dots of
`Ppu.dot` reach dot 0 of line 0 in `Start rd c (copyY (copyX w t) t)`, where `w` is whatever
`v` was at dot 256 — so all 15 bits of the first tile address come from `t`. -/
theorem prerender (rd pr c) (s : State) (hr : s.rendering = true) (hc : s.ctrl = c)
    (hd : s.dot = 0) (hl : s.scanline = 261) :
    ∃ w, Start rd c (copyY (copyX w s.t) s.t)
        (run (Nes.Ppu.dot rd pr) (341 - (if s.frameOdd then 1 else 0)) s) ∧
      (run (Nes.Ppu.dot rd pr) (341 - (if s.frameOdd then 1 else 0)) s).scanline = 0 ∧
      Cfg s (run (Nes.Ppu.dot rd pr) (341 - (if s.frameOdd then 1 else 0)) s) := by
  have hf : ∀ s : State, s.rendering = true → BgEq (bgDot rd s.advance) (Nes.Ppu.dot rd pr s) :=
    fun s hr => bgEq_ppuDot rd pr s hr
  have hd0 : s.dot.toNat = 0 := by rw [hd]; rfl
  have hact : activeLine (261 : UInt16) = true := by decide
  obtain ⟨c256, d256, l256, o256⟩ := walk rd pr s hr 256 (by omega) (Or.inr (by omega))
  refine ⟨(run (Nes.Ppu.dot rd pr) 256 s).v, ?_⟩
  obtain ⟨v320, c320, d320, l320⟩ := late rd pr _ (c256.ren hr) (by rw [l256, hl]; exact hact)
    (by omega) 63 (by decide)
  simp only [lateV, l256, hl, true_and, show 280 ≤ 257 + 63 by decide, ↓reduceIte, c256.t] at v320
  obtain ⟨c320', -, -, o320⟩ := walk rd pr _ (c256.ren hr) 64 (by omega) (Or.inr (by omega))
  rw [← run_add] at v320 c320 d320 l320 c320' o320
  simp only [Nat.reduceAdd] at v320 c320 d320 l320 c320' o320
  have r320 := c320.ren (c256.ren hr)
  obtain ⟨rdy, d337, l337⟩ := prefetch rd c _ _ hf _ r320
    (by rw [l320, l256, hl]; exact hact) (by rw [c320.ctrl, c256.ctrl, hc])
    (pos_dot _ 320 (by decide) (by omega)) v320
  obtain ⟨c337, -, -, o337⟩ := walk rd pr _ r320 17 (by omega) (Or.inr (by omega))
  rw [← run_add] at rdy d337 l337 c337 o337
  simp only [Nat.reduceAdd] at rdy d337 l337 c337 o337
  have cA := c256.trans (c320.trans c337)
  -- 338 (latches the odd-frame skip), 339
  obtain ⟨r1, d1, l1, c1, o1⟩ := idle_one rd pr c _ _ rdy (by rw [d337]; decide) (by rw [d337]; decide)
    (Or.inr (by rw [d337]; decide))
  have lat1 := (step_info rd pr _ rdy.ren).2.2.2.2
  have p1 : (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s)).dot = 338 :=
    pos_dot _ 338 (by decide) (by rw [d1, d337]; rfl)
  simp only [l1, l337, l320, l256, hl, p1, and_self, ↓reduceIte] at lat1
  have d337n : (run (Nes.Ppu.dot rd pr) 337 s).dot.toNat = 337 := by rw [d337]; rfl
  obtain ⟨r2, d2, l2, c2, o2⟩ := idle_one rd pr c _ _ r1 (by omega) (by omega) (Or.inr (by omega))
  have lat2 := (step_info rd pr _ r1.ren).2.2.2.2
  have n338 : ¬ ((Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s))).scanline = 261 ∧
      (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s))).dot = 338) := by
    rintro ⟨-, e⟩; rw [e] at d2; rw [d1, d337] at d2; exact absurd d2 (by decide)
  simp only [n338, ↓reduceIte] at lat2
  have hl2 : (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s))).scanline = 261 := by
    rw [l2, l1, l337, l320, l256, hl]
  have hd2 : (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s))).dot.toNat = 339 := by
    rw [d2, d1, d337]; rfl
  have ho2 : (Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s))).frameOdd =
      s.frameOdd := by rw [o2, o1, o337, o320, o256]
  have e339 : Nes.Ppu.dot rd pr (Nes.Ppu.dot rd pr (run (Nes.Ppu.dot rd pr) 337 s)) =
      run (Nes.Ppu.dot rd pr) 339 s := by
    rw [← run_succ1 (Nes.Ppu.dot rd pr), ← run_succ1 (Nes.Ppu.dot rd pr)]
  rw [e339] at r2 lat2 hl2 hd2 ho2 c2
  have cB := cA.trans (c1.trans c2)
  rw [lat1] at lat2
  cases hodd : s.frameOdd
  · -- even frame: 340, then (0, 0)
    obtain ⟨-, a2⟩ := advance_339 _ hd2 hl2
    obtain ⟨a3, a4, -⟩ := a2 (by rw [ho2, hodd])
    obtain ⟨c3, d3, l3, -, -⟩ := step_info rd pr _ r2.ren
    have r3 := Ready.idle rd c _ _ hf _ r2 (Or.inr (by
      rw [d3]; exact ⟨(le_u16 (n := 338) (by decide)).mpr (by omega),
        (u16_le (n := 340) (by decide)).mpr (by omega)⟩))
    rw [← run_succ1 (Nes.Ppu.dot rd pr)] at r3 c3 d3 l3
    obtain ⟨c4, d4, l4, -, -⟩ := step_info rd pr _ r3.ren
    obtain ⟨a5, a6⟩ := sfb_advance_wrap261 _ (by rw [d3, a3]) (by rw [l3, a4])
    have r4 := Ready.idle rd c _ _ hf _ r3 (Or.inl (by rw [d4, a5]))
    rw [← run_succ1 (Nes.Ppu.dot rd pr)] at r4 c4 d4 l4
    simp only [Nat.reduceAdd] at r4 c4 d4 l4
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
    exact ⟨r4.start (by rw [d4, a5]) (by rw [l4, a6]; decide), by rw [l4, a6],
      cB.trans (c3.trans c4)⟩
  · -- odd frame: the idle dot is skipped, (261, 339) → (0, 0)
    obtain ⟨a1, -⟩ := advance_339 _ hd2 hl2
    obtain ⟨a3, a4⟩ := a1 (by rw [ho2, hodd]) lat2
    obtain ⟨c3, d3, l3, -, -⟩ := step_info rd pr _ r2.ren
    have r3 := Ready.idle rd c _ _ hf _ r2 (Or.inl (by rw [d3, a3]))
    rw [← run_succ1 (Nes.Ppu.dot rd pr)] at r3 c3 d3 l3
    simp only [Nat.reduceAdd] at r3 c3 d3 l3
    simp only [↓reduceIte, Nat.reduceSub]
    exact ⟨r3.start (by rw [d3, a3]) (by rw [l3, a4]; decide), by rw [l3, a4], cB.trans c3⟩

/-! ### Vertical blank: lines 241–260 -/

theorem wrap_step (rd pr) (s : State) (hr : s.rendering = true) (hd : s.dot.toNat = 340)
    (hl : s.scanline ≠ 261) :
    (Nes.Ppu.dot rd pr s).dot = 0 ∧ (Nes.Ppu.dot rd pr s).scanline = s.scanline + 1 ∧
    Cfg s (Nes.Ppu.dot rd pr s) ∧ (Nes.Ppu.dot rd pr s).frameOdd = s.frameOdd := by
  obtain ⟨c', d', l', o', -⟩ := step_info rd pr s hr
  have hd' : s.dot = 340 := pos_dot _ 340 (by decide) hd
  obtain ⟨a1, a2⟩ := sfb_advance_wrap s hd hl
  refine ⟨by rw [d', a1], by rw [l', a2], c', ?_⟩
  rw [o']; simp [State.advance, hd', hl]

/-- A whole non-pre-render line from dot 0: 341 dots to dot 0 of the next line. -/
theorem full_line (rd pr) (s : State) (hr : s.rendering = true) (hd : s.dot = 0)
    (hl : s.scanline.toNat < 261) :
    (run (Nes.Ppu.dot rd pr) 341 s).dot = 0 ∧
    (run (Nes.Ppu.dot rd pr) 341 s).scanline.toNat = s.scanline.toNat + 1 ∧
    Cfg s (run (Nes.Ppu.dot rd pr) 341 s) ∧ (run (Nes.Ppu.dot rd pr) 341 s).frameOdd = s.frameOdd := by
  have hd0 : s.dot.toNat = 0 := by rw [hd]; rfl
  have n261 : s.scanline ≠ 261 := fun e => by rw [e] at hl; exact absurd hl (by decide)
  obtain ⟨c1, d1, l1, o1⟩ := walk rd pr s hr 340 (by omega) (Or.inl n261)
  obtain ⟨a1, a2, a3, a4⟩ := wrap_step rd pr _ (c1.ren hr) (by omega) (by rw [l1]; exact n261)
  rw [← run_succ1 (Nes.Ppu.dot rd pr)] at a1 a2 a3 a4
  refine ⟨a1, ?_, c1.trans a3, by rw [a4, o1]⟩
  rw [a2, l1, UInt16.toNat_add]; simp; omega

theorem vblank_lines (rd pr) (s : State) (hr : s.rendering = true) (hd : s.dot = 0) :
    ∀ m, s.scanline.toNat + m ≤ 261 →
    (run (Nes.Ppu.dot rd pr) (341 * m) s).dot = 0 ∧
    (run (Nes.Ppu.dot rd pr) (341 * m) s).scanline.toNat = s.scanline.toNat + m ∧
    Cfg s (run (Nes.Ppu.dot rd pr) (341 * m) s) ∧
    (run (Nes.Ppu.dot rd pr) (341 * m) s).frameOdd = s.frameOdd
  | 0, _ => ⟨by simp [run, hd], by simp [run], Cfg.refl _, by simp [run]⟩
  | m + 1, hm => by
    obtain ⟨d, l, c, o⟩ := vblank_lines rd pr s hr hd m (by omega)
    obtain ⟨d', l', c', o'⟩ := full_line rd pr _ (c.ren hr) d (by omega)
    rw [← run_add, show 341 * m + 341 = 341 * (m + 1) by omega] at d' l' c' o'
    exact ⟨d', by rw [l', l]; omega, c.trans c', by rw [o', o]⟩

/-- From anywhere in lines 241–260, `341·(261 - line) - dot` dots reach dot 0 of the
pre-render line. -/
theorem to_prerender (rd pr) (s : State) (hr : s.rendering = true)
    (hl1 : 241 ≤ s.scanline.toNat) (hl2 : s.scanline.toNat ≤ 260) (hd : s.dot.toNat ≤ 340) :
    (run (Nes.Ppu.dot rd pr) (341 * (261 - s.scanline.toNat) - s.dot.toNat) s).dot = 0 ∧
    (run (Nes.Ppu.dot rd pr) (341 * (261 - s.scanline.toNat) - s.dot.toNat) s).scanline = 261 ∧
    Cfg s (run (Nes.Ppu.dot rd pr) (341 * (261 - s.scanline.toNat) - s.dot.toNat) s) ∧
    (run (Nes.Ppu.dot rd pr) (341 * (261 - s.scanline.toNat) - s.dot.toNat) s).frameOdd =
      s.frameOdd := by
  have n261 : s.scanline ≠ 261 := fun e => by rw [e] at hl2; exact absurd hl2 (by decide)
  obtain ⟨c1, d1, l1, o1⟩ := walk rd pr s hr (340 - s.dot.toNat) (by omega) (Or.inl n261)
  obtain ⟨a1, a2, a3, a4⟩ := wrap_step rd pr _ (c1.ren hr) (by omega) (by rw [l1]; exact n261)
  rw [← run_succ1 (Nes.Ppu.dot rd pr)] at a1 a2 a3 a4
  obtain ⟨b1, b2, b3, b4⟩ := vblank_lines rd pr _ (a3.ren (c1.ren hr)) a1 (260 - s.scanline.toNat)
    (by rw [a2, l1, UInt16.toNat_add]; simp; omega)
  rw [← run_add, show 340 - s.dot.toNat + 1 + 341 * (260 - s.scanline.toNat) =
    341 * (261 - s.scanline.toNat) - s.dot.toNat by omega] at b1 b2 b3 b4
  refine ⟨b1, ?_, c1.trans (a3.trans b3), by rw [b4, a4, o1]⟩
  apply (u16_eq_iff _ 261 (by decide)).mpr
  rw [b2, a2, l1, UInt16.toNat_add]; simp; omega

/-! ### The frame, pipeline side -/

/-- Static-frame hypotheses on the snapshot `s0` (the run itself is `Ppu.dot rd pr` iterated, so
no register / VRAM / OAM write can occur and `rd`, `pr` are constant by construction):
rendering enabled, and `s0` in vertical blank (lines 241–260), at a valid dot. -/
structure Static (s0 : State) : Prop where
  ren : s0.rendering = true
  vbl1 : 241 ≤ s0.scanline.toNat
  vbl2 : s0.scanline.toNat ≤ 260
  dot : s0.dot.toNat ≤ 340

/-- Dots from `s0` to dot 0 of line 0: the rest of vblank, then the pre-render line (one dot
shorter on odd frames). -/
def frameStart (s0 : State) : Nat :=
  341 * (261 - s0.scanline.toNat) - s0.dot.toNat + (341 - if s0.frameOdd then 1 else 0)

/-- Background pixels of the first frame after `s0`, pipeline side: screen pixel `(x, y)` is
produced at dot `x + 1` of line `y`, `frameStart s0 + 341·y + x + 1` dots after `s0`, and is
pixel `(x + fine x) mod 8` of the tile `(x + fine x) / 8` coarse-X steps after the first tile of
line `y`, which is `nextU t` iterated `y` times on `copyY (copyX w t) t`. -/
theorem bg_frame_pipeline (rd pr) (s0 : State) (hs : Static s0) :
    ∃ w, ∀ y, y < 240 → ∀ x, x < 256 →
      (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0).scanline.toNat = y ∧
      (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0).dot.toNat = x + 1 ∧
      bgPixelRaw (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0) =
        tilePx (tileBits rd s0.ctrl (Nat.repeat incX ((x + (s0.x &&& 7).toNat) / 8)
            (Nat.repeat (nextU s0.t) y (copyY (copyX w s0.t) s0.t))))
          ((x + (s0.x &&& 7).toNat) % 8).toUInt16 := by
  obtain ⟨p1, p2, pc, po⟩ := to_prerender rd pr s0 hs.ren hs.vbl1 hs.vbl2 hs.dot
  obtain ⟨w, st, l0, cf⟩ := prerender rd pr s0.ctrl _ (pc.ren hs.ren) (by rw [pc.ctrl]) p1 p2
  rw [← run_add, po, pc.t] at st
  rw [← run_add, po] at l0
  rw [← run_add, po] at cf
  have cf := pc.trans cf
  have hfs : 341 * (261 - s0.scanline.toNat) - s0.dot.toNat + (341 - if s0.frameOdd then 1 else 0)
      = frameStart s0 := rfl
  rw [hfs] at st l0 cf
  refine ⟨w, fun y hy x hx => ?_⟩
  obtain ⟨st', ly, cy⟩ := lines rd pr _ _ _ st l0 y hy
  rw [← run_add, cf.t] at st'
  rw [← run_add] at ly cy
  have hpix := bg_scanline_ppuDot rd pr s0.ctrl _ _ st' (x + 1) (by omega) (by omega)
  obtain ⟨cx, dx, lx, -⟩ := walk rd pr _ st'.ren (x + 1)
    (by rw [st'.dot]; simp; omega) (Or.inl (ne261_of_lt st'.line))
  rw [← run_add] at hpix cx dx lx
  rw [Nat.add_sub_cancel, cy.x, cf.x] at hpix
  refine ⟨by rw [lx, ly], by rw [dx, st'.dot]; simp, hpix⟩

/-! ### Loopy arithmetic: horizontal / vertical positions -/

/-- Horizontal tile position of a loopy word, `0 … 63`: coarse X + 32 · horizontal nametable. -/
def hx (w : UInt16) : Nat := w.toNat % 32 + 32 * (w.toNat / 1024 % 2)
/-- Vertical pixel position of a loopy word, `0 … 511`: fine Y + 8 · coarse Y + 256 · vertical
nametable (rows 240–255 are the out-of-range coarse Y 30/31). -/
def vy (w : UInt16) : Nat := w.toNat / 4096 % 8 + 8 * (w.toNat / 32 % 32) + 256 * (w.toNat / 2048 % 2)

/-- One `incY` on the vertical position: rows `< 240` count modulo 240 and toggle the nametable
on the wrap; rows 240–255 count to 255 and wrap to 0 without toggling. -/
def vstep (b : Nat) : Nat :=
  if b % 256 = 239 then (if b < 256 then 256 else 0) else if b % 256 = 255 then b - 255 else b + 1

local macro "u16_nat" h:ident : tactic => `(tactic| (
  have h' := congrArg UInt16.toNat $h
  simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
    UInt16.reduceToNat, Nat.reducePow] at h'
  first | (simp only [hx, vy] at *; omega) | omega))

theorem hx_incX (w : UInt16) : hx (incX w) = (hx w + 1) % 64 := by
  have h : incX w % 32 + 32 * (incX w / 1024 % 2) = (w % 32 + 32 * (w / 1024 % 2) + 1) % 64 := by
    simp only [incX]; bv_decide
  u16_nat h

theorem vy_incX (w : UInt16) : vy (incX w) = vy w := by
  have h : incX w / 4096 % 8 + 8 * (incX w / 32 % 32) + 256 * (incX w / 2048 % 2) =
      w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2) := by
    simp only [incX]; bv_decide
  u16_nat h

theorem hx_incY (w : UInt16) : hx (incY w) = hx w := by
  have h : incY w % 32 + 32 * (incY w / 1024 % 2) = w % 32 + 32 * (w / 1024 % 2) := by
    simp only [incY, bne_iff_ne, beq_iff_eq, ne_eq]; bv_decide
  u16_nat h

theorem hx_copyX (v t : UInt16) : hx (copyX v t) = hx t := by
  have h : copyX v t % 32 + 32 * (copyX v t / 1024 % 2) = t % 32 + 32 * (t / 1024 % 2) := by
    simp only [copyX, maskX]; bv_decide
  u16_nat h

theorem vy_copyX (v t : UInt16) : vy (copyX v t) = vy v := by
  have h : copyX v t / 4096 % 8 + 8 * (copyX v t / 32 % 32) + 256 * (copyX v t / 2048 % 2) =
      v / 4096 % 8 + 8 * (v / 32 % 32) + 256 * (v / 2048 % 2) := by
    simp only [copyX, maskX]; bv_decide
  u16_nat h

theorem hx_copyY (v t : UInt16) : hx (copyY v t) = hx v := by
  have h : copyY v t % 32 + 32 * (copyY v t / 1024 % 2) = v % 32 + 32 * (v / 1024 % 2) := by
    simp only [copyY, maskY]; bv_decide
  u16_nat h

theorem vy_copyY (v t : UInt16) : vy (copyY v t) = vy t := by
  have h : copyY v t / 4096 % 8 + 8 * (copyY v t / 32 % 32) + 256 * (copyY v t / 2048 % 2) =
      t / 4096 % 8 + 8 * (t / 32 % 32) + 256 * (t / 2048 % 2) := by
    simp only [copyY, maskY]; bv_decide
  u16_nat h

theorem vy_toNat (w : UInt16) :
    (w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2)).toNat = vy w := by
  simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
    UInt16.reduceToNat, Nat.reducePow, vy]
  omega

theorem vy_incY (w : UInt16) : vy (incY w) = vstep (vy w) := by
  have h : incY w / 4096 % 8 + 8 * (incY w / 32 % 32) + 256 * (incY w / 2048 % 2) =
      (if (w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2)) % 256 = 239 then
        (if w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2) < 256 then 256 else 0)
       else if (w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2)) % 256 = 255 then
        w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2) - 255
       else w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2) + 1) := by
    simp only [incY, bne_iff_ne, beq_iff_eq, ne_eq]; bv_decide
  have hi := congrArg UInt16.toNat h
  rw [vy_toNat] at hi
  have hb := vy_toNat w
  have hlt : vy w < 512 := by simp only [vy]; omega
  generalize w / 4096 % 8 + 8 * (w / 32 % 32) + 256 * (w / 2048 % 2) = b at hi hb
  rw [hi]
  unfold vstep
  have m1 : b % 256 = 239 ↔ b.toNat % 256 = 239 := by rw [← UInt16.toNat_inj]; simp
  have m2 : b % 256 = 255 ↔ b.toNat % 256 = 255 := by rw [← UInt16.toNat_inj]; simp
  have m3 : b < 256 ↔ b.toNat < 256 := by rw [UInt16.lt_iff_toNat_lt]; simp
  rw [← hb]
  by_cases c1 : b.toNat % 256 = 239
  · rw [ite_eq_left (m1.mpr c1), ite_eq_left c1]
    by_cases c3 : b.toNat < 256
    · rw [ite_eq_left (m3.mpr c3), ite_eq_left c3]; rfl
    · rw [ite_eq_right (fun h => c3 (m3.mp h)), ite_eq_right c3]; rfl
  · rw [ite_eq_right (fun h => c1 (m1.mp h)), ite_eq_right c1]
    by_cases c2 : b.toNat % 256 = 255
    · rw [ite_eq_left (m2.mpr c2), ite_eq_left c2]
      rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]; simp
    · rw [ite_eq_right (fun h => c2 (m2.mp h)), ite_eq_right c2]
      rw [UInt16.toNat_add]; simp; omega

/-! ### Closed forms: `k` coarse-X steps, `y` lines -/

theorem hx_repeat (k : Nat) (w : UInt16) : hx (Nat.repeat incX k w) = (hx w + k) % 64 := by
  induction k with
  | zero => simp only [Nat.repeat, Nat.add_zero]; simp only [hx]; omega
  | succ k ih => rw [repeat_succ, hx_incX, ih]; omega

theorem vy_repeat (k : Nat) (w : UInt16) : vy (Nat.repeat incX k w) = vy w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repeat_succ, vy_incX, ih]

theorem hx_nextU (t u : UInt16) : hx (nextU t u) = hx t := hx_copyX _ _
theorem vy_nextU (t u : UInt16) : vy (nextU t u) = vstep (vy u) := by
  rw [nextU, vy_copyX, vy_incY, vy_repeat]

theorem hx_lines (t u : UInt16) (hu : hx u = hx t) (y : Nat) :
    hx (Nat.repeat (nextU t) y u) = hx t := by
  cases y with
  | zero => exact hu
  | succ y => exact hx_nextU _ _

theorem vy_lines (t u : UInt16) (y : Nat) :
    vy (Nat.repeat (nextU t) y u) = Nat.repeat vstep y (vy u) := by
  induction y with
  | zero => rfl
  | succ y ih => show vy (nextU t _) = vstep _; rw [vy_nextU, ih]

/-- Vertical position after `y` line increments from `b0` (for `y < 240`; see `scrollY`). -/
def vclosed (b0 y : Nat) : Nat :=
  if b0 % 256 < 240 then 256 * ((b0 / 256 + (b0 % 256 + y) / 240) % 2) + (b0 % 256 + y) % 240
  else 256 * (b0 / 256) + (b0 % 256 + y) % 256

theorem vclosed_step (b0 y : Nat) (hy : y + 1 < 240) :
    vstep (vclosed b0 y) = vclosed b0 (y + 1) := by
  unfold vclosed
  by_cases h0 : b0 % 256 < 240
  · simp only [h0, ↓reduceIte]; unfold vstep; repeat' split
    all_goals omega
  · simp only [h0, ↓reduceIte]; unfold vstep; repeat' split
    all_goals omega

theorem vy_lt (w : UInt16) : vy w < 512 := by simp only [vy]; omega

theorem repeat_vstep (b0 : Nat) (hb : b0 < 512) : ∀ y, y < 240 → Nat.repeat vstep y b0 = vclosed b0 y
  | 0, _ => by simp only [Nat.repeat, vclosed]; split <;> omega
  | y + 1, hy => by
    show vstep (Nat.repeat vstep y b0) = _
    rw [repeat_vstep b0 hb y (by omega), vclosed_step b0 y hy]

/-! ### Bus addresses of a loopy word in `Nat` -/

/-- Background index of a tile pixel, written exactly as `Declarative.bgPixel` after the scroll:
column `col` / horizontal nametable `nx`, row `row` / vertical nametable `ny`. -/
def pixN (rd : UInt16 → UInt8) (bgT : Bool) (col nx row ny : Nat) : UInt8 :=
  let nt := 0x2000 + 0x400 * (2 * ny + nx)
  let tile := rd (nt + 32 * (row / 8) + col / 8).toUInt16
  let attr := rd (nt + 0x3C0 + 8 * (row / 32) + col / 32).toUInt16
  let pal := attr.toNat / 2 ^ (4 * (row / 16 % 2) + 2 * (col / 16 % 2)) % 4
  let pt := (if bgT then 0x1000 else 0) + 16 * tile.toNat + row % 8
  let pat := Declarative.bit (rd pt.toUInt16) (7 - col % 8) +
    2 * Declarative.bit (rd (pt + 8).toUInt16) (7 - col % 8)
  if pat = 0 then 0 else (4 * pal + pat).toUInt8

theorem bgPixel_pixN (s0 : State) (rd : UInt16 → UInt8) (x y : Nat) :
    Declarative.bgPixel s0 rd x y = pixN rd s0.bgTable (Declarative.scrollX s0 x).1
      (Declarative.scrollX s0 x).2 (Declarative.scrollY s0 y).1 (Declarative.scrollY s0 y).2 := rfl

local macro "to_nat" : tactic => `(tactic| (
  simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
    UInt16.reduceToNat, Nat.reducePow, hx, vy, UInt8.toNat_toUInt16, Nat.toNat_toUInt16] at *))

theorem hx_lo (w : UInt16) : hx w % 32 = w.toNat % 32 := by simp only [hx]; omega
theorem hx_hi (w : UInt16) : hx w / 32 = w.toNat / 1024 % 2 := by simp only [hx]; omega
theorem vy_hi (w : UInt16) : vy w / 256 = w.toNat / 2048 % 2 := by simp only [vy]; omega
theorem vy_row (w : UInt16) : vy w % 256 = w.toNat / 4096 % 8 + 8 * (w.toNat / 32 % 32) := by
  simp only [vy]; omega

theorem ntAddr_nat (w : UInt16) :
    ntAddr w = (0x2000 + 0x400 * (2 * (vy w / 256) + hx w / 32) + 32 * (vy w % 256 / 8) +
      hx w % 32).toUInt16 := by
  have h : ntAddr w = 0x2000 + 0x400 * (2 * (w / 2048 % 2) + w / 1024 % 2) + 32 * (w / 32 % 32) +
      w % 32 := by simp only [ntAddr]; bv_decide
  rw [h, hx_lo, hx_hi, vy_hi, vy_row, show ∀ a b : Nat, a < 8 → (a + 8 * b) / 8 = b by
    intro a b h; omega]
  · apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow]
    simp
  · omega

theorem atAddr_nat (w : UInt16) :
    atAddr w = (0x2000 + 0x400 * (2 * (vy w / 256) + hx w / 32) + 0x3C0 + 8 * (vy w % 256 / 32) +
      hx w % 32 / 4).toUInt16 := by
  have h : atAddr w = 0x2000 + 0x400 * (2 * (w / 2048 % 2) + w / 1024 % 2) + 0x3C0 +
      8 * (w / 32 % 32 / 4) + w % 32 / 4 := by simp only [atAddr]; bv_decide
  rw [h, hx_lo, hx_hi, vy_hi, vy_row, show ∀ a b : Nat, a < 8 → (a + 8 * b) / 32 = b / 4 by
    intro a b h; omega]
  · apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow]
    simp
  · omega

theorem atSelect_nat (w : UInt16) (b : UInt8) :
    (atSelect w b &&& 3).toNat =
      b.toNat / 2 ^ (4 * (vy w % 256 / 16 % 2) + 2 * (hx w % 32 / 2 % 2)) % 4 := by
  have h : atSelect w b &&& 3 = (b >>> (4 * (w / 64 % 2) + 2 * (w / 2 % 2)).toUInt8) &&& 3 := by
    simp only [atSelect]; bv_decide
  rw [h, UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    show (3 : UInt8).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  congr 3
  have hw : w.toNat < 65536 := UInt16.toNat_lt w
  have e1 : ∀ a b : Nat, a < 8 → (a + 8 * b) / 16 = b / 2 := by intro a b h; omega
  have e2 : w.toNat / 32 % 32 / 2 % 2 = w.toNat / 64 % 2 := by omega
  rw [vy_row, hx_lo, e1 _ _ (by omega), e2, show w.toNat % 32 / 2 % 2 = w.toNat / 2 % 2 by omega]
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod,
    UInt16.toNat_div, UInt16.reduceToNat, Nat.reducePow]
  omega

theorem ptAddrOf_lo (c b : UInt8) (w : UInt16) :
    ptAddrOf c b w false =
      ((if c &&& 0x10 != 0 then 0x1000 else 0) + 16 * b.toNat + vy w % 256 % 8).toUInt16 := by
  rw [vy_row]
  apply UInt16.toNat_inj.mp
  have hb : b.toNat < 256 := b.toNat_lt
  cases hc : (c &&& 0x10 != 0)
  · have h : ptAddrOf c b w false = 16 * b.toUInt16 + w / 4096 % 8 := by
      simp only [ptAddrOf, hc]; simp only [Bool.false_eq_true, ↓reduceIte] at *
      bv_decide
    rw [h]; simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow, UInt8.toNat_toUInt16]
    simp <;> omega
  · have h : ptAddrOf c b w false = 0x1000 + 16 * b.toUInt16 + w / 4096 % 8 := by
      simp only [ptAddrOf, hc]; simp only [↓reduceIte] at *
      bv_decide
    rw [h]; simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow, UInt8.toNat_toUInt16]
    simp <;> omega

theorem ptAddrOf_hi (c b : UInt8) (w : UInt16) :
    ptAddrOf c b w true =
      ((if c &&& 0x10 != 0 then 0x1000 else 0) + 16 * b.toNat + vy w % 256 % 8 + 8).toUInt16 := by
  rw [vy_row]
  apply UInt16.toNat_inj.mp
  have hb : b.toNat < 256 := b.toNat_lt
  cases hc : (c &&& 0x10 != 0)
  · have h : ptAddrOf c b w true = 16 * b.toUInt16 + w / 4096 % 8 + 8 := by
      simp only [ptAddrOf, hc]; simp only [Bool.false_eq_true, ↓reduceIte] at *
      bv_decide
    rw [h]; simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow, UInt8.toNat_toUInt16]
    simp <;> omega
  · have h : ptAddrOf c b w true = 0x1000 + 16 * b.toUInt16 + w / 4096 % 8 + 8 := by
      simp only [ptAddrOf, hc]; simp only [↓reduceIte] at *
      bv_decide
    rw [h]; simp only [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_mod, UInt16.toNat_div,
      UInt16.reduceToNat, Nat.reducePow, UInt8.toNat_toUInt16]
    simp <;> omega

theorem bit_nat (b c : UInt8) (hc : c < 8) :
    ((b >>> (7 - c)) &&& 1).toNat = Declarative.bit b (7 - c.toNat) := by
  have hc' : c.toNat < 8 := by rw [UInt8.lt_iff_toNat_lt] at hc; exact hc
  rw [UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    show (1 : UInt8).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; simp; omega)]
  simp only [Declarative.bit, UInt8.reduceToNat]
  congr 3
  omega

/-- `tilePx` in `Nat`: pattern bits `bit lo/hi (7 - c)`, palette `attr & 3`. -/
theorem tilePx_nat (T : Tile) (c : Nat) (hc : c < 8) :
    tilePx T c.toUInt16 =
      if Declarative.bit T.lo (7 - c) + 2 * Declarative.bit T.hi (7 - c) = 0 then 0
      else (4 * (T.attr &&& 3).toNat +
        (Declarative.bit T.lo (7 - c) + 2 * Declarative.bit T.hi (7 - c))).toUInt8 := by
  have c8 : c.toUInt16 = c.toUInt8.toUInt16 := by
    apply UInt16.toNat_inj.mp; simp; omega
  have hc8 : c.toUInt8 < 8 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
  have hcn : c.toUInt8.toNat = c := by simp; omega
  have h : tilePx T c.toUInt8.toUInt16 =
      if ((T.lo >>> (7 - c.toUInt8)) &&& 1) + 2 * ((T.hi >>> (7 - c.toUInt8)) &&& 1) = 0 then 0
      else 4 * (T.attr &&& 3) + (((T.lo >>> (7 - c.toUInt8)) &&& 1) +
        2 * ((T.hi >>> (7 - c.toUInt8)) &&& 1)) := by
    simp only [tilePx, beq_iff_eq]
    generalize c.toUInt8 = d at hc8
    bv_decide
  rw [c8, h]
  have e0 := bit_nat T.lo _ hc8
  have e1 := bit_nat T.hi _ hc8
  rw [hcn] at e0 e1
  have b0 : Declarative.bit T.lo (7 - c) < 2 := by simp only [Declarative.bit]; omega
  have b1 : Declarative.bit T.hi (7 - c) < 2 := by simp only [Declarative.bit]; omega
  have ha : (T.attr &&& 3).toNat < 4 := by
    rw [UInt8.toNat_and, show (3 : UInt8).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  generalize (T.lo >>> (7 - c.toUInt8)) &&& 1 = p0 at e0
  generalize (T.hi >>> (7 - c.toUInt8)) &&& 1 = p1 at e1
  generalize Declarative.bit T.lo (7 - c) = n0 at e0 b0
  generalize Declarative.bit T.hi (7 - c) = n1 at e1 b1
  generalize T.attr &&& 3 = a at ha
  have hp : (p0 + 2 * p1).toNat = n0 + 2 * n1 := by
    rw [UInt8.toNat_add, UInt8.toNat_mul]; simp; omega
  by_cases hz : n0 + 2 * n1 = 0
  · have : p0 + 2 * p1 = 0 := by apply UInt8.toNat_inj.mp; rw [hp, hz]; rfl
    simp only [this, hz, ↓reduceIte]
  · have : ¬ p0 + 2 * p1 = 0 := fun h => hz (by rw [← hp, h]; rfl)
    simp only [this, hz, ↓reduceIte]
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_add, UInt8.toNat_mul, hp]; simp <;> omega

/-- The pipeline's tile pixel (`tileBits` / `tilePx`) of loopy word `w` at column `c` is the
`Declarative` lookup at column `8·coarseX + c`, row `vy w mod 256`, nametable bits from `w`. -/
theorem tile_pixN (rd : UInt16 → UInt8) (ctrl : UInt8) (w : UInt16) (c : Nat) (hc : c < 8) :
    tilePx (tileBits rd ctrl w) c.toUInt16 =
      pixN rd (ctrl &&& 0x10 != 0) (8 * (hx w % 32) + c) (hx w / 32) (vy w % 256) (vy w / 256) := by
  rw [tilePx_nat _ _ hc]
  simp only [tileBits, atSelect_nat, ptAddrOf_lo, ptAddrOf_hi, ntAddr_nat, atAddr_nat]
  have e1 : (8 * (hx w % 32) + c) / 8 = hx w % 32 := by omega
  have e2 : (8 * (hx w % 32) + c) / 32 = hx w % 32 / 4 := by omega
  have e3 : (8 * (hx w % 32) + c) / 16 % 2 = hx w % 32 / 2 % 2 := by omega
  have e4 : (8 * (hx w % 32) + c) % 8 = c := by omega
  simp only [pixN, e1, e2, e3, e4]

/-! ### The declarative scroll in terms of `hx` / `vy` -/

theorem coarseX_nat (t : UInt16) : (Loopy.coarseX t).toNat = t.toNat % 32 := by
  have h : Loopy.coarseX t = t % 32 := by simp only [Loopy.coarseX]; bv_decide
  rw [h, UInt16.toNat_mod]; rfl
theorem nt_nat (t : UInt16) : (Loopy.nt t).toNat = t.toNat / 1024 % 4 := by
  have h : Loopy.nt t = t / 1024 % 4 := by simp only [Loopy.nt]; bv_decide
  rw [h, UInt16.toNat_mod, UInt16.toNat_div]; rfl
theorem coarseY_nat (t : UInt16) : (Loopy.coarseY t).toNat = t.toNat / 32 % 32 := by
  have h : Loopy.coarseY t = t / 32 % 32 := by simp only [Loopy.coarseY]; bv_decide
  rw [h, UInt16.toNat_mod, UInt16.toNat_div]; rfl
theorem fineY_nat (t : UInt16) : (Loopy.fineY t).toNat = t.toNat / 4096 % 8 := by
  have h : Loopy.fineY t = t / 4096 % 8 := by simp only [Loopy.fineY]; bv_decide
  rw [h, UInt16.toNat_mod, UInt16.toNat_div]; rfl
theorem fineX_nat (x : UInt8) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [UInt8.toNat_and, show (7 : UInt8).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem scrollX_eq (s0 : State) (x : Nat) :
    Declarative.scrollX s0 x =
      (8 * ((hx s0.t + (x + s0.x.toNat % 8) / 8) % 64 % 32) + (x + s0.x.toNat % 8) % 8,
       (hx s0.t + (x + s0.x.toNat % 8) / 8) % 64 / 32) := by
  simp only [Declarative.scrollX, coarseX_nat, nt_nat, hx]
  generalize s0.t.toNat = T
  have hf : s0.x.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize s0.x.toNat % 8 = f at hf
  have e : T / 1024 % 4 % 2 = T / 1024 % 2 := by omega
  rw [e]
  have hH : T / 1024 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hc : T % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize T / 1024 % 2 = H at hH
  generalize T % 32 = cx at hc
  congr 1 <;> omega

theorem scrollY_eq (s0 : State) (y : Nat) :
    Declarative.scrollY s0 y = (vclosed (vy s0.t) y % 256, vclosed (vy s0.t) y / 256) := by
  simp only [Declarative.scrollY, coarseY_nat, fineY_nat, nt_nat, vclosed, vy]
  have hr : s0.t.toNat / 4096 % 8 + 8 * (s0.t.toNat / 32 % 32) < 256 := by omega
  have hb : s0.t.toNat / 2048 % 2 < 2 := Nat.mod_lt _ (by decide)
  have e0 : ∀ a n : Nat, a < 256 → (a + 256 * n) % 256 = a ∧ (a + 256 * n) / 256 = n := by
    intro a n h; omega
  obtain ⟨e1, e2⟩ := e0 _ (s0.t.toNat / 2048 % 2) hr
  have e3 : s0.t.toNat / 1024 % 4 / 2 = s0.t.toNat / 2048 % 2 := by
    have : ∀ T : Nat, T / 1024 % 4 / 2 = T / 2048 % 2 := by intro T; omega
    exact this _
  have e4 : 8 * (s0.t.toNat / 32 % 32) + s0.t.toNat / 4096 % 8 =
      s0.t.toNat / 4096 % 8 + 8 * (s0.t.toNat / 32 % 32) := by omega
  simp only [e1, e2, e3, e4]
  split <;> (congr 1 <;> omega)

/-- **Background half of T-PPU-6, arithmetic link.** The tile pixel the pipeline draws at screen
`(x, y)` — pixel `(x + fine x) mod 8` of the tile `(x + fine x) / 8` coarse-X steps after the
first tile of line `y` — is `Declarative.bgPixel s0 rd x y`, whatever `v` was before the
pre-render line's copies (`w`). -/
theorem tile_eq_declarative (rd : UInt16 → UInt8) (s0 : State) (w : UInt16) (y x : Nat)
    (hy : y < 240) :
    tilePx (tileBits rd s0.ctrl (Nat.repeat incX ((x + (s0.x &&& 7).toNat) / 8)
        (Nat.repeat (nextU s0.t) y (copyY (copyX w s0.t) s0.t))))
      ((x + (s0.x &&& 7).toNat) % 8).toUInt16 = Declarative.bgPixel s0 rd x y := by
  rw [tile_pixN _ _ _ _ (Nat.mod_lt _ (by decide)), bgPixel_pixN, scrollX_eq, scrollY_eq,
    hx_repeat, vy_repeat, hx_lines _ _ (by rw [hx_copyY, hx_copyX]), vy_lines, vy_copyY,
    repeat_vstep _ (vy_lt _) y hy, fineX_nat]
  rfl

/-! ### T-PPU-6, background half -/

/-- **T-PPU-6 (background half).** Let `s0` be a PPU state in vertical blank (lines 241–260)
with rendering enabled, and run the PPU alone (`Ppu.dot rd pr` iterated: no register, VRAM or
OAM writes, fixed readers). Screen pixel `(x, y)` of the next frame (`x < 256`, `y < 240`) is
produced `frameStart s0 + 341·y + x + 1` dots later, at dot `x + 1` of line `y`, and the
background pixel the pipeline selects there (`bgPixelRaw`, unmasked) is
`Declarative.bgPixel s0 rd x y`. -/
theorem T_PPU_6_bg (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s0 : State) (hs : Static s0) :
    ∀ y, y < 240 → ∀ x, x < 256 →
      (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0).scanline.toNat = y ∧
      (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0).dot.toNat = x + 1 ∧
      bgPixelRaw (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * y + (x + 1)) s0) =
        Declarative.bgPixel s0 rd x y := by
  obtain ⟨w, h⟩ := bg_frame_pipeline rd pr s0 hs
  intro y hy x hx
  obtain ⟨h1, h2, h3⟩ := h y hy x hx
  exact ⟨h1, h2, h3.trans (tile_eq_declarative rd s0 w y x hy)⟩

end Nes.Ppu.Proofs
