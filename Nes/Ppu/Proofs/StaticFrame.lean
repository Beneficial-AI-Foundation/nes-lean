import Nes.Ppu.Proofs.StaticFrameBg
import Nes.Ppu.Proofs.StaticFrameSpr

/-!
# `Nes.Ppu.Proofs.StaticFrame` — T-PPU-6, the static-frame rendering theorem

## Spec

Throughout, `f = Nes.Ppu.dot rd pr` (the full PPU dot with fixed pure readers: a PPU-only run,
so no register, VRAM, palette or OAM write can occur) and `run f n` is `f` applied `n` times.

* **Hypotheses** (`StaticFull s0`): `Static s0` (rendering enabled, `s0` in vertical blank,
  lines 241–260, at a valid dot) and the power-up sizes of the buffers the pipeline indexes:
  secondary OAM 32 bytes, the four sprite-slot arrays 8 bytes, the frame 61440 bytes.
* **Invariants of one dot** (`sf_keep_ppuDot`, `sf_keep_run`): OAM and those sizes never change.
* **Positions** (`sf_pos`): for `k ≤ 341·240`, the state `frameStart s0 + k` dots after `s0`
  is at line `k / 341`, dot `k mod 341`, with `t x ctrl mask` of `s0` (`frameStart s0`: dot 0 of
  line 0, see `StaticFrameBg`). In particular `frameStart s0 + 341·240` is (240, 0), right after
  the last visible line.
* **Line 0** (`sf_line0_count`, `sf_line0_pixel`): pre-render dot 257 sets `sprCount := 0`
  (`sf_cnt_257`), and no later dot before line 0's dot 256 changes it (`sf_cnt_ppuDot`: only a
  dot reaching dot 257 writes `sprCount`), so the slot scan of line 0 is empty; with the
  background half this gives `frame[x] = Declarative.pixel s0 rd pr x 0`.
* **Lines 1–239** (`sf_line_pixel`): `T_PPU_6_spr_pixel` applied to the state at dot 0 of line
  `y - 1` (sizes, OAM, `ctrl`, mask from the invariants), with the background half.
* **Write once** (`sf_frame_ppuDot`, `sf_persist`): a dot reaching `(l, d)` writes at most the
  byte `256·l + d - 1` (only when `l < 240`, `1 ≤ d ≤ 256`), so byte `256·y + x`, written by the
  dot reaching `(y, x + 1)`, is not touched again before `(240, 0)`.
* **T-PPU-6** (`T_PPU_6`): `(run f (frameStart s0 + 341·240) s0).frame = Declarative.frame s0
  rd pr`, byte for byte (`T_PPU_6_pixel`: `getByte … (256·y + x) = Declarative.pixel s0 rd pr
  x y` for `y < 240`, `x < 256`).
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.Sprites Nes.Ppu.Proofs.SpriteEval Nes.Ppu.Proofs.StaticSpr

/-! ### Sizes and OAM along a run -/

/-- Fields a PPU dot never changes: OAM and the sizes of the indexed buffers. -/
structure SfKeep (a b : State) : Prop where
  oam : b.oam = a.oam
  sec : b.secOam.size = a.secOam.size
  attr : b.sprAttr.size = a.sprAttr.size
  sx : b.sprX.size = a.sprX.size
  lo : b.sprPatLo.size = a.sprPatLo.size
  hi : b.sprPatHi.size = a.sprPatHi.size
  fr : b.frame.size = a.frame.size

theorem SfKeep.refl (s : State) : SfKeep s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SfKeep.trans {a b c : State} (h1 : SfKeep a b) (h2 : SfKeep b c) : SfKeep a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6, h2.7.trans h1.7⟩
theorem SfKeep.ite {c : Prop} [Decidable c] {s a b : State} (ha : SfKeep s a) (hb : SfKeep s b) :
    SfKeep s (if c then a else b) := by split <;> assumption

local macro "keep_tac" : tactic => `(tactic| (repeat' split) <;>
  exact ⟨rfl, by simp [ByteArray.size_set!], by simp [ByteArray.size_set!],
    by simp [ByteArray.size_set!], by simp [ByteArray.size_set!], by simp [ByteArray.size_set!],
    by simp [ByteArray.size_set!]⟩)

theorem sf_keep_advance (s : State) : SfKeep s s.advance := by unfold State.advance; keep_tac
theorem sf_keep_bgDot (rd) (s : State) : SfKeep s (Nes.Ppu.bgDot rd s) := by unfold Nes.Ppu.bgDot; keep_tac
theorem sf_keep_evalDot (s : State) : SfKeep s (evalDot s) := by unfold evalDot; dsimp only; keep_tac
theorem sf_keep_fetchDot (rd) (s : State) : SfKeep s (fetchDot rd s) := by
  unfold fetchDot; dsimp only; keep_tac
theorem sf_keep_pixel (pr b) (s : State) : SfKeep s (Render.pixel pr b s) := by
  unfold Render.pixel; dsimp only; keep_tac
theorem sf_keep_dotEvents (s : State) : SfKeep s (State.dotEvents s) := by
  unfold State.dotEvents; keep_tac

theorem sf_keep_ppuDot (rd pr) (s : State) : SfKeep s (Nes.Ppu.dot rd pr s) := by
  have h0 : SfKeep s { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } :=
    (sf_keep_advance s).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have c1 : ∀ t, SfKeep s t → SfKeep s (Nes.Ppu.bgDot rd t) := fun t h => h.trans (sf_keep_bgDot rd t)
  have c2 : ∀ t, SfKeep s t → SfKeep s (evalDot t) := fun t h => h.trans (sf_keep_evalDot t)
  have c3 : ∀ t, SfKeep s t → SfKeep s (fetchDot rd t) := fun t h => h.trans (sf_keep_fetchDot rd t)
  have c4 : ∀ b t, SfKeep s t → SfKeep s (Render.pixel pr b t) :=
    fun b t h => h.trans (sf_keep_pixel pr b t)
  have hr : SfKeep s (render rd pr s.advance) := by
    unfold render
    dsimp only
    exact SfKeep.ite (c4 _ _ (SfKeep.ite (c3 _ (SfKeep.ite (c2 _ (c1 _ h0)) (c1 _ h0)))
      (SfKeep.ite (c2 _ (c1 _ h0)) (c1 _ h0)))) (c4 _ _ h0)
  have he := hr.trans (sf_keep_dotEvents _)
  unfold Nes.Ppu.dot
  dsimp only
  exact SfKeep.ite (he.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) he

theorem sf_keep_run (rd pr) (s : State) : ∀ k, SfKeep s (run (Nes.Ppu.dot rd pr) k s)
  | 0 => SfKeep.refl s
  | k + 1 => (sf_keep_run rd pr s k).trans (sf_keep_ppuDot rd pr _)

/-! ### Positions along the frame -/

theorem sf_start (rd pr) (s0 : State) (hs : Static s0) :
    (run (Nes.Ppu.dot rd pr) (frameStart s0) s0).dot = 0 ∧
    (run (Nes.Ppu.dot rd pr) (frameStart s0) s0).scanline = 0 ∧
    Cfg s0 (run (Nes.Ppu.dot rd pr) (frameStart s0) s0) := by
  obtain ⟨p1, p2, pc, po⟩ := to_prerender rd pr s0 hs.ren hs.vbl1 hs.vbl2 hs.dot
  obtain ⟨w, st, l0, cf⟩ := prerender rd pr s0.ctrl _ (pc.ren hs.ren) (by rw [pc.ctrl]) p1 p2
  rw [← run_add, po] at st l0 cf
  exact ⟨st.dot, l0, pc.trans cf⟩

/-- **Positions.** `frameStart s0 + k` dots after `s0` (`k ≤ 341·240`) the PPU is at line
`k / 341`, dot `k mod 341`, with `s0`'s `t x ctrl mask`. -/
theorem sf_pos (rd pr) (s0 : State) (hs : Static s0) : ∀ k, k ≤ 341 * 240 →
    (run (Nes.Ppu.dot rd pr) (frameStart s0 + k) s0).scanline.toNat = k / 341 ∧
    (run (Nes.Ppu.dot rd pr) (frameStart s0 + k) s0).dot.toNat = k % 341 ∧
    Cfg s0 (run (Nes.Ppu.dot rd pr) (frameStart s0 + k) s0)
  | 0, _ => by
    obtain ⟨a, b, c⟩ := sf_start rd pr s0 hs
    simp only [Nat.add_zero]
    exact ⟨by rw [b]; rfl, by rw [a]; rfl, c⟩
  | k + 1, hk => by
    obtain ⟨l, d, c⟩ := sf_pos rd pr s0 hs k (by omega)
    rw [← Nat.add_assoc, run_succ1]
    have hr := c.ren hs.ren
    obtain ⟨c', d', l', -, -⟩ := step_info rd pr _ hr
    have hl : (run (Nes.Ppu.dot rd pr) (frameStart s0 + k) s0).scanline ≠ 261 := by
      intro e; rw [e] at l; simp at l; omega
    by_cases h340 : k % 341 = 340
    · obtain ⟨a1, a2⟩ := sfb_advance_wrap _ (by rw [d]; exact h340) hl
      refine ⟨?_, ?_, c.trans c'⟩
      · rw [l', a2, UInt16.toNat_add, l]; simp; omega
      · rw [d', a1]; simp; omega
    · obtain ⟨a1, a2, -⟩ := advance_mid _ (by omega) (Or.inl hl)
      exact ⟨by rw [l', a2, l]; omega, by rw [d', a1, d]; omega, c.trans c'⟩

/-! ### The sprite count (line 0) -/

theorem sf_adv_dot (s : State) : s.advance.dot = 0 ∨ s.advance.dot = s.dot + 1 := by
  unfold State.advance; repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem sf_adv_257 (s : State) (h : s.dot.toNat ≠ 256) : s.advance.dot ≠ 257 := by
  rcases sf_adv_dot s with e | e <;> rw [e]
  · decide
  · intro h'
    have : s.dot = 256 := by bv_decide
    exact h (by rw [this]; rfl)

/-- Dot and slot count. -/
structure SfCnt (a b : State) : Prop where
  dot : b.dot = a.dot
  cnt : b.sprCount = a.sprCount

theorem SfCnt.trans {a b c : State} (h1 : SfCnt a b) (h2 : SfCnt b c) : SfCnt a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
theorem SfCnt.ite {c : Prop} [Decidable c] {s a b : State} (ha : SfCnt s a) (hb : SfCnt s b) :
    SfCnt s (if c then a else b) := by split <;> assumption

theorem sf_fetch_key (d : UInt16) (h1 : d ≠ 257) (h2 : ¬(d < 257 || d > 320) = true) :
    ((d - 257) >>> 3).toNat ≠ 0 ∨ ((d - 257) &&& 7) ≠ 0 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h2
  have : (d - 257) >>> 3 ≠ 0 ∨ ((d - 257) &&& 7) ≠ 0 := by bv_decide
  rcases this with h | h
  · left; intro e; apply h; exact UInt16.toNat_inj.mp e
  · exact Or.inr h

theorem sf_cnt_fetch (rd) (t : State) (h : t.dot ≠ 257) : SfCnt t (fetchDot rd t) := by
  unfold fetchDot; dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · rename_i h2
    rcases sf_fetch_key t.dot h h2 with k | k
    · have k' : (((t.dot - 257) >>> 3).toNat == 0) = false := by simpa using k
      simp only [k', Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals exact ⟨rfl, rfl⟩
    · have k' : (((t.dot - 257) &&& 7) == 0) = false := by simpa using k
      simp only [k', Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals exact ⟨rfl, rfl⟩

/-- **`sprCount` is only written by a dot reaching dot 257.** -/
theorem sf_cnt_ppuDot (rd pr) (s : State) (h : s.dot.toNat ≠ 256) :
    (Nes.Ppu.dot rd pr s).sprCount = s.sprCount := by
  have h257 := sf_adv_257 s h
  have h0 : SfCnt s.advance { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } := ⟨rfl, rfl⟩
  have c1 : ∀ t, SfCnt s.advance t → SfCnt s.advance (Nes.Ppu.bgDot rd t) :=
    fun t h => h.trans ⟨(slotEq_bgDot rd t).dot, (slotEq_bgDot rd t).sprCount⟩
  have c2 : ∀ t, SfCnt s.advance t → SfCnt s.advance (evalDot t) :=
    fun t h => h.trans ⟨(slotEq_evalDot t).dot, (slotEq_evalDot t).sprCount⟩
  have c3 : ∀ t, SfCnt s.advance t → SfCnt s.advance (fetchDot rd t) :=
    fun t h => h.trans (sf_cnt_fetch rd t (by rw [h.dot]; exact h257))
  have c4 : ∀ b t, SfCnt s.advance t → SfCnt s.advance (Render.pixel pr b t) :=
    fun b t h => h.trans ⟨(slotEq_pixel pr b t).dot, (slotEq_pixel pr b t).sprCount⟩
  have hr : SfCnt s.advance (render rd pr s.advance) := by
    unfold render
    dsimp only
    exact SfCnt.ite (c4 _ _ (SfCnt.ite (c3 _ (SfCnt.ite (c2 _ (c1 _ h0)) (c1 _ h0)))
      (SfCnt.ite (c2 _ (c1 _ h0)) (c1 _ h0)))) (c4 _ _ h0)
  have he := hr.trans ⟨(slotEq_dotEvents _).dot, (slotEq_dotEvents _).sprCount⟩
  have : SfCnt s.advance (Nes.Ppu.dot rd pr s) := by
    unfold Nes.Ppu.dot
    dsimp only
    exact SfCnt.ite (he.trans ⟨rfl, rfl⟩) he
  rw [this.cnt, (slotEq_advance s).1]

/-- **Pre-render dot 257 empties the slots for line 0.** -/
theorem sf_cnt_257 (rd pr) (s : State) (hr : s.rendering = true) (hd : s.dot = 256)
    (hl : s.scanline = 261) : (Nes.Ppu.dot rd pr s).sprCount = 0 := by
  have ha : s.advance = { s with dot := 257 } := by
    rw [advance_lt s (by rw [hd]; decide), hd]; rfl
  have hF : ∀ u : State, u.dot = 257 → u.scanline = 261 → (fetchDot rd u).sprCount = 0 := by
    intro u h1 h2; simp [fetchDot, h1, h2]
  have hR : (render rd pr s.advance).sprCount = 0 := by
    unfold render; dsimp only
    obtain ⟨k1, k2, -, -, -⟩ :=
      bgDot_keeps rd { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 }
    have hren : ({ s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } : State).rendering
        = true := by rw [ha]; exact hr
    rw [ite_eq_left hren]
    have n240 : ¬ (Nes.Ppu.bgDot rd
        { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 }).scanline < 240 := by
      rw [k2, ha]; dsimp only; rw [hl]; decide
    rw [ite_eq_right n240]
    have act : Bg.activeLine (Nes.Ppu.bgDot rd
        { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 }).scanline = true := by
      rw [k2, ha]; dsimp only; rw [hl]; decide
    rw [ite_eq_left act, (slotEq_pixel pr _ _).sprCount]
    exact hF _ (by rw [k1, ha]) (by rw [k2, ha]; exact hl)
  unfold Nes.Ppu.dot; dsimp only
  split
  · show (State.dotEvents (render rd pr s.advance)).sprCount = 0
    rw [(slotEq_dotEvents _).sprCount, hR]
  · rw [(slotEq_dotEvents _).sprCount, hR]

theorem sf_cnt_run (rd pr) (s : State) : ∀ k, (∀ j, j < k → (run (Nes.Ppu.dot rd pr) j s).dot.toNat ≠ 256) →
    (run (Nes.Ppu.dot rd pr) k s).sprCount = s.sprCount
  | 0, _ => rfl
  | k + 1, h => by
    rw [run_succ1, sf_cnt_ppuDot rd pr _ (h k (by omega))]
    exact sf_cnt_run rd pr s k (fun j hj => h j (by omega))

/-! ### Frame writes -/

/-- Frame, dot and line. -/
structure SfFr (a b : State) : Prop where
  fr : b.frame = a.frame
  dot : b.dot = a.dot
  line : b.scanline = a.scanline

theorem SfFr.trans {a b c : State} (h1 : SfFr a b) (h2 : SfFr b c) : SfFr a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3⟩
theorem SfFr.ite {c : Prop} [Decidable c] {s a b : State} (ha : SfFr s a) (hb : SfFr s b) :
    SfFr s (if c then a else b) := by split <;> assumption

theorem sf_fr_fetch (rd) (t : State) : SfFr t (fetchDot rd t) := by
  unfold fetchDot; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem sf_fr_evalDot (t : State) : SfFr t (evalDot t) :=
  ⟨evalDot_frame t, (evalDot_fields t).2.2.1, (evalDot_fields t).2.2.2⟩

theorem sf_fr_bgDot (rd) (t : State) : SfFr t (Nes.Ppu.bgDot rd t) :=
  ⟨bgDot_frame rd t, (bgDot_keeps rd t).1, (bgDot_keeps rd t).2.1⟩

/-- `Render.pixel` at `(l, d)` writes at most byte `256·l + d - 1` (`l < 240`, `1 ≤ d ≤ 256`). -/
theorem sf_pixel_frame (pr b) (u : State) (i : Nat)
    (h : ¬ (u.scanline.toNat < 240 ∧ 1 ≤ u.dot.toNat ∧ u.dot.toNat ≤ 256 ∧
      i = 256 * u.scanline.toNat + u.dot.toNat - 1)) :
    getByte (Render.pixel pr b u).frame i = getByte u.frame i := by
  unfold Render.pixel; dsimp only
  split
  · rfl
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have d1 : u.dot.toNat ≠ 0 := fun e => h1 (UInt16.toNat_inj.mp (by rw [e]; rfl))
    have d2 : u.dot.toNat ≤ 256 := by
      rw [gt_iff_lt, UInt16.lt_iff_toNat_lt] at h2; simp at h2; omega
    have d3 : u.scanline.toNat < 240 := by
      rw [ge_iff_le, UInt16.le_iff_toNat_le] at h3; simp at h3; omega
    have hidx : (u.scanline.toUInt32 * 256 + (u.dot - 1).toUInt8.toUInt32).toNat =
        256 * u.scanline.toNat + u.dot.toNat - 1 := by
      have e1 : (u.dot - 1).toNat = u.dot.toNat - 1 := by
        rw [UInt16.toNat_sub_of_le]
        · rfl
        · rw [UInt16.le_iff_toNat_le]; simp; omega
      have e2 : (u.dot - 1).toUInt8.toNat = u.dot.toNat - 1 := by
        rw [UInt16.toNat_toUInt8, e1]; omega
      rw [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, e2]
      simp; omega
    rw [getByte_set, hidx, ite_eq_right]
    rintro ⟨e, -⟩
    exact h ⟨d3, by omega, d2, e.symm⟩

/-- **A dot writes at most the byte of the pixel it reaches.** -/
theorem sf_frame_ppuDot (rd pr) (s : State) (i : Nat)
    (h : ¬ ((Nes.Ppu.dot rd pr s).scanline.toNat < 240 ∧ 1 ≤ (Nes.Ppu.dot rd pr s).dot.toNat ∧
      (Nes.Ppu.dot rd pr s).dot.toNat ≤ 256 ∧
      i = 256 * (Nes.Ppu.dot rd pr s).scanline.toNat + (Nes.Ppu.dot rd pr s).dot.toNat - 1)) :
    getByte (Nes.Ppu.dot rd pr s).frame i = getByte s.frame i := by
  obtain ⟨f1, f2, -⟩ := dot_fields rd pr s
  rw [f1, f2] at h
  have ha : s.advance.frame = s.frame := by
    unfold State.advance; repeat' split
    all_goals rfl
  have h0 : SfFr s.advance { s.advance with a12 := busAddr s.advance &&& 0x1000 != 0 } :=
    ⟨rfl, rfl, rfl⟩
  have c1 : ∀ t, SfFr s.advance t → SfFr s.advance (Nes.Ppu.bgDot rd t) :=
    fun t h => h.trans (sf_fr_bgDot rd t)
  have c2 : ∀ t, SfFr s.advance t → SfFr s.advance (evalDot t) :=
    fun t h => h.trans (sf_fr_evalDot t)
  have c3 : ∀ t, SfFr s.advance t → SfFr s.advance (fetchDot rd t) :=
    fun t h => h.trans (sf_fr_fetch rd t)
  have c4 : ∀ b t, SfFr s.advance t →
      getByte (Render.pixel pr b t).frame i = getByte s.advance.frame i := by
    intro b t ht
    rw [sf_pixel_frame pr b t i (by rw [ht.dot, ht.line]; exact h), ht.fr]
  have hr : getByte (render rd pr s.advance).frame i = getByte s.advance.frame i := by
    unfold render
    dsimp only
    split
    · exact c4 _ _ (SfFr.ite (c3 _ (SfFr.ite (c2 _ (c1 _ h0)) (c1 _ h0)))
        (SfFr.ite (c2 _ (c1 _ h0)) (c1 _ h0)))
    · exact c4 _ _ h0
  have he : ∀ u : State, (State.dotEvents u).frame = u.frame := by
    intro u; unfold State.dotEvents; repeat' split
    all_goals rfl
  have hd : (Nes.Ppu.dot rd pr s).frame = (render rd pr s.advance).frame := by
    unfold Nes.Ppu.dot; dsimp only; split <;> exact he _
  rw [hd, hr, ha]

/-- **Write once.** Byte `256·y + x`, written by the dot reaching `(y, x + 1)`, is not touched
again up to `(240, 0)`. -/
theorem sf_persist (rd pr) (s0 : State) (hs : Static s0) (y x : Nat) (hx : x < 256) :
    ∀ m, 341 * y + (x + 1) + m ≤ 341 * 240 →
    getByte (run (Nes.Ppu.dot rd pr) (frameStart s0 + (341 * y + (x + 1) + m)) s0).frame
        (256 * y + x) =
      getByte (run (Nes.Ppu.dot rd pr) (frameStart s0 + (341 * y + (x + 1))) s0).frame
        (256 * y + x)
  | 0, _ => by simp only [Nat.add_zero]
  | m + 1, hm => by
    obtain ⟨l, d, -⟩ := sf_pos rd pr s0 hs (341 * y + (x + 1) + m + 1) hm
    rw [show frameStart s0 + (341 * y + (x + 1) + m + 1) =
      frameStart s0 + (341 * y + (x + 1) + m) + 1 by omega, run_succ1] at l d
    rw [show frameStart s0 + (341 * y + (x + 1) + (m + 1)) =
      frameStart s0 + (341 * y + (x + 1) + m) + 1 by omega, run_succ1]
    rw [sf_frame_ppuDot rd pr _ _ (by rw [l, d]; omega)]
    exact sf_persist rd pr s0 hs y x hx m (by omega)

/-! ### Line 0 -/

theorem sf_run_zero (f : State → State) (s : State) : run f 0 s = s := rfl

/-- Static-frame hypotheses plus the power-up sizes of the buffers the pipeline indexes. -/
structure StaticFull (s0 : State) : Prop extends Static s0 where
  sec : s0.secOam.size = 32
  attr : s0.sprAttr.size = 8
  sx : s0.sprX.size = 8
  lo : s0.sprPatLo.size = 8
  hi : s0.sprPatHi.size = 8
  frame : s0.frame.size = 61440

/-- **No sprites on line 0.** Up to dot 255 of line 0 the slot count is 0 (set at pre-render
dot 257, untouched since). -/
theorem sf_line0_count (rd pr) (s0 : State) (hs : Static s0) (x : Nat) (hx : x < 256) :
    (run (Nes.Ppu.dot rd pr) (frameStart s0 + x) s0).sprCount = 0 := by
  obtain ⟨p1, p2, pc, -⟩ := to_prerender rd pr s0 hs.ren hs.vbl1 hs.vbl2 hs.dot
  generalize hA : 341 * (261 - s0.scanline.toNat) - s0.dot.toNat = A at p1 p2 pc
  have hfs : frameStart s0 = A + (341 - if s0.frameOdd then 1 else 0) := by rw [← hA]; rfl
  generalize hP : run (Nes.Ppu.dot rd pr) A s0 = P at p1 p2 pc
  have hr := pc.ren hs.ren
  have p1n : P.dot.toNat = 0 := by rw [p1]; rfl
  have wk : ∀ j, j ≤ 339 → (run (Nes.Ppu.dot rd pr) j P).dot.toNat = j := by
    intro j hj
    obtain ⟨-, d, -, -⟩ := walk rd pr P hr j (by omega) (Or.inr (by omega))
    rw [d, p1n]; omega
  obtain ⟨c256, -, l256, -⟩ := walk rd pr P hr 256 (by omega) (Or.inr (by omega))
  have h257 : (run (Nes.Ppu.dot rd pr) 257 P).sprCount = 0 := by
    rw [run_succ1]
    exact sf_cnt_257 rd pr _ (c256.ren hr) (pos_dot _ 256 (by decide) (wk 256 (by omega)))
      (by rw [l256, p2])
  have h339 : (run (Nes.Ppu.dot rd pr) 339 P).sprCount = 0 := by
    rw [show (339 : Nat) = 257 + 82 from rfl, run_add, sf_cnt_run rd pr _ 82 ?_, h257]
    intro j hj; rw [← run_add, wk _ (by omega)]; omega
  have hpre : (run (Nes.Ppu.dot rd pr) (341 - if s0.frameOdd then 1 else 0) P).sprCount = 0 := by
    have e : (341 - if s0.frameOdd then 1 else 0) = 339 + (2 - if s0.frameOdd then 1 else 0) := by
      split <;> rfl
    rw [e, run_add, sf_cnt_run rd pr _ _ ?_, h339]
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by split at hj <;> omega
    rcases hj' with rfl | rfl
    · rw [sf_run_zero, wk 339 (Nat.le_refl _)]; decide
    · rw [run_succ1, sf_run_zero, (dot_fields rd pr _).1]
      rcases sf_adv_dot (run (Nes.Ppu.dot rd pr) 339 P) with e | e <;> rw [e]
      · decide
      · rw [UInt16.toNat_add, wk 339 (Nat.le_refl _)]; decide
  rw [hfs, run_add, run_add, hP, sf_cnt_run rd pr _ x ?_, hpre]
  intro j hj
  obtain ⟨-, d, -⟩ := sf_pos rd pr s0 hs j (by omega)
  rw [← hP, ← run_add, ← run_add, ← Nat.add_assoc, ← hfs, d]; omega

/-- **Line 0 of the frame.** -/
theorem sf_line0_pixel (rd pr) (s0 : State) (hs : StaticFull s0) (x : Nat) (hx : x < 256) :
    getByte (run (Nes.Ppu.dot rd pr) (frameStart s0 + (341 * 0 + (x + 1))) s0).frame (256 * 0 + x) =
      Declarative.pixel s0 rd pr x 0 := by
  obtain ⟨l, d, c⟩ := sf_pos rd pr s0 hs.toStatic x (by omega)
  have hb := (T_PPU_6_bg rd pr s0 hs.toStatic 0 (by decide) x hx).2.2
  rw [show frameStart s0 + 341 * 0 + (x + 1) = frameStart s0 + x + 1 by omega, run_succ1] at hb
  rw [show frameStart s0 + (341 * 0 + (x + 1)) = frameStart s0 + x + 1 by omega, run_succ1]
  have hcnt := sf_line0_count rd pr s0 hs.toStatic x hx
  refine frame_byte rd pr s0 _ x 0 (c.ren hs.ren) (by rw [l]; omega) (by decide) (by rw [d]; omega)
    hx c.mask ((frameSize_run rd pr s0 _).trans hs.frame) hb ?_
  have h0 : Render.spritePixel (run (Nes.Ppu.dot rd pr) (frameStart s0 + x) s0) x.toUInt8 = 0 := by
    unfold Render.spritePixel; rw [hcnt, show min (0 : UInt8) 8 = 0 from rfl]
    simp [Render.spritePixelAux]
  rw [h0, decode_zero]; simp [Declarative.spritePixel]

/-! ### Lines 1–239 -/

/-- **Line `L + 1` of the frame**, from the state at dot 0 of line `L`. -/
theorem sf_line_pixel (rd pr) (s0 : State) (hs : StaticFull s0) (L x : Nat) (hL : L + 1 < 240)
    (hx : x < 256) :
    getByte (run (Nes.Ppu.dot rd pr) (frameStart s0 + (341 * (L + 1) + (x + 1))) s0).frame
        (256 * (L + 1) + x) = Declarative.pixel s0 rd pr x (L + 1) := by
  obtain ⟨l, d, c⟩ := sf_pos rd pr s0 hs.toStatic (341 * L) (by omega)
  have K := sf_keep_run rd pr s0 (frameStart s0 + 341 * L)
  have hb := (T_PPU_6_bg rd pr s0 hs.toStatic (L + 1) hL x hx).2.2
  rw [show frameStart s0 + 341 * (L + 1) + (x + 1) = frameStart s0 + 341 * L + (341 + x + 1) by omega,
    run_add] at hb
  have hl : (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * L) s0).scanline.toNat = L := by
    rw [l]; omega
  have hd0 : (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * L) s0).dot = 0 :=
    UInt16.toNat_inj.mp (by rw [d, UInt16.toNat_zero]; omega)
  have P := T_PPU_6_spr_pixel rd pr _ s0 (c.ren hs.ren) (by rw [hl]; exact hL) hd0
    (K.sec.trans hs.sec) (K.attr.trans hs.attr) (K.sx.trans hs.sx) (K.lo.trans hs.lo)
    (K.hi.trans hs.hi) (K.fr.trans hs.frame) K.oam c.ctrl c.mask x hx (by rw [hl]; exact hb)
  rw [hl, ← run_add, show frameStart s0 + 341 * L + (341 + x + 1) =
    frameStart s0 + (341 * (L + 1) + (x + 1)) by omega] at P
  exact P

/-! ### T-PPU-6 -/

/-- **T-PPU-6, pointwise.** For `s0` in vertical blank with rendering enabled (and power-up
buffer sizes), running the PPU alone (`Ppu.dot rd pr`: no register, VRAM, palette or OAM
writes) to dot 0 of line 240 leaves every pixel `(x, y)` of the frame equal to
`Declarative.pixel s0 rd pr x y`. -/
theorem T_PPU_6_pixel (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s0 : State) (hs : StaticFull s0) :
    ∀ y, y < 240 → ∀ x, x < 256 →
      getByte (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * 240) s0).frame (256 * y + x) =
        Declarative.pixel s0 rd pr x y := by
  intro y hy x hx
  have P := sf_persist rd pr s0 hs.toStatic y x hx (341 * 240 - (341 * y + (x + 1))) (by omega)
  rw [show 341 * y + (x + 1) + (341 * 240 - (341 * y + (x + 1))) = 341 * 240 by omega] at P
  rw [P]
  rcases y with _ | L
  · exact sf_line0_pixel rd pr s0 hs x hx
  · exact sf_line_pixel rd pr s0 hs L x hy hx

/-- **T-PPU-6 (static-frame rendering).** Let `s0` be a PPU state in vertical blank (lines
241–260) with rendering enabled and power-up buffer sizes, and run the PPU alone
(`Ppu.dot rd pr` iterated: no register, VRAM, palette or OAM writes; fixed readers). When the
last visible line is done (`frameStart s0 + 341·240` dots: line 240, dot 0) the frame buffer is
exactly the declarative frame: `frame[256·y + x] = Declarative.pixel s0 rd pr x y` for all
`x < 256`, `y < 240`. -/
theorem T_PPU_6 (rd : UInt16 → UInt8) (pr : UInt8 → UInt8) (s0 : State) (hs : StaticFull s0) :
    (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * 240) s0).frame = Declarative.frame s0 rd pr := by
  have hsz := (sf_keep_run rd pr s0 (frameStart s0 + 341 * 240)).fr.trans hs.frame
  have hpix := T_PPU_6_pixel rd pr s0 hs
  generalize (run (Nes.Ppu.dot rd pr) (frameStart s0 + 341 * 240) s0).frame = F at hsz hpix
  rcases F with ⟨A⟩
  unfold Declarative.frame
  congr 1
  apply Array.ext
  · simp only [ByteArray.size] at hsz
    simp [hsz, frameWidth, frameHeight]
  · intro i h1 h2
    have hi : i < 61440 := by simp only [ByteArray.size] at hsz; omega
    have := hpix (i / 256) (by omega) (i % 256) (by omega)
    rw [show 256 * (i / 256) + i % 256 = i by omega] at this
    simp only [getByte, ByteArray.size, h1, dite_true, ByteArray.getElem_eq_getElem_data] at this
    simp [this]

end Nes.Ppu.Proofs
