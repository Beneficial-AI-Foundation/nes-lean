import Nes.System.Nes
import Nes.Ppu.Proofs.Timing

namespace Nes.System.Proofs

open Nes.System Nes.Ppu Nes.Ppu.Proofs Nes.Bus

/-- The parts of the machine that only the PPU dots move: position and frame counter. -/
structure PosEq (n m : Nes) : Prop where
  dot : m.ppu.dot = n.ppu.dot
  scanline : m.ppu.scanline = n.ppu.scanline
  frame : m.frame = n.frame
  clock : m.clock = n.clock
  resetLine : m.resetLine = n.resetLine

theorem PosEq.refl (n : Nes) : PosEq n n := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem PosEq.trans {a b c : Nes} (h1 : PosEq a b) (h2 : PosEq b c) : PosEq a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5⟩

theorem ppu_cpuRead_pos (rd : State → State × UInt8) (hrd : ∀ s, (rd s).1.dot = s.dot ∧ (rd s).1.scanline = s.scanline)
    (s : State) (a : UInt16) :
    (s.cpuRead rd a).1.dot = s.dot ∧ (s.cpuRead rd a).1.scanline = s.scanline := by
  unfold State.cpuRead
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact hrd s
  · exact ⟨rfl, rfl⟩

theorem cpuRead_pos (n : Nes) (a : UInt16) : PosEq n (n.cpuRead a).1 := by
  unfold Nes.cpuRead
  split
  · exact .refl _
  split
  · have := ppu_cpuRead_pos (State.read2007 (Nes.ppuPeek n.cart n.ciram n.ciram_size)
      (Nes.palPeek n.pal n.pal_size)) (fun s => by
        unfold State.read2007; dsimp only; split <;> exact ⟨rfl, rfl⟩) n.ppu a
    exact ⟨this.1, this.2, rfl, rfl, rfl⟩
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ppuPoke_pos (n : Nes) (a : UInt16) (v : UInt8) : PosEq n (n.ppuPoke a v) := by
  unfold Nes.ppuPoke; dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ppu_cpuWrite_pos (s : State) (a : UInt16) (v : UInt8) :
    (s.cpuWrite a v).1.dot = s.dot ∧ (s.cpuWrite a v).1.scanline = s.scanline := by
  unfold State.cpuWrite; dsimp only
  split <;> simp only [State.writeCtrl, State.writeMask, State.writeOamAddr, State.writeOamData,
    State.writeScroll, State.writeAddr, State.writeData, State.incAddr] <;> (try split) <;> simp

theorem cpuWrite_pos (n : Nes) (a : UInt16) (v : UInt8) : PosEq n (n.cpuWrite a v) := by
  unfold Nes.cpuWrite
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  split
  · have h := ppu_cpuWrite_pos n.ppu a v
    generalize n.ppu.cpuWrite a v = r at h
    obtain ⟨ppu, wr⟩ := r
    dsimp only at h ⊢
    cases wr with
    | none => exact ⟨h.1, h.2, rfl, rfl, rfl⟩
    | some w => exact (⟨h.1, h.2, rfl, rfl, rfl⟩ : PosEq n { n with ppu }).trans (ppuPoke_pos _ _ _)
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### One PPU dot moves the position like `State.advance` -/

/-- Fields that the rendering half of a PPU dot leaves alone. -/
structure Keeps (s t : State) : Prop where
  dot : t.dot = s.dot
  scanline : t.scanline = s.scanline
  frameOdd : t.frameOdd = s.frameOdd
  oam : t.oam = s.oam
  oamAddr : t.oamAddr = s.oamAddr
  mask : t.mask = s.mask

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Keeps.trans {a b c : State} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
   h2.6.trans h1.6⟩
theorem Keeps.ite {c : Prop} [Decidable c] {s a b : State} (ha : Keeps s a) (hb : Keeps s b) :
    Keeps s (if c then a else b) := by split <;> assumption

/-- Push the projections of `Keeps` through the `if`s of a `{ s with … }` chain. -/
macro "keeps_tac" : tactic => `(tactic| (constructor <;>
  simp only [apply_ite State.dot, apply_ite State.scanline, apply_ite State.frameOdd,
    apply_ite State.oam, apply_ite State.oamAddr, apply_ite State.mask, ite_self]))

theorem keeps_bgDot (rd) (s : State) : Keeps s (bgDot rd s) := by
  simp only [bgDot, Bg.bgShift, Bg.bgReload]; keeps_tac
theorem keeps_evalDot (s : State) : Keeps s (Sprites.evalDot s) := by
  simp only [Sprites.evalDot, Sprites.evalAct]; keeps_tac
theorem keeps_fetchDot (rd) (s : State) : Keeps s (Sprites.fetchDot rd s) := by
  simp only [Sprites.fetchDot]; keeps_tac
theorem keeps_pixel (pr) (b) (s : State) : Keeps s (Render.pixel pr b s) := by
  simp only [Render.pixel]; keeps_tac
theorem keeps_dotEvents (s : State) : Keeps s (State.dotEvents s) := by
  simp only [State.dotEvents]; keeps_tac

theorem keeps_render (rd pr) (s : State) : Keeps s (render rd pr s) := by
  have c1 : ∀ t, Keeps s t → Keeps s (bgDot rd t) := fun t h => h.trans (keeps_bgDot rd t)
  have c2 : ∀ t, Keeps s t → Keeps s (Sprites.evalDot t) := fun t h => h.trans (keeps_evalDot t)
  have c3 : ∀ t, Keeps s t → Keeps s (Sprites.fetchDot rd t) :=
    fun t h => h.trans (keeps_fetchDot rd t)
  have c4 : ∀ b t, Keeps s t → Keeps s (Render.pixel pr b t) :=
    fun b t h => h.trans (keeps_pixel pr b t)
  have h1 : Keeps s { s with a12 := busAddr s &&& 0x1000 != 0 } := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold render
  dsimp only
  exact Keeps.ite (c4 _ _ (Keeps.ite (c3 _ (Keeps.ite (c2 _ (c1 _ h1)) (c1 _ h1)))
    (Keeps.ite (c2 _ (c1 _ h1)) (c1 _ h1)))) (c4 _ _ h1)

/-- A PPU dot (`Nes.Ppu.dot`) moves `(dot, scanline, frameOdd)` exactly as `State.advance` and
keeps OAM, `OAMADDR` and `PPUMASK`. -/
theorem ppu_dot_like_advance (rd pr) (s : State) :
    (Nes.Ppu.dot rd pr s).dot = (State.advance s).dot ∧
    (Nes.Ppu.dot rd pr s).scanline = (State.advance s).scanline ∧
    (Nes.Ppu.dot rd pr s).frameOdd = (State.advance s).frameOdd ∧
    (Nes.Ppu.dot rd pr s).oam = s.oam ∧ (Nes.Ppu.dot rd pr s).oamAddr = s.oamAddr ∧
    (Nes.Ppu.dot rd pr s).mask = s.mask := by
  have ha : (State.advance s).oam = s.oam ∧ (State.advance s).oamAddr = s.oamAddr ∧
      (State.advance s).mask = s.mask := by
    unfold State.advance; repeat' split
    all_goals exact ⟨rfl, rfl, rfl⟩
  have k := (keeps_render rd pr (State.advance s)).trans (keeps_dotEvents _)
  have : Keeps (State.advance s) (Nes.Ppu.dot rd pr s) := by
    unfold Nes.Ppu.dot; dsimp only
    exact Keeps.ite (k.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) k
  exact ⟨this.1, this.2, this.3, this.4.trans ha.1, this.5.trans ha.2.1, this.6.trans ha.2.2⟩

/-! ### One system dot -/

theorem lin_le (s : State) (hv : Valid s) : lin s ≤ 89341 := by
  unfold Valid lin at *; omega

/-- One `Nes.ppuDot`: the position steps by one, or wraps to `(0, 0)` from the frame's last dot
(`lin ≥ 89340`) and the frame counter counts it. -/
def DotStep (a b : Nes) : Prop :=
  Valid b.ppu ∧ b.clock = a.clock ∧
    ((lin b.ppu = lin a.ppu + 1 ∧ b.frame = a.frame) ∨
     (89340 ≤ lin a.ppu ∧ lin b.ppu = 0 ∧ b.frame = a.frame + 1))

theorem ppuDot_step (n : Nes) (hv : Valid n.ppu) : DotStep n n.ppuDot := by
  have k := ppu_dot_like_advance (Nes.ppuPeek n.cart n.ciram n.ciram_size)
    (Nes.palPeek n.pal n.pal_size) n.ppu
  have hp : n.ppuDot.ppu = Nes.Ppu.dot (Nes.ppuPeek n.cart n.ciram n.ciram_size)
    (Nes.palPeek n.pal n.pal_size) n.ppu := rfl
  have hf : n.ppuDot.frame =
      if n.ppuDot.ppu.dot == 0 && n.ppuDot.ppu.scanline == 0 then n.frame + 1 else n.frame := rfl
  have hl : lin n.ppuDot.ppu = lin (State.advance n.ppu) := by
    unfold lin; rw [hp, k.1, k.2.1]
  have hV : Valid n.ppuDot.ppu ↔ Valid (State.advance n.ppu) := by
    unfold Valid; rw [hp, k.1, k.2.1]
  have wrap : lin (State.advance n.ppu) = 0 → Valid (State.advance n.ppu) →
      89340 ≤ lin n.ppu → DotStep n n.ppuDot := by
    intro h0 hv' hle
    have hv'' := hV.2 hv'
    obtain ⟨hd, hs⟩ := pos_of_lin0 _ hv'' (by rw [hl]; exact h0)
    refine ⟨hv'', rfl, Or.inr ⟨hle, by rw [hl]; exact h0, ?_⟩⟩
    rw [hf, hd, hs]; rfl
  have hle := lin_le _ hv
  by_cases h1 : lin n.ppu = 89341
  · have w := advance_wrap _ hv h1
    exact wrap w.1 w.2.1 (by omega)
  by_cases h2 : lin n.ppu = 89340 ∧ n.ppu.frameOdd = true ∧ n.ppu.renderLatch = true
  · have w := advance_skip _ hv h2.1 h2.2.1 h2.2.2
    exact wrap w.1 w.2.1 (by omega)
  have w := advance_step _ hv (by omega) h2
  refine ⟨hV.2 w.2.1, rfl, Or.inl ⟨by rw [hl]; exact w.1, ?_⟩⟩
  rw [hf]
  have : ¬ (n.ppuDot.ppu.dot = 0 ∧ n.ppuDot.ppu.scanline = 0) := by
    intro ⟨a, b⟩
    have : lin n.ppuDot.ppu = 0 := by unfold lin; rw [a, b]; rfl
    omega
  simp only [beq_iff_eq, Bool.and_eq_true] at this ⊢
  simp [this]

theorem DotStep.posEq {a b c : Nes} (h : DotStep a b) (e : PosEq b c) : DotStep a c := by
  have hl : lin c.ppu = lin b.ppu := by unfold lin; rw [e.1, e.2]
  have hv : Valid c.ppu ↔ Valid b.ppu := by unfold Valid; rw [e.1, e.2]
  refine ⟨hv.2 h.1, e.4.trans h.2.1, ?_⟩
  rw [hl, e.3]; exact h.2.2

theorem posEq_valid {a b : Nes} (e : PosEq a b) (hv : Valid a.ppu) : Valid b.ppu := by
  unfold Valid at *; rw [e.1, e.2]; exact hv

theorem posEq_lin {a b : Nes} (e : PosEq a b) : lin b.ppu = lin a.ppu := by
  unfold lin; rw [e.1, e.2]

/-! ### The bus-access part of a cycle -/

theorem ppuDots_one (n : Nes) : Nes.ppuDots (3 - preDots) n = n.ppuDot := rfl

theorem dmaCycle_split (n : Nes) : ∃ m, PosEq n m ∧ PosEq m.ppuDot n.dmaCycle := by
  unfold Nes.dmaCycle
  split
  · refine ⟨_, ?_, by rw [ppuDots_one]; exact .refl _⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rename_i a _
    have h := cpuRead_pos n a
    generalize n.cpuRead a = r at h
    obtain ⟨m, v⟩ := r
    dsimp only at h ⊢
    refine ⟨_, ?_, by rw [ppuDots_one]; exact .refl _⟩
    exact h.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rename_i v _
    have h := cpuWrite_pos n 0x2004 v
    refine ⟨_, ?_, by rw [ppuDots_one]; exact .refl _⟩
    exact h.trans ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cpuCycle_split (n : Nes) : ∃ m, PosEq n m ∧ PosEq m.ppuDot n.cpuCycle := by
  unfold Nes.cpuCycle
  split
  · rename_i a _
    have h := cpuRead_pos n a
    generalize n.cpuRead a = r at h
    obtain ⟨m, v⟩ := r
    dsimp only at h ⊢
    refine ⟨_, ?_, by rw [ppuDots_one]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact h.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rename_i a v _
    have h := cpuWrite_pos n a v
    dsimp only
    refine ⟨_, ?_, by rw [ppuDots_one]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact h.trans ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### One CPU cycle -/

/-- One `stepCycle` for the position: `+3` dots, or the frame wrapped during the cycle (at most
once: wraps are ≥ 89340 dots apart) — the PPU ends at `lin ≤ 2` and the frame counter
counted it. -/
def CycStep (a b : Nes) : Prop :=
  Valid b.ppu ∧
    ((lin b.ppu = lin a.ppu + 3 ∧ b.frame = a.frame) ∨ (lin b.ppu ≤ 2 ∧ b.frame = a.frame + 1))

theorem cycStep_of_dots {a b c d : Nes} (h1 : DotStep a b) (h2 : DotStep b c) (h3 : DotStep c d) :
    CycStep a d := by
  refine ⟨h3.1, ?_⟩
  rcases h1.2.2 with ⟨l1, f1⟩ | ⟨w1, l1, f1⟩ <;> rcases h2.2.2 with ⟨l2, f2⟩ | ⟨w2, l2, f2⟩ <;>
    rcases h3.2.2 with ⟨l3, f3⟩ | ⟨w3, l3, f3⟩
  all_goals first
    | (exfalso; omega)
    | (left; exact ⟨by omega, by rw [f3, f2, f1]⟩)
    | (right; exact ⟨by omega, by rw [f3, f2, f1]⟩)

theorem latchReset_pos (n : Nes) : PosEq n n.latchReset := by
  unfold Nes.latchReset; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The body of a cycle before the clock tick (from the state after the RESET latch). -/
def body (n : Nes) : Nes :=
  if (Nes.ppuDots preDots n).dma.active then (Nes.ppuDots preDots n).dmaCycle
  else (Nes.ppuDots preDots n).cpuCycle

/-- `stepCycle` is `tick ∘ body ∘ latchReset`. -/
theorem stepCycle_eq (n : Nes) : Nes.stepCycle n = (body n.latchReset).tick := by
  unfold Nes.stepCycle body Nes.cpuCycle
  dsimp only
  cases (Nes.ppuDots preDots n.latchReset).dma.active
  · cases (Nes.ppuDots preDots n.latchReset).cpu.busOp <;> rfl
  · rfl

theorem tick_clock (n : Nes) : n.tick.clock = n.clock.tick := rfl

theorem body_split (n : Nes) : ∃ m, PosEq n.ppuDot.ppuDot m ∧ PosEq m.ppuDot (body n) := by
  unfold body
  split
  · exact dmaCycle_split _
  · exact cpuCycle_split _

theorem ppuDot_clock (m : Nes) : m.ppuDot.clock = m.clock := rfl

/-- `stepCycle` ticks the clock once. -/
theorem stepCycle_clock (n : Nes) : (Nes.stepCycle n).clock = n.clock.tick := by
  obtain ⟨m, h1, h2⟩ := body_split n.latchReset
  rw [stepCycle_eq, tick_clock, h2.4, ppuDot_clock, h1.4, ppuDot_clock, ppuDot_clock,
    (latchReset_pos n).4]

/-- `stepCycle` keeps the RESET line. -/
theorem stepCycle_resetLine (n : Nes) : (Nes.stepCycle n).resetLine = n.resetLine := by
  obtain ⟨m, h1, h2⟩ := body_split n.latchReset
  rw [stepCycle_eq]; show (body n.latchReset).resetLine = _
  rw [h2.5]; show m.resetLine = _; rw [h1.5]; exact (latchReset_pos n).5

/-- `stepCycle` moves the PPU 3 dots (with at most one frame wrap, counted). -/
theorem stepCycle_pos (n : Nes) (hv : Valid n.ppu) : CycStep n (Nes.stepCycle n) := by
  have e0 := latchReset_pos n
  have hv0 := posEq_valid e0 hv
  obtain ⟨m, h1, h2⟩ := body_split n.latchReset
  have d1 := (ppuDot_step n.latchReset hv0)
  have d2 := (ppuDot_step _ d1.1).posEq h1
  have d3 := (ppuDot_step m (posEq_valid h1 (ppuDot_step _ d1.1).1)).posEq h2
  have c := cycStep_of_dots d1 d2 d3
  rw [stepCycle_eq]
  have hl : lin n.latchReset.ppu = lin n.ppu := posEq_lin e0
  refine ⟨c.1, ?_⟩
  show (lin (body n.latchReset).ppu = lin n.ppu + 3 ∧ (body n.latchReset).frame = n.frame) ∨
    (lin (body n.latchReset).ppu ≤ 2 ∧ (body n.latchReset).frame = n.frame + 1)
  rw [← hl, ← e0.3]; exact c.2

/-! ### T-SYS-1 -/

/-- The clock invariant: `ppuDots = 3 · cpuCycles`, `apuHalf = cpuCycles`, `cpuOdd` is the
parity of `cpuCycles` (all mod 2⁶⁴). -/
def ClockInv (c : Clock) : Prop :=
  c.ppuDots = 3 * c.cpuCycles ∧ c.apuHalf = c.cpuCycles ∧ c.cpuOdd = (c.cpuCycles % 2 == 1)

theorem u64_parity_succ (x : UInt64) : ((x + 1) % 2 == 1) = !(x % 2 == 1) := by
  have h := x.toNat_lt
  have e : ((x + 1) % 2).toNat = (x.toNat + 1) % 2 := by
    rw [UInt64.toNat_mod, UInt64.toNat_add]; simp
  have e' : (x % 2).toNat = x.toNat % 2 := by rw [UInt64.toNat_mod]; simp
  have q : ∀ y : UInt64, (y == 1) = (y.toNat == 1) := by
    intro y; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, ← UInt64.toNat_inj]; simp
  rw [q, q, e, e']
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · have : (x.toNat + 1) % 2 = 1 := by omega
    rw [this, h0]; rfl
  · have : (x.toNat + 1) % 2 = 0 := by omega
    rw [this, h1]; rfl

theorem clockInv_tick (c : Clock) (h : ClockInv c) : ClockInv c.tick := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show c.ppuDots + 3 = 3 * (c.cpuCycles + 1)
    rw [h1, UInt64.mul_add, UInt64.mul_one]
  · show c.apuHalf + 1 = c.cpuCycles + 1
    rw [h2]
  · show (!c.cpuOdd) = ((c.cpuCycles + 1) % 2 == 1)
    rw [h3, u64_parity_succ]

theorem runCycles_succ (k : Nat) (n : Nes) :
    Nes.runCycles (k + 1) n = Nes.runCycles k (Nes.stepCycle n) := rfl

theorem toU64_succ (k : Nat) : (k + 1).toUInt64 = k.toUInt64 + 1 := UInt64.ofNat_add k 1

/-- `Clock.tick` iterated. -/
def ticks : Nat → Clock → Clock
  | 0, c => c
  | k + 1, c => ticks k c.tick

/-- `runCycles k` ticks the clock `k` times. -/
theorem runCycles_clock (k : Nat) (n : Nes) : (Nes.runCycles k n).clock = ticks k n.clock := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [runCycles_succ, ih, stepCycle_clock]; rfl

theorem ticks_cpuCycles (k : Nat) (c : Clock) :
    (ticks k c).cpuCycles = c.cpuCycles + k.toUInt64 := by
  induction k generalizing c with
  | zero => simp [ticks]
  | succ k ih =>
    rw [ticks, ih]
    show c.cpuCycles + 1 + k.toUInt64 = c.cpuCycles + (k + 1).toUInt64
    rw [toU64_succ, UInt64.add_assoc, UInt64.add_comm 1]

theorem ticks_ppuDots (k : Nat) (c : Clock) :
    (ticks k c).ppuDots = c.ppuDots + 3 * k.toUInt64 := by
  induction k generalizing c with
  | zero => simp [ticks]
  | succ k ih =>
    rw [ticks, ih]
    show c.ppuDots + 3 + 3 * k.toUInt64 = c.ppuDots + 3 * (k + 1).toUInt64
    rw [toU64_succ, UInt64.mul_add, UInt64.mul_one, UInt64.add_assoc, UInt64.add_comm 3]

/-- **T-SYS-1 (clock invariant).** From any state whose clock satisfies the invariant (e.g.
`powerOn`, `T_SYS_1_powerOn`), after `k` `stepCycle`s it still holds — `ppuDots = 3 · cpuCycles`,
`apuHalf = cpuCycles` — and `cpuCycles` advanced by `k`. -/
theorem T_SYS_1_clock (k : Nat) (n : Nes) (h : ClockInv n.clock) :
    ClockInv (Nes.runCycles k n).clock ∧
      (Nes.runCycles k n).clock.cpuCycles = n.clock.cpuCycles + k.toUInt64 := by
  rw [runCycles_clock]
  refine ⟨?_, ticks_cpuCycles k _⟩
  generalize n.clock = c at h
  induction k generalizing c with
  | zero => exact h
  | succ k ih => exact ih _ (clockInv_tick _ h)

/-- The power-on clock satisfies the invariant (all counters zero). -/
theorem T_SYS_1_powerOn (cart : Nes.Cart.Cart) : ClockInv (Nes.powerOn cart).clock := by
  refine ⟨rfl, rfl, rfl⟩

/-! ### T-SYS-3 -/

theorem u64_succ_ne (f : UInt64) : (f + 1 != f) = true := by
  have h := f.toNat_lt
  simp only [bne_iff_ne, ne_eq]
  intro e
  have := congrArg UInt64.toNat e
  rw [UInt64.toNat_add] at this; simp at this; omega

theorem pos_of_lin_le2 (s : State) (h : lin s ≤ 2) : s.scanline = 0 ∧ s.dot.toNat ≤ 2 := by
  unfold lin at h
  refine ⟨?_, by omega⟩
  rw [← UInt16.toNat_inj]; simp; omega

/-- `runFrame.go`: with enough fuel to reach the end of the frame, stops on the cycle that
wraps the PPU to `(0, 0)`, with the frame counter one up. -/
theorem runFrame_go (k : Nat) (f : UInt64) (n : Nes) (hv : Valid n.ppu) (hf : n.frame = f)
    (hk : 89342 ≤ lin n.ppu + 3 * k) :
    (Nes.runFrame.go k f n).frame = f + 1 ∧ (Nes.runFrame.go k f n).ppu.scanline = 0 ∧
      (Nes.runFrame.go k f n).ppu.dot.toNat ≤ 2 ∧ Valid (Nes.runFrame.go k f n).ppu := by
  induction k generalizing n with
  | zero => have := lin_le _ hv; omega
  | succ k ih =>
    have c := stepCycle_pos n hv
    unfold Nes.runFrame.go
    dsimp only
    rcases c.2 with ⟨hl, hfr⟩ | ⟨hl, hfr⟩
    · have : ((Nes.stepCycle n).frame != f) = false := by rw [hfr, hf]; simp
      rw [this]
      exact ih _ c.1 (hfr.trans hf) (by omega)
    · have : ((Nes.stepCycle n).frame != f) = true := by rw [hfr, hf]; exact u64_succ_ne f
      simp only [this, ite_true]
      have p := pos_of_lin_le2 _ hl
      exact ⟨by rw [← hf]; exact hfr, p.1, p.2, c.1⟩

/-- **T-SYS-3 (frame progress).** From any state with the PPU counters in range, `runFrame`
with at least `frameFuel = 29781` cycles of fuel advances the frame counter by exactly 1 and
stops at the start of the next frame: scanline 0, dot `≤ 2` — `(0, 0)` up to the CPU-cycle
granularity of the master step (the wrap dot is the 1st, 2nd or 3rd dot of the last cycle). -/
theorem T_SYS_3_frame (n : Nes) (hv : Valid n.ppu) (fuel : Nat) (hfuel : Nes.frameFuel ≤ fuel) :
    (n.runFrame fuel).frame = n.frame + 1 ∧ (n.runFrame fuel).ppu.scanline = 0 ∧
      (n.runFrame fuel).ppu.dot.toNat ≤ 2 ∧ Valid (n.runFrame fuel).ppu := by
  have := lin_le _ hv
  exact runFrame_go fuel n.frame n hv rfl (by unfold Nes.frameFuel at hfuel; omega)

/-- **T-SYS-3 (frames).** `runFrames k input` emits exactly `k` frames. -/
theorem T_SYS_3_frames (k : Nat) (input : Nat → UInt8 × UInt8) (n : Nes) (hv : Valid n.ppu) :
    (n.runFrames k input).frame = n.frame + k.toUInt64 ∧ Valid (n.runFrames k input).ppu := by
  unfold Nes.runFrames
  suffices ∀ i k n, Valid n.ppu →
      (Nes.runFrames.go input i k n).frame = n.frame + k.toUInt64 ∧
        Valid (Nes.runFrames.go input i k n).ppu from this 0 k n hv
  intro i k
  induction k generalizing i with
  | zero => intro n hv; exact ⟨by simp [Nes.runFrames.go], hv⟩
  | succ k ih =>
    intro n hv
    unfold Nes.runFrames.go
    dsimp only
    have t := T_SYS_3_frame { n with pads := n.pads.setButtons (input i).1 (input i).2 } hv
      Nes.frameFuel (Nat.le_refl _)
    have r := ih (i + 1) _ t.2.2.2
    refine ⟨?_, r.2⟩
    rw [r.1, t.1, toU64_succ, UInt64.add_assoc, UInt64.add_comm 1]

/-- The power-on PPU is at `(0, 0)`, so T-SYS-3 applies from power-on. -/
theorem valid_powerOn (cart : Nes.Cart.Cart) : Valid (Nes.powerOn cart).ppu := by
  unfold Valid; exact ⟨by simp [Nes.powerOn, State.init], by simp [Nes.powerOn, State.init]⟩
