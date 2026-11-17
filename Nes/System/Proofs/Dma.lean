import Nes.System.Proofs.Clock

namespace Nes.System.Proofs

open Nes.System Nes.Ppu Nes.Bus

/-! ### UInt16 facts about the counter, decided over the 256 pairs -/

theorem pair_facts : ∀ r : Fin 256,
    let c : UInt16 := (2 * (r.val + 1)).toUInt16
    ¬ (c > 512) ∧ (c &&& 1 == 0) = true ∧ ((512 - c) >>> 1) = (255 - r.val).toUInt16 ∧
    ¬ (c - 1 > 512) ∧ (c - 1 &&& 1 == 0) = false ∧ c - 1 - 1 = (2 * r.val).toUInt16 := by
  decide +kernel

/-! ### The DMA unit with the OAM it writes (abstract machine) -/

/-- The part of the machine a DMA cycle changes: the DMA unit, OAM and `OAMADDR`. -/
structure DmaView where
  dma : OamDma
  oam : ByteArray
  oamAddr : UInt8

/-- One DMA cycle on the view; `src a` is the byte the CPU bus returns for `a`. -/
def DmaView.step (src : UInt16 → UInt8) (x : DmaView) : DmaView :=
  match x.dma.op with
  | .idle => { x with dma := x.dma.complete 0 }
  | .read a => { x with dma := x.dma.complete (src a) }
  | .write v =>
    { dma := x.dma.complete v, oam := x.oam.set! x.oamAddr.toNat v, oamAddr := x.oamAddr + 1 }

/-- `k` DMA cycles. -/
def DmaView.run (src : UInt16 → UInt8) : Nat → DmaView → DmaView
  | 0, x => x
  | k + 1, x => DmaView.run src k (x.step src)

/-- OAM after writing `f 0, …, f (k-1)` through `$2004` from `OAMADDR = a`. -/
def oamFill (oam : ByteArray) (a : UInt8) (f : Nat → UInt8) : Nat → ByteArray
  | 0 => oam
  | k + 1 => (oamFill oam a f k).set! (a + k.toUInt8).toNat (f k)

theorem u16_sub_sub (a b c : UInt16) : a - b - c = a - (b + c) :=
  UInt16.toBitVec_inj.mp (by simp [BitVec.sub_sub])

theorem toU16_succ (k : Nat) : (k + 1).toUInt16 = k.toUInt16 + 1 := UInt16.ofNat_add k 1
theorem toU8_succ (k : Nat) : (k + 1).toUInt8 = k.toUInt8 + 1 := UInt8.ofNat_add k 1

theorem complete_left (d : OamDma) (v : UInt8) : (d.complete v).left = d.left - 1 := by
  unfold OamDma.complete; dsimp only; split <;> rfl

theorem complete_page (d : OamDma) (v : UInt8) : (d.complete v).page = d.page := by
  unfold OamDma.complete; dsimp only; split <;> rfl

theorem complete_get (d : OamDma) (v : UInt8) (h1 : ¬ d.left > 512) (h2 : (d.left &&& 1 == 0) = true) :
    d.complete v = { d with left := d.left - 1, latch := v } := by
  have : d.left ≤ 512 := UInt16.not_lt.mp h1
  unfold OamDma.complete; simp [this, h2]

theorem complete_put (d : OamDma) (v : UInt8) (h2 : (d.left &&& 1 == 0) = false) :
    d.complete v = { d with left := d.left - 1 } := by
  unfold OamDma.complete; simp [h2]

theorem step_dma (src) (x : DmaView) :
    (x.step src).dma.left = x.dma.left - 1 ∧ (x.step src).dma.page = x.dma.page := by
  unfold DmaView.step; split <;> exact ⟨complete_left _ _, complete_page _ _⟩

theorem run_left (src) (k : Nat) (x : DmaView) :
    (DmaView.run src k x).dma.left = x.dma.left - k.toUInt16 ∧
      (DmaView.run src k x).dma.page = x.dma.page := by
  induction k generalizing x with
  | zero => simp [DmaView.run]
  | succ k ih =>
    rw [DmaView.run, (ih _).1, (ih _).2, (step_dma src x).1, (step_dma src x).2]
    refine ⟨?_, rfl⟩
    rw [u16_sub_sub, UInt16.add_comm, toU16_succ]

/-- The 256 get/put pairs: from `2r` cycles left with `256 - r` bytes written, the remaining
`2r` cycles write the rest. -/
theorem run_pairs (src : UInt16 → UInt8) (oam0 : ByteArray) (a0 : UInt8) (r : Nat) (hr : r ≤ 256)
    (x : DmaView) (hl : x.dma.left = (2 * r).toUInt16)
    (ho : x.oam = oamFill oam0 a0 (fun i => src (x.dma.page.toUInt16 * 256 + i.toUInt16)) (256 - r))
    (ha : x.oamAddr = a0 + (256 - r).toUInt8) :
    (DmaView.run src (2 * r) x).oam =
        oamFill oam0 a0 (fun i => src (x.dma.page.toUInt16 * 256 + i.toUInt16)) 256 ∧
      (DmaView.run src (2 * r) x).oamAddr = a0 := by
  induction r generalizing x with
  | zero => simp [DmaView.run] at ho ha ⊢; exact ⟨ho, ha⟩
  | succ r ih =>
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := pair_facts ⟨r, by omega⟩
    dsimp only at f1 f2 f3 f4 f5 f6
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega, DmaView.run, DmaView.run]
    -- the get
    have hop1 : x.dma.op = .read (x.dma.page.toUInt16 * 256 + (255 - r).toUInt16) := by
      unfold OamDma.op; dsimp only; simp only [hl, f1, f2, f3, ite_false, ite_true]
    obtain ⟨v, hv⟩ : ∃ v, src (x.dma.page.toUInt16 * 256 + (255 - r).toUInt16) = v := ⟨_, rfl⟩
    have hx1 : x.step src = { x with dma := { x.dma with left := x.dma.left - 1, latch := v } } := by
      unfold DmaView.step; rw [hop1]; dsimp only
      rw [complete_get _ _ (by rw [hl]; exact f1) (by rw [hl]; exact f2), hv]
    rw [hx1]
    have hop2 : ({ x.dma with left := x.dma.left - 1, latch := v } : OamDma).op = .write v := by
      unfold OamDma.op; dsimp only; simp only [hl, f4, f5, ite_false]; rfl
    have hx2 := ih (by omega)
      { dma := { x.dma with left := x.dma.left - 1 - 1, latch := v },
        oam := x.oam.set! x.oamAddr.toNat v, oamAddr := x.oamAddr + 1 }
      (by dsimp only; rw [hl, f6])
      (by
        dsimp only
        rw [ho, show 256 - r = (255 - r) + 1 by omega, oamFill, ha,
          show 256 - (r + 1) = 255 - r by omega, hv])
      (by dsimp only; rw [ha, show 256 - (r + 1) = 255 - r by omega,
        show 256 - r = (255 - r) + 1 by omega, toU8_succ, UInt8.add_assoc])
    unfold DmaView.step
    rw [hop2]
    dsimp only
    rw [complete_put _ _ (by dsimp only; rw [hl]; exact f5)]
    exact hx2

theorem left_pos : ∀ j : Fin 514, ((514 : UInt16) - j.val.toUInt16 != 0) = true ∧
    (j.val < 513 → ((513 : UInt16) - j.val.toUInt16 != 0) = true) := by
  decide +kernel

theorem step_idle (src) (x : DmaView) (h : x.dma.left > 512) :
    x.step src = { x with dma := { x.dma with left := x.dma.left - 1 } } := by
  have hop : x.dma.op = .idle := by unfold OamDma.op; simp [h]
  have hc : x.dma.complete 0 = { x.dma with left := x.dma.left - 1 } := by
    have : ¬ x.dma.left ≤ 512 := fun h' => absurd h (UInt16.not_lt.mpr h')
    unfold OamDma.complete; simp [this]
  unfold DmaView.step; rw [hop]; dsimp only; rw [hc]

/-- **T-SYS-2 (DMA unit).** A transfer started by `$4014 ← p` on an even (`odd = false`) / odd
CPU cycle is active for exactly `513` / `514` cycles, whatever the bus returns, and leaves OAM
holding the 256 bytes read from `p·256 + i` (`i = 0 … 255`) written from `OAMADDR = a0` on
(mod 256), with `OAMADDR` back at `a0`. -/
theorem T_SYS_2_machine (src : UInt16 → UInt8) (d0 : OamDma) (p : UInt8) (odd : Bool)
    (oam0 : ByteArray) (a0 : UInt8) :
    let L := if odd then 514 else 513
    let x0 : DmaView := ⟨d0.start p odd, oam0, a0⟩
    (∀ j < L, (DmaView.run src j x0).dma.active = true) ∧
      (DmaView.run src L x0).dma.active = false ∧
      (DmaView.run src L x0).oam =
        oamFill oam0 a0 (fun i => src (p.toUInt16 * 256 + i.toUInt16)) 256 ∧
      (DmaView.run src L x0).oamAddr = a0 := by
  intro L x0
  have hpage : x0.dma.page = p := rfl
  refine ⟨?_, ?_⟩
  · intro j hj
    have := (run_left src j x0).1
    unfold OamDma.active; rw [this]
    have lp := left_pos ⟨j, by cases odd <;> simp [L] at hj <;> omega⟩
    cases odd
    · exact lp.2 (by simp [L] at hj; exact hj)
    · exact lp.1
  -- the idle cycles, then the pairs
  have pairs : ∀ y : DmaView, y.dma.left = (2 * 256).toUInt16 → y.dma.page = p → y.oam = oam0 →
      y.oamAddr = a0 →
      (DmaView.run src (2 * 256) y).dma.active = false ∧
      (DmaView.run src (2 * 256) y).oam =
        oamFill oam0 a0 (fun i => src (p.toUInt16 * 256 + i.toUInt16)) 256 ∧
      (DmaView.run src (2 * 256) y).oamAddr = a0 := by
    intro y hl hp ho ha
    have r := run_pairs src oam0 a0 256 (Nat.le_refl _) y hl (by rw [ho, hp]; rfl)
      (by rw [ha]; simp)
    rw [hp] at r
    refine ⟨?_, r.1, r.2⟩
    unfold OamDma.active; rw [(run_left src _ y).1, hl]; decide
  have run_succ : ∀ k x, DmaView.run src (k + 1) x = DmaView.run src k (x.step src) :=
    fun _ _ => rfl
  cases odd
  · have e : L = 2 * 256 + 1 := rfl
    simp only [e]
    rw [run_succ, step_idle src x0 (by show (513 : UInt16) > 512; decide)]
    exact pairs _ (by show (513 : UInt16) - 1 = (2 * 256).toUInt16; decide) rfl rfl rfl
  · have e : L = 2 * 256 + 1 + 1 := rfl
    simp only [e]
    rw [run_succ, run_succ, step_idle src x0 (by show (514 : UInt16) > 512; decide),
      step_idle src _ (by show (514 : UInt16) - 1 > 512; decide)]
    exact pairs _ (by show (514 : UInt16) - 1 - 1 = (2 * 256).toUInt16; decide) rfl rfl rfl

/-! ### The system during DMA -/

/-- The DMA-relevant part of the machine. -/
def view (n : Nes) : DmaView := ⟨n.dma, n.ppu.oam, n.ppu.oamAddr⟩

theorem ppuDot_dma (n : Nes) :
    n.ppuDot.ppu.oam = n.ppu.oam ∧ n.ppuDot.ppu.oamAddr = n.ppu.oamAddr ∧ n.ppuDot.dma = n.dma ∧
      n.ppuDot.ram = n.ram ∧ n.ppuDot.cpu = n.cpu ∧ n.ppuDot.clock = n.clock :=
  have k := ppu_dot_like_advance (Nes.ppuPeek n.cart n.ciram n.ciram_size)
    (Nes.palPeek n.pal n.pal_size) n.ppu
  ⟨k.2.2.2.1, k.2.2.2.2.1, rfl, rfl, rfl, rfl⟩

theorem cpuWrite_2004 (n : Nes) (v : UInt8) :
    (n.cpuWrite 0x2004 v).ppu.oam = n.ppu.oam.set! n.ppu.oamAddr.toNat v ∧
      (n.cpuWrite 0x2004 v).ppu.oamAddr = n.ppu.oamAddr + 1 ∧
      (n.cpuWrite 0x2004 v).dma = n.dma ∧ (n.cpuWrite 0x2004 v).ram = n.ram ∧
      (n.cpuWrite 0x2004 v).cpu = n.cpu := by
  simp [Nes.cpuWrite, State.cpuWrite, State.writeOamData]

theorem cpuWrite_4014 (n : Nes) (v : UInt8) :
    (n.cpuWrite 0x4014 v).dma = n.dma.start v n.clock.cpuOdd := by
  simp [Nes.cpuWrite]; rfl

theorem cpuRead_ram (n : Nes) (a : UInt16) (h : a < 0x2000) :
    (n.cpuRead a).1 = n ∧ (n.cpuRead a).2 = n.ram[(ramIndex a).val]'(fin_lt_size n.ram_size _) := by
  simp [Nes.cpuRead, h]

theorem cpuRead_ram_eq (n m : Nes) (a : UInt16) (h : a < 0x2000) (hr : m.ram = n.ram) :
    (m.cpuRead a).2 = (n.cpuRead a).2 := by
  rw [(cpuRead_ram n a h).2, (cpuRead_ram m a h).2]; simp only [hr]

theorem op_read_lt (d : OamDma) (hp : d.page < 0x20) (ha : d.active = true) (a : UInt16)
    (h : d.op = .read a) : a < 0x2000 := by
  unfold OamDma.op at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · rename_i h1 h2
    cases h
    unfold OamDma.active at ha
    have hc1 : d.left.toNat ≤ 512 := by
      have := UInt16.not_lt.mp h1; exact UInt16.le_iff_toNat_le.mp this
    have hc0 : d.left.toNat ≠ 0 := by
      intro e; simp [← UInt16.toNat_inj, e] at ha
    have hc2 : d.left.toNat % 2 = 0 := by
      have := congrArg UInt16.toNat (beq_iff_eq.mp h2)
      rw [UInt16.toNat_and] at this; simpa [Nat.and_one_is_mod] using this
    have hp' : d.page.toNat < 32 := UInt8.lt_iff_toNat_lt.mp hp
    have hsub : (512 - d.left).toNat = 512 - d.left.toNat :=
      UInt16.toNat_sub_of_le _ _ (UInt16.le_iff_toNat_le.mpr (by show d.left.toNat ≤ 512; omega))
    rw [UInt16.lt_iff_toNat_lt]
    simp [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_shiftRight, hsub]
    omega
  · cases h

/-- A cycle while the DMA unit runs (source page in work RAM): the view takes one abstract DMA
step (`src` = the RAM bytes), the CPU core is not clocked, RAM is untouched. -/
theorem latchReset_of (n : Nes) (h : n.resetLine = false) : n.latchReset = n := by
  simp [Nes.latchReset, h]

theorem stepCycle_dma (n : Nes) (src : UInt16 → UInt8) (hrst : n.resetLine = false)
    (hact : n.dma.active = true)
    (hp : n.dma.page < 0x20) (hsrc : ∀ a, a < 0x2000 → src a = (n.cpuRead a).2) :
    view (Nes.stepCycle n) = (view n).step src ∧ (Nes.stepCycle n).ram = n.ram ∧
      (Nes.stepCycle n).cpu = n.cpu := by
  have d1 := ppuDot_dma n
  have d2 := ppuDot_dma n.ppuDot
  have hact2 : (Nes.ppuDots preDots n).dma.active = true := hact
  rw [stepCycle_eq, latchReset_of n hrst]
  unfold body
  simp only [hact2, ite_true]
  show view (Nes.ppuDot (Nes.ppuDot n)).dmaCycle = _ ∧ (Nes.ppuDot (Nes.ppuDot n)).dmaCycle.ram = _ ∧
    (Nes.ppuDot (Nes.ppuDot n)).dmaCycle.cpu = _
  unfold view
  have ho : n.ppuDot.ppuDot.ppu.oam = n.ppu.oam := by rw [d2.1, d1.1]
  have hoa : n.ppuDot.ppuDot.ppu.oamAddr = n.ppu.oamAddr := by rw [d2.2.1, d1.2.1]
  have hd : n.ppuDot.ppuDot.dma = n.dma := rfl
  have hram : n.ppuDot.ppuDot.ram = n.ram := rfl
  have hcpu : n.ppuDot.ppuDot.cpu = n.cpu := rfl
  have hsrc' : ∀ a, a < 0x2000 → src a = (n.ppuDot.ppuDot.cpuRead a).2 := fun a h =>
    (hsrc a h).trans (cpuRead_ram_eq _ _ a h hram).symm
  generalize n.ppuDot.ppuDot = m at ho hoa hd hram hcpu hsrc' ⊢
  rw [← hd] at hp hact
  rw [← hd, ← ho, ← hoa, ← hram, ← hcpu]
  unfold Nes.dmaCycle DmaView.step
  dsimp only
  rcases hop : m.dma.op with _ | a | v
  · dsimp only
    rw [ppuDots_one]
    have d3 := ppuDot_dma { m with dma := m.dma.complete 0 }
    rw [d3.1, d3.2.1, d3.2.2.1, d3.2.2.2.1, d3.2.2.2.2.1]
    exact ⟨rfl, rfl, rfl⟩
  · have hlt := op_read_lt _ hp hact a hop
    have r := cpuRead_ram m a hlt
    have hv := hsrc' a hlt
    dsimp only
    rw [r.1, ← hv, ppuDots_one]
    have d3 := ppuDot_dma { m with bus := m.bus.latch (src a), dma := m.dma.complete (src a) }
    rw [d3.1, d3.2.1, d3.2.2.1, d3.2.2.2.1, d3.2.2.2.2.1]
    exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    have w := cpuWrite_2004 m v
    rw [ppuDots_one]
    generalize m.cpuWrite 0x2004 v = mw at w
    have d3 := ppuDot_dma { mw with bus := mw.bus.latch v, dma := mw.dma.complete v }
    rw [d3.1, d3.2.1, d3.2.2.1, d3.2.2.2.1, d3.2.2.2.2.1]
    dsimp only
    rw [w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2]
    exact ⟨rfl, rfl, rfl⟩

theorem dma_run (j : Nat) (n1 : Nes) (src : UInt16 → UInt8) (hrst : n1.resetLine = false)
    (hsrc : ∀ a, a < 0x2000 → src a = (n1.cpuRead a).2) (hp : n1.dma.page < 0x20)
    (hact : ∀ i < j, (DmaView.run src i (view n1)).dma.active = true) :
    view (Nes.runCycles j n1) = DmaView.run src j (view n1) ∧
      (Nes.runCycles j n1).ram = n1.ram ∧ (Nes.runCycles j n1).cpu = n1.cpu := by
  induction j generalizing n1 with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
    have s := stepCycle_dma n1 src hrst (hact 0 (by omega)) hp hsrc
    have hpage : (Nes.stepCycle n1).dma.page = n1.dma.page := by
      have := congrArg (fun x => x.dma.page) s.1
      simp only [view] at this; rw [this]; exact (step_dma src _).2
    have r := ih (Nes.stepCycle n1) (by rw [stepCycle_resetLine]; exact hrst)
      (fun a h => (hsrc a h).trans (cpuRead_ram_eq _ _ a h s.2.1).symm)
      (by rw [hpage]; exact hp)
      (fun i hi => by rw [s.1]; exact hact (i + 1) (by omega))
    rw [runCycles_succ, r.1, r.2.1, r.2.2, s.1, s.2.1, s.2.2]
    exact ⟨rfl, rfl, rfl⟩

/-- The `$4014` write cycle arms the DMA unit (`OamDma.start`, parity of that cycle). -/
theorem write4014 (n : Nes) (p : UInt8) (hrst : n.resetLine = false)
    (hop : n.cpu.busOp = .write 0x4014 p) (hidle : n.dma.active = false) :
    (Nes.stepCycle n).dma = n.dma.start p n.clock.cpuOdd := by
  have hidle2 : (Nes.ppuDots preDots n).dma.active = false := hidle
  have hop2 : (Nes.ppuDots preDots n).cpu.busOp = .write 0x4014 p := hop
  rw [stepCycle_eq, latchReset_of n hrst]
  unfold body
  simp only [hidle2, Bool.false_eq_true, ite_false]
  show (Nes.cpuCycle (Nes.ppuDots preDots n)).dma = _
  unfold Nes.cpuCycle
  rw [hop2]
  dsimp only
  rw [ppuDots_one]
  show (n.ppuDot.ppuDot.cpuWrite 0x4014 p).dma = _
  rw [cpuWrite_4014]; rfl

/-- **T-SYS-2 (OAM DMA postcondition).** Let the CPU's bus operation be the write `$4014 ← p`
(DMA idle), with the source page in work RAM (`p < $20`). After that cycle (`n1`):
* the DMA unit runs for exactly `L = 513` cycles if the write landed on an even CPU cycle, `514`
  if odd; during them the CPU core is halted (unchanged), after them the DMA is idle;
* OAM holds the 256 bytes read through the CPU bus (`cpuRead`) from `p·256 + i`, written from
  `OAMADDR` on (mod 256) — so `OAM = page p` when `OAMADDR = 0` — and `OAMADDR` is back where
  it was;
* the clock ticked `L` times: the PPU advanced `3 · L` dots (T-SYS-1).
-/
theorem T_SYS_2_oam_dma (n : Nes) (p : UInt8) (hp : p < 0x20) (hrst : n.resetLine = false)
    (hop : n.cpu.busOp = .write 0x4014 p) (hidle : n.dma.active = false) :
    let L := if n.clock.cpuOdd then 514 else 513
    let n1 := Nes.stepCycle n
    let m := Nes.runCycles L n1
    (∀ j < L, (Nes.runCycles j n1).dma.active = true ∧ (Nes.runCycles j n1).cpu = n1.cpu) ∧
      m.dma.active = false ∧ m.cpu = n1.cpu ∧
      m.ppu.oam = oamFill n1.ppu.oam n1.ppu.oamAddr
        (fun i => (n1.cpuRead (p.toUInt16 * 256 + i.toUInt16)).2) 256 ∧
      m.ppu.oamAddr = n1.ppu.oamAddr ∧
      m.clock = ticks L n1.clock ∧ m.clock.ppuDots = n1.clock.ppuDots + 3 * L.toUInt64 := by
  intro L n1 m
  have hd : n1.dma = n.dma.start p n.clock.cpuOdd := write4014 n p hrst hop hidle
  have hrst1 : n1.resetLine = false := by
    show (Nes.stepCycle n).resetLine = false; rw [stepCycle_resetLine]; exact hrst
  have hview : view n1 = ⟨n.dma.start p n.clock.cpuOdd, n1.ppu.oam, n1.ppu.oamAddr⟩ := by
    unfold view; rw [hd]
  have mach := T_SYS_2_machine (fun a => (n1.cpuRead a).2) n.dma p n.clock.cpuOdd
    n1.ppu.oam n1.ppu.oamAddr
  dsimp only at mach
  rw [← hview] at mach
  have hpage : n1.dma.page < 0x20 := by rw [hd]; exact hp
  have run := fun j (hj : j ≤ L) => dma_run j n1 (fun a => (n1.cpuRead a).2) hrst1 (fun _ _ => rfl)
    hpage (fun i hi => mach.1 i (by omega))
  have fin := run L (Nat.le_refl _)
  have hclk := runCycles_clock L n1
  refine ⟨fun j hj => ⟨?_, (run j (by omega)).2.2⟩, ?_, fin.2.2, ?_, ?_, hclk, ?_⟩
  · have := congrArg DmaView.dma (run j (by omega)).1
    simp only [view] at this; rw [this]; exact mach.1 j hj
  · have := congrArg DmaView.dma fin.1
    simp only [view] at this; rw [this]; exact mach.2.1
  · have := congrArg DmaView.oam fin.1
    simp only [view] at this; rw [this]; exact mach.2.2.1
  · have := congrArg DmaView.oamAddr fin.1
    simp only [view] at this; rw [this]; exact mach.2.2.2
  · rw [hclk, ticks_ppuDots]
