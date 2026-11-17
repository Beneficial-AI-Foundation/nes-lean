import Nes.System.Proofs.Clock
import Nes.System.Proofs.Dma
import Nes.Cpu.Proofs.InterruptsLatency

/-!
# `Nes.System.Proofs.Interrupts` — T-SYS-4: interrupt delivery in the whole machine

## Spec

* `cpuPre n`: the machine of one `stepCycle` just before the CPU core completes the cycle —
  after the RESET latch, all three PPU dots and the CPU's bus access — with the byte read or
  written. `cycleLines n = (cpuPre n).1.lines`, `cycleData n = (cpuPre n).2`.
* `T_SYS_4_step_cpu` (wiring of `stepCycle`): with no DMA running, the CPU core after a cycle is
  `n.latchReset.cpu.complete (cycleLines n) (cycleData n)` — the lines handed to
  `Core.complete` are the lines of the machine *after the cycle's three dots*.
* `T_SYS_4_irq_wiring`: those lines are `irq = cart.irq || apuIrq` (wired-OR; `apuIrq = false`
  until M5, `T_SYS_4_apuIrq`), `nmi = ppu.nmiLine` (the PPU's `/NMI` output after the dots),
  `reset = false` (RESET goes through `latchReset`).
* `T_SYS_4_cpu_projection`: with the RESET line low and no DMA active in the first `k`
  cycles, `(runCycles k n).cpu = coreRun (sysLines n) (sysData n) n.cpu k`: the system's CPU
  is the core driven by the induced line schedule `sysLines n i` and bus-data stream
  `sysData n i` (cycle `i` of the system run).
* `T_SYS_4_cpu_projection_mem`: if moreover the induced lines follow a schedule `ls` and every
  byte the CPU reads from the system agrees with what the flat-memory run `runSched i ls cpu m`
  would read (bus coherence), the system's CPU equals the core of `runSched` (T-CPU-7's model)
  cycle by cycle.
* `T_SYS_4_nmi` (T-CPU-7 ∘ T-PPU-5): from an instruction boundary (T-CPU-7's preconditions on
  `n.cpu`), if the PPU's NMI line as the CPU samples it is low in the instruction's system
  cycles `0 … j-2` and high (held) in cycles `j-1 …` of the window, the IRQ line constant,
  RESET low, no DMA, the CPU's reads coherent with a flat image `m`, and no JAM: `d` system
  cycles after the edge, `d ≤ (8 - (j - 1)) + 15` (≤ 23; ≤ 22 for `j ≥ 2`), the CPU is at a
  boundary with I set and `PC = mem16[$FFFA]`. Vblank holds the line high for ~2273 CPU cycles
  (T-PPU-5: `T_PPU_5_nmi_at_vblank` raises it at (241, 1) when NMI is enabled), far more than
  the window, unless the program reads `$2002` or clears `$2000.7` — hence the hold is a
  hypothesis.

## Gaps

* The bus-coherence hypothesis: T-CPU-7 is stated over a flat 64 KiB `Mem`; the system's bus has
  side-effecting registers, so `T_SYS_4_nmi` assumes the reads in the window agree with some
  flat image (true for code and vectors in RAM/PRG-ROM that do not touch changing I/O).
  The general projection (`T_SYS_4_cpu_projection`) has no such hypothesis.
* IRQ held constant in the window (as T-CPU-7 requires).
-/

namespace Nes.System.Proofs

open Nes.System Nes.Cpu Nes.Cpu.Proofs MicroState

/-! ## Wiring -/

/-- The machine of one cycle just before `Core.complete` (after the RESET latch, the `preDots`
dots, the CPU's bus access with the open-bus latch, the remaining dot), and the byte read or
written. Valid when no DMA runs (`stepCycle` then takes the CPU branch). -/
def busAccess (n : Nes) : Nes × UInt8 :=
  match n.cpu.busOp with
  | .read a =>
    let (n, v) := n.cpuRead a
    (Nes.ppuDots (3 - preDots) { n with bus := n.bus.latch v }, v)
  | .write a v =>
    let n := n.cpuWrite a v
    (Nes.ppuDots (3 - preDots) { n with bus := n.bus.latch v }, v)

/-- The machine of one cycle just before `Core.complete` (after the RESET latch, the `preDots`
dots, the CPU's bus access with the open-bus latch, the remaining dot), and the byte read or
written. Valid when no DMA runs (`stepCycle` then takes the CPU branch). -/
def cpuPre (n : Nes) : Nes × UInt8 := busAccess (Nes.ppuDots preDots n.latchReset)

/-- The interrupt lines the CPU core samples in the cycle starting from `n`. -/
def cycleLines (n : Nes) : IntLines := (cpuPre n).1.lines

/-- The bus byte the CPU core completes the cycle starting from `n` with. -/
def cycleData (n : Nes) : UInt8 := (cpuPre n).2

theorem cpuRead_cpu (n : Nes) (a : UInt16) : (n.cpuRead a).1.cpu = n.cpu := by
  unfold Nes.cpuRead
  repeat' split
  all_goals rfl

theorem ppuPoke_cpu (n : Nes) (a : UInt16) (v : UInt8) : (n.ppuPoke a v).cpu = n.cpu := by
  unfold Nes.ppuPoke
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem cpuWrite_cpu (n : Nes) (a : UInt16) (v : UInt8) : (n.cpuWrite a v).cpu = n.cpu := by
  unfold Nes.cpuWrite
  repeat' split
  all_goals first | rfl | exact ppuPoke_cpu _ _ _

theorem pre_dma (n : Nes) : (Nes.ppuDots preDots n.latchReset).dma = n.dma := by
  unfold Nes.latchReset; split <;> rfl

/-- `cpuCycle` completes the core with the lines of the machine after the bus access and the
last dot. -/
theorem cpuCycle_cpu (m : Nes) :
    m.cpuCycle.cpu = m.cpu.complete (busAccess m).1.lines (busAccess m).2 := by
  unfold Nes.cpuCycle busAccess
  rcases hb : m.cpu.busOp with a | ⟨a, v⟩
  · dsimp only
    have hc := cpuRead_cpu m a
    rcases hr : m.cpuRead a with ⟨r, v⟩
    rw [hr] at hc
    dsimp only
    show r.cpu.complete _ _ = _
    rw [hc]
  · dsimp only
    have hc := cpuWrite_cpu m a v
    generalize m.cpuWrite a v = w at hc ⊢
    show w.cpu.complete _ _ = _
    rw [hc]

/-- **T-SYS-4 (wiring of `stepCycle`).** With no DMA running, one system cycle completes the CPU
core with the lines `cycleLines n` (the machine's lines after all three dots of the cycle and
the bus access) and the bus byte `cycleData n`. -/
theorem T_SYS_4_step_cpu (n : Nes) (hdma : n.dma.active = false) :
    (Nes.stepCycle n).cpu = n.latchReset.cpu.complete (cycleLines n) (cycleData n) := by
  have h2 : (Nes.ppuDots preDots n.latchReset).dma.active = false := by rw [pre_dma]; exact hdma
  rw [stepCycle_eq]
  show (body n.latchReset).cpu = _
  unfold body cycleLines cycleData cpuPre
  simp only [h2, Bool.false_eq_true, ite_false]
  rw [cpuCycle_cpu]
  rfl

/-- The APU's IRQ output is not modelled yet (M5). -/
theorem T_SYS_4_apuIrq (n : Nes) : n.apuIrq = false := rfl

/-- **T-SYS-4 (interrupt wiring).** The IRQ line the CPU samples in a cycle is the wired-OR of
the mapper's and the APU's IRQ outputs, the NMI line is the PPU's `/NMI` output — both of the
machine after the cycle's three dots and bus access — and the RESET input is idle (RESET goes
through `latchReset`). -/
theorem T_SYS_4_irq_wiring (n : Nes) :
    (cycleLines n).irq = ((cpuPre n).1.cart.irq || (cpuPre n).1.apuIrq) ∧
      (cycleLines n).irq = (cpuPre n).1.cart.irq ∧
      (cycleLines n).nmi = (cpuPre n).1.ppu.nmiLine ∧
      (cycleLines n).reset = false := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  show ((cpuPre n).1.cart.irq || false) = _
  simp

/-- The machine `cpuPre` samples is the one after all three dots: the last dot is the final
step of `cpuPre`. -/
theorem T_SYS_4_dots (n : Nes) : ∃ m : Nes, (cpuPre n).1 = m.ppuDot := by
  unfold cpuPre busAccess
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ## Projection onto the CPU core -/

/-- The core driven by a line schedule `ls` and a bus-data stream `vs` (cycle `i` completes
with `ls i`, `vs i`). -/
def coreRun (ls : Nat → IntLines) (vs : Nat → UInt8) (c : Core) : Nat → Core
  | 0 => c
  | k + 1 => (coreRun ls vs c k).complete (ls k) (vs k)

/-- Lines sampled by the CPU in system cycle `i` of the run from `n`. -/
def sysLines (n : Nes) (i : Nat) : IntLines := cycleLines (Nes.runCycles i n)

/-- Bus byte of the CPU in system cycle `i` of the run from `n`. -/
def sysData (n : Nes) (i : Nat) : UInt8 := cycleData (Nes.runCycles i n)

theorem runCycles_succ' (k : Nat) (n : Nes) :
    Nes.runCycles (k + 1) n = Nes.stepCycle (Nes.runCycles k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [Nes.runCycles, ih]; rfl

theorem runCycles_resetLine (k : Nat) (n : Nes) :
    (Nes.runCycles k n).resetLine = n.resetLine := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runCycles_succ', stepCycle_resetLine, ih]

/-- One system cycle, RESET low, no DMA: the CPU completes with the induced lines and byte. -/
theorem step_cpu (n : Nes) (hrst : n.resetLine = false) (hdma : n.dma.active = false) :
    (Nes.stepCycle n).cpu = n.cpu.complete (cycleLines n) (cycleData n) := by
  rw [T_SYS_4_step_cpu n hdma, latchReset_of n hrst]

/-- **T-SYS-4 (CPU projection).** With the RESET line low and no DMA active during the first
`k` cycles, the system's CPU after `k` cycles is the CPU core driven by the line schedule and
bus-data stream the machine induces. -/
theorem T_SYS_4_cpu_projection (n : Nes) (k : Nat) (hrst : n.resetLine = false)
    (hdma : ∀ i, i < k → (Nes.runCycles i n).dma.active = false) :
    (Nes.runCycles k n).cpu = coreRun (sysLines n) (sysData n) n.cpu k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runCycles_succ', step_cpu _ (by rw [runCycles_resetLine]; exact hrst) (hdma k (by omega)),
      ih (fun i hi => hdma i (by omega))]
    rfl

/-- The byte of a write cycle is the written byte. -/
theorem cycleData_write (n : Nes) (hrst : n.resetLine = false) (a : UInt16) (v : UInt8)
    (h : n.cpu.busOp = .write a v) : cycleData n = v := by
  unfold cycleData cpuPre busAccess
  rw [latchReset_of n hrst]
  have hc : (Nes.ppuDots preDots n).cpu = n.cpu := rfl
  generalize Nes.ppuDots preDots n = m at hc
  rw [hc]
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i h'; rw [h] at h'; cases h'; rfl

theorem runSched_succ' (i : Nat) (ls : Nat → IntLines) (c : Core) (m : Mem) :
    runSched (i + 1) ls c m = (runSched i ls c m).1.cycle (ls i) (runSched i ls c m).2 := by
  rw [runSched_add]; rfl

/-- **T-SYS-4 (CPU projection onto T-CPU-7's model).** If, in addition, the induced lines follow
a schedule `ls` and every byte the CPU reads from the system agrees with the flat-memory run
`runSched i ls n.cpu m` (bus coherence), the system's CPU equals that run's core in every cycle
`i ≤ k`. -/
theorem T_SYS_4_cpu_projection_mem (n : Nes) (ls : Nat → IntLines) (m : Mem) (k : Nat)
    (hrst : n.resetLine = false)
    (hdma : ∀ i, i < k → (Nes.runCycles i n).dma.active = false)
    (hl : ∀ i, i < k → sysLines n i = ls i)
    (hd : ∀ i, i < k → ∀ a, (runSched i ls n.cpu m).1.busOp = .read a →
      sysData n i = (runSched i ls n.cpu m).2.read a) :
    ∀ i, i ≤ k → (Nes.runCycles i n).cpu = (runSched i ls n.cpu m).1 := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hr : (Nes.runCycles i n).resetLine = false := by rw [runCycles_resetLine]; exact hrst
    have e := ih (by omega)
    rw [runCycles_succ', step_cpu _ hr (hdma i (by omega)), runSched_succ', e]
    show _ = (Core.cycle _ _ _).1
    have hli := hl i (by omega)
    unfold sysLines at hli
    rw [hli]
    unfold Core.cycle
    split
    · rename_i a ha
      have := hd i (by omega) a ha
      unfold sysData at this
      rw [this]
    · rename_i a v ha
      rw [cycleData_write _ hr a v (by rw [e]; exact ha)]

/-! ## NMI delivery (T-CPU-7 ∘ T-PPU-5) -/

/-- **T-SYS-4 (NMI delivery).** Start from a machine whose CPU is at an opcode-fetch boundary
with idle NMI detectors (T-CPU-7's preconditions), RESET line low. Suppose, for the system
cycles `i < W` of the window (`W = (j - 1) + (8 - (j - 1)) + 15`):
* the PPU's NMI line as the CPU samples it (after the cycle's dots) is low for `i + 1 < j` and
  high from `i = j - 1` on (an edge in the instruction's 1-based cycle `j ≥ 1`, held — vblank
  holds it ~2273 cycles unless `$2002` is read or `$2000.7` cleared);
* the IRQ line (`cart.irq || apuIrq`) is the constant `irq`; no DMA is active;
* the CPU's reads agree with the flat image `m` run by `runSched` (bus coherence);
* T-CPU-7's side conditions (the edge falls inside the instruction; no JAM fetched).
Then `d` system cycles after the edge, `d ≤ (8 - (j - 1)) + 15`, the CPU is at an instruction
boundary with I set and `PC = mem16[$FFFA]` (of the flat image at that point). -/
theorem T_SYS_4_nmi (n : Nes) (irq : Bool) (m : Mem) (j : Nat)
    (hpos : n.cpu.ms.pos = 0) (hint : n.cpu.ms.intPending = false)
    (hh : n.cpu.ms.cpu.halted = false)
    (hrstp : n.cpu.ints.resetPending = false) (hprev : n.cpu.ints.nmiPrev = false)
    (hpend : n.cpu.ints.nmiPending = false) (hpoll : n.cpu.ints.pollNmi = false)
    (hpirq : n.cpu.ints.pollIrq = false) (hj : 1 ≤ j)
    (hrst : n.resetLine = false)
    (hnmi : ∀ i, i < (j - 1) + ((maxCycles - (j - 1)) + maxCycles + 7) →
      (cpuPre (Nes.runCycles i n)).1.ppu.nmiLine = decide (j ≤ i + 1))
    (hirq : ∀ i, i < (j - 1) + ((maxCycles - (j - 1)) + maxCycles + 7) →
      ((cpuPre (Nes.runCycles i n)).1.cart.irq || (cpuPre (Nes.runCycles i n)).1.apuIrq) = irq)
    (hdma : ∀ i, i < (j - 1) + ((maxCycles - (j - 1)) + maxCycles + 7) →
      (Nes.runCycles i n).dma.active = false)
    (hd : ∀ i, i < (j - 1) + ((maxCycles - (j - 1)) + maxCycles + 7) → ∀ a,
      (runSched i (hjNmiFrom j fun _ => irq) n.cpu m).1.busOp = .read a →
      sysData n i = (runSched i (hjNmiFrom j fun _ => irq) n.cpu m).2.read a)
    (hin : ∀ k, 1 ≤ k → k < j → (runSched k (hjNmiFrom j fun _ => irq) n.cpu m).1.ms.pos ≠ 0)
    (hjam : ∀ k, k ≤ 2 * maxCycles + 7 →
      (runSched k (hjNmiFrom j fun _ => irq) n.cpu m).1.ms.pos = 0 →
      (runSched k (hjNmiFrom j fun _ => irq) n.cpu m).1.ms.intPending = false →
      classify (decode ((runSched k (hjNmiFrom j fun _ => irq) n.cpu m).2.read
        (runSched k (hjNmiFrom j fun _ => irq) n.cpu m).1.ms.cpu.pc)) ≠ .jam) :
    ∃ d, d ≤ (maxCycles - (j - 1)) + maxCycles + 7 ∧
      (Nes.runCycles (j - 1 + d) n).cpu.ms.pos = 0 ∧
      (Nes.runCycles (j - 1 + d) n).cpu.ms.cpu.i = true ∧
      (Nes.runCycles (j - 1 + d) n).cpu.ms.cpu.pc =
        UInt16.ofLoHi ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) n.cpu m).2.read 0xFFFA)
          ((runSched (j - 1 + d) (hjNmiFrom j fun _ => irq) n.cpu m).2.read 0xFFFB) := by
  obtain ⟨d, hdle, h1, h2, h3⟩ := T_CPU_7_nmi_latency_edge n.cpu irq m j hpos hint hh hrstp hprev
    hpend hpoll hpirq hj hin hjam
  have hl : ∀ i, i < (j - 1) + ((maxCycles - (j - 1)) + maxCycles + 7) →
      sysLines n i = hjNmiFrom j (fun _ => irq) i := by
    intro i hi
    have e1 := hnmi i hi
    have e2 := hirq i hi
    unfold sysLines cycleLines Nes.lines hjNmiFrom
    rw [e1, e2]
  have e := T_SYS_4_cpu_projection_mem n _ m _ hrst hdma hl hd (j - 1 + d) (by omega)
  exact ⟨d, hdle, by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact h3⟩

end Nes.System.Proofs

