import Nes.Ppu.Data

/-!
# `Nes.Ppu.Proofs.Data` — T-PPU-7 (`$2007` read buffer)

## Spec

Throughout, `rd : UInt16 → UInt8` is the PPU-bus read, `palRd : UInt8 → UInt8` the palette RAM
read, `s : State`, and `a = s.v &&& 0x3FFF` (`s.vramAddr`).

* **T-PPU-7 (buffered).** If `a < $3F00`, `read2007 rd palRd s` returns the old
  `s.readBuffer` and the new `readBuffer` is `rd a` (`T_PPU_7_buffered`).
* **T-PPU-7 (palette).** If `$3F00 ≤ a`, it returns the palette byte immediately, bits 0–5 from
  `palRd (paletteIndex a)` and bits 6–7 from `s.ioLatch` (open bus), and the new `readBuffer`
  is the nametable byte underneath, `rd (a - $1000)` (`T_PPU_7_palette`).
* **T-PPU-7 (increment).** Either way the new `v` is `(s.v + 32) &&& $7FFF` when `ctrl` bit 2
  is set and `(s.v + 1) &&& $7FFF` otherwise, i.e. `v` advances within its 15 bits
  (`T_PPU_7_increment`); `ctrl` is unchanged.
* **T-PPU-7 (two reads).** If `a < $3F00` and the incremented address is also below `$3F00`,
  two consecutive reads return `[s.readBuffer, rd a]`: first the stale buffer, then the byte
  at `a` (`T_PPU_7_two_reads`).
* **T-PPU-7 (settled).** The bus-level read `read2007At now` (which models the refill landing
  after the next CPU cycle) agrees with `read2007` whenever the previous `$2007` read was not on
  the CPU cycle just before `now`, or the address is a palette address: same returned byte,
  same state apart from the bookkeeping fields `prevBuffer`/`lastRead2007`
  (`T_PPU_7_settled`); so the four statements above hold for every settled read. A read on the
  next CPU cycle returns `prevBuffer` and still refills/increments as `read2007`
  (`T_PPU_7_back_to_back`).

Method: unfold and `simp`; no case enumeration.
-/

namespace Nes.Ppu.Proofs

open Nes.Ppu Nes.Ppu.State

theorem T_PPU_7_buffered (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (h : s.v &&& 0x3FFF < 0x3F00) :
    (read2007 rd palRd s).2 = s.readBuffer ∧
    (read2007 rd palRd s).1.readBuffer = rd (s.v &&& 0x3FFF) := by
  simp [read2007, vramAddr, incAddr, h]

theorem T_PPU_7_palette (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (h : 0x3F00 ≤ s.v &&& 0x3FFF) :
    (read2007 rd palRd s).2 =
      (palRd (Nes.Bus.paletteIndex (s.v &&& 0x3FFF)).val.toUInt8 &&& 0x3F) |||
        (s.ioLatch &&& 0xC0) ∧
    (read2007 rd palRd s).1.readBuffer = rd ((s.v &&& 0x3FFF) - 0x1000) := by
  have h' : ¬ (s.v &&& 0x3FFF < 0x3F00) := by
    intro hl; exact absurd (UInt16.lt_of_lt_of_le hl h) (UInt16.lt_irrefl _)
  simp [read2007, vramAddr, incAddr, h']

theorem T_PPU_7_increment (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State) :
    (read2007 rd palRd s).1.v =
      (s.v + (if s.ctrl &&& 0x04 != 0 then 32 else 1)) &&& 0x7FFF ∧
    (read2007 rd palRd s).1.ctrl = s.ctrl := by
  by_cases h : s.vramAddr < 0x3F00 <;> simp [read2007, h, incAddr, vramInc32]

theorem T_PPU_7_two_reads (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8) (s : State)
    (h₁ : s.v &&& 0x3FFF < 0x3F00) (h₂ : s.incAddr.v &&& 0x3FFF < 0x3F00) :
    let (s₁, r₁) := read2007 rd palRd s
    let (_, r₂) := read2007 rd palRd s₁
    [r₁, r₂] = [s.readBuffer, rd (s.v &&& 0x3FFF)] := by
  have e₁ : read2007 rd palRd s =
      ({ s with readBuffer := rd (s.v &&& 0x3FFF), ioLatch := s.readBuffer }.incAddr,
        s.readBuffer) := by
    simp [read2007, vramAddr, h₁]
  rw [e₁]
  show [s.readBuffer, (read2007 rd palRd _).2] = _
  have h₂' : ({ s with readBuffer := rd (s.v &&& 0x3FFF), ioLatch := s.readBuffer }.incAddr
      ).vramAddr < 0x3F00 := h₂
  simp only [read2007, h₂', ite_true]
  rfl

theorem T_PPU_7_settled (now : UInt64) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8)
    (s : State) (h : ¬(now = s.lastRead2007 + 1 ∧ s.vramAddr < 0x3F00)) :
    read2007At now rd palRd s =
      ({ (read2007 rd palRd s).1 with prevBuffer := s.readBuffer, lastRead2007 := now },
        (read2007 rd palRd s).2) := by
  unfold read2007At
  have : (now == s.lastRead2007 + 1 && decide (s.vramAddr < 0x3F00)) = false := by
    simpa [Bool.and_eq_true, beq_iff_eq] using h
  simp only [this]
  rfl

theorem T_PPU_7_back_to_back (now : UInt64) (rd : UInt16 → UInt8) (palRd : UInt8 → UInt8)
    (s : State) (h₁ : now = s.lastRead2007 + 1) (h₂ : s.vramAddr < 0x3F00) :
    (read2007At now rd palRd s).2 = s.prevBuffer ∧
    (read2007At now rd palRd s).1.readBuffer = (read2007 rd palRd s).1.readBuffer ∧
    (read2007At now rd palRd s).1.v = (read2007 rd palRd s).1.v := by
  unfold read2007At
  simp [h₁, h₂]

end Nes.Ppu.Proofs
