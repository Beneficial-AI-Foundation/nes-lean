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

end Nes.Ppu.Proofs
