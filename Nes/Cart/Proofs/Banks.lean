import Nes.Cart.Mapper

/-!
# T-CART-2 — bank offsets are in range (NROM)

Range safety is by construction: every mapper's `prgOffset` / `chrOffset` returns a
`Fin rom.prg.size` / `Fin rom.chrLen`, so ROM reads cannot go out of bounds. This file
states that explicitly for every `MapperState` constructor and pins down NROM's layout.

## Spec

* `MapperState.prgOffset_lt` / `chrOffset_lt`: for every mapper and every register state the
  computed PRG offset is `< rom.prg.size` and the CHR offset is `< rom.chrLen` (CHR-ROM size,
  or 8 KiB for CHR-RAM).
* `Nrom.prgOffset_lt` / `Nrom.chrOffset_lt`: the same for NROM directly.
* `Nrom.prgOffset_32k`: with 32 KiB of PRG, CPU `$8000+i` reads PRG byte `i`.
* `Nrom.prgOffset_16k`: with 16 KiB of PRG, CPU `a` in `$8000–$FFFF` reads byte
  `(a - $8000) mod $4000`; `Nrom.prgOffset_16k_mirror`: `$C000+i` reads the same byte as
  `$8000+i`.
* `Nrom.chrOffset_8k`: with an 8 KiB CHR space, PPU `a < $2000` reads CHR byte `a`.
-/

namespace Nes.Cart

theorem MapperState.prgOffset_lt (rom : Rom) (m : MapperState) (a : UInt16) :
    (m.prgOffset rom a).val < rom.prg.size := by
  cases m <;> exact Fin.isLt _

theorem MapperState.chrOffset_lt (rom : Rom) (m : MapperState) (a : UInt16) :
    (m.chrOffset rom a).val < rom.chrLen := by
  cases m <;> exact Fin.isLt _

namespace Nrom

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

private theorem toNat_and_7fff (a : UInt16) : (a &&& 0x7FFF).toNat = a.toNat % 32768 := by
  rw [UInt16.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 15

private theorem toNat_and_1fff (a : UInt16) : (a &&& 0x1FFF).toNat = a.toNat % 8192 := by
  rw [UInt16.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 13

theorem prgOffset_32k (rom : Rom) (s : State) (a : UInt16) (h : rom.prg.size = 32768)
    (ha : 0x8000 ≤ a) : (prgOffset rom s a).val = a.toNat - 0x8000 := by
  have hu := a.toNat_lt
  have : 32768 ≤ a.toNat := ha
  simp only [prgOffset, toNat_and_7fff, h]
  omega

theorem prgOffset_16k (rom : Rom) (s : State) (a : UInt16) (h : rom.prg.size = 16384)
    (ha : 0x8000 ≤ a) : (prgOffset rom s a).val = (a.toNat - 0x8000) % 16384 := by
  have hu := a.toNat_lt
  have : 32768 ≤ a.toNat := ha
  simp only [prgOffset, toNat_and_7fff, h]
  omega

theorem prgOffset_16k_mirror (rom : Rom) (s : State) (a : UInt16) (h : rom.prg.size = 16384)
    (ha : 0x8000 ≤ a) (hb : a < 0xC000) : prgOffset rom s (a + 0x4000) = prgOffset rom s a := by
  have : 32768 ≤ a.toNat := ha
  have : a.toNat < 49152 := hb
  have hadd : (a + 0x4000).toNat = a.toNat + 16384 := by
    rw [UInt16.toNat_add]; simp; omega
  apply Fin.ext
  simp only [prgOffset, toNat_and_7fff, h, hadd]
  omega

theorem chrOffset_8k (rom : Rom) (s : State) (a : UInt16) (h : rom.chrLen = 8192)
    (ha : a < 0x2000) : (chrOffset rom s a).val = a.toNat := by
  have : a.toNat < 8192 := ha
  simp only [chrOffset, toNat_and_1fff, h]
  omega

end Nrom

end Nes.Cart
