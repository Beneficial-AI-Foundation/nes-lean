import Nes.Cart.Mapper

/-!
# T-CART-2 — bank offsets are in range (NROM, CNROM, MMC1, UxROM, AxROM)

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
* `Cnrom.prgOffset_lt` / `Cnrom.chrOffset_lt`: CNROM offsets are in range (by construction).
* `Cnrom.regWrite_bank_le`: a latched bank never exceeds `bankMask rom`;
  `Cnrom.regWrite_bank_lt`: with `chrLen = 8 KiB · 2^k` (`k ≤ 8`) the latched bank is
  `< 2^k`, i.e. a valid bank index.
* `Cnrom.chrOffset_banked`: with `chrLen = 8 KiB · 2^k` and a valid bank, PPU `a < $2000`
  reads CHR byte `bank · $2000 + a` (no wrap-around).
* `Mmc1.prgOffset_lt` / `chrOffset_lt`, `Uxrom.*`, `Axrom.*`: offsets in range (by
  construction).
* `Mmc1.prgOffset_mode3_fixed`: in PRG mode 3 with `n ≤ 16` 16 KiB banks, CPU `$C000+i` reads
  the last bank (`(n-1)·$4000 + i`); `Mmc1.prgOffset_mode3_switch`: `$8000+i` reads bank
  `prg mod 16` when it exists.
* `Uxrom.prgOffset_fixed`: with `n` 16 KiB banks, CPU `$C000+i` reads `(n-1)·$4000 + i`;
  `Uxrom.prgOffset_switch`: `$8000+i` reads `bank·$4000 + i` for a valid bank.
* `Axrom.prgOffset_banked`: with `n` 32 KiB banks and a valid bank `reg mod 8`, CPU `$8000+i`
  reads `(reg mod 8)·$8000 + i`.
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

namespace Cnrom

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

theorem regWrite_bank_le (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (ha : 0x8000 ≤ a) :
    (regWrite rom s a v).bank ≤ bankMask rom := by
  simp only [regWrite, ha, ↓reduceIte]
  show (_ &&& bankMask rom).toNat ≤ (bankMask rom).toNat
  rw [UInt8.toNat_and]
  exact Nat.and_le_right

theorem regWrite_bank_lt (rom : Rom) (s : State) (a : UInt16) (v : UInt8) (ha : 0x8000 ≤ a)
    (k : Nat) (hk : k ≤ 8) (h : rom.chrLen = 8192 * 2 ^ k) :
    (regWrite rom s a v).bank.toNat < 2 ^ k := by
  simp only [regWrite, ha, ↓reduceIte, bankMask, h]
  rw [UInt8.toNat_and, Nat.mul_div_cancel_left _ (by decide), Nat.toUInt8, UInt8.toNat_ofNat']
  have hp : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hk
  have hp0 : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ hp0

theorem chrOffset_banked (rom : Rom) (s : State) (a : UInt16) (k : Nat)
    (h : rom.chrLen = 8192 * 2 ^ k) (hb : s.bank.toNat < 2 ^ k) (ha : a < 0x2000) :
    (chrOffset rom s a).val = s.bank.toNat * 8192 + a.toNat := by
  have : a.toNat < 8192 := ha
  have hlt : s.bank.toNat * 8192 + a.toNat < 8192 * 2 ^ k := by
    have : (s.bank.toNat + 1) * 8192 ≤ 2 ^ k * 8192 := Nat.mul_le_mul_right _ hb
    rw [Nat.mul_comm 8192]; rw [Nat.add_mul] at this; omega
  simp only [chrOffset, h]
  rw [show (a &&& 0x1FFF).toNat = a.toNat % 8192 from by
    rw [UInt16.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod a.toNat 13]
  rw [Nat.mod_eq_of_lt this]
  exact Nat.mod_eq_of_lt hlt

end Cnrom

private theorem toNat_and_3fff (a : UInt16) : (a &&& 0x3FFF).toNat = a.toNat % 16384 := by
  rw [UInt16.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 14

private theorem toNat_and_7fff' (a : UInt16) : (a &&& 0x7FFF).toNat = a.toNat % 32768 := by
  rw [UInt16.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 15

namespace Mmc1

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

theorem prgOffset_mode3_fixed (rom : Rom) (s : State) (a : UInt16) (n : Nat)
    (h : rom.prg.size = 16384 * n) (hn : 1 ≤ n) (hn16 : n ≤ 16) (hm : prgMode s = 3)
    (ha : 0xC000 ≤ a) : (prgOffset rom s a).val = (n - 1) * 16384 + (a.toNat - 0xC000) := by
  have hu := a.toNat_lt
  have : 49152 ≤ a.toNat := ha
  have hb : banks rom = n := by simp [banks, h]
  have hout : ¬ (rom.prg.size > 0x40000) := by omega
  simp only [prgOffset, hm, toNat_and_3fff, hb, h, ha, ↓reduceIte]
  simp only [show ¬ ((3 : UInt8) < 2) from by decide, show ((3 : UInt8) == 2) = false from by
    decide, ↓reduceIte, Bool.false_eq_true]
  simp only [show decide (16384 * n > 262144) = false from by simp; omega, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  split
  · have : n = 16 := by omega
    subst this; omega
  · have : (n - 1) * 16384 + a.toNat % 16384 < 16384 * n := by
      have : a.toNat % 16384 < 16384 := Nat.mod_lt _ (by decide)
      cases n with
      | zero => omega
      | succ k => simp only [Nat.add_sub_cancel]; rw [Nat.mul_succ, Nat.mul_comm]; omega
    rw [Nat.mod_eq_of_lt this]; omega

theorem prgOffset_mode3_switch (rom : Rom) (s : State) (a : UInt16) (n : Nat)
    (h : rom.prg.size = 16384 * n) (hn16 : n ≤ 16) (hm : prgMode s = 3)
    (hb : (s.prg &&& 0x0F).toNat < n) (ha : 0x8000 ≤ a) (ha' : a < 0xC000) :
    (prgOffset rom s a).val = (s.prg &&& 0x0F).toNat * 16384 + (a.toNat - 0x8000) := by
  have : 32768 ≤ a.toNat := ha
  have : a.toNat < 49152 := ha'
  have hc : ¬ (0xC000 ≤ a) := fun h => absurd ha' (UInt16.not_lt.mpr h)
  simp only [prgOffset, hm, toNat_and_3fff, h, hc, ↓reduceIte]
  simp only [show ¬ ((3 : UInt8) < 2) from by decide, show ((3 : UInt8) == 2) = false from by
    decide, ↓reduceIte, Bool.false_eq_true]
  simp only [show decide (16384 * n > 262144) = false from by simp; omega, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  have hlt : (s.prg &&& 0x0F).toNat * 16384 + a.toNat % 16384 < 16384 * n := by
    have : a.toNat % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have : ((s.prg &&& 0x0F).toNat + 1) * 16384 ≤ n * 16384 := Nat.mul_le_mul_right _ hb
    rw [Nat.add_mul] at this; omega
  rw [Nat.mod_eq_of_lt hlt]; omega

end Mmc1

namespace Uxrom

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

theorem prgOffset_fixed (rom : Rom) (s : State) (a : UInt16) (n : Nat)
    (h : rom.prg.size = 16384 * n) (hn : 1 ≤ n) (ha : 0xC000 ≤ a) :
    (prgOffset rom s a).val = (n - 1) * 16384 + (a.toNat - 0xC000) := by
  have hu := a.toNat_lt
  have : 49152 ≤ a.toNat := ha
  have hc : ¬ (a < 0xC000) := UInt16.not_lt.mpr ha
  have hb : banks rom = n := by simp [banks, h]
  simp only [prgOffset, hc, ↓reduceIte, hb, toNat_and_3fff, h]
  have : (n - 1) * 16384 + a.toNat % 16384 < 16384 * n := by
    have : a.toNat % 16384 < 16384 := Nat.mod_lt _ (by decide)
    cases n with
    | zero => omega
    | succ k => simp only [Nat.add_sub_cancel]; rw [Nat.mul_succ, Nat.mul_comm]; omega
  rw [Nat.mod_eq_of_lt this]; omega

theorem prgOffset_switch (rom : Rom) (s : State) (a : UInt16) (n : Nat)
    (h : rom.prg.size = 16384 * n) (hb : s.bank.toNat < n) (ha : 0x8000 ≤ a)
    (ha' : a < 0xC000) :
    (prgOffset rom s a).val = s.bank.toNat * 16384 + (a.toNat - 0x8000) := by
  have : 32768 ≤ a.toNat := ha
  have : a.toNat < 49152 := ha'
  simp only [prgOffset, ha', ↓reduceIte, toNat_and_3fff, h]
  have hlt : s.bank.toNat * 16384 + a.toNat % 16384 < 16384 * n := by
    have : a.toNat % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have : (s.bank.toNat + 1) * 16384 ≤ n * 16384 := Nat.mul_le_mul_right _ hb
    rw [Nat.add_mul] at this; omega
  rw [Nat.mod_eq_of_lt hlt]; omega

end Uxrom

namespace Axrom

theorem prgOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (prgOffset rom s a).val < rom.prg.size := Fin.isLt _

theorem chrOffset_lt (rom : Rom) (s : State) (a : UInt16) :
    (chrOffset rom s a).val < rom.chrLen := Fin.isLt _

theorem prgOffset_banked (rom : Rom) (s : State) (a : UInt16) (n : Nat)
    (h : rom.prg.size = 32768 * n) (hb : (s.reg &&& 7).toNat < n) (ha : 0x8000 ≤ a) :
    (prgOffset rom s a).val = (s.reg &&& 7).toNat * 32768 + (a.toNat - 0x8000) := by
  have hu := a.toNat_lt
  have : 32768 ≤ a.toNat := ha
  simp only [prgOffset, toNat_and_7fff', h]
  have hlt : (s.reg &&& 7).toNat * 32768 + a.toNat % 32768 < 32768 * n := by
    have : a.toNat % 32768 < 32768 := Nat.mod_lt _ (by decide)
    have : ((s.reg &&& 7).toNat + 1) * 32768 ≤ n * 32768 := Nat.mul_le_mul_right _ hb
    rw [Nat.add_mul] at this; omega
  rw [Nat.mod_eq_of_lt hlt]; omega

end Axrom

end Nes.Cart
