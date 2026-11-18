import Nes.Apu.Dmc

/-!
# `Nes.Apu.Proofs.Dmc` — T-APU-3 (DMC addressing and DMA)

## Spec

* `T_APU_3_wrap`: a fetch at `$FFFF` that does not end a looping sample moves the address to
  `$8000` (NESdev "APU DMC", memory reader).
* `T_APU_3_length`: after `setEnabled true` on a finished channel with loop clear, the
  bytes-remaining counter is non-zero after `k < L·16 + 1` fetches and `0` after exactly
  `L·16 + 1` fetches.
* `T_APU_3_loop`: with loop set, the fetch that empties the counter restarts address and
  length from `$4012`/`$4013`.
* `T_APU_3_irq`: the fetch ending a non-looping sample sets the IRQ flag iff IRQ is enabled
  (starting from a clear flag).
* `T_APU_3_stall`: `dmaStall` is 3/4 on the halt-on-get/put cases, 2 during OAM DMA
  (NESdev "DMA").
* `dmc_output_bounds`: `output ∈ [0, 127]`; `level ≤ 127` is preserved by `tick`, `write`,
  `setEnabled`, `dmaComplete`.
-/

namespace Nes.Apu.Proofs

open Nes.Apu Nes.Apu.Dmc

/-- `n` fetches each delivering byte `b`. -/
def fetchN (b : UInt8) : Nat → Dmc → Dmc
  | 0, d => d
  | n + 1, d => fetchN b n (dmaComplete d b)

theorem u16_ne_zero {r : UInt16} (hr : r ≠ 0) : 1 ≤ r.toNat := by
  have : r.toNat ≠ 0 := fun h0 => hr (UInt16.toNat_inj.mp (by simpa using h0))
  omega

theorem u16_sub_one {r : UInt16} (hr : r ≠ 0) : (r - 1).toNat = r.toNat - 1 := by
  have := u16_ne_zero hr
  rw [UInt16.toNat_sub_of_le]; · rfl
  simpa [UInt16.le_iff_toNat_le] using this

theorem u16_sub_one_eq_zero {r : UInt16} (hr : r ≠ 0) (h : r - 1 = 0) : r = 1 := by
  have := u16_sub_one hr; rw [h] at this
  have := u16_ne_zero hr
  apply UInt16.toNat_inj.mp; simp at *; omega

theorem T_APU_3_wrap (d : Dmc) (b : UInt8) (ha : d.curAddr = 0xFFFF)
    (hr : d.bytesRemaining ≠ 0) (hl : d.loop = false ∨ d.bytesRemaining ≠ 1) :
    (dmaComplete d b).curAddr = 0x8000 := by
  have h1 : (d.bytesRemaining == 0) = false := by simpa using hr
  simp only [dmaComplete, h1, nextAddr, ha]
  rcases hl with hl | hl
  · simp [hl]
  · have : (d.bytesRemaining - 1 == 0) = false := by
      simpa using fun h => hl (u16_sub_one_eq_zero hr h)
    simp [this]

/-- One non-looping fetch decrements a non-zero counter and keeps `loop`. -/
theorem fetch_dec (d : Dmc) (b : UInt8) (hl : d.loop = false) (hr : d.bytesRemaining ≠ 0) :
    (dmaComplete d b).bytesRemaining.toNat = d.bytesRemaining.toNat - 1 ∧
    (dmaComplete d b).loop = false := by
  have h1 : (d.bytesRemaining == 0) = false := by simpa using hr
  simp only [dmaComplete, h1, hl]
  simp [u16_sub_one hr]

theorem fetchN_count (b : UInt8) :
    ∀ (k : Nat) (d : Dmc), d.loop = false → k ≤ d.bytesRemaining.toNat →
      (fetchN b k d).bytesRemaining.toNat = d.bytesRemaining.toNat - k
  | 0, d, _, _ => by simp [fetchN]
  | k + 1, d, hl, hk => by
    have hr : d.bytesRemaining ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    obtain ⟨h1, h2⟩ := fetch_dec d b hl hr
    simp only [fetchN]
    rw [fetchN_count b k _ h2 (by omega), h1]; omega

theorem startLen_toNat (d : Dmc) : d.startLen.toNat = d.lenReg.toNat * 16 + 1 := by
  have := d.lenReg.toNat_lt
  simp [startLen, UInt16.toNat_add, UInt16.toNat_mul]
  omega

theorem T_APU_3_length (d : Dmc) (b : UInt8) (hl : d.loop = false)
    (h0 : d.bytesRemaining = 0) (k : Nat) :
    let s := setEnabled d true
    (k < d.lenReg.toNat * 16 + 1 → (fetchN b k s).bytesRemaining ≠ 0) ∧
    (fetchN b (d.lenReg.toNat * 16 + 1) s).bytesRemaining = 0 := by
  intro s
  have hs : s.bytesRemaining = d.startLen ∧ s.loop = false := by
    simp [s, setEnabled, h0, hl]
  have hlen := startLen_toNat d
  constructor
  · intro hk h
    have := fetchN_count b k s hs.2 (by rw [hs.1]; omega)
    rw [h, hs.1] at this; simp at this; omega
  · have := fetchN_count b (d.lenReg.toNat * 16 + 1) s hs.2 (by rw [hs.1]; omega)
    rw [hs.1] at this
    apply UInt16.toNat_inj.mp; simp; omega

theorem T_APU_3_loop (d : Dmc) (b : UInt8) (hl : d.loop = true) (h1 : d.bytesRemaining = 1) :
    (dmaComplete d b).curAddr = d.startAddr ∧
    (dmaComplete d b).bytesRemaining = d.startLen ∧
    (dmaComplete d b).irqFlag = d.irqFlag := by
  simp [dmaComplete, h1, hl]

theorem T_APU_3_irq (d : Dmc) (b : UInt8) (hl : d.loop = false) (h1 : d.bytesRemaining = 1)
    (hi : d.irqFlag = false) :
    (dmaComplete d b).irqFlag = d.irqEnable ∧ (dmaComplete d b).bytesRemaining = 0 := by
  simp [dmaComplete, h1, hl, hi]

theorem T_APU_3_stall :
    dmaStall true false false = 3 ∧ dmaStall false false false = 4 ∧
    dmaStall false true false = 3 ∧ dmaStall true true false = 4 ∧
    (∀ g w, dmaStall g w true = 2) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro g w; simp [dmaStall]

theorem dmc_output_bounds (d : Dmc) : (output d).toNat ≤ 127 := by
  simp only [output, UInt8.toNat_and]
  exact Nat.and_le_right

theorem stepLevel_le (s : Bool) (sh l : UInt8) (h : l.toNat ≤ 127) :
    (stepLevel s sh l).toNat ≤ 127 := by
  unfold stepLevel
  split
  · exact h
  · split
    · split
      · rename_i h2; simp [UInt8.le_iff_toNat_le] at h2
        simp [UInt8.toNat_add]; omega
      · exact h
    · split
      · rename_i h2; simp [UInt8.le_iff_toNat_le] at h2
        simp [UInt8.toNat_sub_of_le, UInt8.le_iff_toNat_le, h2]; omega
      · exact h

theorem tick_level (d : Dmc) (h : d.level.toNat ≤ 127) : (tick d).level.toNat ≤ 127 := by
  unfold tick; split
  · exact h
  · exact stepLevel_le _ _ _ h

theorem write_level (d : Dmc) (r v : UInt8) (h : d.level.toNat ≤ 127) :
    (write d r v).level.toNat ≤ 127 := by
  unfold write; split
  · exact h
  · simp only [UInt8.toNat_and]; exact Nat.and_le_right
  · exact h
  · exact h

theorem setEnabled_level (d : Dmc) (e : Bool) : (setEnabled d e).level = d.level := by
  unfold setEnabled; split
  · rfl
  · split <;> rfl

theorem dmaComplete_level (d : Dmc) (b : UInt8) : (dmaComplete d b).level = d.level := by
  unfold dmaComplete; split <;> rfl

end Nes.Apu.Proofs
