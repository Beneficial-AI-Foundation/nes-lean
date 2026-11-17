import Nes.System.SaveState

/-!
# T-REF-3 — save-state round trip (PLAN §6.1)

* `T_REF_3_roundtrip`: `deserialize n.cart.rom (serialize n) = some n` — every field of the
  machine (CPU core, PPU, mapper registers, board/console RAMs, controllers, open bus, clock,
  frame counter, DMA unit, RESET line) survives the round trip; the cartridge image is supplied
  on load.
* `T_REF_3_injective`: on machines with the same cartridge image, `serialize` is injective.

The proof is the composition of the per-type codec laws (`SaveState.Codec.dec_enc`, proved once
per field type and per structure in `Nes.System.SaveState`), plus the header check.
-/

namespace Nes.System.Proofs.SaveState

open Nes.System Nes.System.SaveState

theorem decodeList_encodeList (n : Nes) : decodeList n.cart.rom (encodeList n) = some n := by
  unfold decodeList encodeList
  simp only [List.take_left', List.drop_left', ↓reduceIte]
  rw [show enc (toImage n) = enc (toImage n) ++ [] from (List.append_nil _).symm, dec_enc]
  rfl

/-- T-REF-3: the save-state round trip. -/
theorem T_REF_3_roundtrip (n : Nes) : Nes.deserialize n.cart.rom n.serialize = some n := by
  unfold Nes.deserialize Nes.serialize
  simpa using decodeList_encodeList n

/-- T-REF-3: `serialize` is injective (machines with the same cartridge image). -/
theorem T_REF_3_injective {a b : Nes} (hrom : a.cart.rom = b.cart.rom)
    (h : a.serialize = b.serialize) : a = b := by
  have ha := T_REF_3_roundtrip a
  rw [h, hrom, T_REF_3_roundtrip b] at ha
  exact (Option.some.inj ha).symm

end Nes.System.Proofs.SaveState
