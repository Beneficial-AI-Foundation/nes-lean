/-!
# Nametable mirroring

Shared between the cartridge (the iNES header and mappers choose it) and the PPU bus (it
maps `$2000–$2FFF` onto the 2 KiB of CIRAM).
-/

namespace Nes

/-- How the four logical nametables map onto CIRAM. `fourScreen` uses cartridge VRAM. -/
inductive Mirroring where
  | horizontal | vertical | singleLow | singleHigh | fourScreen
  deriving DecidableEq, Repr, Inhabited

end Nes
