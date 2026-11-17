/-!
# `Nes.Frontend.Palette` — 2C02 NTSC palette (frontend only)

PLAN §5.3: the PPU outputs 6-bit palette indices plus emphasis bits; the mapping to RGB lives only
here, in the frontend.

**Source / licence.** The table is *generated*, not copied from any third-party palette file: it
is the output of the NTSC-signal palette algorithm described on the NESdev wiki ("NTSC video",
palette generation section). For each index the 2C02 composite square wave is synthesised over
12 colour phases from the documented normalised voltage levels (low 0.228 0.312 0.552 0.880,
high 0.616 0.840 1.100 1.100; black 0.312, white 1.100; hues `$x0` = high level only,
`$xD..$xF` = low level only, `$xE/$xF` forced to level 1 = black), averaged into YIQ
(sample angle `π(phase + 3.1)/6`, saturation ×1.5), and converted with the FCC YIQ→RGB matrix,
clamped to 0–255, no gamma. Generated once offline; the numbers are measurements of a physical
signal model and carry no third-party licence (this file is under the project's licence).

**Emphasis.** `rgbOf` approximates the PPUMASK emphasis bits (bit 0 red, bit 1 green, bit 2 blue,
i.e. mask bits 5–7 shifted down — see `Nes.Ppu.Types`) by scaling every *non*-emphasised channel
by the documented attenuation factor 0.746 (integer `c * 746 / 1000`) when any emphasis bit is
set. With all three bits set, all channels are attenuated. (Real hardware attenuates the signal
during the emphasised phases; the per-channel scale is the standard emulator approximation.)
Golden hashes are taken over palette *indices* (`Nes.Frontend.frameHash`), so palette tuning never
invalidates them.
-/

namespace Nes.Frontend

/-- Total byte read: `0` past the end (no panicking accessor under `Nes/`). -/
@[inline] def byteAt (a : ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0


/-- 64 × (R, G, B), indexed by `3 * idx`. -/
def ntscPalette : ByteArray := ByteArray.mk #[
    98, 98, 98, 18, 22, 155, 54, 4, 155, 85, 0, 123,  -- $00
    102, 0, 68, 102, 8, 4, 84, 27, 0, 53, 49, 0,  -- $04
    17, 67, 0, 0, 77, 0, 0, 75, 4, 0, 63, 68,  -- $08
    0, 44, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0,  -- $0C
    171, 171, 171, 62, 67, 248, 110, 43, 248, 152, 29, 204,  -- $10
    176, 31, 129, 176, 48, 42, 151, 74, 0, 109, 104, 0,  -- $14
    61, 128, 0, 19, 141, 0, 0, 140, 42, 0, 123, 129,  -- $18
    20, 97, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0,  -- $1C
    255, 255, 255, 142, 147, 255, 192, 122, 255, 235, 108, 255,  -- $20
    255, 110, 212, 255, 127, 121, 235, 155, 43, 191, 185, 0,  -- $24
    141, 211, 0, 97, 224, 43, 72, 223, 121, 73, 206, 211,  -- $28
    98, 178, 255, 78, 78, 78, 0, 0, 0, 0, 0, 0,  -- $2C
    255, 255, 255, 210, 212, 255, 230, 202, 255, 247, 196, 255,  -- $30
    255, 197, 238, 255, 204, 201, 247, 215, 170, 229, 227, 152,  -- $34
    209, 237, 152, 192, 243, 170, 182, 242, 201, 182, 235, 237,  -- $38
    192, 224, 255, 184, 184, 184, 0, 0, 0, 0, 0, 0  -- $3C
  ]

/-- Attenuate a channel by the 2C02 emphasis factor ≈ 0.746. -/
@[inline] def attenuate (c : UInt8) : UInt8 :=
  (c.toNat * 746 / 1000).toUInt8

/-- RGB of palette index `idx` (low 6 bits used) under emphasis bits `emphasis`
(bit 0 red, bit 1 green, bit 2 blue; higher bits ignored). -/
def rgbOf (idx : UInt8) (emphasis : UInt8) : UInt8 × UInt8 × UInt8 :=
  let i := (idx &&& 0x3F).toNat * 3
  let r := byteAt ntscPalette i
  let g := byteAt ntscPalette (i + 1)
  let b := byteAt ntscPalette (i + 2)
  let e := emphasis &&& 7
  if e == 0 then (r, g, b) else if e == 7 then (attenuate r, attenuate g, attenuate b) else
    (if e &&& 1 == 0 then attenuate r else r,
     if e &&& 2 == 0 then attenuate g else g,
     if e &&& 4 == 0 then attenuate b else b)

end Nes.Frontend
