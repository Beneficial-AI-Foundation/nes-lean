import Nes

/-!
# `Play.Core` — the emulator session the live players drive

Pure functions exported to C (`Play/app.c`), shared by the native `nes-play` window and the
browser build. C holds the only reference to a `Session` and passes it back owned, so each
`frame` updates the emulator state in place.
-/

open Nes.Frontend

namespace Play

structure Session where
  nes : Nes.System.Nes
  ds : Downsampler
  /-- The last frame as 256×240 RGB24. -/
  rgb : ByteArray

/-- Power on a cartridge image (iNES). `.error` carries a message for the user. -/
@[export nes_core_load]
def load (rom : ByteArray) : Except String Session := do
  let cart ← Nes.Cart.Cart.load rom
  let nes := Nes.System.Nes.powerOn cart
  return { nes, ds := Downsampler.init (highPass := true), rgb := toRgb nes.ppu.frame 0 }

/-- Run one frame. `keys` bits 0–7 are controller 1 (A B Select Start Up Down Left Right);
bit 9 presses the console's reset button first. The frame's audio (44.1 kHz mono s16le)
is left in `pcm`. -/
@[export nes_core_frame]
def frame (s : Session) (keys : UInt32) : Session :=
  let nes := if keys &&& 0x200 != 0 then s.nes.reset else s.nes
  let nes := { nes with pads := nes.pads.setButtons (keys &&& 0xFF).toUInt8 0 }
  let (nes, ds) := nes.runFrameAudio { s.ds with out := ByteArray.empty }
  { nes, ds, rgb := toRgb nes.ppu.frame nes.ppu.emphasis }

@[export nes_core_rgb] def rgb (s : Session) : ByteArray := s.rgb
@[export nes_core_pcm] def pcm (s : Session) : ByteArray := s.ds.out

end Play
