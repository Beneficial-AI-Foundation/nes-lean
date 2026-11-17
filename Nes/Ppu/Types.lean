import Nes.Ppu.Loopy

/-!
# `Nes.Ppu.Types` — 2C02 PPU state

Representation (hot path, PLAN §4 / §10 decision 6): every register and counter is a fixed-width
machine integer (`UInt8`/`UInt16`, unboxed scalars in compiled code) rather than `BitVec n` /
`Fin n` (which are `Nat`-backed and boxed at run time):

* `v t : UInt16` (15 bits used; spec view `Loopy.toFields`, see `Nes.Ppu.Loopy`), `x : UInt8`
  (3 bits used), `dot : UInt16` (0–340), `scanline : UInt16` (0–261, 261 = pre-render).
* Byte memories (`oam` 256 B, `secOam` 32 B, the eight sprite-slot arrays and the frame
  buffer 256×240 B) are `ByteArray`s: unboxed bytes updated in place when unshared, whereas a
  `Vector UInt8` stores boxed scalars (8 B per byte, M1 benchmark). Their sizes are not in the
  type; `State.init` allocates them at the right size and every accessor here is bounds-checked
  (`getByte` returns 0 / `ByteArray.set!` is a no-op out of range), so no access can fail.
* `frame` holds one 6-bit palette index per pixel (row-major, `y * 256 + x`); colour emphasis is
  the `emphasis` field (mask bits 5–7), latched per frame. The palette→RGB mapping lives only in
  the frontend.

Which item fills which fields: registers (`Nes.Ppu.Registers`): `ctrl mask status oamAddr v t
x w ioLatch oam nmiOut`; the `$2007` read buffer: `readBuffer`; timing: `dot scanline frameOdd
status nmiOut suppressVbl frameReady emphasis`; background pipeline: `bg*`; sprite pipeline:
`secOam eval* spr*`; mapper hook: `a12`.

## Spec

* `State` is the PPU state listed above; `State.init` is the power-up state: all registers 0,
  `w = false`, OAM / secondary OAM / sprite slots / frame zero-filled at sizes 256, 32, 8, 61440,
  `dot = 0`, `scanline = 0`, even frame, NMI line low.
* `getByte a i` is byte `i` of `a`, or 0 if `i` is out of range.
* `ctrl`/`mask`/`status` bit accessors (`State.nmiEnable`, `State.vramInc32`, `State.vblank`, …)
  test the documented bit of the raw register byte.
-/

namespace Nes.Ppu

/-- Frame width and height in pixels. -/
def frameWidth : Nat := 256
def frameHeight : Nat := 240

/-- Bounds-checked byte read; 0 when out of range. -/
@[inline] def getByte (a : ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0

/-- A zero-filled byte array of length `n`. -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- 2C02 PPU state. -/
structure State where
  /-- `$2000` PPUCTRL. -/
  ctrl : UInt8
  /-- `$2001` PPUMASK. -/
  mask : UInt8
  /-- `$2002` PPUSTATUS: only bits 5 (sprite overflow), 6 (sprite-0 hit), 7 (vblank) are kept. -/
  status : UInt8
  /-- `$2003` OAMADDR. -/
  oamAddr : UInt8
  /-- Current VRAM address (loopy `v`, 15 bits). -/
  v : UInt16
  /-- Temporary VRAM address (loopy `t`, 15 bits). -/
  t : UInt16
  /-- Fine X scroll (3 bits). -/
  x : UInt8
  /-- First/second write toggle shared by `$2005`/`$2006`. -/
  w : Bool
  /-- `$2007` read buffer. -/
  readBuffer : UInt8
  /-- PPU I/O data-bus latch: returned for write-only registers and the low bits of `$2002`. -/
  ioLatch : UInt8
  /-- Primary OAM, 256 bytes. -/
  oam : ByteArray
  /-- Secondary OAM, 32 bytes. -/
  secOam : ByteArray
  /-- Background pattern shifters (high byte = current tile). -/
  bgPatLo : UInt16
  bgPatHi : UInt16
  /-- Background attribute shifters. -/
  bgAttrLo : UInt16
  bgAttrHi : UInt16
  /-- Background fetch latches for the next tile. -/
  bgNextTile : UInt8
  bgNextAttr : UInt8
  bgNextLo : UInt8
  bgNextHi : UInt8
  /-- Sprite evaluation state: OAM index `n`, byte `m`, secondary-OAM write index, read latch. -/
  evalN : UInt8
  evalM : UInt8
  evalSec : UInt8
  evalLatch : UInt8
  /-- Number of sprites selected for the line being drawn (0–8). -/
  sprCount : UInt8
  /-- Per-slot (8) sprite pattern shifters, attribute latches and X counters. -/
  sprPatLo : ByteArray
  sprPatHi : ByteArray
  sprAttr : ByteArray
  sprX : ByteArray
  /-- Sprite 0 is in the secondary OAM being evaluated / being drawn. -/
  spr0Next : Bool
  spr0Line : Bool
  /-- Dot within the scanline, 0–340. -/
  dot : UInt16
  /-- Scanline, 0–261 (240 post-render, 241–260 vblank, 261 pre-render). -/
  scanline : UInt16
  /-- Odd frame (the pre-render line is one dot shorter when rendering). -/
  frameOdd : Bool
  /-- NMI output line (`ctrl` bit 7 ∧ vblank), sampled by the CPU. -/
  nmiOut : Bool
  /-- A `$2002` read landed on the dot vblank is set: suppress the flag / NMI this frame. -/
  suppressVbl : Bool
  /-- PPU address bus A12 as of the last dot (mapper hook, MMC3 IRQ counter). -/
  a12 : Bool
  /-- 256×240 palette indices (6 bits each), row-major. -/
  frame : ByteArray
  /-- Colour-emphasis bits (`mask` bits 5–7, in bits 0–2) for `frame`. -/
  emphasis : UInt8
  /-- A complete frame is in `frame` (set at vblank start, cleared by the frontend). -/
  frameReady : Bool

namespace State

/-- Power-up state. -/
def init : State :=
  { ctrl := 0, mask := 0, status := 0, oamAddr := 0, v := 0, t := 0, x := 0, w := false,
    readBuffer := 0, ioLatch := 0, oam := zeroBytes 256, secOam := zeroBytes 32,
    bgPatLo := 0, bgPatHi := 0, bgAttrLo := 0, bgAttrHi := 0,
    bgNextTile := 0, bgNextAttr := 0, bgNextLo := 0, bgNextHi := 0,
    evalN := 0, evalM := 0, evalSec := 0, evalLatch := 0, sprCount := 0,
    sprPatLo := zeroBytes 8, sprPatHi := zeroBytes 8, sprAttr := zeroBytes 8, sprX := zeroBytes 8,
    spr0Next := false, spr0Line := false, dot := 0, scanline := 0, frameOdd := false,
    nmiOut := false, suppressVbl := false, a12 := false,
    frame := zeroBytes (frameWidth * frameHeight), emphasis := 0, frameReady := false }

instance : Inhabited State := ⟨init⟩

/-! ### Register bit accessors -/

/-- `ctrl` bit 2: VRAM address increment 32 (down) instead of 1 (across). -/
@[inline] def vramInc32 (s : State) : Bool := s.ctrl &&& 0x04 != 0
/-- `ctrl` bit 3: sprite pattern table at `$1000` (8×8 sprites only). -/
@[inline] def sprTable (s : State) : Bool := s.ctrl &&& 0x08 != 0
/-- `ctrl` bit 4: background pattern table at `$1000`. -/
@[inline] def bgTable (s : State) : Bool := s.ctrl &&& 0x10 != 0
/-- `ctrl` bit 5: 8×16 sprites. -/
@[inline] def sprTall (s : State) : Bool := s.ctrl &&& 0x20 != 0
/-- `ctrl` bit 7: generate NMI at vblank. -/
@[inline] def nmiEnable (s : State) : Bool := s.ctrl &&& 0x80 != 0

/-- `mask` bit 1/2: show background/sprites in the leftmost 8 pixels. -/
@[inline] def bgLeft (s : State) : Bool := s.mask &&& 0x02 != 0
@[inline] def sprLeft (s : State) : Bool := s.mask &&& 0x04 != 0
/-- `mask` bit 3/4: background/sprite rendering enabled. -/
@[inline] def showBg (s : State) : Bool := s.mask &&& 0x08 != 0
@[inline] def showSpr (s : State) : Bool := s.mask &&& 0x10 != 0
/-- Rendering is enabled when either layer is shown. -/
@[inline] def rendering (s : State) : Bool := s.mask &&& 0x18 != 0

/-- `status` bits 5–7. -/
@[inline] def sprOverflow (s : State) : Bool := s.status &&& 0x20 != 0
@[inline] def spr0Hit (s : State) : Bool := s.status &&& 0x40 != 0
@[inline] def vblank (s : State) : Bool := s.status &&& 0x80 != 0

end State

end Nes.Ppu
