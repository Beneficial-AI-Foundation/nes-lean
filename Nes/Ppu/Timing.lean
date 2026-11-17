import Nes.Ppu.Types

/-!
# `Nes.Ppu.Timing` — dot/scanline counters, vblank, odd-frame skip, NMI line

The 2C02 runs 341 dots per scanline and 262 scanlines per frame: lines 0–239 visible, 240
post-render, 241–260 vertical blank, 261 pre-render. This module advances the counters and
performs the *timing* events only (vblank flag, flag clears, NMI output, frame-ready). It does
no rendering work: background fetches, sprite evaluation and pixel output are per-dot functions
of other modules, composed with `advance`/`dotEvents` by `Nes.Ppu.Step` (see `tick`).

Position convention: `(scanline, dot)` in a `State` is the dot **just executed**. `tick` moves
to the next dot (`advance`) and then executes that dot's timing events (`dotEvents`). So a CPU
access performed on a state at `(241, 0)` happens between dot 0 and dot 1 of line 241, i.e.
one PPU clock before the vblank flag is set.

Sources (NESdev wiki, "PPU frame timing", "PPU rendering", "NMI"):
* Vblank flag set at dot 1 of line 241; vblank, sprite-0 hit and sprite overflow cleared at
  dot 1 of the pre-render line 261.
* With rendering enabled, odd frames are one dot shorter: the PPU jumps from (261, 339)
  straight to (0, 0) (the idle dot is skipped). Rendering is sampled at that dot.
* NMI output = `ctrl.7 ∧ vblank` (`nmiOut`); the CPU detects its rising edge. Hence
  enabling NMI during vblank raises the line again (retrigger; `writeCtrl`), and clearing
  vblank by a `$2002` read drops it.
* "Reading $2002 one PPU clock before [the flag is set] reads it as clear and never sets the
  flag or generates NMI for that frame. Reading on the same PPU clock or one later reads it as
  set, clears it, and suppresses the NMI for that frame." (`readStatus`, `suppressVbl`; the
  "same clock or one later" half falls out of `readStatus` clearing `nmiOut` before the CPU
  samples it, which depends on the CPU/PPU interleave below.)

Integration hint (system clock item): the M2 blargg scaffolding found that, within one CPU
cycle, running 2 PPU dots before the CPU bus access and 1 after passes `cpu_interrupts_v2`;
the `$2002` race and `ppu_vbl_nmi` (`testdata/nes-test-roms/ppu_vbl_nmi/`) are the ground
truth for that alignment.

## Spec

* Constants: `dotsPerLine = 341`, `linesPerFrame = 262`, `vblankLine = 241`,
  `preRenderLine = 261`, `dotsPerFrame = 89342`.
* `advance s` (only `dot scanline frameOdd` change): if `(scanline, dot) = (261, 339)`,
  `frameOdd` and rendering is enabled → `(0, 0)` and `frameOdd` flips; else if `dot = 340`:
  line 261 → `(0, 0)` with `frameOdd` flipped, other lines → `(scanline + 1, 0)`; else
  `dot + 1`.
* `dotEvents s` (only `status nmiOut suppressVbl frameReady emphasis` change): at `(241, 1)`:
  `suppressVbl := false`, `frameReady := true`, `emphasis := mask >> 5`, and unless
  `suppressVbl` was set, `vblank := true` and `nmiOut := nmiEnable`. At `(261, 1)`: vblank,
  sprite-0 hit and overflow cleared, `nmiOut := false`. Elsewhere: nothing.
* `tick = dotEvents ∘ advance`. `nmiLine s = s.nmiOut` (asserted = true; the CPU side is
  edge-triggered).
* `ticks n s` is `tick` applied `n` times.
-/

namespace Nes.Ppu

/-- Dots per scanline. -/
def dotsPerLine : Nat := 341
/-- Scanlines per frame. -/
def linesPerFrame : Nat := 262
/-- First vblank scanline (flag set at its dot 1). -/
def vblankLine : Nat := 241
/-- Pre-render scanline (flags cleared at its dot 1). -/
def preRenderLine : Nat := 261
/-- Dots in a full frame (even frames, or rendering disabled). -/
def dotsPerFrame : Nat := dotsPerLine * linesPerFrame

namespace State

/-- NMI output line as seen by the CPU (`true` = asserted). The CPU latches a rising edge. -/
@[inline] def nmiLine (s : State) : Bool := s.nmiOut

/-- Advance `(scanline, dot, frameOdd)` by one PPU clock, with the odd-frame skip. -/
@[inline] def advance (s : State) : State :=
  if s.dot == 339 && s.scanline == 261 && s.frameOdd && s.rendering then
    { s with dot := 0, scanline := 0, frameOdd := !s.frameOdd }
  else if s.dot == 340 then
    if s.scanline == 261 then { s with dot := 0, scanline := 0, frameOdd := !s.frameOdd }
    else { s with dot := 0, scanline := s.scanline + 1 }
  else { s with dot := s.dot + 1 }

/-- Timing events of the dot `(scanline, dot)` just reached. -/
@[inline] def dotEvents (s : State) : State :=
  if s.dot == 1 then
    if s.scanline == 241 then
      if s.suppressVbl then
        { s with suppressVbl := false, frameReady := true, emphasis := s.mask >>> 5 }
      else
        { s with status := s.status ||| 0x80, nmiOut := s.nmiEnable, suppressVbl := false,
                 frameReady := true, emphasis := s.mask >>> 5 }
    else if s.scanline == 261 then
      { s with status := s.status &&& 0x1F, nmiOut := false }
    else s
  else s

/-- One PPU clock of timing. `Nes.Ppu.Step` composes the rendering work between the two halves:
`dotEvents (render (advance s))`, where `render` runs the background / sprite per-dot
functions for the new `(scanline, dot)` (note the odd-frame skip means `(261, 340)` is never
executed on such frames). -/
@[inline] def tick (s : State) : State :=
  dotEvents (advance s)

/-- `tick` applied `n` times (spec / proof helper; not for the hot path). -/
def ticks : Nat → State → State
  | 0, s => s
  | n + 1, s => ticks n (tick s)

end State

/-- CPU cycles per frame of `dotsPerFrame` dots (3 dots per CPU cycle on NTSC): `29780 + 2/3`. -/
def cpuCyclesPerFrame : Rat := (dotsPerFrame : Rat) / 3

/-- NTSC PPU clock in Hz: master clock `236.25 MHz / 11` divided by 4. -/
def ppuHz : Rat := 236250000 / 44

/-- Average NTSC frame rate with rendering enabled (frames alternate 89342 / 89341 dots). -/
def frameRate : Rat := ppuHz / (178683 / 2)

end Nes.Ppu
