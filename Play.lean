import Nes

/-!
# `nes-play` — live window with keyboard and sound

The platform layer around the verified emulator: an SDL3 window (`Play/sdl_shim.c`) shows
each frame, the APU output is streamed to the default audio device, and the keyboard drives
controller 1. It lives outside `Nes/` because it needs `IO` and C externs; the emulator
itself is the same pure `Nes.System.Nes.runFrameAudio` the headless CLI uses.

Pacing: the downsampler emits exactly 44 100 samples per emulated NTSC second, so the loop
keeps the audio queue near three frames deep and sleeps while it is fuller. Speed therefore
follows the sound card's clock. Without an audio device it paces by the wall clock instead.

Keys: arrows = D-pad, X = A, Z = B, Enter = Start, Right Shift / Tab = Select,
P = pause, R = reset, Esc = quit.
-/

open Nes.Frontend

namespace Play

@[extern "nes_play_open"] opaque sdlOpen (title : @& String) (scale : UInt32) : BaseIO UInt32
@[extern "nes_play_error"] opaque sdlError : BaseIO String
@[extern "nes_play_poll"] opaque sdlPoll : BaseIO UInt32
@[extern "nes_play_present"] opaque sdlPresent (rgb : @& ByteArray) : BaseIO Unit
@[extern "nes_play_audio"] opaque sdlAudio (pcm : @& ByteArray) : BaseIO Unit
@[extern "nes_play_queued"] opaque sdlQueued : BaseIO UInt32
@[extern "nes_play_has_audio"] opaque sdlHasAudio : BaseIO UInt32
@[extern "nes_play_close"] opaque sdlClose : BaseIO Unit

/-- Audio queue target: three NTSC frames of 16-bit mono at 44.1 kHz (≈ 50 ms). -/
def queueTarget : UInt32 := 3 * 2 * 735

/-- Nanoseconds per NTSC frame (60.0988 Hz), for wall-clock pacing without audio. -/
def frameNanos : Nat := 16_639_267

def keysHelp : String :=
  "keys: arrows = D-pad, X = A, Z = B, Enter = Start, Right Shift/Tab = Select,\n      \
   P = pause, R = reset, Esc = quit"

def usage : String := "usage: nes-play <rom.nes> [--scale N]\n" ++ keysHelp

partial def loop (n : Nes.System.Nes) (ds : Downsampler) (audio : Bool) (paused : Bool)
    (deadline : Nat) : IO Unit := do
  let keys ← sdlPoll
  if keys &&& 0x100 != 0 then return
  let paused := if keys &&& 0x400 != 0 then !paused else paused
  let n := if keys &&& 0x200 != 0 then n.reset else n
  if paused then
    sdlPresent (toRgb n.ppu.frame n.ppu.emphasis)
    IO.sleep 16
    return ← loop n ds audio paused ((← IO.monoNanosNow) + frameNanos)
  let n := { n with pads := n.pads.setButtons (keys &&& 0xFF).toUInt8 0 }
  let (n, ds) := n.runFrameAudio ds
  if audio then sdlAudio ds.out
  sdlPresent (toRgb n.ppu.frame n.ppu.emphasis)
  let ds := { ds with out := ByteArray.empty }
  if audio then
    while (← sdlQueued) > queueTarget do IO.sleep 1
    loop n ds audio paused deadline
  else
    let now ← IO.monoNanosNow
    if now < deadline then IO.sleep ((deadline - now) / 1_000_000).toUInt32
    loop n ds audio paused (max (deadline + frameNanos) now)

def parseScale : List String → Except String UInt32
  | [] => .ok 3
  | ["--scale", k] => match k.toNat? with
    | some s => if 1 ≤ s ∧ s ≤ 8 then .ok s.toUInt32 else .error "--scale: N must be 1..8"
    | none => .error s!"--scale: bad number {k}"
  | a :: _ => .error s!"nes-play: unexpected argument `{a}`"

end Play

open Play in
def main (args : List String) : IO UInt32 := do
  let (rom, rest) ← match args with
    | rom :: rest => if rom == "--help" || rom == "-h" then IO.println usage; return 0
                     else pure (rom, rest)
    | [] => IO.eprintln usage; return 2
  let scale ← match parseScale rest with
    | .ok s => pure s
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  let cart ← match Nes.Cart.Cart.load (← IO.FS.readBinFile rom) with
    | .ok c => pure c
    | .error e => IO.eprintln s!"nes-play: {rom}: {e}"; return 1
  let title := (System.FilePath.fileName rom).getD rom
  let rc ← sdlOpen s!"nes-lean — {title}" scale
  if rc != 0 then
    let what := if rc == 1 then "init" else if rc == 2 then "window" else "texture"
    IO.eprintln s!"nes-play: SDL {what} failed: {← sdlError}"; return 1
  let audio := (← sdlHasAudio) != 0
  unless audio do IO.eprintln s!"nes-play: no audio device ({← sdlError}); playing silently"
  IO.println keysHelp
  try
    loop (Nes.System.Nes.powerOn cart) (Downsampler.init (highPass := true)) audio false
      ((← IO.monoNanosNow) + frameNanos)
  finally
    sdlClose
  return 0
