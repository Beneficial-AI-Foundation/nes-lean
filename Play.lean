import Play.Core

/-!
# `nes-play` — live window with keyboard and sound

The platform layer around the verified emulator: `Play/app.c` (SDL3 app callbacks) shows each
frame, streams the APU output to the default audio device and reads the keyboard as
controller 1; the emulator itself is `Play.Core`, the same pure `runFrameAudio` the headless
CLI uses. The browser build (`web/`) runs the same `app.c` and `Play.Core` compiled to
WebAssembly. This lives outside `Nes/` because it needs `IO` and C externs.

Keys: arrows = D-pad, X = A, Z = B, Enter = Start, Right Shift / Tab = Select,
P = pause, R = reset, Esc = quit. A ROM can also be dropped onto the window.
-/

namespace Play

/-- Run the SDL app loop (`Play/native.c`) with these arguments; returns the exit code. -/
@[extern "nes_play_run"] opaque run (args : @& List String) : BaseIO UInt32

def usage : String :=
  "usage: nes-play [<rom.nes>] [--scale N]\n\
   keys: arrows = D-pad, X = A, Z = B, Enter = Start, Right Shift/Tab = Select,\n      \
   P = pause, R = reset, Esc = quit; drop a .nes file on the window to load it"

end Play

def main (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "--help" || a == "-h") then
    IO.println Play.usage; return 0
  IO.println Play.usage
  Play.run args
