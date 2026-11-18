import Lake

open System Lake DSL

package nes where
  testDriver := "Test"
  version := v!"0.1.0"

require batteries from git "https://github.com/leanprover-community/batteries"@"v4.36.0"

@[default_target] lean_lib Nes where precompileModules := true

-- Test-suite modules (`Test.*`); the `Test` exe imports them. Lake only builds a module
-- that some lean_lib owns, so the suites live in this library.
lean_lib TestSuite where globs := #[`Test.+]

@[default_target] lean_exe nes where
  root := `Main
  moreLeancArgs := #["-O3", "-DNDEBUG"]

lean_exe Test where root := `Test.Main

/-! ## `nes-play`: live window (keyboard + sound) over SDL3

Not a default target: `lake build` and CI do not need SDL. Build it with
`lake build nes-play` after installing SDL3 (`brew install sdl3`, `apt install libsdl3-dev`). -/

/-- `pkg-config <flag> sdl3`, split into arguments; empty when SDL3 or pkg-config is absent. -/
def sdl3Flags (flag : String) : IO (Array String) := do
  try
    let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, "sdl3"] }
    if out.exitCode != 0 then return #[]
    return (out.stdout.split Char.isWhitespace).filterMap (fun s =>
      let s := s.toString; if s.isEmpty then none else some s) |>.toArray
  catch _ => return #[]

target sdlShim.o pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "Play" / "sdl_shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← sdl3Flags "--cflags")
  buildO (pkg.buildDir / "c" / "sdl_shim.o") src weakArgs #["-O2", "-fPIC"]

lean_exe «nes-play» where
  root := `Play
  moreLeancArgs := #["-O3", "-DNDEBUG"]
  moreLinkObjs := #[sdlShim.o]
  -- macOS: the shim's entry point keeps the main thread for Cocoa (see Play/sdl_shim.c).
  moreLinkArgs := run_io do
    let darwin := System.Platform.isOSX
    return (← sdl3Flags "--libs") ++ (if darwin then #["-Wl,-e,_nes_play_entry"] else #[])
