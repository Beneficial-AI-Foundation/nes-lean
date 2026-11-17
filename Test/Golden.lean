import Nes

/-!
# Golden frame hashes of homebrew ROMs (PLAN.md §7, end-to-end regression)

Each entry: a ROM (path relative to `testdata/`, fetched by `scripts/fetch-testdata.sh`, never
committed), a frame count from power-on with no input, and the expected `frameHash` (FNV-1a 64
over the 256×240 palette-index bytes) of the frame finished at the `frames`-th vblank start —
the same frame `nes run <rom> --frames N` reports. Only hashes are committed, never ROMs or
images.

Entries were checked visually (PNG via `nes run … --png`) before being recorded:
* `spritecans-2011/spritecans.nes` (blargg/tepples "Sprite Cans 2011", NROM-128, horizontal
  mirroring): frames 60 and 120 show the title text ("OBEY YOUR THIRST", credits, copyright)
  with the first can sprite; frame 600 shows dozens of bouncing cans in front of the text.

Consecutive entries for the same ROM with increasing frame counts continue one run.
The suite skips when `testdata/` is absent.
-/

namespace Test.Golden

open Nes.Frontend

def dataDir : System.FilePath := "testdata"

/-- `(rom path relative to testdata, frames, expected frame hash)`. -/
def table : List (String × Nat × String) :=
  [("nes-test-roms/spritecans-2011/spritecans.nes", 60, "07e982a570087379"),
   ("nes-test-roms/spritecans-2011/spritecans.nes", 120, "6e207aa1ad58d617"),
   ("nes-test-roms/spritecans-2011/spritecans.nes", 600, "77a4e4e325a92630")]

def runFrames : Nat → Nes.System.Nes → Nes.System.Nes
  | 0, n => n
  | k + 1, n => runFrames k n.runFrame

def run : IO UInt32 := do
  unless ← dataDir.pathExists do
    IO.println "golden: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut fails := 0
  -- the run in progress: (rom, frames done, console)
  let mut cur : Option (String × Nat × Nes.System.Nes) := none
  for (rom, frames, want) in table do
    let path := dataDir / rom
    unless ← path.pathExists do
      IO.println s!"golden: SKIP {rom} (missing)"
      continue
    let start ← match cur with
      | some (r, done, n) => if r == rom && done ≤ frames then pure (some (done, n)) else pure none
      | none => pure none
    let start ← match start with
      | some s => pure (some s)
      | none =>
        match Nes.Cart.Cart.load (← IO.FS.readBinFile path) with
        | .ok c => pure (some (0, Nes.System.Nes.powerOn c))
        | .error e =>
          IO.println s!"golden: FAIL {rom}: load error: {e}"
          fails := fails + 1
          pure none
    let some (done, n) := start | continue
    let n := runFrames (frames - done) n
    cur := some (rom, frames, n)
    let got := hex64 (frameHash n.ppu.frame)
    if got == want then
      IO.println s!"golden: ok   {rom} @{frames} {got}"
    else
      IO.println s!"golden: FAIL {rom} @{frames} got {got} want {want}"
      fails := fails + 1
  IO.println s!"golden: {table.length - fails}/{table.length} (failures {fails})"
  return if fails == 0 then 0 else 1

end Test.Golden
