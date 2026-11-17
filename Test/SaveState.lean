import Nes.System.SaveState

/-!
# Save-state tests (`Nes.System.SaveState`)

For each ROM: power on, run 100 frames, `serialize`, `deserialize` (with the ROM), then run the
original and the restored machine 100 more frames under the same input script; the 100 frame
hashes must agree. Also: re-serializing the restored machine gives the same bytes; truncated,
over-long and bad-magic buffers are rejected. Skips when `testdata/` is absent.
-/

namespace Test.SaveState

open Nes.System Nes.Frontend

def dataDir : System.FilePath := "testdata"

def roms : List String :=
  ["nes-test-roms/spritecans-2011/spritecans.nes",   -- NROM
   "nes-test-roms/other/BladeBuster.nes"]            -- MMC3

/-- A script exercising the controllers: Start on a few frames, then A/right. -/
def script (k : Nat) : List (UInt8 × UInt8) :=
  (List.range k).map fun i => if i % 17 == 3 then (0x08, 0) else if i % 5 == 0 then (0x81, 0x01)
    else (0, 0)

def checkRom (rom : String) : IO Bool := do
  let path := dataDir / rom
  unless ← path.pathExists do
    IO.println s!"savestate: SKIP {rom} (missing)"
    return true
  match Nes.Cart.Cart.load (← IO.FS.readBinFile path) with
  | .error e =>
    IO.println s!"savestate: FAIL {rom}: load error: {e}"
    return false
  | .ok c =>
    let n := (Nes.powerOn c).runScriptHashes (script 100) |>.1
    let b := n.serialize
    let some m := Nes.deserialize c.rom b
      | IO.println s!"savestate: FAIL {rom}: deserialize returned none"; return false
    let mut ok := true
    if m.serialize != b then
      IO.println s!"savestate: FAIL {rom}: re-serialization differs"; ok := false
    let (_, h1) := n.runScriptHashes (script 100)
    let (_, h2) := m.runScriptHashes (script 100)
    if h1 != h2 then
      IO.println s!"savestate: FAIL {rom}: frame hashes differ after restore"; ok := false
    let hashes := h1.toArray
    if hashes.size != 100 then
      IO.println s!"savestate: FAIL {rom}: {hashes.size} hashes"; ok := false
    if (Nes.deserialize c.rom (b.extract 0 (b.size - 1))).isSome then
      IO.println s!"savestate: FAIL {rom}: truncated buffer accepted"; ok := false
    if (Nes.deserialize c.rom (b.extract 0 (b.size / 2))).isSome then
      IO.println s!"savestate: FAIL {rom}: half buffer accepted"; ok := false
    if (Nes.deserialize c.rom (b.push 0)).isSome then
      IO.println s!"savestate: FAIL {rom}: over-long buffer accepted"; ok := false
    if (Nes.deserialize c.rom (b.set! 0 0)).isSome then
      IO.println s!"savestate: FAIL {rom}: bad magic accepted"; ok := false
    if ok then
      IO.println s!"savestate: ok {rom} ({b.size} bytes, last hash {(hashes.back?.getD 0)})"
    return ok

def run : IO UInt32 := do
  unless ← dataDir.pathExists do
    IO.println "savestate: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut fails : UInt32 := 0
  for rom in roms do
    unless ← checkRom rom do fails := fails + 1
  return fails

end Test.SaveState
