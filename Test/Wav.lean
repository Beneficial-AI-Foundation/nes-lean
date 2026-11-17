import Nes.Frontend.Wav
import Nes.Apu.Mixer

/-!
# WAV / downsampler tests (`Nes.Frontend.Wav`)

* Header fields of `wav` (RIFF/WAVE/fmt/data, sizes, rate, byte rate, block align, bits), odd pad.
* Downsampled lengths are exactly `⌊n · 44100 / 1789773⌋` (1 s of CPU samples → 44100).
* Box average: a constant input reproduces the constant; a ramp stays monotone.
* High-pass: a DC step decays to ≈ 0; a 440 Hz sine keeps 880 ± 2 zero crossings per second.
* `mixSample` corner values (silence 0, full scale saturates at 65535).
* The 440 Hz WAV is written under `.lake/test-out/`; if `python3` exists it is parsed with the
  `wave` module and the frames compared to our bytes.
-/

namespace Test.Wav

open Nes.Frontend

def u16At (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat ||| (b.get! (i+1)).toNat <<< 8
def u32At (b : ByteArray) (i : Nat) : Nat := u16At b i ||| u16At b (i+2) <<< 16
def s16At (b : ByteArray) (i : Nat) : Int :=
  let u := u16At b (2 * i)
  if u ≥ 32768 then (u : Int) - 65536 else u
def asciiAt (b : ByteArray) (i : Nat) : String := String.fromUTF8! (b.extract i (i+4))

/-- `n` CPU-rate samples of a sine at `hz` (amplitude `amp` around 32768). -/
def sine (n : Nat) (hz amp : Float) : Array UInt16 := Id.run do
  let mut a := Array.mkEmpty n
  for i in [0:n] do
    let v := 32768.0 + amp * Float.sin (2.0 * 3.141592653589793 * hz * i.toFloat / 1789773.0)
    a := a.push v.toUInt16
  return a

def zeroCrossings (b : ByteArray) : Nat := Id.run do
  let n := b.size / 2
  let mut c := 0
  for i in [1:n] do
    if (s16At b (i-1) < 0) != (s16At b i < 0) then c := c + 1
  return c

def pyCheck : String := "
import sys, wave
w = wave.open(sys.argv[1], 'rb')
assert w.getnchannels() == 1 and w.getsampwidth() == 2 and w.getframerate() == 44100, w.getparams()
fr = w.readframes(w.getnframes())
raw = open(sys.argv[2], 'rb').read()
assert fr == raw and w.getnframes() == len(raw) // 2
print('python wave OK %d frames @ %d Hz' % (w.getnframes(), w.getframerate()))
"

def run : IO UInt32 := do
  let check (name : String) (ok : Bool) : StateT Nat IO Unit := do
    unless ok do
      IO.println s!"  wav FAIL: {name}"
      modify (· + 1)
  let pcm := ByteArray.mk #[1, 2, 3, 4, 5, 6]
  let w := wav pcm 44100
  let s1 := sine 1789773 440.0 12000.0
  let hp := downsample s1 44100 true
  let ramp := downsample ((Array.range 100000).map (fun i => (i * 65535 / 100000).toUInt16))
  let ((), fails) ← (do
    check "riff" (asciiAt w 0 == "RIFF" && u32At w 4 == 36 + 6 && asciiAt w 8 == "WAVE")
    check "fmt" (asciiAt w 12 == "fmt " && u32At w 16 == 16 && u16At w 20 == 1 && u16At w 22 == 1)
    check "rates" (u32At w 24 == 44100 && u32At w 28 == 88200 && u16At w 32 == 2 && u16At w 34 == 16)
    check "data" (asciiAt w 36 == "data" && u32At w 40 == 6 && w.size == 50 && w.extract 44 50 == pcm)
    let w5 := wav (ByteArray.mk #[1, 2, 3, 4, 5]) 8000
    check "odd pad" (w5.size == 50 && u32At w5 4 == 36 + 6 && u32At w5 40 == 5)
    check "alpha 44.1k" (hpAlpha 44100 == 32353)
    check "1 s → 44100 samples" (hp.size == 2 * 44100)
    check "ramp length" (ramp.size == 2 * (100000 * 44100 / 1789773))
    check "ramp monotone" ((List.range (ramp.size / 2 - 1)).all fun i => s16At ramp i ≤ s16At ramp (i+1))
    let dc := downsample (Array.replicate 50000 (40000 : UInt16))
    check "dc no-hp" ((List.range (dc.size / 2)).all fun i => s16At dc i == 40000 - 32768)
    let step := downsample (Array.replicate 1789773 (40000 : UInt16) |>.set! 0 0) 44100 true
    check "dc hp decays" ((s16At step (step.size / 2 - 1)).natAbs ≤ 1)
    let zc := zeroCrossings hp
    check s!"440 Hz crossings {zc}" (878 ≤ zc && zc ≤ 882)
    check "mix silence" (Nes.Apu.mixSample 0 0 0 0 0 == 0)
    check "mix saturates" (Nes.Apu.mixSample 15 15 15 15 127 == 65535)
    check "mix masks" (Nes.Apu.mixSample 0x1F 0 0 0 0xFF == Nes.Apu.mixSample 0xF 0 0 0 0x7F)
    ).run 0
  let dir : System.FilePath := ".lake/test-out"
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / "sine440.wav") (wav hp 44100)
  IO.FS.writeBinFile (dir / "sine440.pcm") hp
  let mut fails := fails
  let mut pyNote := "python3 not run"
  try
    let out ← IO.Process.output
      { cmd := "python3", args := #["-I", "-c", pyCheck, (dir / "sine440.wav").toString,
          (dir / "sine440.pcm").toString] }
    if out.exitCode == 0 then pyNote := String.ofList (out.stdout.toList.filter (· != '\n'))
    else
      IO.println s!"  wav FAIL: python check\n{out.stderr}"
      fails := fails + 1
  catch _ => pure ()
  IO.println s!"wav: {if fails == 0 then "PASS" else s!"{fails} FAIL"} — header, lengths, box/high-pass, 440 Hz crossings {zeroCrossings hp}; {pyNote}"
  return if fails == 0 then 0 else 1

end Test.Wav
