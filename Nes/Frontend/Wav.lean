/-!
# `Nes.Frontend.Wav` — WAV encoder and CPU-rate → 44.1 kHz downsampler (frontend only)

PLAN §5.4: the APU produces one mixer sample per CPU cycle (`Nes.Apu.mixSample`, fixed point
`[0, 65535]`); conversion to an audio stream lives here. Everything is pure integer code
(`UInt64` / `Int64`, no `Float`).

**Downsampler.** A box filter: all input samples falling into one output period are averaged.
Output instants are placed Bresenham-style with an exact integer phase accumulator: every input
sample adds `outRate` to `phase`; when `phase ≥ inRate` one output sample (the window average)
is emitted and `inRate` is subtracted. Hence `n` input samples produce exactly
`⌊n · outRate / inRate⌋` outputs, with no drift. `inRate` defaults to `cpuHz = 1789773` (NTSC
CPU clock 21.477272 MHz / 12 = 1789772.7 Hz, rounded; pitch error 2·10⁻⁷).

**Output level / DC.** The window average `a ∈ [0, 65535]` is centred to `a − 32768`
(signed 16-bit). With `highPass := true` a first-order high-pass at ≈ 90 Hz (the first of the
NES's analog output filters, NESdev "APU Mixer") is applied instead, which also removes the DC
offset: `y[i] = α · (y[i−1] + x[i] − x[i−1])`, `α = fs / (fs + 2π·90)` in Q15
(`32353 / 32768` at 44.1 kHz), initialised with `x[−1] = x[0]` so there is no start-up thump.
Results are clamped to `[−32768, 32767]` (only a near-full-scale step can clip).
The box filter is a crude anti-alias filter (first null at 44.1 kHz); this is a debugging /
test output path, not a hi-fi resampler.

**WAV.** `wav samples rate` wraps 16-bit little-endian mono PCM in a canonical 44-byte RIFF/WAVE
header (`fmt ` chunk: PCM = 1, 1 channel, `rate`, byte rate `2·rate`, block align 2, 16 bits).
-/

namespace Nes.Frontend

/-- NTSC CPU clock, Hz (rounded). -/
def cpuHz : UInt64 := 1789773

/-- Default audio output rate, Hz. -/
def audioHz : UInt64 := 44100

/-- Streaming box-filter downsampler state (see module doc). -/
structure Downsampler where
  inRate : UInt64 := cpuHz
  outRate : UInt64 := audioHz
  highPass : Bool := false
  /-- High-pass coefficient α in Q15. -/
  alpha : Int64 := 32353
  phase : UInt64 := 0
  acc : UInt64 := 0
  count : UInt64 := 0
  started : Bool := false
  prevX : Int64 := 0
  prevY : Int64 := 0
  /-- Output: 16-bit little-endian signed PCM. -/
  out : ByteArray := ByteArray.empty

/-- `α = fs / (fs + 2π·90)` in Q15 (2π·90 ≈ 565.4867). -/
def hpAlpha (outRate : UInt64) : Int64 :=
  let fs := outRate.toNat
  (Int.ofNat (32768 * fs * 10000 / (fs * 10000 + 5654867))).toInt64

/-- A fresh downsampler. `outRate` must be positive and ≤ `inRate`. -/
def Downsampler.init (outRate : UInt64 := audioHz) (highPass : Bool := false)
    (inRate : UInt64 := cpuHz) : Downsampler :=
  { inRate, outRate, highPass, alpha := hpAlpha outRate }

/-- Append a signed sample (clamped to 16 bits), little-endian. -/
@[inline] def pushS16 (b : ByteArray) (y : Int64) : ByteArray :=
  let c : Int64 := if y < -32768 then -32768 else if y > 32767 then 32767 else y
  let u := (c + 65536).toUInt64
  (b.push u.toUInt8).push (u >>> 8).toUInt8

/-- Emit one output sample from a window average `avg ∈ [0, 65535]`. -/
def Downsampler.emit (s : Downsampler) (avg : UInt64) : Downsampler :=
  let x : Int64 := avg.toInt64
  if s.highPass then
    let px := if s.started then s.prevX else x
    let y := s.alpha * (s.prevY + x - px) / 32768
    { s with started := true, prevX := x, prevY := y, out := pushS16 s.out y }
  else
    { s with started := true, out := pushS16 s.out (x - 32768) }

/-- Feed one CPU-rate mixer sample. -/
@[inline] def Downsampler.push (s : Downsampler) (x : UInt16) : Downsampler :=
  let acc := s.acc + x.toUInt64
  let count := s.count + 1
  let phase := s.phase + s.outRate
  if phase ≥ s.inRate then
    { s with phase := phase - s.inRate, acc := 0, count := 0 }.emit (acc / count)
  else
    { s with phase, acc, count }

/-- Downsample a whole CPU-rate buffer to 16-bit LE PCM. -/
def downsample (xs : Array UInt16) (outRate : UInt64 := audioHz) (highPass : Bool := false) :
    ByteArray :=
  (xs.foldl Downsampler.push (Downsampler.init outRate highPass)).out

@[inline] def pushU16LE (b : ByteArray) (x : UInt32) : ByteArray :=
  (b.push x.toUInt8).push (x >>> 8).toUInt8

@[inline] def pushU32LE (b : ByteArray) (x : UInt32) : ByteArray :=
  pushU16LE (pushU16LE b x) (x >>> 16)

/-- RIFF/WAVE file around 16-bit LE mono PCM `samples` at `rate` Hz. An odd-length payload gets
the RIFF pad byte (the `data` chunk size still states the unpadded length). -/
def wav (samples : ByteArray) (rate : UInt32) : ByteArray :=
  let n := samples.size.toUInt32
  let pad := samples.size % 2
  let ascii (b : ByteArray) (s : String) : ByteArray := b ++ s.toUTF8
  let h := ByteArray.emptyWithCapacity (44 + samples.size + pad)
  let h := pushU32LE (ascii h "RIFF") (36 + n + pad.toUInt32)
  let h := ascii h "WAVE"
  let h := pushU32LE (ascii h "fmt ") 16
  let h := pushU16LE h 1          -- PCM
  let h := pushU16LE h 1          -- mono
  let h := pushU32LE h rate
  let h := pushU32LE h (2 * rate) -- byte rate
  let h := pushU16LE h 2          -- block align
  let h := pushU16LE h 16         -- bits per sample
  let h := pushU32LE (ascii h "data") n
  let h := h ++ samples
  if pad == 1 then h.push 0 else h

end Nes.Frontend
