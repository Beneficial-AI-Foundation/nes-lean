import Nes.Apu.Pulse
import Nes.Apu.Triangle
import Nes.Apu.Noise

/-!
# APU unit spot checks (pulse / triangle / noise / length / envelope / sweep)

Each check is a closed `Bool`; `checks_pass` proves they all hold (kernel evaluation), and
`run` re-evaluates them at runtime, printing failures. References: NESdev "APU Pulse",
"APU Triangle", "APU Noise", "APU Length Counter", "APU Envelope", "APU Sweep"; the noise
LFSR reference values were computed independently.
-/

namespace Test.ApuUnits

open Nes.Apu

/-- Apply `f` `n` times. -/
def iter {α} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- Sample `out` `count` times, applying `f` `gap` times between samples. -/
def samples {α β} (f : α → α) (out : α → β) (gap : Nat) : Nat → α → List β
  | 0, _ => []
  | n + 1, a => out a :: samples f out gap n (iter f gap a)

/-- Pulse 1, duty `d`, constant volume 15, period 8 (one step = 9 APU cycles), length on. -/
def pulseAt (d : UInt8) : Pulse :=
  (Pulse.init1.setEnabled true).write 0 ((d <<< 6) ||| 0x30 ||| 15) |>.write 2 8 |>.write 3 0x08

def pulseWave (d : UInt8) : List UInt8 := samples Pulse.tick Pulse.output 9 16 (pulseAt d)

def rep2 (l : List UInt8) : List UInt8 := (l ++ l).map (· * 15)

def tri : Triangle :=
  ((({} : Triangle).setEnabled true).write 0 0x7F |>.write 2 2 |>.write 3 0x08).quarterFrame

def noise : Noise :=
  ({} : Noise).setEnabled true |>.write 0 0x3F |>.write 2 0 |>.write 3 0x08

/-- Envelope decay levels over `n` quarter frames, starting with the start flag set. -/
def envLevels (loop : Bool) (n : Nat) : List UInt8 :=
  samples Envelope.quarterFrame Envelope.output 1 n
    (({ start := true } : Envelope).write (if loop then 0x20 else 0)).quarterFrame

def sw (v : UInt8) : Sweep := ({} : Sweep).write v

def checks : List (String × Bool) :=
  [ ("pulse duty 0 waveform", pulseWave 0 == rep2 [0, 1, 0, 0, 0, 0, 0, 0]),
    ("pulse duty 1 waveform", pulseWave 1 == rep2 [0, 1, 1, 0, 0, 0, 0, 0]),
    ("pulse duty 2 waveform", pulseWave 2 == rep2 [0, 1, 1, 1, 1, 0, 0, 0]),
    ("pulse duty 3 waveform", pulseWave 3 == rep2 [1, 0, 0, 1, 1, 1, 1, 1]),
    ("pulse period < 8 mutes", ((pulseAt 3).write 2 7).output == 0),
    ("pulse length 0 silences", ((pulseAt 3).setEnabled false).output == 0),
    ("pulse disabled ignores length load",
      ((Pulse.init2.write 3 0x08).lengthNonzero == false)),
    ("pulse $4003 loads length 254", (pulseAt 0).len.counter == 254),
    ("triangle sequence",
      samples Triangle.tick Triangle.output 3 32 tri ==
        [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
         0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
    ("triangle ultrasonic holds output",
      samples Triangle.tick Triangle.output 1 8 (iter Triangle.tick 9 tri |>.write 2 1) ==
        List.replicate 8 12),
    ("triangle halts with linear 0",
      samples Triangle.tick Triangle.output 3 4 { tri with linear := 0 } == [15, 15, 15, 15]),
    ("triangle linear reload/clear",
      (tri.linReloadFlag == false) && tri.linear == 127 && tri.quarterFrame.linear == 126),
    ("noise LFSR from seed 1",
      samples Noise.tick (·.lfsr) 2 8 (Noise.tick noise) ==
        ([0x4000, 0x2000, 0x1000, 0x800, 0x400, 0x200, 0x100, 0x80] : List UInt16) &&
      (iter Noise.tick 1 noise).lfsr == 0x4000 && (iter Noise.tick 29 noise).lfsr == 0x4001),
    ("noise first outputs from seed 1",
      samples Noise.tick Noise.output 2 20 (Noise.tick noise) ==
        [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 0, 15, 15, 15, 15, 15]),
    ("noise period table", noiseReload 0 == 1 && noiseReload 15 == 2033),
    ("envelope decay then hold",
      envLevels false 18 == [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0]),
    ("envelope decay then loop",
      envLevels true 18 == [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14]),
    ("length halt", ({ counter := 5, halt := true } : Length).halfFrame.counter == 5 &&
      ({ counter := 5 } : Length).halfFrame.counter == 4),
    ("sweep add", (sw 0x81).target true 0x100 == 0x180),
    ("sweep negate pulse 1 (ones' complement)", (sw 0x89).target true 0x100 == 0x7F),
    ("sweep negate pulse 2 (two's complement)", (sw 0x89).target false 0x100 == 0x80),
    ("sweep mute by target > $7FF even if disabled",
      (sw 0x00).muted false 0x400 && !(sw 0x01).muted false 0x400),
    ("sweep mute by period < 8", (sw 0x00).muted true 7 && !(sw 0x00).muted true 8),
    ("sweep half-frame updates period",
      ((pulseAt 2).write 1 0x81 |>.halfFrame).period == 12 &&
      ((pulseAt 2).write 1 0x80 |>.halfFrame).period == 8) ]

theorem checks_pass : checks.all (·.2) = true := by decide +kernel

def run : IO UInt32 := do
  let mut fails : UInt32 := 0
  for (name, ok) in checks do
    unless ok do
      IO.println s!"  FAIL apu units: {name}"
      fails := fails + 1
  IO.println s!"APU units: {checks.length - fails.toNat}/{checks.length} spot checks pass"
  return fails

end Test.ApuUnits
