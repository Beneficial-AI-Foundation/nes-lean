import Nes.Input.Controller

/-!
# `Nes.Input.Proofs.Controller` — standard-controller read protocol

* `controller_reads_in_order`: after strobe 1→0 with live buttons `b`, the first 8 reads of a
  port return bits 0..7 of `b` (A, B, Select, Start, Up, Down, Left, Right).
* `controller_after_8`: every read after those 8 returns 1.
* `controller_strobe_high`: with the strobe high a read returns live button A and leaves the
  state unchanged (nothing advances).

Method: reduce `State.readN` to `Pad.readN` on the selected shift register, close the
8-read byte fact by `decide` over all 256 bytes, and the tail by induction.
-/

namespace Nes.Input.Proofs

open Nes.Input

/-- `n` reads of a bare shift register. -/
def padReadN (p : Pad) : Nat → Pad × List UInt8
  | 0 => (p, [])
  | n + 1 => let (p', v) := p.read; let (p'', vs) := padReadN p' n; (p'', v :: vs)

/-- The live buttons of a port. -/
def liveOf (s : State) : Port → Buttons
  | .p1 => s.live1
  | .p2 => s.live2

/-- The state after the game's latch sequence: set buttons, write 1, write 0. -/
def latched (s : State) (b1 b2 : Buttons) : State :=
  ((s.setButtons b1 b2).write4016 1).write4016 0

theorem latched_eq (s : State) (b1 b2 : Buttons) :
    latched s b1 b2 = { s with strobe := false, live1 := b1, live2 := b2,
                               p1 := { shift := b1 }, p2 := { shift := b2 } } := by
  simp [latched, State.write4016, State.setButtons]

theorem readN_p1 (s : State) (h : s.strobe = false) (n : Nat) :
    s.readN .p1 n = ({ s with p1 := (padReadN s.p1 n).1 }, (padReadN s.p1 n).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [State.readN, State.read, h, padReadN, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ rfl]

theorem readN_p2 (s : State) (h : s.strobe = false) (n : Nat) :
    s.readN .p2 n = ({ s with p2 := (padReadN s.p2 n).1 }, (padReadN s.p2 n).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [State.readN, State.read, h, padReadN, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ rfl]

/-- The 8-read byte fact, exhaustively over all 256 button bytes. -/
theorem pad_read8 : ∀ b : UInt8,
    padReadN { shift := b } 8 =
      ({ shift := 0xFF }, (List.range 8).map fun i => Buttons.bit b i.toUInt8) := by
  decide

theorem pad_readN_ff (k : Nat) :
    padReadN { shift := 0xFF } k = ({ shift := 0xFF }, List.replicate k 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [padReadN, Pad.read]; rw [show ((0xFF : UInt8) >>> 1 ||| 0x80) = 0xFF by decide, ih]; rfl

theorem readN_latched (s : State) (b1 b2 : Buttons) (port : Port) :
    ((latched s b1 b2).readN port 8).2 =
      (List.range 8).map fun i => Buttons.bit (liveOf (latched s b1 b2) port) i.toUInt8 := by
  rw [latched_eq]
  cases port
  · rw [readN_p1 _ rfl]; exact congrArg Prod.snd (pad_read8 b1)
  · rw [readN_p2 _ rfl]; exact congrArg Prod.snd (pad_read8 b2)

/-- After strobe 1→0 with buttons `b1`/`b2`, the first 8 reads of a port return bits 0..7 of
that port's buttons, in order. -/
theorem controller_reads_in_order (s : State) (b1 b2 : Buttons) (port : Port) :
    ((latched s b1 b2).readN port 8).2 =
      (List.range 8).map fun i => Buttons.bit (match port with | .p1 => b1 | .p2 => b2) i.toUInt8 := by
  rw [readN_latched, latched_eq]; cases port <;> rfl

/-- After those 8 reads, the next `k` reads (9th and later) all return 1. -/
theorem controller_after_8 (s : State) (b1 b2 : Buttons) (port : Port) (k : Nat) :
    ((((latched s b1 b2).readN port 8).1).readN port k).2 = List.replicate k 1 := by
  rw [latched_eq]
  cases port
  · rw [readN_p1 (⟨false, ⟨b1⟩, ⟨b2⟩, b1, b2⟩ : State) rfl 8, pad_read8,
      readN_p1 _ rfl, pad_readN_ff]
  · rw [readN_p2 (⟨false, ⟨b1⟩, ⟨b2⟩, b1, b2⟩ : State) rfl 8, pad_read8,
      readN_p2 _ rfl, pad_readN_ff]

/-- With the strobe high, a read returns live button A and the state (shift registers
included) does not change. -/
theorem controller_strobe_high (s : State) (h : s.strobe = true) (port : Port) :
    s.read port = (s, liveOf s port &&& 1) := by
  cases port <;> simp [State.read, h, liveOf]

end Nes.Input.Proofs
