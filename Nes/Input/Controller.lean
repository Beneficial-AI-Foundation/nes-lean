/-!
# Standard controllers (`$4016` / `$4017`)

NESdev "Standard controller". A write to `$4016` sets the strobe (bit 0) for **both** ports.
While the strobe is high the shift registers continuously reload from the live buttons, so a
read returns button A and nothing advances. On the falling edge the buttons are latched; each
read of `$4016` (port 1) / `$4017` (port 2) then returns the next bit in D0, in the order
A, B, Select, Start, Up, Down, Left, Right.

The shift register is modelled as the hardware 4021: a read shifts right and fills bit 7 with
1, so after 8 reads it holds `0xFF` and every further read returns 1 (official-controller
behaviour) with no separate counter.

`read` returns only the driven bits: the value is `0` or `1` and `drivenMask = 0x01`; the CPU
bus integrator fills D1–D7 from open bus.
-/

namespace Nes.Input

/-- Eight buttons packed in a byte: bit 0 = A, 1 = B, 2 = Select, 3 = Start, 4 = Up,
5 = Down, 6 = Left, 7 = Right (the order they are shifted out). -/
abbrev Buttons := UInt8

namespace Buttons

/-- Bit `i` (0 or 1) of the button byte. -/
@[inline] def bit (b : Buttons) (i : UInt8) : UInt8 := (b >>> i) &&& 1

/-- Build from named flags (test helper). -/
@[inline] def mk (a b select start up down left right : Bool) : Buttons :=
  (if a then 0x01 else 0) ||| (if b then 0x02 else 0) ||| (if select then 0x04 else 0) |||
  (if start then 0x08 else 0) ||| (if up then 0x10 else 0) ||| (if down then 0x20 else 0) |||
  (if left then 0x40 else 0) ||| (if right then 0x80 else 0)

/-- Build from a list of flags in shift order (A first); missing entries are released. -/
def ofList (l : List Bool) : Buttons :=
  (l.take 8).zipIdx.foldl (fun acc (p, i) => if p then acc ||| ((1 : UInt8) <<< i.toUInt8) else acc) 0

end Buttons

/-- The D0 bits driven by a controller read; the rest come from open bus. -/
def drivenMask : UInt8 := 0x01

/-- Which controller port: `$4016` or `$4017`. -/
inductive Port where
  | p1 | p2
  deriving DecidableEq, Repr, Inhabited

/-- One controller's 8-bit shift register (bit 0 is the next bit out). -/
structure Pad where
  shift : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Shift one bit out (D0) and fill bit 7 with 1. -/
@[inline] def Pad.read (p : Pad) : Pad × UInt8 :=
  ({ shift := (p.shift >>> 1) ||| 0x80 }, p.shift &&& 1)

/-- Both ports: strobe latch, shift registers, and the live buttons the frontend sets. -/
structure State where
  strobe : Bool := false
  p1 : Pad := {}
  p2 : Pad := {}
  live1 : Buttons := 0
  live2 : Buttons := 0
  deriving DecidableEq, Repr, Inhabited

namespace State

/-- Frontend: set the live buttons for both ports (once per frame). -/
@[inline] def setButtons (s : State) (b1 b2 : Buttons) : State :=
  { s with live1 := b1, live2 := b2 }

/-- CPU write to `$4016`: bit 0 is the strobe. While the strobe is (or was) high the shift
registers reload from the live buttons; on the falling edge that reload is the latch. -/
@[inline] def write4016 (s : State) (v : UInt8) : State :=
  let st := v &&& 1 != 0
  if s.strobe || st then
    { s with strobe := st, p1 := { shift := s.live1 }, p2 := { shift := s.live2 } }
  else s

/-- CPU read of `$4016` (`p1`) / `$4017` (`p2`): the D0 bit (`0`/`1`; mask `drivenMask`).
With the strobe high it is live button A and the state is unchanged. -/
@[inline] def read (s : State) (port : Port) : State × UInt8 :=
  if s.strobe then
    (s, match port with | .p1 => s.live1 &&& 1 | .p2 => s.live2 &&& 1)
  else match port with
    | .p1 => let (p, v) := s.p1.read; ({ s with p1 := p }, v)
    | .p2 => let (p, v) := s.p2.read; ({ s with p2 := p }, v)

/-- `n` consecutive reads of one port, returning the final state and the values in order
(specification helper). -/
def readN (s : State) (port : Port) : Nat → State × List UInt8
  | 0 => (s, [])
  | n + 1 =>
    let (s', v) := s.read port
    let (s'', vs) := s'.readN port n
    (s'', v :: vs)

end State

end Nes.Input
