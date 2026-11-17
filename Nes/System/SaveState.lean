import Nes.System.Nes
import Nes.Frontend.Image

/-!
# `Nes.System.SaveState` — save states and input scripts (PLAN §5.5)

A save state is the mutable part of the `Nes` structure, serialized. The cartridge image
(`Cart.rom`) is immutable and is *not* saved: it is supplied again on load.

* `serialize : Nes → ByteArray` — magic `"NESS"`, a format version byte, then every mutable
  field in declaration order;
* `deserialize (rom : Rom) (b : ByteArray) : Option Nes` — the inverse; `none` on a bad magic /
  version, a truncated or over-long buffer, a bad tag, or a RAM of the wrong size (the size
  invariants `ram_size` … of `Nes` and `CartState` are re-established by checking).

T-REF-3 (`Nes.System.Proofs.SaveState`): `deserialize n.cart.rom (serialize n) = some n`, hence
`serialize` is injective on machines with the same cartridge image.

## Format

Little-endian fixed width for `UInt16/32/64`; one byte for `UInt8`; `Bool` = `0/1` (any non-zero
byte decodes as `true`); enumerations and `MapperState` = one tag byte (+ payload); `ByteArray` =
length (unsigned LEB128) + bytes. Structures are the concatenation of their fields.

## Combinator library

`Codec α` bundles `enc : α → List UInt8`, `dec : List UInt8 → Option (α × List UInt8)` (returns
the unconsumed rest) and the law `dec (enc x ++ r) = some (x, r)`. Instances: `UInt8/16/32/64`,
`Bool`, `Unit`, `ByteArray`, `{b : ByteArray // b.size = n}`, products, and `Codec.mapOpt` (a
codec through an embedding `f` with a partial left inverse `g`, `g (f a) = some a`). Every
structure is coded through its tuple of fields (`Codec.map`, the left inverse is the anonymous
constructor, so the law is `rfl` by structure eta, and a new field is a compile error until it
is added here). The round trip of the whole machine is the composition of these laws; no proof
unfolds the full encoding.

Work is on `List UInt8` (proof-friendly); the conversion to `ByteArray` is at the boundary only.

## Input scripts

`runScript obs n script`: one entry `(player 1, player 2)` buttons per frame; sets the
controllers, runs a frame (`runFrame`), records `obs` of the machine. `runScriptHashes` records
the frame hash (`Nes.Frontend.frameHash`): the whole run is a pure function of
`(power-on machine, script)`. Prefix stability (T-REF-4) is in `Nes.System.Proofs.Determinism`.
-/

namespace Nes.System.SaveState

/-- A lawful binary codec. -/
class Codec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  dec_enc : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r)

export Codec (enc dec dec_enc)

attribute [simp] Codec.dec_enc

/-! ### Fixed-width little-endian naturals -/

/-- The low `k` bytes of `n`, little-endian. -/
def encLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: encLE k (n / 256)

/-- Read `k` bytes as a little-endian natural. -/
def decLE : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, l => some (0, l)
  | _ + 1, [] => none
  | k + 1, b :: l =>
    match decLE k l with
    | some (m, r) => some (b.toNat + 256 * m, r)
    | none => none

theorem decLE_encLE (k n : Nat) (r : List UInt8) :
    decLE k (encLE k n ++ r) = some (n % 256 ^ k, r) := by
  induction k generalizing n with
  | zero => simp [encLE, decLE, Nat.mod_one]
  | succ k ih =>
    simp only [encLE, decLE, List.cons_append, ih]
    have : (n % 256).toUInt8.toNat = n % 256 := by simp
    rw [this, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

/-! ### Variable-length naturals (unsigned LEB128) -/

/-- Unsigned LEB128: 7 bits per byte, bit 7 set on every byte but the last. -/
def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encNat (n / 128)
termination_by n
decreasing_by omega

def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: l =>
    if b.toNat < 128 then some (b.toNat, l)
    else
      match decNat l with
      | some (m, r) => some (b.toNat - 128 + 128 * m, r)
      | none => none

theorem decNat_encNat (n : Nat) (r : List UInt8) : decNat (encNat n ++ r) = some (n, r) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encNat]
    by_cases h : n < 128
    · have : n.toUInt8.toNat = n := by simp; omega
      simp [h, decNat, this]
    · have hb : (n % 128 + 128).toUInt8.toNat = n % 128 + 128 := by simp; omega
      have hlt : n / 128 < n := by omega
      simp only [h, ↓reduceIte, List.cons_append, decNat, hb, ih _ hlt]
      simp only [show ¬ (n % 128 + 128 < 128) by omega, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq, and_true]
      omega

/-! ### Basic instances -/

instance : Codec Unit where
  enc _ := []
  dec l := some ((), l)
  dec_enc _ _ := rfl

instance : Codec UInt8 where
  enc x := [x]
  dec
    | x :: r => some (x, r)
    | [] => none
  dec_enc _ _ := rfl

instance : Codec Bool where
  enc b := [if b then 1 else 0]
  dec
    | x :: r => some (x != 0, r)
    | [] => none
  dec_enc b _ := by cases b <;> rfl

instance : Codec UInt16 where
  enc x := encLE 2 x.toNat
  dec l :=
    match decLE 2 l with
    | some (m, r) => some (UInt16.ofNat m, r)
    | none => none
  dec_enc x r := by
    simp only [decLE_encLE]
    rw [Nat.mod_eq_of_lt (by have := x.toNat_lt; simpa using this), UInt16.ofNat_toNat]

instance : Codec UInt32 where
  enc x := encLE 4 x.toNat
  dec l :=
    match decLE 4 l with
    | some (m, r) => some (UInt32.ofNat m, r)
    | none => none
  dec_enc x r := by
    simp only [decLE_encLE]
    rw [Nat.mod_eq_of_lt (by have := x.toNat_lt; simpa using this), UInt32.ofNat_toNat]

instance : Codec UInt64 where
  enc x := encLE 8 x.toNat
  dec l :=
    match decLE 8 l with
    | some (m, r) => some (UInt64.ofNat m, r)
    | none => none
  dec_enc x r := by
    simp only [decLE_encLE]
    rw [Nat.mod_eq_of_lt (by have := x.toNat_lt; simpa using this), UInt64.ofNat_toNat]

instance : Codec ByteArray where
  enc b := encNat b.size ++ b.data.toList
  dec l :=
    match decNat l with
    | some (k, r) => if k ≤ r.length then some (⟨(r.take k).toArray⟩, r.drop k) else none
    | none => none
  dec_enc b r := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    simp only [List.append_assoc, decNat_encNat, List.length_append, hs,
      show b.size ≤ b.size + r.length by omega, ↓reduceIte, List.take_left' hs,
      List.drop_left' hs]

instance [Codec α] [Codec β] : Codec (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec l :=
    match dec l with
    | some (a, r) =>
      match dec r with
      | some (b, r') => some ((a, b), r')
      | none => none
    | none => none
  dec_enc p r := by simp only [List.append_assoc, dec_enc]

/-- A codec through an embedding `f` with a partial left inverse `g`. -/
@[reducible] def Codec.mapOpt [Codec β] (f : α → β) (g : β → Option α) (h : ∀ a, g (f a) = some a) :
    Codec α where
  enc a := enc (f a)
  dec l :=
    match dec l with
    | some (b, r) =>
      match g b with
      | some a => some (a, r)
      | none => none
    | none => none
  dec_enc a r := by simp only [dec_enc, h]

/-- A codec through an embedding `f` with a left inverse `g`. -/
@[reducible] def Codec.map [Codec β] (f : α → β) (g : β → α) (h : ∀ a, g (f a) = a) : Codec α :=
  Codec.mapOpt f (fun b => some (g b)) (fun a => by rw [h])

/-- Byte arrays of a fixed size (the RAMs): the size is checked on decode. -/
instance (n : Nat) : Codec { b : ByteArray // b.size = n } :=
  Codec.mapOpt Subtype.val (fun b => if h : b.size = n then some ⟨b, h⟩ else none)
    (fun a => by simp [a.property])

/-! ### CPU -/

open Nes.Cpu in
instance : Codec Cpu.State :=
  Codec.map (fun s => (s.a, s.x, s.y, s.sp, s.pc, s.p, s.halted))
    (fun (a, x, y, sp, pc, p, halted) => ⟨a, x, y, sp, pc, p, halted⟩) (fun _ => rfl)

instance : Codec Cpu.MicroState :=
  Codec.map
    (fun s => (s.cpu, s.op, s.pos, s.addr, s.base, s.data, s.crossed, s.intPending, s.inInt,
      s.suppressWrites, s.vec))
    (fun (cpu, op, pos, addr, base, data, crossed, intPending, inInt, suppressWrites, vec) =>
      ⟨cpu, op, pos, addr, base, data, crossed, intPending, inInt, suppressWrites, vec⟩)
    (fun _ => rfl)

instance : Codec Cpu.IntState :=
  Codec.map
    (fun s => (s.nmiPrev, s.nmiPending, s.irqPending, s.resetPending, s.pollNmi, s.pollIrq))
    (fun (a, b, c, d, e, f) => ⟨a, b, c, d, e, f⟩) (fun _ => rfl)

/-- Tag of an interrupt kind. -/
def intKindTag : Cpu.IntKind → UInt8
  | .none => 0 | .nmi => 1 | .irq => 2 | .brk => 3 | .reset => 4

def intKindOfTag : UInt8 → Option Cpu.IntKind
  | 0 => some .none | 1 => some .nmi | 2 => some .irq | 3 => some .brk | 4 => some .reset
  | _ => none

instance : Codec Cpu.IntKind :=
  Codec.mapOpt intKindTag intKindOfTag (fun k => by cases k <;> rfl)

instance : Codec Cpu.Core :=
  Codec.map (fun c => (c.ms, c.ints, c.cyc, c.kind, c.iBefore))
    (fun (ms, ints, cyc, kind, iBefore) => ⟨ms, ints, cyc, kind, iBefore⟩) (fun _ => rfl)

/-! ### PPU -/

instance : Codec Ppu.State :=
  Codec.map
    (fun s => (s.ctrl, s.mask, s.status, s.oamAddr, s.v, s.t, s.x, s.w, s.readBuffer, s.ioLatch,
      s.oam, s.secOam, s.bgPatLo, s.bgPatHi, s.bgAttrLo, s.bgAttrHi, s.bgNextTile, s.bgNextAttr,
      s.bgNextLo, s.bgNextHi, s.evalN, s.evalM, s.evalSec, s.evalLatch, s.sprCount, s.sprPatLo,
      s.sprPatHi, s.sprAttr, s.sprX, s.spr0Next, s.spr0Line, s.dot, s.scanline, s.frameOdd,
      s.nmiOut, s.suppressVbl, s.a12, s.frame, s.emphasis, s.frameReady, s.renderLatch,
      s.prevBuffer, s.lastRead2007))
    (fun (ctrl, mask, status, oamAddr, v, t, x, w, readBuffer, ioLatch, oam, secOam, bgPatLo,
        bgPatHi, bgAttrLo, bgAttrHi, bgNextTile, bgNextAttr, bgNextLo, bgNextHi, evalN, evalM,
        evalSec, evalLatch, sprCount, sprPatLo, sprPatHi, sprAttr, sprX, spr0Next, spr0Line, dot,
        scanline, frameOdd, nmiOut, suppressVbl, a12, frame, emphasis, frameReady,
        renderLatch, prevBuffer, lastRead2007) =>
      ⟨ctrl, mask, status, oamAddr, v, t, x, w, readBuffer, ioLatch, oam, secOam, bgPatLo,
        bgPatHi, bgAttrLo, bgAttrHi, bgNextTile, bgNextAttr, bgNextLo, bgNextHi, evalN, evalM,
        evalSec, evalLatch, sprCount, sprPatLo, sprPatHi, sprAttr, sprX, spr0Next, spr0Line, dot,
        scanline, frameOdd, nmiOut, suppressVbl, a12, frame, emphasis, frameReady, renderLatch,
        prevBuffer, lastRead2007⟩)
    (fun _ => rfl)

/-! ### Cartridge -/

instance : Codec Cart.Nrom.State := Codec.map (fun _ => ()) (fun () => ⟨⟩) (fun _ => rfl)

instance : Codec Cart.Cnrom.State := Codec.map (·.bank) (⟨·⟩) (fun _ => rfl)

instance : Codec Cart.Uxrom.State := Codec.map (·.bank) (⟨·⟩) (fun _ => rfl)

instance : Codec Cart.Axrom.State := Codec.map (·.reg) (⟨·⟩) (fun _ => rfl)

instance : Codec Cart.Mmc1.State :=
  Codec.map (fun s => (s.shift, s.count, s.control, s.chr0, s.chr1, s.prg, s.consecCycle))
    (fun (shift, count, control, chr0, chr1, prg, consecCycle) =>
      ⟨shift, count, control, chr0, chr1, prg, consecCycle⟩) (fun _ => rfl)

instance : Codec Cart.Mmc3.State :=
  Codec.map
    (fun s => (s.bankSelect, s.r0, s.r1, s.r2, s.r3, s.r4, s.r5, s.r6, s.r7, s.mirH,
      s.ramProtect, s.irqLatch, s.irqCounter, s.irqReload, s.irqEnabled, s.irqPending,
      s.lowDots))
    (fun (bankSelect, r0, r1, r2, r3, r4, r5, r6, r7, mirH, ramProtect, irqLatch, irqCounter,
        irqReload, irqEnabled, irqPending, lowDots) =>
      ⟨bankSelect, r0, r1, r2, r3, r4, r5, r6, r7, mirH, ramProtect, irqLatch, irqCounter,
        irqReload, irqEnabled, irqPending, lowDots⟩)
    (fun _ => rfl)

open Cart in
/-- Mapper state: tag byte (0 NROM, 1 CNROM, 2 MMC1, 3 UxROM, 4 AxROM, 5 MMC3), then payload. -/
instance : Codec MapperState where
  enc
    | .nrom s => 0 :: enc s
    | .cnrom s => 1 :: enc s
    | .mmc1 s => 2 :: enc s
    | .uxrom s => 3 :: enc s
    | .axrom s => 4 :: enc s
    | .mmc3 s => 5 :: enc s
  dec
    | t :: l =>
      let wrap {σ : Type} [Codec σ] (k : σ → MapperState) : Option (MapperState × List UInt8) :=
        match dec l with
        | some (s, r) => some (k s, r)
        | none => none
      if t == 0 then wrap .nrom else if t == 1 then wrap .cnrom else if t == 2 then wrap .mmc1
      else if t == 3 then wrap .uxrom else if t == 4 then wrap .axrom
      else if t == 5 then wrap .mmc3 else none
    | [] => none
  dec_enc m r := by cases m <;> simp

instance : Codec Cart.CartState :=
  Codec.map
    (fun s => (s.mapper, (⟨s.prgRam, s.prgRam_size⟩ : { b : ByteArray // b.size = 8192 }),
      (⟨s.chrRam, s.chrRam_size⟩ : { b : ByteArray // b.size = 8192 })))
    (fun (mapper, prgRam, chrRam) => ⟨mapper, prgRam.val, chrRam.val, prgRam.property,
      chrRam.property⟩)
    (fun _ => rfl)

/-! ### Controllers, bus, DMA -/

instance : Codec Input.Pad := Codec.map (·.shift) (⟨·⟩) (fun _ => rfl)

instance : Codec Input.State :=
  Codec.map (fun s => (s.strobe, s.p1, s.p2, s.live1, s.live2))
    (fun (strobe, p1, p2, live1, live2) => ⟨strobe, p1, p2, live1, live2⟩) (fun _ => rfl)

instance : Codec Bus.OpenBus := Codec.map (·.last) (⟨·⟩) (fun _ => rfl)

instance : Codec Bus.OamDma :=
  Codec.map (fun s => (s.page, s.left, s.latch)) (fun (page, left, latch) => ⟨page, left, latch⟩)
    (fun _ => rfl)

/-! ### APU -/

instance : Codec Apu.FrameCounter :=
  Codec.map (fun s => (s.cycle, s.resetIn, s.mode5, s.inhibit, s.irq))
    (fun (cycle, resetIn, mode5, inhibit, irq) => ⟨cycle, resetIn, mode5, inhibit, irq⟩)
    (fun _ => rfl)

instance : Codec Apu.Length :=
  Codec.map (fun s => (s.counter, s.halt)) (fun (counter, halt) => ⟨counter, halt⟩) (fun _ => rfl)

instance : Codec Apu.Envelope :=
  Codec.map (fun s => (s.start, s.loop, s.constVol, s.volume, s.divider, s.decay))
    (fun (start, loop, constVol, volume, divider, decay) =>
      ⟨start, loop, constVol, volume, divider, decay⟩) (fun _ => rfl)

instance : Codec Apu.Sweep :=
  Codec.map (fun s => (s.enabled, s.divPeriod, s.negate, s.shift, s.reload, s.divider))
    (fun (enabled, divPeriod, negate, shift, reload, divider) =>
      ⟨enabled, divPeriod, negate, shift, reload, divider⟩) (fun _ => rfl)

instance : Codec Apu.Pulse :=
  Codec.map (fun s => (s.duty, s.seq, s.timer, s.period, s.len, s.env, s.sweep, s.enabled, s.ones))
    (fun (duty, seq, timer, period, len, env, sweep, enabled, ones) =>
      ⟨duty, seq, timer, period, len, env, sweep, enabled, ones⟩) (fun _ => rfl)

instance : Codec Apu.Triangle :=
  Codec.map (fun s => (s.timer, s.period, s.seq, s.len, s.linear, s.linReload, s.linReloadFlag,
      s.control, s.enabled))
    (fun (timer, period, seq, len, linear, linReload, linReloadFlag, control, enabled) =>
      ⟨timer, period, seq, len, linear, linReload, linReloadFlag, control, enabled⟩)
    (fun _ => rfl)

instance : Codec Apu.Noise :=
  Codec.map (fun s => (s.timer, s.reload, s.mode, s.lfsr, s.len, s.env, s.enabled))
    (fun (timer, reload, mode, lfsr, len, env, enabled) =>
      ⟨timer, reload, mode, lfsr, len, env, enabled⟩) (fun _ => rfl)

instance : Codec Apu.Dmc :=
  Codec.map (fun s => (s.irqEnable, s.loop, s.period, s.timer, s.level, s.addrReg, s.lenReg,
      s.curAddr, s.bytesRemaining, s.buffer, s.bufferEmpty, s.shift, s.bitsRemaining, s.silence,
      s.irqFlag))
    (fun (irqEnable, loop, period, timer, level, addrReg, lenReg, curAddr, bytesRemaining,
        buffer, bufferEmpty, shift, bitsRemaining, silence, irqFlag) =>
      ⟨irqEnable, loop, period, timer, level, addrReg, lenReg, curAddr, bytesRemaining, buffer,
        bufferEmpty, shift, bitsRemaining, silence, irqFlag⟩)
    (fun _ => rfl)

instance : Codec Apu.Apu :=
  Codec.map (fun s => (s.fc, s.p1, s.p2, s.tri, s.noise, s.dmc, s.odd, s.haltMask, s.haltVal,
      s.loadMask, s.loadVal))
    (fun (fc, p1, p2, tri, noise, dmc, odd, haltMask, haltVal, loadMask, loadVal) =>
      ⟨fc, p1, p2, tri, noise, dmc, odd, haltMask, haltVal, loadMask, loadVal⟩) (fun _ => rfl)

/-! ### The machine -/

/-- Everything mutable in a `Nes`, as a tuple (the cartridge's image is left out). -/
abbrev Image :=
  Cpu.Core × Ppu.State × Cart.CartState × { b : ByteArray // b.size = 2048 } ×
    { b : ByteArray // b.size = 2048 } × { b : ByteArray // b.size = 32 } × Input.State ×
    Bus.OpenBus × UInt64 × UInt64 × UInt64 × Bool × UInt64 × Bus.OamDma × Bool × Apu.Apu ×
    UInt8 × Bool

/-- The mutable fields of `n`. -/
def toImage (n : Nes) : Image :=
  (n.cpu, n.ppu, n.cart.st, ⟨n.ram, n.ram_size⟩, ⟨n.ciram, n.ciram_size⟩, ⟨n.pal, n.pal_size⟩,
    n.pads, n.bus, n.clkCpu, n.clkPpu, n.clkApu, n.clkOdd, n.frame, n.dma, n.resetLine,
    n.apu, n.dmcLeft, n.dmcAlign)

/-- Rebuild a machine from its mutable fields and the cartridge image. -/
def ofImage (rom : Cart.Rom) : Image → Nes
  | (cpu, ppu, st, ram, ciram, pal, pads, bus, clkCpu, clkPpu, clkApu, clkOdd, frame, dma,
      resetLine, apu, dmcLeft, dmcAlign) =>
    ⟨cpu, ppu, ⟨rom, st⟩, ram.val, ciram.val, pal.val, pads, bus, clkCpu, clkPpu, clkApu, clkOdd,
      frame, dma, resetLine, apu, dmcLeft, dmcAlign, ram.property, ciram.property, pal.property⟩

theorem ofImage_toImage (n : Nes) : ofImage n.cart.rom (toImage n) = n := rfl

/-- File magic `"NESS"`. -/
def magic : List UInt8 := [0x4E, 0x45, 0x53, 0x53]

/-- Format version (bump when a field is added to the machine). -/
def version : UInt8 := 3

/-- The header: magic and version. -/
def header : List UInt8 := magic ++ [version]

/-- The save state as a byte list. -/
def encodeList (n : Nes) : List UInt8 := header ++ enc (toImage n)

/-- Decode a byte list (the whole list must be consumed). -/
def decodeList (rom : Cart.Rom) (l : List UInt8) : Option Nes :=
  if l.take header.length = header then
    match dec (l.drop header.length) with
    | some (img, []) => some (ofImage rom img)
    | _ => none
  else none

end SaveState

namespace Nes

open SaveState

/-- Serialize the mutable state of the machine (not the cartridge image). -/
def serialize (n : Nes) : ByteArray := ⟨(encodeList n).toArray⟩

/-- Rebuild a machine from a save state and the cartridge image it was taken with; `none` if
the buffer is not a well-formed save state. -/
def deserialize (rom : Cart.Rom) (b : ByteArray) : Option Nes := decodeList rom b.data.toList

/-! ### Input scripts -/

/-- Run one frame per script entry `(player 1, player 2)` (buttons set before the frame),
recording `obs` of the machine after each frame. -/
def runScript {α : Type} (obs : Nes → α) : Nes → List (UInt8 × UInt8) → Nes × List α
  | n, [] => (n, [])
  | n, (b1, b2) :: s =>
    let n := { n with pads := n.pads.setButtons b1 b2 }.runFrame
    let r := runScript obs n s
    (r.1, obs n :: r.2)

/-- `runScript` recording the frame hash (`Nes.Frontend.frameHash`) after each frame. -/
def runScriptHashes (n : Nes) (script : List (UInt8 × UInt8)) : Nes × List UInt64 :=
  runScript (fun n => Frontend.frameHash n.ppu.frame) n script

end Nes

end Nes.System
