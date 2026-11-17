import Nes.Cpu.Core
import Nes.Ppu.Step
import Nes.Ppu.Data
import Nes.Cart.Mapper
import Nes.Input.Controller
import Nes.Bus.Map
import Nes.Bus.OpenBus

/-!
# `Nes.System.Nes` — the machine and its clock (minimal M3 version)

`Nes` bundles the CPU core, the PPU, the cartridge, the console's RAMs (2 KiB work RAM, 2 KiB
CIRAM nametable RAM, 32 B palette RAM), the controllers, the CPU open-bus latch, the CPU-cycle
counter and the OAM-DMA unit. `stepCycle` is the only clock: one CPU cycle = three PPU dots
(NTSC), PLAN §3.2. This is the M3 integration point; M4 extends it (APU, DMA details, save
states, T-SYS-*).

## Memory representation

The three console RAMs are `ByteArray`s (unboxed bytes, in place when unshared — the PPU's
memories use the same representation, PLAN §10 decision 6 / M1 benchmark: `Vector UInt8` stores
boxed scalars) *with their sizes as structure invariants* (`ram_size` …), so every access is by
a `Fin` index (`Nes.Bus.ramIndex`, `ciramIndex`, `paletteIndex`) and needs no bounds check.

## Clocking (`stepCycle`)

One CPU cycle:

1. `preDots` (= 2) PPU dots (`Ppu.dot`; after each, the cartridge sees the PPU's A12 line);
2. the CPU's bus access (`Core.busOp`): read or write through the CPU bus below; the value
   read or written is latched on the open bus — or, while OAM DMA runs, the DMA unit's access
   instead (the CPU is halted);
3. the remaining `3 - preDots` (= 1) PPU dot;
4. `Core.complete` with the byte read and the interrupt lines as they stand now
   (`nmi = Ppu.nmiOut`, `irq = cart IRQ`; no APU yet); not called on DMA cycles.

Interleave evidence (`Test.BlarggPpu`): with `preDots = 2` all ten `ppu_vbl_nmi` ROMs pass;
`preDots = 0`, `1` and `3` each fail `05-nmi_timing`, `06-suppression`, `07-nmi_on_timing` and
`08-nmi_off_timing` (the NMI line is sampled one dot too early / late relative to the
`$2002` / `$2000` access).

## CPU bus (`cpuRead` / `cpuWrite`, decode as `Nes.Bus.decode`)

* `$0000–$1FFF`: work RAM, mirrored every 2 KiB.
* `$2000–$3FFF`: PPU registers (`Ppu.State.cpuRead` / `cpuWrite`); `$2007` reads go through
  `read2007` on the PPU bus below; `$2007` writes perform the returned `VramWrite` on it.
* `$4014` write: OAM DMA from page `v`. `$4016` write: controller strobe. `$4016/$4017` read:
  controller D0 over open bus (`drivenMask`).
* Other `$4000–$4017` (APU): **not modelled yet** — reads return open bus, writes are ignored
  (M5 adds the APU; `$4015` reads should not latch the external bus — irrelevant until then).
* `$4018–$FFFF`: cartridge (`Cart.cpuRead` with the open-bus value / `Cart.cpuWrite`).

Every read latches the returned byte on the open bus, every write the written byte.

## PPU bus (`ppuPeek` / `ppuPoke`, decode as `Nes.Bus.ppuDecode`)

`$0000–$1FFF` cartridge CHR; `$2000–$3EFF` CIRAM at `ciramIndex (cart mirroring)` (four-screen
carts: not supported yet, they fall back to `ciramIndex .fourScreen`); `$3F00–$3FFF` palette RAM
at `paletteIndex` (6 bits stored).

## OAM DMA (minimal; TODO M4 DMA item / T-SYS-2)

A `$4014` write arms `dmaCount := 513` (`514` when the write is on an odd CPU cycle — the
alignment cycle). The following cycles are DMA cycles instead of CPU cycles: while
`dmaCount > 512` an idle (halt/alignment) cycle; then 512 cycles alternating a read of
`page·256 + i` through the CPU bus and a write of that byte to `$2004`. The CPU core is not
clocked during DMA (its interrupt detectors do not sample — an approximation; no DMC DMA).

## Spec

* `stepCycle` advances the PPU by exactly 3 dots and `clock` by 1.
* `runCycles k` is `stepCycle` iterated `k` times.
* `runFrame fuel` runs cycles until the PPU raises `frameReady` (vblank start) or `fuel`
  cycles elapse, then clears `frameReady`.
* `powerOn cart`: RAMs zeroed, PPU `State.init`, CPU `Core.powerOn` (RESET sequence first).
-/

namespace Nes.System

open Nes.Bus Nes.Cart

/-- The whole console. -/
structure Nes where
  cpu : Cpu.Core
  ppu : Ppu.State
  cart : Cart
  /-- 2 KiB work RAM. -/
  ram : ByteArray
  /-- 2 KiB nametable RAM. -/
  ciram : ByteArray
  /-- 32 B palette RAM. -/
  pal : ByteArray
  pads : Input.State
  bus : OpenBus
  /-- CPU cycles executed (DMA cycles included). -/
  clock : UInt64
  /-- OAM DMA: source page, remaining cycles (0 = idle), byte in flight. -/
  dmaPage : UInt8
  dmaCount : UInt16
  dmaLatch : UInt8
  ram_size : ram.size = 2048
  ciram_size : ciram.size = 2048
  pal_size : pal.size = 32

/-- A `Fin n` index is in bounds of a byte array of size `n`. -/
theorem fin_lt_size {a : ByteArray} {k : Nat} (h : a.size = k) (i : Fin k) : i.val < a.size := by
  rw [h]; exact i.isLt

/-- PPU dots run before the CPU's bus access in each CPU cycle (the rest run after it). -/
def preDots : Nat := 2

namespace Nes

/-! ### PPU bus -/

/-- PPU-bus read of `a` (14 bits): CHR, or a CIRAM nametable cell (palette addresses read the
nametable underneath; the palette is `palPeek`). -/
@[inline] def ppuPeek (cart : Cart) (ciram : ByteArray) (h : ciram.size = 2048) (a : UInt16) :
    UInt8 :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then cart.ppuRead a
  else ciram[(ciramIndex cart.mirroring a).val]'(fin_lt_size h (ciramIndex cart.mirroring a))

/-- Palette RAM read at index `i` (0–31; `$10/$14/$18/$1C` aliased). -/
@[inline] def palPeek (pal : ByteArray) (h : pal.size = 32) (i : UInt8) : UInt8 :=
  let j := paletteIndex i.toUInt16
  pal[j.val]'(fin_lt_size h j)

/-- PPU-bus write (`$2007`). -/
@[inline] def ppuPoke (n : Nes) (a : UInt16) (v : UInt8) : Nes :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then { n with cart := n.cart.ppuWrite a v }
  else if a < 0x3F00 then
    let i := ciramIndex n.cart.mirroring a
    { n with ciram := n.ciram.set i.val v (fin_lt_size n.ciram_size i),
             ciram_size := by rw [ByteArray.size_set']; exact n.ciram_size }
  else
    let i := paletteIndex a
    { n with pal := n.pal.set i.val (v &&& 0x3F) (fin_lt_size n.pal_size i),
             pal_size := by rw [ByteArray.size_set']; exact n.pal_size }

/-- One PPU dot; the cartridge then sees A12. -/
@[inline] def ppuDot (n : Nes) : Nes :=
  let ppu := Ppu.dot (ppuPeek n.cart n.ciram n.ciram_size) (palPeek n.pal n.pal_size) n.ppu
  { n with ppu, cart := n.cart.ppuA12 ppu.a12 }

/-- `k` PPU dots (`k ≤ 3`). -/
@[inline] def ppuDots : Nat → Nes → Nes
  | 0, n => n
  | k + 1, n => ppuDots k n.ppuDot

/-! ### CPU bus -/

/-- CPU read of `a` (side effects included); the caller latches the open bus. -/
@[inline] def cpuRead (n : Nes) (a : UInt16) : Nes × UInt8 :=
  if a < 0x2000 then
    let i := ramIndex a
    (n, n.ram[i.val]'(fin_lt_size n.ram_size i))
  else if a < 0x4000 then
    let rd := Ppu.State.read2007 (ppuPeek n.cart n.ciram n.ciram_size) (palPeek n.pal n.pal_size)
    let (ppu, v) := n.ppu.cpuRead rd a
    ({ n with ppu }, v)
  else if a < 0x4018 then
    if a == 0x4016 then
      let (pads, v) := n.pads.read .p1
      ({ n with pads }, mergeOpen Input.drivenMask v n.bus.last)
    else if a == 0x4017 then
      let (pads, v) := n.pads.read .p2
      ({ n with pads }, mergeOpen Input.drivenMask v n.bus.last)
    else (n, n.bus.last)   -- APU: not modelled yet
  else (n, n.cart.cpuRead a n.bus.last)

/-- CPU write of `v` to `a`; the caller latches the open bus. -/
@[inline] def cpuWrite (n : Nes) (a : UInt16) (v : UInt8) : Nes :=
  if a < 0x2000 then
    let i := ramIndex a
    { n with ram := n.ram.set i.val v (fin_lt_size n.ram_size i),
             ram_size := by rw [ByteArray.size_set']; exact n.ram_size }
  else if a < 0x4000 then
    let (ppu, wr) := n.ppu.cpuWrite a v
    let n := { n with ppu }
    match wr with
    | some w => n.ppuPoke w.addr w.data
    | none => n
  else if a < 0x4018 then
    if a == 0x4014 then
      { n with dmaPage := v, dmaCount := if n.clock &&& 1 == 1 then 514 else 513 }
    else if a == 0x4016 then { n with pads := n.pads.write4016 v }
    else n   -- APU: not modelled yet
  else { n with cart := n.cart.cpuWrite a v }

/-- Interrupt lines seen by the CPU. -/
@[inline] def lines (n : Nes) : Cpu.IntLines :=
  { nmi := n.ppu.nmiLine, irq := n.cart.irq, reset := false }

/-! ### Clock -/

/-- The bus access of one DMA cycle (CPU halted). -/
@[inline] def dmaAccess (n : Nes) : Nes :=
  let c := n.dmaCount
  if c > 512 then { n with dmaCount := c - 1 }
  else if c &&& 1 == 0 then
    let a := (n.dmaPage.toUInt16 <<< 8) ||| ((512 - c) >>> 1)
    let (n, v) := n.cpuRead a
    { n with bus := n.bus.latch v, dmaLatch := v, dmaCount := c - 1 }
  else
    let v := n.dmaLatch
    let n := n.cpuWrite 0x2004 v
    { n with bus := n.bus.latch v, dmaCount := c - 1 }

/-- One CPU cycle: `preDots` dots, the bus access, the remaining dots, CPU completion. -/
def stepCycle (n : Nes) : Nes :=
  let n := ppuDots preDots n
  if n.dmaCount != 0 then
    let n := ppuDots (3 - preDots) n.dmaAccess
    { n with clock := n.clock + 1 }
  else
    match n.cpu.busOp with
    | .read a =>
      let (n, v) := n.cpuRead a
      let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
      { n with cpu := n.cpu.complete n.lines v, clock := n.clock + 1 }
    | .write a v =>
      let n := n.cpuWrite a v
      let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
      { n with cpu := n.cpu.complete n.lines v, clock := n.clock + 1 }

/-- `k` CPU cycles. -/
def runCycles : Nat → Nes → Nes
  | 0, n => n
  | k + 1, n => runCycles k n.stepCycle

/-- Run until the PPU signals a finished frame (vblank start), at most `fuel` cycles;
`frameReady` is cleared on return. -/
def runFrame (n : Nes) (fuel : Nat := 40000) : Nes :=
  go fuel n
where
  go : Nat → Nes → Nes
    | 0, n => n
    | k + 1, n =>
      let n := n.stepCycle
      if n.ppu.frameReady then { n with ppu := { n.ppu with frameReady := false } }
      else go k n

/-- Power-on state with `cart` inserted. -/
def powerOn (cart : Cart) : Nes :=
  { cpu := Cpu.Core.powerOn Cpu.State.init, ppu := Ppu.State.init, cart,
    ram := Ppu.zeroBytes 2048, ciram := Ppu.zeroBytes 2048, pal := Ppu.zeroBytes 32,
    pads := {}, bus := {}, clock := 0, dmaPage := 0, dmaCount := 0, dmaLatch := 0,
    ram_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data],
    ciram_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data],
    pal_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data] }

/-- Warm reset (the console's reset button): CPU RESET sequence; the PPU's `$2000`/`$2001`
and write toggle are cleared (NESdev "PPU power up state"). -/
def reset (n : Nes) : Nes :=
  { n with cpu := n.cpu.reset,
           ppu := { n.ppu with ctrl := 0, mask := 0, w := false, readBuffer := 0 } }

end Nes

end Nes.System
