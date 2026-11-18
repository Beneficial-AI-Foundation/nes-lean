import Nes.Cpu.Core
import Nes.Ppu.Step
import Nes.Ppu.Data
import Nes.Cart.Mapper
import Nes.Input.Controller
import Nes.Bus.Map
import Nes.Bus.OpenBus
import Nes.Bus.Dma
import Nes.Apu.Apu
import Nes.Frontend.Wav

/-!
# `Nes.System.Nes` — the machine and its master clock

`Nes` bundles the CPU core, the PPU, the cartridge, the console's RAMs (2 KiB work RAM, 2 KiB
CIRAM nametable RAM, 32 B palette RAM), the controllers, the CPU open-bus latch, the master
clock (`Clock`), the frame counter, the OAM-DMA unit (`Nes.Bus.Dma`), the APU (`Nes.Apu.Apu`)
with the DMC DMA unit (`dmcLeft`, `dmcAlign`) and the RESET line. `stepCycle` is the only
clock: one CPU cycle = three PPU dots (NTSC) and one APU cycle, PLAN §3.2.

## Memory representation

The three console RAMs are `ByteArray`s (unboxed bytes, in place when unshared — the PPU's
memories use the same representation, PLAN §10 decision 6 / M1 benchmark: `Vector UInt8` stores
boxed scalars) *with their sizes as structure invariants* (`ram_size` …), so every access is by
a `Fin` index (`Nes.Bus.ramIndex`, `ciramIndex`, `paletteIndex`) and needs no bounds check.

## Clocking (`stepCycle`)

One CPU cycle (the master step):

0. `latchReset` (RESET line);
1. `preDots` (= 2) PPU dots (`ppuDot`: `Ppu.dot`, then the cartridge sees the PPU's A12 line,
   then `frame += 1` if the PPU just reached `(0, 0)`);
2. the APU's cycle (`apuTick` = `Apu.tick`: frame counter, channel timers; before the bus
   access, so that a `$4017` write's reset delay and same-cycle register quirks count as
   `Nes.Apu.FrameCounter` / `Nes.Apu.Apu` specify), then the bus access: while the DMC DMA unit
   is busy (`dmcBusy`, decided before the APU tick), its cycle (`dmcCycle`, below); else while
   the OAM DMA unit is `active`, its access (`dmaCycle`: idle, a get through
   the CPU bus, or a put to `$2004`; the CPU core is halted — not clocked); otherwise the CPU's
   (`cpuCycle`: `Core.busOp`, read or write through the CPU bus below). The value read or
   written is latched on the open bus;
3. the remaining `3 - preDots` (= 1) PPU dot;
4. CPU cycles only: `Core.complete` with the byte read and the interrupt `lines` as they stand
   now;
5. `tick` (`Clock.tick` on the counters, stored unboxed in `Nes` as `clkCpu clkPpu clkApu
   clkOdd`; `Nes.clock` is the `Clock` view): `cpuCycles + 1`, `ppuDots + 3`, `apuHalf + 1`,
   `cpuOdd` flipped.

**Deviation from PLAN §3.2** ("one CPU micro-cycle, then three PPU dots, then …"): the dots are
split 2 before / 1 after the bus access. Evidence (`Test.BlarggPpu`): with `preDots = 2` all ten
`ppu_vbl_nmi` ROMs pass; `preDots = 0`, `1` and `3` each fail `05-nmi_timing`,
`06-suppression`, `07-nmi_on_timing` and `08-nmi_off_timing` (the NMI line is sampled one dot
too early / late relative to the `$2002` / `$2000` access). The APU cycle runs before the bus
access, not after the dots (step 2); DMA/IRQ/NMI lines are resolved by step 2 (DMA) and step 4
(`lines`).

**Interrupt wiring** (`lines`): `nmi = Ppu.nmiLine` (the PPU's `/NMI` output), `irq = cart.irq
|| apuIrq` (wired-OR; `apuIrq = Apu.irq`: frame IRQ or DMC IRQ); the RESET line `resetLine`
(`setResetLine`) is latched into the CPU's `resetPending` at the start of every cycle while asserted (`latchReset`,
the same effect as `lines.reset` in `IntState.sampleCycle`, one φ2 earlier; kept out of
`lines` because a non-constant `reset` there costs ~4% of emulation speed). `reset` is the reset
*button*: a one-shot RESET sequence plus the PPU register clears.

**Loops** (all fuel-based): `runCycles k` (= `stepCycle^k`); `runDots k` (= `runCycles ⌈k/3⌉`:
the step is a whole CPU cycle, so dots are rounded up); `runFrame fuel` runs until the frame
counter changes, i.e. the PPU wrapped to `(0, 0)` — it stops at `(0, d)`, `d ≤ 2`, the dots of
that last cycle after the wrap — or `fuel` cycles elapse (`frameFuel = 29781 ≥ ⌈89342/3⌉`
always suffices); `runFrames k input` runs `k` frames with the controllers set from `input i`
before frame `i`.

## CPU bus (`cpuRead` / `cpuWrite`, decode as `Nes.Bus.decode`)

* `$0000–$1FFF`: work RAM, mirrored every 2 KiB.
* `$2000–$3FFF`: PPU registers (`Ppu.State.cpuRead` / `cpuWrite`); `$2007` reads go through
  `read2007` on the PPU bus below; `$2007` writes perform the returned `VramWrite` on it.
* `$4014` write: OAM DMA from page `v`. `$4016` write: controller strobe. `$4016/$4017` read:
  controller D0 over open bus (`drivenMask`).
* `$4000–$4013`, `$4015`, `$4017` writes: the APU (`Apu.write`; `$4017` gets `!clkOdd` as
  the write-cycle parity, the M2 scaffolding's convention). `$4015` read: `Apu.read4015` (clears the frame IRQ), bit 5 open bus; the value
  is latched like every read (the real 2A03 keeps it off the external bus — not modelled; the
  M2-validated scaffolding did the same). Other `$4000–$4014` reads: open bus.
* `$4018–$FFFF`: cartridge (`Cart.cpuRead` with the open-bus value / `Cart.cpuWrite`).

Every read latches the returned byte on the open bus, every write the written byte.

## DMC DMA (`dmcCycle`; NESdev "DMA")

When the DMC's sample buffer is empty with bytes remaining (`Dmc.dmaRequest`) the DMC DMA unit
halts the CPU on its next *read* cycle (writes are never halted: the request waits). The halted
CPU repeats its read on the halt / dummy / alignment cycles (so `$2007` is read 2–3 extra times,
a held `$4016` read clocks the controller once more — `dmc_dma_during_read4`), then the unit
fetches `dmcAddr` through the CPU bus on a get cycle (even CPU cycle): 3 cycles from a halt on a
get cycle, 4 from a put cycle (`Dmc.dmaStall`). During OAM DMA the CPU is already halted: the
DMC's halt/dummy cycles overlap OAM DMA's, its fetch takes an OAM get cycle, and OAM DMA spends
one cycle realigning (`dmcAlign`): 2 cycles in all. The halted CPU core is not clocked (no
interrupt polling), as during OAM DMA.

## Audio

`Apu.sample` is the mixer output of the current APU state; `runFrameAudio` (= `runFrame` plus
one sample per CPU cycle pushed into a `Frontend.Downsampler`) collects it without slowing
`runFrame`.

## PPU bus (`ppuPeek` / `ppuPoke`, decode as `Nes.Bus.ppuDecode`)

`$0000–$1FFF` cartridge CHR; `$2000–$3EFF` CIRAM at `ciramIndex (cart mirroring)` (four-screen
carts: not supported yet, they fall back to `ciramIndex .fourScreen`); `$3F00–$3FFF` palette RAM
at `paletteIndex` (6 bits stored).

## OAM DMA

`Nes.Bus.Dma`: a `$4014 ← p` write arms `dma.start p clock.cpuOdd` (513 cycles, 514 when the
write's CPU cycle is odd); `stepCycle` runs the unit's cycles (halt/alignment, then 256
get/put pairs through `cpuRead` / `cpuWrite $2004`) instead of CPU cycles.

## Spec (`Nes.System.Proofs.Clock`, `Nes.System.Proofs.Dma`)

* T-SYS-1: `stepCycle` ticks `clock` once; hence `ppuDots = 3 · cpuCycles` and
  `apuHalf = cpuCycles` after any number of cycles from `powerOn` (`T_SYS_1_clock`).
* T-SYS-3: with the PPU counters in range, `runFrame` (fuel ≥ `frameFuel`) advances `frame` by
  exactly 1 and stops at scanline 0, dot ≤ 2; `runFrames k` advances it by `k`.
* T-SYS-2: after `$4014 ← p` (page in work RAM) the CPU is halted 513/514 cycles, OAM holds the
  page (written from `OAMADDR`), the PPU advanced `3 ×` that.
* `powerOn cart`: RAMs zeroed, PPU `State.init` at `(0, 0)`, CPU `Core.powerOn` (RESET sequence
  first), clock and frame counter 0, DMA idle, RESET line released.
-/

namespace Nes.System

open Nes.Bus Nes.Cart

/-- Master-clock counters (PLAN §3.1). Invariant (T-SYS-1): `ppuDots = 3 · cpuCycles`,
`apuHalf = cpuCycles`, `cpuOdd = (cpuCycles odd)`. -/
structure Clock where
  /-- CPU cycles executed (DMA cycles included). -/
  cpuCycles : UInt64 := 0
  /-- PPU dots executed. -/
  ppuDots : UInt64 := 0
  /-- APU half-cycles (= CPU cycles; counted although there is no APU yet). -/
  apuHalf : UInt64 := 0
  /-- Parity of `cpuCycles` (the index of the cycle about to run is odd). -/
  cpuOdd : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- One CPU cycle of the master clock: 3 dots, 1 APU half-cycle. -/
@[inline] def Clock.tick (c : Clock) : Clock :=
  { cpuCycles := c.cpuCycles + 1, ppuDots := c.ppuDots + 3, apuHalf := c.apuHalf + 1,
    cpuOdd := !c.cpuOdd }

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
  /-- Master clock (`stepCycle` is the only thing that advances it), stored as unboxed scalar
  fields so the per-cycle tick updates the machine in place; `Nes.clock` bundles them. -/
  clkCpu : UInt64
  clkPpu : UInt64
  clkApu : UInt64
  clkOdd : Bool
  /-- Frames started: incremented on every PPU dot that reaches `(0, 0)`. -/
  frame : UInt64
  /-- The OAM DMA unit (`$4014`). -/
  dma : OamDma
  /-- The console's RESET line (`true` = asserted). -/
  resetLine : Bool
  /-- The APU (`Nes.Apu.Apu`). -/
  apu : Apu.Apu
  /-- DMC DMA unit: CPU cycles left until (and including) the DMC fetch, once the CPU is halted
  (`0` = not halted; the fetch is the cycle with `dmcLeft = 1`). -/
  dmcLeft : UInt8
  /-- DMC DMA stole an OAM DMA get: OAM DMA spends the next cycle realigning. -/
  dmcAlign : Bool
  ram_size : ram.size = 2048
  ciram_size : ciram.size = 2048
  pal_size : pal.size = 32

/-- The master-clock counters as a `Clock`. -/
@[inline] def Nes.clock (n : Nes) : Clock :=
  { cpuCycles := n.clkCpu, ppuDots := n.clkPpu, apuHalf := n.clkApu, cpuOdd := n.clkOdd }

/-- A `Fin n` index is in bounds of a byte array of size `n`. -/
theorem fin_lt_size {a : ByteArray} {k : Nat} (h : a.size = k) (i : Fin k) : i.val < a.size := by
  rw [h]; exact i.isLt

/-- PPU dots run before the CPU's bus access in each CPU cycle (the rest run after it). -/
def preDots : Nat := 2

namespace Nes

/-! ### DMC DMA (`dmcCycle`; NESdev "DMA")

When the DMC's sample buffer is empty with bytes remaining (`Dmc.dmaRequest`) the DMC DMA unit
halts the CPU on its next *read* cycle (writes are never halted: the request waits). The halted
CPU repeats its read on the halt / dummy / alignment cycles (so `$2007` is read 2–3 extra times,
a held `$4016` read clocks the controller once more — `dmc_dma_during_read4`), then the unit
fetches `dmcAddr` through the CPU bus on a get cycle (even CPU cycle): 3 cycles from a halt on a
get cycle, 4 from a put cycle (`Dmc.dmaStall`). During OAM DMA the CPU is already halted: the
DMC's halt/dummy cycles overlap OAM DMA's, its fetch takes an OAM get cycle, and OAM DMA spends
one cycle realigning (`dmcAlign`): 2 cycles in all. The halted CPU core is not clocked (no
interrupt polling), as during OAM DMA.

## Audio

`Apu.sample` is the mixer output of the current APU state; `runFrameAudio` (= `runFrame` plus
one sample per CPU cycle pushed into a `Frontend.Downsampler`) collects it without slowing
`runFrame`.

## PPU bus -/

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

/-- `Ppu.dot` reading this console's memories. Deliberately *not* `@[inline]`: compiled on its
own, its body gets `Ppu.dot` specialized to the concrete readers (no closures, no `lean_apply`),
with the specialization closing over `cart ciram pal` only — not the whole `Nes`, which would
keep `ppu` shared during the dot and copy the PPU state (and its 60 KiB frame) on every dot. -/
def ppuDotWith (cart : Cart) (ciram : ByteArray) (h : ciram.size = 2048) (pal : ByteArray)
    (hp : pal.size = 32) (ppu : Ppu.State) : Ppu.State :=
  Ppu.dot (fun a => ppuPeek cart ciram h a) (fun i => palPeek pal hp i) ppu

/-- `Cart.ppuA12`, out of line: compiled on its own (cart owned and unshared on entry) the cart,
cart-state and mapper cells are updated in place; inlined into `ppuDot`, the nested projections
are hoisted above the outer cell's reset, so the inner cells look shared and are reallocated
on every dot. -/
@[noinline] def cartA12 (c : Cart) (b : Bool) : Cart := c.ppuA12 b

/-- One PPU dot; the cartridge then sees A12. -/
@[inline] def ppuDot (n : Nes) : Nes :=
  let ppu := ppuDotWith n.cart n.ciram n.ciram_size n.pal n.pal_size n.ppu
  { n with ppu, cart := cartA12 n.cart ppu.a12,
           frame := if ppu.dot == 0 && ppu.scanline == 0 then n.frame + 1 else n.frame }

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
    let rd := Ppu.State.read2007At n.clkCpu (fun a => ppuPeek n.cart n.ciram n.ciram_size a)
      (fun i => palPeek n.pal n.pal_size i)
    let (ppu, v) := n.ppu.cpuRead rd a
    ({ n with ppu }, v)
  else if a < 0x4018 then
    if a == 0x4016 then
      let (pads, v) := n.pads.read .p1
      ({ n with pads }, mergeOpen Input.drivenMask v n.bus.last)
    else if a == 0x4017 then
      let (pads, v) := n.pads.read .p2
      ({ n with pads }, mergeOpen Input.drivenMask v n.bus.last)
    else if a == 0x4015 then
      let (apu, v) := n.apu.read4015
      ({ n with apu }, v ||| (n.bus.last &&& 0x20))
    else (n, n.bus.last)   -- write-only APU registers
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
    if a == 0x4014 then { n with dma := n.dma.start v n.clkOdd }
    else if a == 0x4016 then { n with pads := n.pads.write4016 v }
    -- `$4017` parity: `!clkOdd` = the M2 scaffolding's convention (its cycle counter had
    -- already ticked for the write cycle); blargg's jitter tests pass with either parity.
    else { n with apu := n.apu.write a v (!n.clkOdd) }
  else { n with cart := n.cart.cpuWrite a v n.clkCpu }

/-- IRQ output of the APU (frame counter / DMC). -/
@[inline] def apuIrq (n : Nes) : Bool := n.apu.irq

/-- Interrupt lines seen by the CPU's `Core.complete`: NMI from the PPU, IRQ = mapper IRQ OR
APU IRQ (wired-OR). RESET is latched by `latchReset` at the start of each cycle instead (a
constant `reset := false` here keeps the inlined `Core.complete` ~4% faster). -/
@[inline] def lines (n : Nes) : Cpu.IntLines :=
  { nmi := n.ppu.nmiLine, irq := n.cart.irq || n.apuIrq, reset := false }

/-- While the console's RESET line is asserted, the CPU latches a RESET request (its
`resetPending`, as `IntState.sampleCycle` does for `lines.reset`) every cycle. -/
@[inline] def latchReset (n : Nes) : Nes :=
  if n.resetLine then
    { n with cpu := { n.cpu with ints := { n.cpu.ints with resetPending := true } } }
  else n

/-! ### Clock -/

/-- The rest of a DMA cycle (CPU halted): the DMA unit's bus access, then the remaining dots. -/
@[noinline] def dmaCycle (n : Nes) : Nes :=
  match n.dma.op with
  | .idle => ppuDots (3 - preDots) { n with dma := n.dma.complete 0 }
  | .read a =>
    let (n, v) := n.cpuRead a
    ppuDots (3 - preDots) { n with bus := n.bus.latch v, dma := n.dma.complete v }
  | .write v =>
    let n := n.cpuWrite 0x2004 v
    ppuDots (3 - preDots) { n with bus := n.bus.latch v, dma := n.dma.complete v }

/-- The rest of an ordinary cycle: the CPU's bus access, the remaining dots, CPU completion.
(Specification form; `stepCycle` inlines it together with the clock tick, `stepCycle_eq`.) -/
@[inline] def cpuCycle (n : Nes) : Nes :=
  match n.cpu.busOp with
  | .read a =>
    let (n, v) := n.cpuRead a
    let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
    { n with cpu := n.cpu.complete n.lines v }
  | .write a v =>
    let n := n.cpuWrite a v
    let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
    { n with cpu := n.cpu.complete n.lines v }

/-- `Apu.tick`, out of line (in place on the unshared APU, as `cartA12`). -/
@[noinline] def apuStep (a : Apu.Apu) : Apu.Apu := a.tick

/-- The APU's cycle (it runs before the cycle's bus access: `Apu.tick` doc). -/
@[inline] def apuTick (n : Nes) : Nes := { n with apu := apuStep n.apu }

/-- Is the DMC DMA unit using this cycle? (A fetch is requested, or under way, or OAM DMA must
realign after a stolen get.) Decided at the start of the cycle, from the state the previous
cycle left. -/
@[inline] def dmcBusy (n : Nes) : Bool := n.dmcLeft != 0 || n.dmcAlign || n.apu.dmc.dmaRequest

/-- A halted CPU cycle of the DMC DMA (halt / dummy / alignment, OAM DMA not running): the CPU's
pending read is repeated on the bus (NESdev "DMA": the halted 6502 keeps driving its read
address), except that a *repeated* read of `$4016/$4017` has no effect (the controller ports
are clocked once per run of consecutive reads, `dmc_dma_during_read4/dma_4016_read`). `first`:
the halt cycle itself (a normal read). -/
@[inline] def stallRead (n : Nes) (first : Bool) : Nes :=
  match n.cpu.busOp with
  | .read a =>
    if !first && (a == 0x4016 || a == 0x4017) then ppuDots (3 - preDots) n
    else
      let (n, v) := n.cpuRead a
      ppuDots (3 - preDots) { n with bus := n.bus.latch v }
  | .write _ _ => ppuDots (3 - preDots) n

/-- A cycle of the DMC DMA unit (`dmcBusy`), after the `preDots` dots and the APU tick:

* `dmcLeft = 1`: the **fetch** (a get cycle): `cpuRead dmcAddr`, delivered to the DMC. If OAM
  DMA is running and was about to do a get, that get is stolen (OAM DMA is not advanced) and
  OAM DMA realigns on the next cycle (`dmcAlign`): the documented 2-cycle cost; an OAM halt /
  alignment cycle simply elapses alongside.
* `dmcLeft > 1`: a halt / dummy / alignment cycle: OAM DMA's cycle if it runs, else the halted
  CPU's repeated read (`stallRead`).
* `dmcAlign`: OAM DMA's realignment cycle (no bus access).
* otherwise a fetch is requested: the DMA unit tries to **halt** the CPU. While OAM DMA runs the
  CPU is already halted; else only a read cycle can be halted — a write cycle runs normally and
  the request waits. The halt cycle starts the count `Dmc.dmaStall` (3 if the halt is on a get
  cycle — halt, dummy, fetch — or 4 on a put cycle — halt, dummy, alignment, fetch). Get cycles
  are the even CPU cycles (`clkOdd = false`), as for OAM DMA. -/
@[noinline] def dmcCycle (n : Nes) : Nes :=
  let k := n.dmcLeft
  if k == 1 then
    let oamGet := n.dma.active && (match n.dma.op with | .idle => false | _ => true)
    let oamIdle := n.dma.active && !oamGet
    let (n, v) := n.cpuRead n.apu.dmc.dmaAddr
    ppuDots (3 - preDots)
      { n with bus := n.bus.latch v, apu := n.apu.dmcDmaComplete v, dmcLeft := 0,
               dmcAlign := oamGet, dma := if oamIdle then n.dma.complete 0 else n.dma }
  else if k != 0 then
    let n := { n with dmcLeft := k - 1 }
    if n.dma.active then n.dmaCycle else n.stallRead false
  else if n.dmcAlign then
    ppuDots (3 - preDots) { n with dmcAlign := false }
  else
    let len := Apu.Dmc.dmaStall (!n.clkOdd) false false
    if n.dma.active then { n with dmcLeft := len - 1 }.dmaCycle
    else match n.cpu.busOp with
      | .read _ => { n with dmcLeft := len - 1 }.stallRead true
      | .write _ _ => n.cpuCycle

/-- Advance the master clock by one CPU cycle (`Clock.tick` on the stored counters). -/
@[inline] def tick (n : Nes) : Nes :=
  { n with clkCpu := n.clkCpu + 1, clkPpu := n.clkPpu + 3, clkApu := n.clkApu + 1,
           clkOdd := !n.clkOdd }

/-- One CPU cycle (the master step): RESET latch, `preDots` dots, the APU's cycle, the bus
access of the CPU (or of the DMC DMA unit / the OAM DMA unit while they run), the remaining
dots, CPU completion, clock tick. Equal to
`tick ∘ (if dmcBusy then dmcCycle else if dma.active then dmaCycle else cpuCycle) ∘ apuTick`
after `ppuDots preDots ∘ latchReset` (the branch is decided before the APU tick); the CPU branch
is written out so that the completion and the tick are one in-place update. -/
def stepCycle (n : Nes) : Nes :=
  let n := ppuDots preDots n.latchReset
  if n.dmcBusy then n.apuTick.dmcCycle.tick
  else if n.dma.active then n.apuTick.dmaCycle.tick
  else
    let n := n.apuTick
    match n.cpu.busOp with
    | .read a =>
      let (n, v) := n.cpuRead a
      let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
      { n with cpu := n.cpu.complete n.lines v, clkCpu := n.clkCpu + 1, clkPpu := n.clkPpu + 3,
               clkApu := n.clkApu + 1, clkOdd := !n.clkOdd }
    | .write a v =>
      let n := n.cpuWrite a v
      let n := ppuDots (3 - preDots) { n with bus := n.bus.latch v }
      { n with cpu := n.cpu.complete n.lines v, clkCpu := n.clkCpu + 1, clkPpu := n.clkPpu + 3,
               clkApu := n.clkApu + 1, clkOdd := !n.clkOdd }

/-- `k` CPU cycles. -/
def runCycles : Nat → Nes → Nes
  | 0, n => n
  | k + 1, n => runCycles k n.stepCycle

/-- At least `k` PPU dots: `⌈k / 3⌉` whole CPU cycles (the step is one CPU cycle). -/
def runDots (k : Nat) (n : Nes) : Nes := runCycles ((k + 2) / 3) n

/-- Fuel that always suffices for `runFrame` (`Nes.System.Proofs.Clock.T_SYS_3_frame`): a
frame is at most 89342 dots, `⌈89342 / 3⌉ = 29781` cycles. -/
def frameFuel : Nat := 29781

/-- Clear the frontend's frame-ready flag. -/
@[inline] def clearFrameReady (n : Nes) : Nes := { n with ppu := { n.ppu with frameReady := false } }

/-- Run until the PPU starts a new frame (reaches `(0, 0)`; the cycle that gets there is
completed, so the PPU stops at `(0, d)` with `d < 3`), at most `fuel` cycles. `frameReady` is
cleared on return. -/
def runFrame (n : Nes) (fuel : Nat := frameFuel) : Nes :=
  go fuel n.frame n
where
  go : Nat → UInt64 → Nes → Nes
    | 0, _, n => n
    | k + 1, f, n =>
      let n := n.stepCycle
      if n.frame != f then n.clearFrameReady else go k f n

/-- `runFrame` collecting audio: after every cycle the APU's sample (`Apu.sample`) is pushed
into the downsampler `ds`. Same machine trajectory as `runFrame` (`runFrameAudio_fst`). -/
def runFrameAudio (n : Nes) (ds : Frontend.Downsampler) (fuel : Nat := frameFuel) :
    Nes × Frontend.Downsampler :=
  go fuel n.frame n ds
where
  go : Nat → UInt64 → Nes → Frontend.Downsampler → Nes × Frontend.Downsampler
    | 0, _, n, ds => (n, ds)
    | k + 1, f, n, ds =>
      let n := n.stepCycle
      let ds := ds.push n.apu.sample
      if n.frame != f then (n.clearFrameReady, ds) else go k f n ds

theorem runFrameAudio_go_fst (k : Nat) (f : UInt64) (n : Nes) (ds : Frontend.Downsampler) :
    (runFrameAudio.go k f n ds).1 = runFrame.go k f n := by
  induction k generalizing n ds with
  | zero => rfl
  | succ k ih =>
    simp only [runFrameAudio.go, runFrame.go]
    split <;> simp [ih]

/-- `runFrameAudio` runs the machine exactly as `runFrame`. -/
theorem runFrameAudio_fst (n : Nes) (ds : Frontend.Downsampler) (fuel : Nat) :
    (n.runFrameAudio ds fuel).1 = n.runFrame fuel :=
  runFrameAudio_go_fst _ _ _ _

/-- `k` frames; before frame `i` (0-based within this call) the controllers are set to
`input i` (player 1, player 2). -/
def runFrames (k : Nat) (input : Nat → UInt8 × UInt8) (n : Nes) : Nes :=
  go 0 k n
where
  go : Nat → Nat → Nes → Nes
    | _, 0, n => n
    | i, k + 1, n =>
      let (b1, b2) := input i
      go (i + 1) k ({ n with pads := n.pads.setButtons b1 b2 }.runFrame)

/-- Power-on state with `cart` inserted. -/
def powerOn (cart : Cart) : Nes :=
  { cpu := Cpu.Core.powerOn Cpu.State.init, ppu := Ppu.State.init, cart,
    ram := Ppu.zeroBytes 2048, ciram := Ppu.zeroBytes 2048, pal := Ppu.zeroBytes 32,
    pads := {}, bus := {}, clkCpu := 0, clkPpu := 0, clkApu := 0, clkOdd := false,
    frame := 0, dma := {}, resetLine := false, apu := Apu.Apu.powerOn, dmcLeft := 0,
    dmcAlign := false,
    ram_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data],
    ciram_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data],
    pal_size := by simp [Ppu.zeroBytes, ← ByteArray.size_data] }

/-- Drive the console's RESET line (`true` = asserted). While asserted the CPU latches RESET
every cycle (`latchReset`; it re-enters the RESET sequence until released). -/
@[inline] def setResetLine (n : Nes) (b : Bool) : Nes := { n with resetLine := b }

/-- Warm reset (the console's reset button): CPU RESET sequence; the PPU's `$2000`/`$2001`
and write toggle are cleared (NESdev "PPU power up state"); the APU is reset (`Apu.reset`:
`$4015 ← 0`, `$4017` rewritten) and a DMC DMA in progress is dropped. -/
def reset (n : Nes) : Nes :=
  { n with cpu := n.cpu.reset,
           ppu := { n.ppu with ctrl := 0, mask := 0, w := false, readBuffer := 0 },
           apu := n.apu.reset, dmcLeft := 0, dmcAlign := false }

end Nes

end Nes.System
