/-!
# `Nes.Bus.Dma` — the OAM DMA unit (`$4014`) as an explicit state machine

Reference: NESdev wiki, "PPU registers" (`OAMDMA`) and "DMA" (OAM DMA timing).

A CPU write of `p` to `$4014` starts a transfer of the 256 bytes `$pp00–$ppFF` to `$2004`
(OAMDATA, so the bytes land at `OAMADDR, OAMADDR+1, …` mod 256). The 2A03 halts the CPU and
runs the DMA unit on the bus instead:

* one **halt** cycle, plus one **alignment** cycle when the `$4014` write landed on an odd CPU
  cycle (the unit must start its get/put pairs on a get cycle);
* 256 **get/put pairs**: a read of `$pp00 + i` *through the CPU bus* (so the source can be work
  RAM, cartridge RAM/ROM, or even I/O registers, with their side effects), then a write of the
  byte read to `$2004`.

Total: **513** CPU cycles (write on an even cycle) or **514** (odd), after which the CPU core
resumes exactly where it was halted.

## The machine

`OamDma` holds `page`, `left` (cycles still to run; `0` = idle) and `latch` (the byte in
flight). Cycle `left = c` performs `op`:

* `c > 512`: `.idle` (halt / alignment cycle; no bus access);
* `c ≤ 512`, `c` even: `.read (page·256 + (512 - c)/2)` (a *get*);
* `c ≤ 512`, `c` odd: `.write latch` to `$2004` (a *put*).

`complete d v` ends the cycle (`left - 1`; on a get, `latch := v`, the byte read). The system
(`Nes.System.Nes.stepCycle`) performs the bus access of `op` and calls `complete`; while
`active` it does not clock the CPU core.

## Deviations / TODO

* The halt cycle performs no bus access (real hardware repeats the halted CPU read — visible
  only for read-sensitive registers such as `$2002`/`$4016`), and the halt is taken on the cycle
  after the `$4014` write even when that cycle is a CPU write (hardware waits for a read cycle).
* **DMC DMA (M5 hook):** the APU's sample fetches steal cycles from (and interleave with) OAM
  DMA — `sprdma_and_dmc_dma`. There is no APU yet; when it lands, `op` gains a priority check
  for a pending DMC fetch (taking the cycle, without advancing `left`, on get cycles).

## Spec (`Nes.System.Proofs.Dma`, T-SYS-2)

* `start p odd` is active for exactly `513` (`odd = false`) / `514` (`odd = true`) `complete`
  steps, whatever bytes are read; the first `1`/`2` steps are `.idle`, then step `k + 2i` reads
  `p·256 + i` and step `k + 2i + 1` writes the byte read at step `k + 2i`.
-/

namespace Nes.Bus

/-- OAM DMA state. -/
structure OamDma where
  /-- Source page (`$pp00–$ppFF`). -/
  page : UInt8 := 0
  /-- CPU cycles still to run (`0` = idle). -/
  left : UInt16 := 0
  /-- The byte read by the last get cycle. -/
  latch : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/-- What the DMA unit does on the bus this cycle. -/
inductive DmaOp where
  /-- Halt / alignment cycle: no bus access. -/
  | idle
  /-- Get: read this CPU address. -/
  | read (a : UInt16)
  /-- Put: write this byte to `$2004`. -/
  | write (v : UInt8)
  deriving Repr, DecidableEq, Inhabited

namespace OamDma

/-- Cycles of a transfer started by a write on an even / odd CPU cycle. -/
@[inline] def length (odd : Bool) : UInt16 := if odd then 514 else 513

/-- The transfer started by a `$4014 ← page` write (`odd`: the write's CPU cycle is odd). -/
@[inline] def start (d : OamDma) (page : UInt8) (odd : Bool) : OamDma :=
  { d with page, left := length odd }

/-- Is a transfer running (the CPU halted)? -/
@[inline] def active (d : OamDma) : Bool := d.left != 0

/-- The bus access of this cycle. -/
@[inline] def op (d : OamDma) : DmaOp :=
  let c := d.left
  if c > 512 then .idle
  else if c &&& 1 == 0 then .read (d.page.toUInt16 * (256 : UInt16) + ((512 - c) >>> 1))
  else .write d.latch

/-- End the cycle; `v` is the byte read (used on get cycles only). -/
@[inline] def complete (d : OamDma) (v : UInt8) : OamDma :=
  let c := d.left
  if c ≤ 512 && c &&& 1 == 0 then { d with left := c - 1, latch := v }
  else { d with left := c - 1 }

end OamDma

end Nes.Bus
