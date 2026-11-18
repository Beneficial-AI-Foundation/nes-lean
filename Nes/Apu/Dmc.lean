/-!
# `Nes.Apu.Dmc` — the delta modulation channel (DMC) and its DMA interface

References: NESdev wiki, "APU DMC" (registers, output unit, memory reader) and "DMA"
(DMC DMA timing, interaction with OAM DMA).

## Registers

* `$4010` `IL--.RRRR`: IRQ enable (`I`; clearing it also clears the DMC IRQ flag), loop (`L`),
  rate index `R` → NTSC period in CPU cycles
  `428 380 340 320 286 254 226 214 190 160 142 128 106 84 72 54`.
* `$4011` `-DDD.DDDD`: direct load of the 7-bit output level.
* `$4012` `AAAA.AAAA`: sample address `$C000 + A·64`.
* `$4013` `LLLL.LLLL`: sample length `L·16 + 1` bytes.
* `$4015` (via `setEnabled`): enable with bytes remaining `= 0` restarts the sample; disable
  sets bytes remaining to `0`; any `$4015` write clears the DMC IRQ flag.

## Units

* **Timer**: modelled per CPU cycle — reload `period - 1`, so the output unit is clocked
  once every `period` CPU cycles (hardware counts APU cycles with half the value; equivalent).
* **Output unit**: on each timer clock, if the silence flag is clear, bit 0 of the shift
  register adds `+2` (`1`) or `-2` (`0`) to the 7-bit level, skipped when it would leave
  `[0, 127]`; the shift register shifts right; the bits-remaining counter decrements. When it
  reaches `0` a new output cycle starts: bits remaining `:= 8`; if the sample buffer is empty
  the silence flag is set, otherwise it is cleared and the buffer moves into the shift register
  (emptying the buffer).
* **Memory reader**: while the sample buffer is empty and bytes remaining `≠ 0` the DMC
  requests a DMA fetch of `curAddr` (`dmaRequest` / `dmaAddr`). `dmaComplete b` fills the
  buffer, advances the address (`$FFFF` wraps to `$8000`) and decrements bytes remaining; on
  reaching `0` the sample restarts if loop is set, else the IRQ flag is raised if enabled.

## DMC DMA stall (`dmaStall`)

Per NESdev "DMA" (DMC DMA): the DMA unit *halts* the CPU on a read cycle (writes are never
halted, so a request landing on a CPU write slips one cycle per write), then spends a *dummy*
cycle, an optional *alignment* cycle, and the *get* (which must fall on a get cycle):
3 cycles when the halt lands on a get cycle (halt-get, dummy-put, get), 4 when it lands on a
put cycle (an alignment put is needed). During OAM DMA the DMC get takes over one of OAM DMA's
get cycles and costs OAM DMA one extra alignment cycle: 2 cycles. (The 1- and 3-cycle cases at
the very end of OAM DMA are cycle-level effects left to the System integration.)

## Integration (System, later)

Each CPU cycle: if `dmaRequest d`, run the stall of `dmaStall …` cycles, read `dmaAddr d`
through the CPU bus, call `dmaComplete d byte`. `tick` once per CPU cycle; `irq` feeds the IRQ
line.

## Spec (`Nes.Apu.Proofs.Dmc`, T-APU-3)

Address wraps `$FFFF → $8000`; bytes remaining hits `0` exactly after `L·16 + 1` fetches;
loop restarts address/length; IRQ at end of non-looping sample iff enabled; `dmaStall`
values; output in `[0, 127]`.
-/

namespace Nes.Apu

/-- DMC channel state. -/
structure Dmc where
  /-- `$4010` bit 7. -/
  irqEnable : Bool := false
  /-- `$4010` bit 6. -/
  loop : Bool := false
  /-- Timer period in CPU cycles (from the `$4010` rate index). -/
  period : UInt16 := 428
  /-- Timer counter (CPU cycles until the next output clock). -/
  timer : UInt16 := 427
  /-- 7-bit output level. -/
  level : UInt8 := 0
  /-- `$4012` raw value. -/
  addrReg : UInt8 := 0
  /-- `$4013` raw value. -/
  lenReg : UInt8 := 0
  /-- Memory reader: current address. -/
  curAddr : UInt16 := 0xC000
  /-- Memory reader: bytes remaining (`0` = sample finished / channel disabled). -/
  bytesRemaining : UInt16 := 0
  /-- Sample buffer. -/
  buffer : UInt8 := 0
  /-- Sample buffer empty flag. -/
  bufferEmpty : Bool := true
  /-- Output unit shift register. -/
  shift : UInt8 := 0
  /-- Output unit bits-remaining counter. -/
  bitsRemaining : UInt8 := 8
  /-- Output unit silence flag. -/
  silence : Bool := true
  /-- DMC interrupt flag. -/
  irqFlag : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Dmc

/-- NTSC rate table (CPU cycles), NESdev "APU DMC". -/
@[inline] def ratePeriod (i : UInt8) : UInt16 :=
  match i &&& 0x0F with
  | 0 => 428 | 1 => 380 | 2 => 340 | 3 => 320
  | 4 => 286 | 5 => 254 | 6 => 226 | 7 => 214
  | 8 => 190 | 9 => 160 | 10 => 142 | 11 => 128
  | 12 => 106 | 13 => 84 | 14 => 72 | _ => 54

/-- Sample start address `$C000 + A·64`. -/
@[inline] def startAddr (d : Dmc) : UInt16 := 0xC000 + d.addrReg.toUInt16 * 64

/-- Sample length `L·16 + 1`. -/
@[inline] def startLen (d : Dmc) : UInt16 := d.lenReg.toUInt16 * 16 + 1

/-- Register write; `reg` is the address low bits (`0..3` ↔ `$4010..$4013`). -/
@[inline] def write (d : Dmc) (reg : UInt8) (v : UInt8) : Dmc :=
  match reg &&& 3 with
  | 0 =>
    let ie := v &&& 0x80 != 0
    { d with irqEnable := ie, loop := v &&& 0x40 != 0, period := ratePeriod v,
             irqFlag := d.irqFlag && ie }
  | 1 => { d with level := v &&& 0x7F }
  | 2 => { d with addrReg := v }
  | _ => { d with lenReg := v }

/-- `$4015` write, DMC bit. Clears the DMC IRQ flag. -/
@[inline] def setEnabled (d : Dmc) (e : Bool) : Dmc :=
  if !e then { d with bytesRemaining := 0, irqFlag := false }
  else if d.bytesRemaining == 0 then
    { d with curAddr := d.startAddr, bytesRemaining := d.startLen, irqFlag := false }
  else { d with irqFlag := false }

/-- `$4015` read bit 4: bytes remaining `> 0`. -/
@[inline] def active (d : Dmc) : Bool := d.bytesRemaining != 0

/-- The DMC IRQ line. -/
@[inline] def irq (d : Dmc) : Bool := d.irqFlag

/-- Channel output, `0..127`. -/
@[inline] def output (d : Dmc) : UInt8 := d.level &&& 0x7F

/-- Next level after one output clock (`±2`, clamped by skipping). -/
@[inline] def stepLevel (silence : Bool) (shift level : UInt8) : UInt8 :=
  if silence then level
  else if shift &&& 1 != 0 then (if level ≤ 125 then level + 2 else level)
  else (if level ≥ 2 then level - 2 else level)

/-- One output-unit clock (timer expiry), straight-line. -/
@[inline] def clockOutput (d : Dmc) : Dmc :=
  let bits := d.bitsRemaining - 1
  let fin := bits == 0
  { d with
    timer := d.period - 1
    level := stepLevel d.silence d.shift d.level
    shift := if fin then d.buffer else d.shift >>> 1
    bitsRemaining := if fin then 8 else bits
    silence := if fin then d.bufferEmpty else d.silence
    bufferEmpty := fin || d.bufferEmpty }

/-- One CPU cycle. -/
@[inline] def tick (d : Dmc) : Dmc :=
  if d.timer != 0 then { d with timer := d.timer - 1 } else clockOutput d

/-- Does the memory reader want a DMA fetch? -/
@[inline] def dmaRequest (d : Dmc) : Bool := d.bufferEmpty && d.bytesRemaining != 0

/-- Address of the requested fetch. -/
@[inline] def dmaAddr (d : Dmc) : UInt16 := d.curAddr

/-- Address after a fetch at `a`: `$FFFF` wraps to `$8000`. -/
@[inline] def nextAddr (a : UInt16) : UInt16 := if a == 0xFFFF then 0x8000 else a + 1

/-- Deliver the fetched byte `b`. -/
@[inline] def dmaComplete (d : Dmc) (b : UInt8) : Dmc :=
  if d.bytesRemaining == 0 then { d with buffer := b, bufferEmpty := false }
  else
    let r := d.bytesRemaining - 1
    let fin := r == 0
    let rst := fin && d.loop
    { d with
      buffer := b
      bufferEmpty := false
      curAddr := if rst then d.startAddr else nextAddr d.curAddr
      bytesRemaining := if rst then d.startLen else r
      irqFlag := d.irqFlag || (fin && !d.loop && d.irqEnable) }

/-- CPU cycles stolen by one DMC DMA fetch (NESdev "DMA", DMC DMA). `getCycle`: the request
cycle is an APU get cycle; `cpuWriting`: the CPU is writing on that cycle (the halt slips one
cycle, flipping parity; for consecutive writes pass the parity of the last write);
`oamActive`: OAM DMA is running. Halt on get → 3 (halt, dummy, get); halt on put → 4 (halt,
dummy, alignment, get); during OAM DMA → 2 (get + OAM realignment). -/
@[inline] def dmaStall (getCycle cpuWriting oamActive : Bool) : UInt8 :=
  if oamActive then 2
  else if (getCycle != cpuWriting) then 3 else 4

end Dmc

end Nes.Apu
