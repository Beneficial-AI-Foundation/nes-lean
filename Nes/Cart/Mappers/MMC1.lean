import Nes.Cart.Mappers.NROM

/-!
# `Nes.Cart.Mappers.MMC1` — mapper 1 (SxROM)

MMC1 (NESdev "MMC1") is programmed through a serial port at `$8000–$FFFF`. Each CPU write
with bit 7 clear shifts bit 0 of the value into a 5-bit shift register (LSB first); the fifth
such write copies the 5-bit value into the internal register selected by address bits 14–13
and clears the shift register. A write with bit 7 set clears the shift register and ORs
`$0C` into the control register (PRG mode 3).

| register | address | bits |
|----------|---------|------|
| control  | `$8000–$9FFF` | `CPPMM`: mirroring `MM` (0 one-screen low, 1 one-screen high, 2 vertical, 3 horizontal), PRG mode `PP`, CHR mode `C` |
| CHR 0    | `$A000–$BFFF` | 4 KiB CHR bank at PPU `$0000` (8 KiB mode: bank pair, bit 0 ignored) |
| CHR 1    | `$C000–$DFFF` | 4 KiB CHR bank at PPU `$1000` (ignored in 8 KiB mode) |
| PRG      | `$E000–$FFFF` | `RPPPP`: 16 KiB PRG bank `PPPP`, PRG-RAM disable `R` (MMC1B) |

PRG modes: 0/1 switch 32 KiB at `$8000` (bank bit 0 ignored); 2 fixes the first bank at
`$8000` and switches `$C000`; 3 switches `$8000` and fixes the last bank at `$C000`.

Design decisions:
* **Consecutive-cycle writes.** The MMC1 ignores a serial write on the CPU cycle right after
  another one (only the first write of a read-modify-write instruction's double write
  counts). The `regWrite` operation of `Nes.Cart.Mapper` carries no time, so the class has
  an extra operation `regWriteAt … cyc` that receives the CPU cycle number (default: ignore
  it). `regWriteAt` drops a serial write whose cycle is `consecCycle` (the cycle right after
  the previous serial write); cycle `0` means "no timing information" and never drops a
  write, so `regWrite = regWriteAt … 0`. The system passes its CPU clock through
  `Cart.cpuWrite … (cyc := clock)`; until it does, the quirk is simply off.
* **PRG-RAM.** `$6000–$7FFF` is 8 KiB board RAM, enabled while PRG register bit 4 is clear
  (MMC1B behaviour; MMC1A ignores the bit, power-on value 0 enables it on both). SNROM's
  extra disable through CHR bit 4 is not modelled.
* **SUROM.** For PRG images above 256 KiB, CHR 0 bit 4 selects the 256 KiB outer PRG bank
  (both halves of the PRG layout, including the fixed bank, live in that outer bank).
* **Bank width.** Offsets are reduced modulo the PRG size / `chrLen`, which for power-of-two
  images masks the bank numbers to the banks present.
* **Power-on.** Control is `$0C` (PRG mode 3, so the reset vector is in the fixed last bank),
  all other registers and the shift register are 0.

## Spec

* `serialWrite s a v` — the serial port as described above (no timing).
* `regWriteAt rom s a v cyc` — writes below `$8000` leave the state unchanged; otherwise if
  `cyc ≠ 0` and `cyc = s.consecCycle` the write is dropped, else it is `serialWrite`; in both
  cases `consecCycle := cyc + 1`. `regWrite rom s a v = regWriteAt rom s a v 0`.
* `prgOffset rom s a = ((outer + b)·$4000 + (a mod $4000)) mod |PRG|`, `b` from the PRG mode.
* `chrOffset rom s a = (bank·$1000 + (a mod $1000)) mod chrLen` for the 4 KiB bank mapped at
  `a` (8 KiB mode: `chr0 &&& $1E` and `+1`).
* `mirroring` from control bits 0–1; `prgRamReadable = prgRamWritable = (prg bit 4 clear)`.
* A12, IRQ: unused.
* T-CART-3 (`Nes.Cart.Proofs.MMC1`): commit after five writes, reset on bit 7.
-/

namespace Nes.Cart.Mmc1

/-- MMC1 register state. -/
structure State where
  /-- Serial shift register (bits arrive at bit 4 and move right). -/
  shift : UInt8 := 0
  /-- Number of bits shifted in since the last commit/reset (0–4). -/
  count : UInt8 := 0
  control : UInt8 := 0x0C
  chr0 : UInt8 := 0
  chr1 : UInt8 := 0
  prg : UInt8 := 0
  /-- A serial write on this CPU cycle is dropped (0: none). -/
  consecCycle : UInt64 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Internal register selected by a serial-port address: bits 14–13. -/
@[inline] def regIdx (addr : UInt16) : UInt16 := (addr >>> 13) &&& 3

/-- The internal register with index `i` (`0` control, `1` CHR 0, `2` CHR 1, `3` PRG). -/
@[inline] def getReg (s : State) (i : UInt16) : UInt8 :=
  if i == 0 then s.control else if i == 1 then s.chr0 else if i == 2 then s.chr1 else s.prg

/-- Set the internal register with index `i`. -/
@[inline] def setReg (s : State) (i : UInt16) (x : UInt8) : State :=
  if i == 0 then { s with control := x }
  else if i == 1 then { s with chr0 := x }
  else if i == 2 then { s with chr1 := x }
  else { s with prg := x }

/-- PRG mode: control bits 2–3. -/
@[inline] def prgMode (s : State) : UInt8 := (s.control >>> 2) &&& 3

/-- The serial port (no timing): reset on bit 7, else shift in bit 0 and commit on the 5th. -/
@[inline] def serialWrite (s : State) (addr : UInt16) (v : UInt8) : State :=
  if v &&& 0x80 != 0 then { s with shift := 0, count := 0, control := s.control ||| 0x0C }
  else
    let sh := (s.shift >>> 1) ||| ((v &&& 1) <<< 4)
    if s.count < 4 then { s with shift := sh, count := s.count + 1 }
    else setReg { s with shift := 0, count := 0 } (regIdx addr) sh

/-- CPU write to `$4020–$FFFF` on CPU cycle `cyc` (`0`: unknown). -/
@[inline] def regWriteAt (_ : Rom) (s : State) (addr : UInt16) (v : UInt8) (cyc : UInt64) :
    State :=
  if 0x8000 ≤ addr then
    let s' := if cyc != 0 && cyc == s.consecCycle then s else serialWrite s addr v
    { s' with consecCycle := cyc + 1 }
  else s

/-- CPU write to `$4020–$FFFF` without timing information. -/
@[inline] def regWrite (rom : Rom) (s : State) (addr : UInt16) (v : UInt8) : State :=
  regWriteAt rom s addr v 0

/-- Number of 16 KiB PRG banks. -/
@[inline] def banks (rom : Rom) : Nat := rom.prg.size / 16384

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF`. -/
@[inline] def prgOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.prg.size :=
  let mode := prgMode s
  let bank := (s.prg &&& 0x0F).toNat
  let outer := if rom.prg.size > 0x40000 && s.chr0 &&& 0x10 != 0 then 16 else 0
  let last := if banks rom ≥ 16 then 15 else banks rom - 1
  let hi := 0xC000 ≤ addr
  let b :=
    if mode < 2 then (bank / 2) * 2 + (if hi then 1 else 0)
    else if mode == 2 then (if hi then bank else 0)
    else (if hi then last else bank)
  ⟨((outer + b) * 16384 + (addr &&& 0x3FFF).toNat) % rom.prg.size, Nat.mod_lt _ rom.prg_pos⟩

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF`. -/
@[inline] def chrOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.chrLen :=
  let a := (addr &&& 0x1FFF).toNat
  let off :=
    if s.control &&& 0x10 == 0 then (s.chr0 &&& 0x1E).toNat * 4096 + a
    else if a < 4096 then s.chr0.toNat * 4096 + a
    else s.chr1.toNat * 4096 + (a - 4096)
  ⟨off % rom.chrLen, Nat.mod_lt _ rom.chrLen_pos⟩

/-- PRG-RAM enabled: PRG register bit 4 clear. -/
@[inline] def prgRamEnabled (s : State) : Bool := s.prg &&& 0x10 == 0

/-- PPU A12 edge input: unused. -/
@[inline] def ppuA12 (_ : Bool) (s : State) : State := s

/-- IRQ line: never asserted. -/
@[inline] def irq (_ : State) : Bool := false

/-- Mirroring from control bits 0–1. -/
@[inline] def mirroring (_ : Rom) (s : State) : Mirroring :=
  let m := s.control &&& 3
  if m == 0 then .singleLow else if m == 1 then .singleHigh
  else if m == 2 then .vertical else .horizontal

end Nes.Cart.Mmc1
