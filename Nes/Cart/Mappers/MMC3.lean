import Nes.Cart.Ines

/-!
# `Nes.Cart.Mappers.MMC3` — mapper 4 (MMC3 / TxROM)

Register interface, bank layout and IRQ counter follow NESdev "MMC3"
(https://www.nesdev.org/wiki/MMC3). CPU writes to `$8000–$FFFF` are decoded by
`addr & $E001` (eight registers, even/odd pairs):

| addr    | register                                                                    |
|---------|-----------------------------------------------------------------------------|
| `$8000` | bank select: bits 0–2 pick `R0–R7`, bit 6 PRG mode, bit 7 CHR A12 inversion |
| `$8001` | bank data: `R[select & 7] := v`                                              |
| `$A000` | mirroring: bit 0 = 0 vertical, 1 horizontal (ignored for four-screen boards) |
| `$A001` | PRG-RAM protect: bit 7 chip enable, bit 6 write protect                      |
| `$C000` | IRQ latch                                                                   |
| `$C001` | IRQ reload: counter := 0, reload on the next clock                           |
| `$E000` | IRQ disable + acknowledge (clears a pending IRQ)                             |
| `$E001` | IRQ enable                                                                  |

## Banks

PRG (8 KiB units, `n = |PRG| / 8 KiB`): mode 0 maps `R6, R7, n-2, n-1` at
`$8000/$A000/$C000/$E000`; mode 1 (bit 6) maps `n-2, R7, R6, n-1`.
CHR (1 KiB units): with bit 7 clear, `$0000` 2 KiB `R0 & $FE`, `$0800` 2 KiB `R1 & $FE`,
`$1000/$1400/$1800/$1C00` 1 KiB `R2–R5`; bit 7 set swaps the two pattern-table halves
(the address's A12 is inverted before the lookup). Offsets are reduced modulo the PRG size /
`chrLen`, so they are in range for every image (T-CART-2) and banks wrap like the
real chip's address lines for power-of-two sizes.

## IRQ counter (T-CART-4)

* **A12 filter.** The chip clocks the counter on a rising edge of PPU A12 only if A12 has been
  low for long enough: NESdev says the edge is ignored unless A12 stayed low across ~3 falling
  edges of M2 (≈ 3 CPU cycles ≈ 9 PPU dots). We count PPU dots: `lowDots` is the number of
  consecutive dots (saturating at 255) that `ppuA12` was called with `false`, reset to 0 on a
  `true` dot. A `true` dot with `lowDots ≥ a12Gap = 10` is a filtered rising edge (same
  threshold as Mesen's A12 watcher). With BG at `$0000` and sprites at `$1000` this gives one
  clock per rendered line (at dot 261, the first sprite pattern fetch); the 4-dot low gaps
  between the eight sprite pattern fetches (and between BG pattern fetches in the opposite
  configuration) are filtered out. `lowDots = 0` means "A12 currently high", so one byte holds
  both the last level and the low time.
* **Clock.** If `counter = 0` or the reload flag is set, `counter := latch` (and the reload flag
  clears); otherwise `counter := counter - 1`. Then, if `counter = 0` and IRQs are enabled, the
  IRQ becomes pending.
* **Behaviour variant.** This is the "new" / Sharp MMC3 behaviour (MMC3B/C, the common one):
  the IRQ is asserted whenever the counter is 0 *after* a clock, so with `latch = 0` it fires
  on every clock, and a `$C001` reload to latch 0 fires. The "old" / NEC MMC3A behaviour
  (assert only when a decrement — or a `$C001`-requested reload to a non-zero value — reaches
  0) is not modelled; mmc3_test_2's `6-MMC3_alt` expects it and is expected to fail.
* The IRQ output is the pending flag; `$E000` clears it and disables, `$E001` enables (it does
  not acknowledge a pending IRQ).

## PRG-RAM

`$A001` bit 7 enables PRG-RAM, bit 6 write-protects it. The power-on value is `$80`
(enabled, writable): the real power-on state is undefined, and test ROMs that report through
`$6000` without touching `$A001` then work.

## Spec

* `prgOffset rom s a = (bank·$2000 + (a mod $2000)) mod |PRG|`, bank as in the table above
  (with `n-2` computed as `n - 2` in ℕ).
* `chrOffset rom s a = (bank·$400 + (a mod $400)) mod chrLen`, bank as above.
* `regWrite rom s a v`: for `a ≥ $8000`, the register `a & $E001` as tabulated; below `$8000`
  no change.
* `ppuA12 b s`: `b = false` → `lowDots := min(lowDots + 1, 255)`; `b = true` → `lowDots := 0`,
  and if the old `lowDots ≥ a12Gap`, `clock` (above).
* `irq s = s.irqPending`; `mirroring` is `fourScreen` for four-screen headers, else the
  `$A000` register. `init h` is the power-on state (mirroring register from the header).
-/

namespace Nes.Cart.Mmc3

/-- Minimum number of PPU dots A12 must stay low before a rising edge clocks the counter. -/
def a12Gap : UInt8 := 10

/-- MMC3 register state. -/
structure State where
  /-- `$8000`: bank-register index (bits 0–2), PRG mode (bit 6), CHR inversion (bit 7). -/
  bankSelect : UInt8 := 0
  r0 : UInt8 := 0
  r1 : UInt8 := 0
  r2 : UInt8 := 0
  r3 : UInt8 := 0
  r4 : UInt8 := 0
  r5 : UInt8 := 0
  r6 : UInt8 := 0
  r7 : UInt8 := 0
  /-- `$A000` bit 0: horizontal mirroring. -/
  mirH : Bool := false
  /-- `$A001`: PRG-RAM protect (bit 7 enable, bit 6 write protect). -/
  ramProtect : UInt8 := 0x80
  irqLatch : UInt8 := 0
  irqCounter : UInt8 := 0
  irqReload : Bool := false
  irqEnabled : Bool := false
  irqPending : Bool := false
  /-- Consecutive PPU dots with A12 low (saturating at 255); 0 while A12 is high. -/
  lowDots : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Power-on state; the `$A000` register starts at the header's hard-wired mirroring. -/
def init (h : Header) : State := { mirH := h.mirroring == .horizontal }

/-- PRG bank (8 KiB units) for the CPU window `w` = `(a >> 13) & 3`. -/
@[inline] def prgBank (rom : Rom) (s : State) (w : UInt16) : Nat :=
  let n := rom.prg.size / 8192
  let swap := s.bankSelect &&& 0x40 != 0
  if w == 0 then (if swap then n - 2 else s.r6.toNat)
  else if w == 1 then s.r7.toNat
  else if w == 2 then (if swap then s.r6.toNat else n - 2)
  else n - 1

/-- Offset into PRG-ROM for a CPU address in `$8000–$FFFF`. -/
@[inline] def prgOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.prg.size :=
  let bank := prgBank rom s ((addr >>> 13) &&& 3)
  ⟨(bank * 8192 + (addr &&& 0x1FFF).toNat) % rom.prg.size, Nat.mod_lt _ rom.prg_pos⟩

/-- CHR bank (1 KiB units) for the 1 KiB slot `k` (0–7) after A12 inversion. -/
@[inline] def chrBank (s : State) (k : UInt16) : UInt8 :=
  if k == 0 then s.r0 &&& 0xFE
  else if k == 1 then s.r0 ||| 1
  else if k == 2 then s.r1 &&& 0xFE
  else if k == 3 then s.r1 ||| 1
  else if k == 4 then s.r2
  else if k == 5 then s.r3
  else if k == 6 then s.r4
  else s.r5

/-- Offset into the CHR space for a PPU address in `$0000–$1FFF`. -/
@[inline] def chrOffset (rom : Rom) (s : State) (addr : UInt16) : Fin rom.chrLen :=
  let a := addr &&& 0x1FFF
  let a' := if s.bankSelect &&& 0x80 != 0 then a ^^^ 0x1000 else a
  let bank := chrBank s (a' >>> 10)
  ⟨(bank.toNat * 1024 + (a &&& 0x3FF).toNat) % rom.chrLen, Nat.mod_lt _ rom.chrLen_pos⟩

/-- `$8001`: store `v` into the bank register selected by `bankSelect & 7`. -/
@[inline] def setBank (s : State) (v : UInt8) : State :=
  let i := s.bankSelect &&& 7
  if i == 0 then { s with r0 := v }
  else if i == 1 then { s with r1 := v }
  else if i == 2 then { s with r2 := v }
  else if i == 3 then { s with r3 := v }
  else if i == 4 then { s with r4 := v }
  else if i == 5 then { s with r5 := v }
  else if i == 6 then { s with r6 := v }
  else { s with r7 := v }

/-- CPU write to `$4020–$FFFF` (registers at `$8000–$FFFF`, decoded by `addr & $E001`). -/
@[inline] def regWrite (_ : Rom) (s : State) (addr : UInt16) (v : UInt8) : State :=
  if addr < 0x8000 then s else
  let r := addr &&& 0xE001
  if r == 0x8000 then { s with bankSelect := v }
  else if r == 0x8001 then setBank s v
  else if r == 0xA000 then { s with mirH := v &&& 1 != 0 }
  else if r == 0xA001 then { s with ramProtect := v }
  else if r == 0xC000 then { s with irqLatch := v }
  else if r == 0xC001 then { s with irqCounter := 0, irqReload := true }
  else if r == 0xE000 then { s with irqEnabled := false, irqPending := false }
  else { s with irqEnabled := true }

/-- One clock of the IRQ counter ("new"/Sharp behaviour, see the module doc). -/
@[inline] def clock (s : State) : State :=
  let c := if s.irqCounter == 0 || s.irqReload then s.irqLatch else s.irqCounter - 1
  { s with irqCounter := c, irqReload := false,
           irqPending := s.irqPending || (c == 0 && s.irqEnabled) }

/-- The PPU drives A12 to `b` this dot: filtered rising edges clock the IRQ counter. -/
@[inline] def ppuA12 (b : Bool) (s : State) : State :=
  if b then
    if s.lowDots == 0 then s
    else if a12Gap ≤ s.lowDots then clock { s with lowDots := 0 }
    else { s with lowDots := 0 }
  else if s.lowDots == 255 then s
  else { s with lowDots := s.lowDots + 1 }

/-- IRQ line: the pending flag. -/
@[inline] def irq (s : State) : Bool := s.irqPending

/-- PRG-RAM readable: `$A001` bit 7. -/
@[inline] def prgRamReadable (s : State) : Bool := s.ramProtect &&& 0x80 != 0

/-- PRG-RAM writable: `$A001` bit 7 set and bit 6 clear. -/
@[inline] def prgRamWritable (s : State) : Bool := s.ramProtect &&& 0xC0 == 0x80

/-- Mirroring: four-screen boards ignore `$A000`. -/
@[inline] def mirroring (rom : Rom) (s : State) : Mirroring :=
  if rom.mirroring == .fourScreen then .fourScreen
  else if s.mirH then .horizontal else .vertical

end Nes.Cart.Mmc3
