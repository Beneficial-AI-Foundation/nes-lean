import Nes.Cart.Ines
import Nes.Cart.Mappers.NROM
import Nes.Cart.Mappers.CNROM
import Nes.Cart.Mappers.MMC1
import Nes.Cart.Mappers.UxROM
import Nes.Cart.Mappers.AxROM
import Nes.Cart.Mappers.MMC3

/-!
# `Nes.Cart.Mapper` — the mapper interface and the cartridge

Design (deviation from PLAN §5.2, which describes a *structure of functions*): the cartridge
is accessed on every CPU and PPU cycle, and a structure of closures costs an indirect call
and keeps the per-mapper state boxed behind an existential. Instead:

* `Mapper σ` is a type class giving each mapper's operations over its own register state
  `σ`. It has the same operation set as the PLAN's structure (CPU/PPU read/write via bank
  offsets, register writes, `ppuA12`, `irq`, `mirroring`), but no instance is ever stored:
  instances are resolved statically.
* `MapperState` is a closed inductive with one constructor per mapper; `CartState` holds it
  together with the generic board RAM (8 KiB PRG-RAM, 8 KiB CHR-RAM). The `Cart.*`
  operations are `@[inline]` `match`-dispatchers, so a call compiles to a tag switch plus a
  direct (inlinable) call.
* Supported: NROM (0), MMC1 (1), UxROM (2), CNROM (3), AxROM (7).
* **Timed register writes.** `regWriteAt` is `regWrite` plus the CPU cycle number of the
  write (`0` = unknown), for mappers whose register logic depends on timing (MMC1 ignores
  serial writes on consecutive cycles). It defaults to `regWrite`. `CartState.cpuWrite` /
  `Cart.cpuWrite` take the cycle as an optional last argument `cyc` (default `0`).
* **Extension point (M4):** a new mapper adds a module under `Nes/Cart/Mappers/`, a
  `Mapper` instance below, a `MapperState` constructor, one arm in each
  `MapperState.*` dispatcher, and a case in `MapperState.ofHeader`.

The ROM (`Rom`) is never part of the mutable state: every operation takes it read-only and
returns only a `CartState` (or a byte). Bank arithmetic returns `Fin rom.prg.size` /
`Fin rom.chrLen`, so ROM and CHR reads are total and bounds-check-free.

## Spec

* `CartState.cpuRead rom st a ob` — `$8000–$FFFF`: PRG-ROM at the mapper's offset;
  `$6000–$7FFF`: PRG-RAM (if the mapper enables reads); otherwise the open-bus value `ob`.
* `CartState.cpuWrite rom st a v (cyc := 0)` — `$6000–$7FFF`: PRG-RAM (if writable); every write to
  `$4020–$FFFF` is also passed to the mapper's register logic.
* `CartState.ppuRead rom st a` — `$0000–$1FFF`: CHR-ROM, or CHR-RAM if the image has none,
  at the mapper's offset.
* `CartState.ppuWrite rom st a v` — writes CHR-RAM (no-op on CHR-ROM carts).
* `CartState.ppuA12`, `irq`, `mirroring` — forwarded to the mapper.
* `Cart` bundles `rom` and `st`; `Cart.load` builds one from an iNES file.
-/

namespace Nes.Cart

/-- The mapper interface over a per-mapper register state `σ`. -/
class Mapper (σ : Type) where
  /-- PRG-ROM offset for a CPU address in `$8000–$FFFF`. -/
  prgOffset : (rom : Rom) → σ → UInt16 → Fin rom.prg.size
  /-- CHR offset (into CHR-ROM, or CHR-RAM if none) for a PPU address in `$0000–$1FFF`. -/
  chrOffset : (rom : Rom) → σ → UInt16 → Fin rom.chrLen
  /-- PRG-RAM at `$6000–$7FFF` is readable. -/
  prgRamReadable : σ → Bool
  /-- PRG-RAM at `$6000–$7FFF` is writable. -/
  prgRamWritable : σ → Bool
  /-- Effect of a CPU write to `$4020–$FFFF` on the mapper registers. -/
  regWrite : Rom → σ → UInt16 → UInt8 → σ
  /-- `regWrite` on CPU cycle `cyc` (`0`: unknown); defaults to ignoring the cycle. -/
  regWriteAt : Rom → σ → UInt16 → UInt8 → UInt64 → σ := fun rom s a v _ => regWrite rom s a v
  /-- The PPU drives address line A12 to this level. -/
  ppuA12 : Bool → σ → σ
  /-- The mapper's IRQ output. -/
  irq : σ → Bool
  /-- Current nametable mirroring. -/
  mirroring : Rom → σ → Mirroring

instance : Mapper Nrom.State where
  prgOffset := Nrom.prgOffset
  chrOffset := Nrom.chrOffset
  prgRamReadable _ := true
  prgRamWritable _ := true
  regWrite := Nrom.regWrite
  ppuA12 := Nrom.ppuA12
  irq := Nrom.irq
  mirroring := Nrom.mirroring

instance : Mapper Cnrom.State where
  prgOffset := Cnrom.prgOffset
  chrOffset := Cnrom.chrOffset
  prgRamReadable _ := true
  prgRamWritable _ := true
  regWrite := Cnrom.regWrite
  ppuA12 := Cnrom.ppuA12
  irq := Cnrom.irq
  mirroring := Cnrom.mirroring

instance : Mapper Mmc1.State where
  prgOffset := Mmc1.prgOffset
  chrOffset := Mmc1.chrOffset
  prgRamReadable := Mmc1.prgRamEnabled
  prgRamWritable := Mmc1.prgRamEnabled
  regWrite := Mmc1.regWrite
  regWriteAt := Mmc1.regWriteAt
  ppuA12 := Mmc1.ppuA12
  irq := Mmc1.irq
  mirroring := Mmc1.mirroring

instance : Mapper Uxrom.State where
  prgOffset := Uxrom.prgOffset
  chrOffset := Uxrom.chrOffset
  prgRamReadable _ := true
  prgRamWritable _ := true
  regWrite := Uxrom.regWrite
  ppuA12 := Uxrom.ppuA12
  irq := Uxrom.irq
  mirroring := Uxrom.mirroring

instance : Mapper Axrom.State where
  prgOffset := Axrom.prgOffset
  chrOffset := Axrom.chrOffset
  prgRamReadable _ := true
  prgRamWritable _ := true
  regWrite := Axrom.regWrite
  ppuA12 := Axrom.ppuA12
  irq := Axrom.irq
  mirroring := Axrom.mirroring

instance : Mapper Mmc3.State where
  prgOffset := Mmc3.prgOffset
  chrOffset := Mmc3.chrOffset
  prgRamReadable := Mmc3.prgRamReadable
  prgRamWritable := Mmc3.prgRamWritable
  regWrite := Mmc3.regWrite
  ppuA12 := Mmc3.ppuA12
  irq := Mmc3.irq
  mirroring := Mmc3.mirroring

/-- Register state of the cartridge's mapper; one constructor per supported mapper. -/
inductive MapperState where
  | nrom (s : Nrom.State)
  | cnrom (s : Cnrom.State)
  | mmc1 (s : Mmc1.State)
  | uxrom (s : Uxrom.State)
  | axrom (s : Axrom.State)
  | mmc3 (s : Mmc3.State)
  deriving DecidableEq, Repr, Inhabited

namespace MapperState

@[inline] def prgOffset (rom : Rom) : MapperState → UInt16 → Fin rom.prg.size
  | .nrom s, a => Mapper.prgOffset rom s a
  | .cnrom s, a => Mapper.prgOffset rom s a
  | .mmc1 s, a => Mapper.prgOffset rom s a
  | .uxrom s, a => Mapper.prgOffset rom s a
  | .axrom s, a => Mapper.prgOffset rom s a
  | .mmc3 s, a => Mapper.prgOffset rom s a

@[inline] def chrOffset (rom : Rom) : MapperState → UInt16 → Fin rom.chrLen
  | .nrom s, a => Mapper.chrOffset rom s a
  | .cnrom s, a => Mapper.chrOffset rom s a
  | .mmc1 s, a => Mapper.chrOffset rom s a
  | .uxrom s, a => Mapper.chrOffset rom s a
  | .axrom s, a => Mapper.chrOffset rom s a
  | .mmc3 s, a => Mapper.chrOffset rom s a

@[inline] def prgRamReadable : MapperState → Bool
  | .nrom s => Mapper.prgRamReadable s
  | .cnrom s => Mapper.prgRamReadable s
  | .mmc1 s => Mapper.prgRamReadable s
  | .uxrom s => Mapper.prgRamReadable s
  | .axrom s => Mapper.prgRamReadable s
  | .mmc3 s => Mapper.prgRamReadable s

@[inline] def prgRamWritable : MapperState → Bool
  | .nrom s => Mapper.prgRamWritable s
  | .cnrom s => Mapper.prgRamWritable s
  | .mmc1 s => Mapper.prgRamWritable s
  | .uxrom s => Mapper.prgRamWritable s
  | .axrom s => Mapper.prgRamWritable s
  | .mmc3 s => Mapper.prgRamWritable s

/-- Register write on CPU cycle `cyc` (`0`: unknown). -/
@[inline] def regWrite (rom : Rom) (m : MapperState) (a : UInt16) (v : UInt8)
    (cyc : UInt64 := 0) : MapperState :=
  match m with
  | .nrom s => .nrom (Mapper.regWriteAt rom s a v cyc)
  | .cnrom s => .cnrom (Mapper.regWriteAt rom s a v cyc)
  | .mmc1 s => .mmc1 (Mapper.regWriteAt rom s a v cyc)
  | .uxrom s => .uxrom (Mapper.regWriteAt rom s a v cyc)
  | .axrom s => .axrom (Mapper.regWriteAt rom s a v cyc)
  | .mmc3 s => .mmc3 (Mapper.regWriteAt rom s a v cyc)

@[inline] def ppuA12 (b : Bool) : MapperState → MapperState
  | .nrom s => .nrom (Mapper.ppuA12 b s)
  | .cnrom s => .cnrom (Mapper.ppuA12 b s)
  | .mmc1 s => .mmc1 (Mapper.ppuA12 b s)
  | .uxrom s => .uxrom (Mapper.ppuA12 b s)
  | .axrom s => .axrom (Mapper.ppuA12 b s)
  | .mmc3 s => .mmc3 (Mapper.ppuA12 b s)

@[inline] def irq : MapperState → Bool
  | .nrom s => Mapper.irq s
  | .cnrom s => Mapper.irq s
  | .mmc1 s => Mapper.irq s
  | .uxrom s => Mapper.irq s
  | .axrom s => Mapper.irq s
  | .mmc3 s => Mapper.irq s

@[inline] def mirroring (rom : Rom) : MapperState → Mirroring
  | .nrom s => Mapper.mirroring rom s
  | .cnrom s => Mapper.mirroring rom s
  | .mmc1 s => Mapper.mirroring rom s
  | .uxrom s => Mapper.mirroring rom s
  | .axrom s => Mapper.mirroring rom s
  | .mmc3 s => Mapper.mirroring rom s

/-- Power-on mapper state for the mapper number in the header. -/
def ofHeader (h : Header) : Except String MapperState :=
  match h.mapper with
  | 0 => .ok (.nrom {})
  | 1 => .ok (.mmc1 {})
  | 2 => .ok (.uxrom {})
  | 3 => .ok (.cnrom {})
  | 7 => .ok (.axrom {})
  | 4 => .ok (.mmc3 (Mmc3.init h))
  | n => .error s!"unsupported mapper {n}"

end MapperState

/-- The mutable part of a cartridge: mapper registers and board RAM. -/
structure CartState where
  mapper : MapperState
  /-- 8 KiB PRG-RAM at CPU `$6000–$7FFF`. -/
  prgRam : ByteArray
  /-- 8 KiB CHR-RAM (used only when the image has no CHR-ROM). -/
  chrRam : ByteArray
  prgRam_size : prgRam.size = 8192
  chrRam_size : chrRam.size = 8192

theorem _root_.ByteArray.size_set' (b : ByteArray) (i : Nat) (v : UInt8) (h : i < b.size) :
    (b.set i v h).size = b.size := by
  simp [← ByteArray.size_data]

namespace CartState

/-- Power-on state: zeroed RAM. -/
def init (m : MapperState) : CartState :=
  { mapper := m, prgRam := ⟨Array.replicate 8192 0⟩, chrRam := ⟨Array.replicate 8192 0⟩,
    prgRam_size := by simp [← ByteArray.size_data],
    chrRam_size := by simp [← ByteArray.size_data] }

/-- PRG-RAM index for a CPU address. -/
@[inline] def prgRamIdx (st : CartState) (a : UInt16) : Fin st.prgRam.size :=
  ⟨(a &&& 0x1FFF).toNat % 8192, by rw [st.prgRam_size]; exact Nat.mod_lt _ (by decide)⟩

/-- CPU read of `$4020–$FFFF`; `ob` is the open-bus value returned for unmapped addresses. -/
@[inline] def cpuRead (rom : Rom) (st : CartState) (a : UInt16) (ob : UInt8) : UInt8 :=
  if 0x8000 ≤ a then rom.prg[st.mapper.prgOffset rom a]
  else if 0x6000 ≤ a then
    if st.mapper.prgRamReadable then st.prgRam[st.prgRamIdx a] else ob
  else ob

/-- CPU write to `$4020–$FFFF` on CPU cycle `cyc` (`0`: unknown; see `Mapper.regWriteAt`). -/
@[inline] def cpuWrite (rom : Rom) (st : CartState) (a : UInt16) (v : UInt8)
    (cyc : UInt64 := 0) : CartState :=
  let st :=
    if 0x6000 ≤ a && a < 0x8000 && st.mapper.prgRamWritable then
      { st with
        prgRam := st.prgRam.set (st.prgRamIdx a) v
        prgRam_size := by rw [ByteArray.size_set']; exact st.prgRam_size }
    else st
  { st with mapper := st.mapper.regWrite rom a v cyc }

/-- PPU read of the pattern-table space `$0000–$1FFF`. -/
@[inline] def ppuRead (rom : Rom) (st : CartState) (a : UInt16) : UInt8 :=
  let off := st.mapper.chrOffset rom a
  if h : rom.chr.size = 0 then
    st.chrRam[off.val]'(st.chrRam_size ▸ Rom.chrLen_of_eq_zero h ▸ off.isLt)
  else
    rom.chr[off.val]'(Rom.chrLen_of_ne_zero h ▸ off.isLt)

/-- PPU write to `$0000–$1FFF`: stores into CHR-RAM; ignored on CHR-ROM carts. -/
@[inline] def ppuWrite (rom : Rom) (st : CartState) (a : UInt16) (v : UInt8) : CartState :=
  let off := st.mapper.chrOffset rom a
  if h : rom.chr.size = 0 then
    { st with
      chrRam := st.chrRam.set off.val v
        (st.chrRam_size ▸ Rom.chrLen_of_eq_zero h ▸ off.isLt)
      chrRam_size := by rw [ByteArray.size_set']; exact st.chrRam_size }
  else st

/-- The PPU drives A12 to `b`. -/
@[inline] def ppuA12 (b : Bool) (st : CartState) : CartState :=
  { st with mapper := st.mapper.ppuA12 b }

/-- The cartridge IRQ line. -/
@[inline] def irq (st : CartState) : Bool := st.mapper.irq

/-- Current nametable mirroring. -/
@[inline] def mirroring (rom : Rom) (st : CartState) : Mirroring := st.mapper.mirroring rom

end CartState

/-- A cartridge: the immutable image plus its mutable state. -/
structure Cart where
  rom : Rom
  st : CartState

namespace Cart

@[inline] def cpuRead (c : Cart) (a : UInt16) (ob : UInt8) : UInt8 := c.st.cpuRead c.rom a ob
@[inline] def cpuWrite (c : Cart) (a : UInt16) (v : UInt8) (cyc : UInt64 := 0) : Cart :=
  { c with st := c.st.cpuWrite c.rom a v cyc }
@[inline] def ppuRead (c : Cart) (a : UInt16) : UInt8 := c.st.ppuRead c.rom a
@[inline] def ppuWrite (c : Cart) (a : UInt16) (v : UInt8) : Cart :=
  { c with st := c.st.ppuWrite c.rom a v }
@[inline] def ppuA12 (c : Cart) (b : Bool) : Cart := { c with st := c.st.ppuA12 b }
@[inline] def irq (c : Cart) : Bool := c.st.irq
@[inline] def mirroring (c : Cart) : Mirroring := c.st.mirroring c.rom

/-- Load an iNES / NES 2.0 image into a powered-on cartridge. -/
def load (b : ByteArray) : Except String Cart := do
  let rom ← Rom.load b
  let m ← MapperState.ofHeader rom.header
  return { rom, st := CartState.init m }

end Cart

end Nes.Cart
