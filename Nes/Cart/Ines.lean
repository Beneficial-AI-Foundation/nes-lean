import Nes.Cart.Mirroring

/-!
# `Nes.Cart.Ines` — iNES / NES 2.0 header, serializer, and the immutable ROM image

An iNES file is a 16-byte header, an optional 512-byte trainer, PRG-ROM (16 KiB units) and
CHR-ROM (8 KiB units). Byte layout (nesdev "INES" / "NES 2.0"):

| byte | contents |
|------|----------|
| 0–3  | `"NES"` `$1A` |
| 4    | PRG-ROM banks, low 8 bits |
| 5    | CHR-ROM banks, low 8 bits |
| 6    | mapper bits 0–3 (high nibble), four-screen (3), trainer (2), battery (1), vertical (0) |
| 7    | mapper bits 4–7 (high nibble), NES 2.0 id `10` (bits 3–2), console type (bits 1–0) |
| 8    | NES 2.0: submapper (high nibble), mapper bits 8–11 (low nibble) |
| 9    | NES 2.0: CHR banks bits 8–11 (high nibble), PRG banks bits 8–11 (low nibble) |
| 10   | NES 2.0: PRG-NVRAM shift (high), PRG-RAM shift (low) |
| 11   | NES 2.0: CHR-NVRAM shift (high), CHR-RAM shift (low) |
| 12   | NES 2.0: CPU/PPU timing (bits 1–0) |
| 13   | NES 2.0: Vs. system / extended console type |
| 14   | NES 2.0: miscellaneous ROM count (bits 1–0) |
| 15   | NES 2.0: default expansion device (bits 5–0) |

For an iNES 1.0 header bytes 8–15 are not interpreted (`serialize` writes zeros). A header
whose bits 3–2 of byte 7 are `01`, or (not NES 2.0 and) any of bytes 12–15 is non-zero, is
"archaic iNES" (e.g. the `DiskDude!` signature): byte 7 is garbage and is ignored.

## Spec

* `Header` stores the header fields at their encoded widths (`UInt8`/`UInt16`), the NES 2.0
  fields being `0` for an iNES 1.0 header. `Header.WF h` says every field fits its bit
  field and the mirroring is one the header can express (not `singleLow`/`singleHigh`).
* `parse b` is `none` unless `b` has at least 16 bytes starting with `"NES\x1A"`.
* `serialize h` is the 16-byte encoding of `h`.
* T-CART-1 (in `Nes.Cart.Proofs.Ines`): `WF h → parse (serialize h) = some h`, and
  `parse b = none` whenever the first four bytes are not `"NES\x1A"`.
* `Rom` is the immutable cartridge image: `prg` and `chr` are `ByteArray`s (unboxed bytes,
  1 B/byte), `prg` is non-empty by a proof field, and `chr` empty means the board has 8 KiB
  of CHR-RAM. `Rom.chrLen` is the size of the CHR space either way; mapper bank arithmetic
  returns `Fin rom.prg.size` / `Fin rom.chrLen`, so reads are total and bounds-check-free.
* `Rom.load b` parses the header, skips the trainer, and slices PRG/CHR out of the file.
-/

namespace Nes.Cart

/-- The iNES / NES 2.0 header, fields at their encoded widths. -/
structure Header where
  /-- PRG-ROM size field in 16 KiB units (8 bits for iNES 1.0, 12 bits for NES 2.0). When
  the NES 2.0 high nibble is `$F` the low byte is an exponent-multiplier (see
  `Header.prgRomSize`). -/
  prgBanks : UInt16
  /-- CHR-ROM size field in 8 KiB units; `0` means the board has CHR-RAM. -/
  chrBanks : UInt16
  /-- Mapper number (8 bits for iNES 1.0, 12 bits for NES 2.0). -/
  mapper : UInt16
  /-- NES 2.0 submapper (4 bits). -/
  submapper : UInt8
  /-- Hard-wired nametable mirroring: `horizontal`, `vertical` or `fourScreen`. -/
  mirroring : Mirroring
  /-- Battery-backed PRG-RAM (or other non-volatile memory). -/
  battery : Bool
  /-- A 512-byte trainer precedes PRG-ROM in the file. -/
  trainer : Bool
  /-- Console type (byte 7 bits 1–0): 0 NES, 1 Vs. System, 2 PlayChoice-10, 3 extended. -/
  consoleType : UInt8
  /-- The header is NES 2.0 (byte 7 bits 3–2 = `10`). -/
  nes2 : Bool
  /-- NES 2.0 PRG-RAM shift count (size = 64 <<< n, or 0). -/
  prgRamShift : UInt8
  /-- NES 2.0 PRG-NVRAM shift count. -/
  prgNvramShift : UInt8
  /-- NES 2.0 CHR-RAM shift count. -/
  chrRamShift : UInt8
  /-- NES 2.0 CHR-NVRAM shift count. -/
  chrNvramShift : UInt8
  /-- NES 2.0 CPU/PPU timing: 0 NTSC, 1 PAL, 2 multi-region, 3 Dendy. -/
  timing : UInt8
  /-- NES 2.0 byte 13 (Vs. PPU/hardware type, or extended console type). -/
  systemType : UInt8
  /-- NES 2.0 number of miscellaneous ROMs (2 bits). -/
  miscRoms : UInt8
  /-- NES 2.0 default expansion device (6 bits). -/
  expansion : UInt8
  deriving DecidableEq, Repr, Inhabited

namespace Header

/-- Well-formedness: every field fits its bit field in the 16-byte encoding, and the
NES 2.0-only fields are zero in an iNES 1.0 header. -/
structure WF (h : Header) : Prop where
  mirroring : h.mirroring = .horizontal ∨ h.mirroring = .vertical ∨ h.mirroring = .fourScreen
  consoleType : h.consoleType < 4
  prgBanks : h.prgBanks < (if h.nes2 then 4096 else 256)
  chrBanks : h.chrBanks < (if h.nes2 then 4096 else 256)
  mapper : h.mapper < (if h.nes2 then 4096 else 256)
  submapper : h.submapper < (if h.nes2 then 16 else 1)
  prgRamShift : h.prgRamShift < (if h.nes2 then 16 else 1)
  prgNvramShift : h.prgNvramShift < (if h.nes2 then 16 else 1)
  chrRamShift : h.chrRamShift < (if h.nes2 then 16 else 1)
  chrNvramShift : h.chrNvramShift < (if h.nes2 then 16 else 1)
  timing : h.timing < (if h.nes2 then 4 else 1)
  systemType : h.systemType < (if h.nes2 then 256 else 1)
  miscRoms : h.miscRoms < (if h.nes2 then 4 else 1)
  expansion : h.expansion < (if h.nes2 then 64 else 1)

/-- PRG-ROM size in bytes. NES 2.0 exponent-multiplier form when the high nibble is `$F`:
`2^E * (2*MM + 1)` with `E` = bits 7–2 and `MM` = bits 1–0 of byte 4. -/
def prgRomSize (h : Header) : Nat :=
  if h.nes2 && (h.prgBanks >>> 8) == 0xF then
    2 ^ ((h.prgBanks &&& 0xFF) >>> 2).toNat * (2 * (h.prgBanks &&& 3).toNat + 1)
  else h.prgBanks.toNat * 16384

/-- CHR-ROM size in bytes (exponent-multiplier form as for `prgRomSize`). -/
def chrRomSize (h : Header) : Nat :=
  if h.nes2 && (h.chrBanks >>> 8) == 0xF then
    2 ^ ((h.chrBanks &&& 0xFF) >>> 2).toNat * (2 * (h.chrBanks &&& 3).toNat + 1)
  else h.chrBanks.toNat * 8192

/-- Byte 6 from its fields. -/
@[inline] def byte6 (h : Header) : UInt8 :=
  ((h.mapper &&& 0xF).toUInt8 <<< 4)
    ||| (if h.mirroring = .fourScreen then 8 else 0)
    ||| (if h.trainer then 4 else 0)
    ||| (if h.battery then 2 else 0)
    ||| (if h.mirroring = .vertical then 1 else 0)

/-- Byte 7 from its fields. -/
@[inline] def byte7 (h : Header) : UInt8 :=
  (((h.mapper >>> 4) &&& 0xF).toUInt8 <<< 4) ||| (if h.nes2 then 8 else 0) ||| h.consoleType

/-- The 16-byte header as an array. NES 2.0 bytes are computed from the (zero, for iNES 1.0)
NES 2.0 fields, so an iNES 1.0 header serializes with zeros in bytes 8–15. -/
def toBytes (h : Header) : Array UInt8 :=
  #[0x4E, 0x45, 0x53, 0x1A,
    h.prgBanks.toUInt8, h.chrBanks.toUInt8, h.byte6, h.byte7,
    ((h.mapper >>> 8) &&& 0xF).toUInt8 ||| (h.submapper <<< 4),
    ((h.prgBanks >>> 8) &&& 0xF).toUInt8 ||| (((h.chrBanks >>> 8) &&& 0xF).toUInt8 <<< 4),
    h.prgRamShift ||| (h.prgNvramShift <<< 4),
    h.chrRamShift ||| (h.chrNvramShift <<< 4),
    h.timing, h.systemType, h.miscRoms, h.expansion]

end Header

/-- Serialize a header to its 16-byte iNES encoding. -/
def serialize (h : Header) : ByteArray := ⟨h.toBytes⟩

/-- Decode a header from bytes 4–15, the magic having been checked. -/
def decode (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) : Header :=
  let mirroring : Mirroring :=
    if b6 &&& 8 != 0 then .fourScreen else if b6 &&& 1 != 0 then .vertical else .horizontal
  let base : Header :=
    { prgBanks := b4.toUInt16, chrBanks := b5.toUInt16, mapper := (b6 >>> 4).toUInt16,
      submapper := 0, mirroring, battery := b6 &&& 2 != 0, trainer := b6 &&& 4 != 0,
      consoleType := 0, nes2 := false, prgRamShift := 0, prgNvramShift := 0,
      chrRamShift := 0, chrNvramShift := 0, timing := 0, systemType := 0, miscRoms := 0,
      expansion := 0 }
  if b7 &&& 0x0C == 0x08 then
    { base with
      prgBanks := b4.toUInt16 ||| ((b9 &&& 0xF).toUInt16 <<< 8)
      chrBanks := b5.toUInt16 ||| ((b9 >>> 4).toUInt16 <<< 8)
      mapper := (b6 >>> 4).toUInt16 ||| ((b7 >>> 4).toUInt16 <<< 4)
        ||| ((b8 &&& 0xF).toUInt16 <<< 8)
      submapper := b8 >>> 4
      consoleType := b7 &&& 3
      nes2 := true
      prgRamShift := b10 &&& 0xF, prgNvramShift := b10 >>> 4
      chrRamShift := b11 &&& 0xF, chrNvramShift := b11 >>> 4
      timing := b12 &&& 3, systemType := b13, miscRoms := b14 &&& 3
      expansion := b15 &&& 0x3F }
  else if b7 &&& 0x0C == 0x04 || b12 != 0 || b13 != 0 || b14 != 0 || b15 != 0 then
    -- archaic iNES: byte 7 (and 8–15) are garbage
    base
  else
    { base with
      mapper := (b6 >>> 4).toUInt16 ||| ((b7 >>> 4).toUInt16 <<< 4)
      consoleType := b7 &&& 3 }

/-- `true` iff the first four bytes are `"NES"` `$1A`. -/
@[inline] def magicOk (b0 b1 b2 b3 : UInt8) : Bool :=
  b0 == 0x4E && b1 == 0x45 && b2 == 0x53 && b3 == 0x1A

/-- Parse the 16-byte header at the start of `b`; `none` if `b` is shorter than 16 bytes or
does not start with `"NES\x1A"`. -/
def parse (b : ByteArray) : Option Header :=
  if h : 16 ≤ b.size then
    if magicOk b[0] b[1] b[2] b[3] then
      some (decode b[4] b[5] b[6] b[7] b[8] b[9] b[10] b[11] b[12] b[13] b[14] b[15])
    else none
  else none

/-- The immutable cartridge image. Mutable cartridge state (mapper registers, PRG-RAM,
CHR-RAM) lives elsewhere (`Nes.Cart.CartState`), so no bus operation can change a `Rom`. -/
structure Rom where
  header : Header
  /-- PRG-ROM bytes (CPU `$8000–$FFFF` via the mapper). -/
  prg : ByteArray
  /-- CHR-ROM bytes (PPU `$0000–$1FFF` via the mapper); empty means 8 KiB CHR-RAM. -/
  chr : ByteArray
  prg_pos : 0 < prg.size

namespace Rom

/-- Size of the CHR space the mapper indexes: CHR-ROM, or the 8 KiB CHR-RAM when the
cartridge has no CHR-ROM. -/
@[inline] def chrLen (rom : Rom) : Nat := if rom.chr.size = 0 then 8192 else rom.chr.size

theorem chrLen_pos (rom : Rom) : 0 < rom.chrLen := by
  unfold chrLen; split <;> omega

theorem chrLen_of_eq_zero {rom : Rom} (h : rom.chr.size = 0) : rom.chrLen = 8192 := by
  simp [chrLen, h]

theorem chrLen_of_ne_zero {rom : Rom} (h : rom.chr.size ≠ 0) : rom.chrLen = rom.chr.size := by
  simp [chrLen, h]

/-- Header mirroring (the hard-wired solder-pad setting). -/
@[inline] def mirroring (rom : Rom) : Mirroring := rom.header.mirroring

/-- Load an iNES / NES 2.0 image: header, optional trainer (skipped), PRG-ROM, CHR-ROM. -/
def load (b : ByteArray) : Except String Rom :=
  match parse b with
  | none => .error "not an iNES file (missing \"NES\\x1A\" header)"
  | some h =>
    let off := 16 + (if h.trainer then 512 else 0)
    let prgSize := h.prgRomSize
    let chrSize := h.chrRomSize
    if b.size < off + prgSize + chrSize then
      .error s!"truncated iNES file: {b.size} bytes, header needs {off + prgSize + chrSize}"
    else
      let prg := b.extract off (off + prgSize)
      let chr := b.extract (off + prgSize) (off + prgSize + chrSize)
      if hp : 0 < prg.size then .ok { header := h, prg, chr, prg_pos := hp }
      else .error "iNES file has no PRG-ROM"

end Rom

end Nes.Cart
