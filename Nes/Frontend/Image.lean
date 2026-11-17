import Nes.Frontend.Palette

/-!
# `Nes.Frontend.Image` — frame → RGB → PPM / PNG, and the golden frame hash

Pure encoders used by the headless CLI (PLAN §5.6). Pure functions only; the caller writes the bytes.

* `toRgb frame emphasis` — 256×240 palette indices → 256×240×3 RGB bytes (`Nes.Frontend.rgbOf`).
* `ppm rgb w h` — binary PPM (`P6`, maxval 255).
* `png rgb w h` — PNG, 8-bit truecolour (colour type 2), no interlace; every row has filter
  byte 0, and the zlib stream uses only *stored* (uncompressed) deflate blocks of ≤ 65 535
  bytes, so no compressor is needed. Chunk CRCs are CRC-32 (IEEE, reflected, poly `0xEDB88320`,
  table-driven); the zlib trailer is Adler-32.
* `frameHash frame` — **the golden-hash definition**: FNV-1a 64-bit (offset basis
  `0xcbf29ce484222325`, prime `0x100000001b3`) over the frame's bytes in order — the 61 440
  palette-index bytes, row-major `y * 256 + x`. Emphasis and the palette are *not* hashed, so the
  hash is stable across platforms and palette changes. Printed as 16 lowercase hex digits.
-/

namespace Nes.Frontend

/-! ## Checksums -/

/-- CRC-32 lookup table (reflected polynomial `0xEDB88320`). -/
def crcTable : Array UInt32 := Id.run do
  let mut t := Array.mkEmpty 256
  for n in [0:256] do
    let mut c : UInt32 := n.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

/-- Continue a CRC-32 over `data[start, stop)`; `crc` is the *pre-conditioned* register
(start from `0xFFFFFFFF`, finish with `^^^ 0xFFFFFFFF`). -/
def crc32Update (crc : UInt32) (data : ByteArray) (start stop : Nat) : UInt32 := Id.run do
  let mut c := crc
  for i in [start:stop] do
    c := crcTable.getD ((c ^^^ (byteAt data i).toUInt32) &&& 0xFF).toNat 0 ^^^ (c >>> 8)
  return c

/-- CRC-32 (IEEE 802.3 / PNG / zlib) of a whole byte array. -/
def crc32 (data : ByteArray) : UInt32 :=
  crc32Update 0xFFFFFFFF data 0 data.size ^^^ 0xFFFFFFFF

/-- Adler-32 (zlib) of a whole byte array. -/
def adler32 (data : ByteArray) : UInt32 := Id.run do
  let mut a : UInt32 := 1
  let mut b : UInt32 := 0
  for i in [0:data.size] do
    a := (a + (byteAt data i).toUInt32) % 65521
    b := (b + a) % 65521
  return (b <<< 16) ||| a

/-- FNV-1a 64-bit of a byte array. -/
def fnv1a64 (data : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for i in [0:data.size] do
    h := (h ^^^ (byteAt data i).toUInt64) * 0x100000001b3
  return h

/-- Golden frame hash: FNV-1a 64 over the 256×240 palette-index bytes (see module doc). -/
def frameHash (frame : ByteArray) : UInt64 := fnv1a64 frame

/-- 16 lowercase hex digits. -/
def hex64 (h : UInt64) : String :=
  let digits := (List.range 16).reverse.map fun k =>
    Nat.toDigits 16 ((h >>> (4 * k).toUInt64) &&& 0xF).toNat |>.headD '0'
  String.ofList digits

/-! ## RGB and PPM -/

/-- Palette indices (one byte per pixel) → packed RGB (3 bytes per pixel). -/
def toRgb (frame : ByteArray) (emphasis : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (frame.size * 3)
  for i in [0:frame.size] do
    let (r, g, b) := rgbOf (byteAt frame i) emphasis
    out := out.push r |>.push g |>.push b
  return out

/-- Append the ASCII bytes of a string. -/
def pushStr (out : ByteArray) (s : String) : ByteArray :=
  out ++ s.toUTF8

/-- Binary PPM (`P6`, maxval 255) of `w × h` packed RGB. -/
def ppm (rgb : ByteArray) (w h : Nat) : ByteArray :=
  pushStr (ByteArray.emptyWithCapacity (rgb.size + 20)) s!"P6\n{w} {h}\n255\n" ++ rgb

/-! ## PNG -/

/-- Append a big-endian 32-bit word. -/
def pushU32BE (out : ByteArray) (x : UInt32) : ByteArray :=
  out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
    |>.push x.toUInt8

/-- Append a PNG chunk: length, type, data, CRC-32 over type ++ data. -/
def pushChunk (out : ByteArray) (ty : String) (data : ByteArray) : ByteArray :=
  let out := pushU32BE out data.size.toUInt32
  let tyStart := out.size
  let out := pushStr out ty ++ data
  let crc := crc32Update 0xFFFFFFFF out tyStart out.size ^^^ 0xFFFFFFFF
  pushU32BE out crc

/-- zlib stream (CMF `0x78`, FLG `0x01`: deflate, 32 KiB window, no dictionary, check bits OK)
holding `raw` in stored deflate blocks of at most 65 535 bytes, then the Adler-32 trailer. -/
def zlibStored (raw : ByteArray) : ByteArray := Id.run do
  let maxBlk := 65535
  let mut out := ByteArray.emptyWithCapacity (raw.size + raw.size / maxBlk * 5 + 16)
  out := out.push 0x78 |>.push 0x01
  let mut pos := 0
  -- ⌈size / 65535⌉ blocks, at least one (an empty final block for empty input).
  for _ in [0:max 1 ((raw.size + maxBlk - 1) / maxBlk)] do
    let len := min maxBlk (raw.size - pos)
    let final : UInt8 := if pos + len == raw.size then 1 else 0
    let l := len.toUInt16
    out := out.push final |>.push l.toUInt8 |>.push (l >>> 8).toUInt8
      |>.push (~~~l).toUInt8 |>.push ((~~~l) >>> 8).toUInt8
    out := raw.copySlice pos out out.size len
    pos := pos + len
  return pushU32BE out (adler32 raw)

/-- PNG (8-bit RGB, filter 0 on every row, stored-deflate IDAT) of `w × h` packed RGB. -/
def png (rgb : ByteArray) (w h : Nat) : ByteArray := Id.run do
  -- Scanlines: filter byte 0 followed by the row's 3w bytes.
  let stride := 3 * w
  let mut raw := ByteArray.emptyWithCapacity ((stride + 1) * h)
  for y in [0:h] do
    raw := raw.push 0
    raw := rgb.copySlice (y * stride) raw raw.size stride
  let ihdr := pushU32BE (pushU32BE .empty w.toUInt32) h.toUInt32
    |>.push 8 |>.push 2 |>.push 0 |>.push 0 |>.push 0
  let mut out := ByteArray.emptyWithCapacity (raw.size + raw.size / 65535 * 5 + 64)
  out := out ++ ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
  out := pushChunk out "IHDR" ihdr
  out := pushChunk out "IDAT" (zlibStored raw)
  out := pushChunk out "IEND" .empty
  return out

end Nes.Frontend
