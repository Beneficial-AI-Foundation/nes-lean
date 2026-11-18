import Nes.Frontend.Image

/-!
# Image encoder tests (`Nes.Frontend.Image`)

* Checksum vectors: CRC-32("123456789") = `0xCBF43926`, Adler-32("Wikipedia") = `0x11E60398`,
  FNV-1a 64("") = `0xcbf29ce484222325`, FNV-1a 64("a") = `0xaf63dc4c8601ec8c`.
* Structural PNG check in Lean: signature, chunk sequence IHDR/IDAT/IEND, every chunk CRC, and
  the stored-deflate payload reassembled equals the filtered scanlines (with Adler-32).
* Sizes of `toRgb` / `ppm`, palette sanity (`$30` white, `$0F` black, emphasis attenuation).
* A synthetic 256×240 gradient frame is written as PNG and PPM under `.lake/test-out/`; if
  `python3` exists the PNG is decoded with `zlib` + `struct` and compared to the RGB bytes.
-/

namespace Test.Image

open Nes.Frontend

def readU32BE (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat <<< 24 ||| (b.get! (i+1)).toNat <<< 16 ||| (b.get! (i+2)).toNat <<< 8
    ||| (b.get! (i+3)).toNat

/-- Walk the PNG; return the list of (type, data) chunks or an error. -/
def parseChunks (p : ByteArray) : Except String (Array (String × ByteArray)) := Id.run do
  let sig := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
  if p.extract 0 8 != sig then return .error "bad signature"
  let mut pos := 8
  let mut out := #[]
  for _ in [0:p.size] do
    if pos ≥ p.size then break
    if pos + 12 > p.size then return .error s!"truncated chunk at {pos}"
    let len := readU32BE p pos
    if pos + 12 + len > p.size then return .error s!"chunk overruns at {pos}"
    let ty := String.fromUTF8! (p.extract (pos+4) (pos+8))
    let data := p.extract (pos+8) (pos+8+len)
    let crc := readU32BE p (pos+8+len)
    if crc != (crc32 (p.extract (pos+4) (pos+8+len))).toNat then
      return .error s!"bad CRC in {ty}"
    out := out.push (ty, data)
    pos := pos + 12 + len
  return .ok out

/-- Undo `zlibStored` (stored blocks only); check header and Adler-32. -/
def inflateStored (z : ByteArray) : Except String ByteArray := Id.run do
  if z.get! 0 != 0x78 || ((z.get! 0).toNat * 256 + (z.get! 1).toNat) % 31 != 0 then
    return .error "bad zlib header"
  let mut pos := 2
  let mut out := ByteArray.empty
  for _ in [0:z.size] do
    let hdr := z.get! pos
    if hdr &&& 6 != 0 then return .error "non-stored block"
    let len := (z.get! (pos+1)).toNat ||| (z.get! (pos+2)).toNat <<< 8
    let nlen := (z.get! (pos+3)).toNat ||| (z.get! (pos+4)).toNat <<< 8
    if len ^^^ nlen != 0xFFFF then return .error "LEN/NLEN mismatch"
    out := out ++ z.extract (pos+5) (pos+5+len)
    pos := pos + 5 + len
    if hdr &&& 1 == 1 then break
  if pos + 4 != z.size then return .error "trailing bytes"
  if readU32BE z pos != (adler32 out).toNat then return .error "bad Adler-32"
  return .ok out

def okEq : Except String ByteArray → ByteArray → Bool
  | .ok a, b => a == b
  | .error _, _ => false

/-- Synthetic gradient: index = ((x / 16) + 16 * (y / 60)) mod 64. -/
def gradientFrame : ByteArray := Id.run do
  let mut f := ByteArray.emptyWithCapacity (256 * 240)
  for y in [0:240] do
    for x in [0:256] do
      f := f.push ((x / 16 + 16 * (y / 60)) % 64).toUInt8
  return f

def pyCheck : String := "
import sys, zlib, struct
p = open(sys.argv[1], 'rb').read(); rgb = open(sys.argv[2], 'rb').read()
assert p[:8] == b'\\x89PNG\\r\\n\\x1a\\n'
pos, idat, w, h = 8, b'', 0, 0
while pos < len(p):
    n, = struct.unpack('>I', p[pos:pos+4]); t = p[pos+4:pos+8]; d = p[pos+8:pos+8+n]
    c, = struct.unpack('>I', p[pos+8+n:pos+12+n])
    assert zlib.crc32(t + d) & 0xffffffff == c, t
    if t == b'IHDR': w, h = struct.unpack('>II', d[:8]); assert d[8:] == bytes([8,2,0,0,0])
    if t == b'IDAT': idat += d
    pos += 12 + n
raw = zlib.decompress(idat)
assert len(raw) == h * (3 * w + 1)
out = b''.join(raw[y*(3*w+1)+1:(y+1)*(3*w+1)] for y in range(h))
assert all(raw[y*(3*w+1)] == 0 for y in range(h))
assert out == rgb
print('python zlib decode OK %dx%d' % (w, h))
"

def run : IO UInt32 := do
  let mut fails : Nat := 0
  let check (name : String) (ok : Bool) : StateT Nat IO Unit := do
    unless ok do
      IO.println s!"  image FAIL: {name}"
      modify (· + 1)
  let ((), f1) ← (do
    check "crc32 123456789" (crc32 "123456789".toUTF8 == 0xCBF43926)
    check "adler32 Wikipedia" (adler32 "Wikipedia".toUTF8 == 0x11E60398)
    check "fnv1a64 empty" (fnv1a64 ByteArray.empty == 0xcbf29ce484222325)
    check "fnv1a64 a" (fnv1a64 "a".toUTF8 == 0xaf63dc4c8601ec8c)
    check "hex64" (hex64 0xcbf29ce484222325 == "cbf29ce484222325")
    check "palette $30 white" (rgbOf 0x30 0 == (255, 255, 255))
    check "palette $0F black" (rgbOf 0x0F 0 == (0, 0, 0))
    check "palette index masked" (rgbOf 0x70 0 == rgbOf 0x30 0)
    check "emphasis red" (rgbOf 0x30 1 == (255, 190, 190))
    check "emphasis all" (rgbOf 0x30 7 == (190, 190, 190))
    -- Stored-block boundaries: 0, exactly one full block, one byte over.
    for n in [0, 65535, 65536, 140000] do
      let raw := ByteArray.mk ((Array.range n).map (fun i : Nat => i.toUInt8))
      check s!"zlib roundtrip {n}" (okEq (inflateStored (zlibStored raw)) raw)
    ).run 0
  fails := fails + f1
  let frame := gradientFrame
  let rgb := toRgb frame 0
  let p := png rgb 256 240
  let m := ppm rgb 256 240
  let ((), f2) ← (do
    check "toRgb size" (rgb.size == 256 * 240 * 3)
    check "ppm size" (m.size == "P6\n256 240\n255\n".length + rgb.size)
    match parseChunks p with
    | .error e => check s!"png structure: {e}" false
    | .ok cs =>
      check "png chunk order" (cs.map (fun c : String × ByteArray => c.1) == #["IHDR", "IDAT", "IEND"])
      check "png IHDR" (cs[0]!.2 == ByteArray.mk #[0,0,1,0, 0,0,0,240, 8,2,0,0,0])
      let rows := Id.run do
        let mut r := ByteArray.empty
        for y in [0:240] do
          r := (r.push 0) ++ rgb.extract (y * 768) ((y + 1) * 768)
        return r
      check "png IDAT payload" (okEq (inflateStored cs[1]!.2) rows)
    ).run 0
  fails := fails + f2
  -- Write files and (optionally) cross-check with Python's zlib.
  let dir : System.FilePath := ".lake/test-out"
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / "gradient.png") p
  IO.FS.writeBinFile (dir / "gradient.ppm") m
  IO.FS.writeBinFile (dir / "gradient.rgb") rgb
  let mut pyNote := "python3 not run"
  try
    let out ← IO.Process.output
      { cmd := "python3", args := #["-I", "-c", pyCheck, (dir / "gradient.png").toString,
          (dir / "gradient.rgb").toString] }
    if out.exitCode == 0 then pyNote := String.ofList (out.stdout.toList.filter (· != '\n'))
    else
      IO.println s!"  image FAIL: python check\n{out.stderr}"
      fails := fails + 1
  catch _ => pure ()
  IO.println s!"image: {if fails == 0 then "PASS" else s!"{fails} FAIL"} — checksums, PNG {p.size} B, PPM {m.size} B, gradient hash {hex64 (frameHash frame)}; {pyNote}"
  return if fails == 0 then 0 else 1

end Test.Image
