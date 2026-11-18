import Nes.Cpu.Core

/-!
# blargg CPU test ROMs (test-only system scaffolding)

Runs blargg's CPU test ROMs (`instr_test-v5`, `instr_misc`, `instr_timing`, `cpu_dummy_*`,
`cpu_exec_space`, `cpu_reset`, `cpu_interrupts_v2`) on the cycle-level `Nes.Cpu.Core`, driven
one bus cycle at a time (`busOp` → access on the bus below → `complete`).

## blargg `$6000` protocol

`$6000` = status (`$80` running, `$81` "press reset after ≥ 100 ms", anything else = final
result, `$00` = pass); `$6001–$6003` = signature `$DE $B0 $61` once the status is valid;
`$6004…` = zero-terminated ASCII text output.

## Scaffolding (NOT the real system — the real PPU is M3, the real APU M5)

* iNES loader for mappers 0 (NROM), 1 (MMC1: serial port with the consecutive-write ignore,
  PRG banking modes 0–3, mirroring) and 3 (CNROM: CHR bank select). PRG-RAM (8 KiB) at
  `$6000–$7FFF` is always enabled. CHR-RAM (8 KiB) when the header has no CHR ROM.
* 2 KiB RAM mirrored over `$0000–$1FFF`; CPU open bus (last byte on the data bus) for
  unmapped reads.
* **Crude PPU register file** (`$2000–$3FFF`): a dot counter (3 dots per CPU cycle, 341×262
  dots per frame, no odd-frame skip) sets the vblank flag at scanline 241 dot 1 and clears it
  at the pre-render line; `$2002` read returns/clears it and resets the `w` toggle; NMI line
  = vblank ∧ `$2000.7`. `$2003/$2004` OAM (byte 2 of each sprite reads back with bits 2–4
  clear), `$2005/$2006` toggle and `t`/`v`, `$2007` with the read buffer, increment 1/32,
  palette reads unbuffered. Nametables follow the cartridge mirroring. No rendering, no
  sprite 0 / overflow, no vblank race suppression, PPU I/O latch without decay.
* **Crude APU**: pulse 1's length counter (load/halt/enable, `$4015` bit 0, clocked on
  half frames and by a `$4017` write with bit 7 — blargg's timing tests sync on it) and the
  frame counter IRQ (4-step mode, flag set at sequencer cycles
  29828–29830, period 29830; `$4017` write resets the sequencer 3/4 cycles later; bit 6
  inhibits and clears) and `$4015` read (bit 6 = frame IRQ, cleared by the read; bit 0 =
  pulse 1 length ≠ 0; other channels/DMC read as 0). No DMC DMA.
* OAM DMA (`$4014`): the CPU is halted for 1 (+1 on an odd cycle) + 512 cycles that copy the
  page to OAM; the CPU's interrupt detectors are not clocked during the DMA (approximation).
-/

namespace Test.Blargg

open Nes Nes.Cpu

/-! ## The test bus -/

structure Bus where
  ram : ByteArray
  prgRam : ByteArray
  prg : ByteArray
  chr : ByteArray
  chrIsRam : Bool
  mapper : UInt8
  /-- Number of 16 KiB PRG banks. -/
  prgBanks : UInt32
  /-- Nametable mirroring: 0 = single A, 1 = single B, 2 = vertical, 3 = horizontal. -/
  mirror : UInt8
  -- MMC1 / CNROM
  shift : UInt8 := 0
  shiftCount : UInt8 := 0
  mmcCtrl : UInt8 := 0x0C
  mmcPrg : UInt8 := 0
  chrBank : UInt8 := 0
  /-- Cycle number of the previous CPU write (MMC1 ignores writes on consecutive cycles). -/
  lastWriteCyc : UInt64 := 0
  /-- CPU data bus (open bus). -/
  openBus : UInt8 := 0
  -- crude PPU
  dot : UInt32 := 0
  vbl : Bool := false
  /-- A `$2002` read one dot before vblank starts suppresses the flag (and NMI) this frame. -/
  vblSuppress : Bool := false
  /-- PPU dots run before the CPU's bus access within a CPU cycle (scaffolding knob). -/
  ppuPre : UInt32 := 2
  pctrl : UInt8 := 0
  pmask : UInt8 := 0
  oamAddr : UInt8 := 0
  oam : ByteArray
  vaddr : UInt16 := 0
  taddr : UInt16 := 0
  wtog : Bool := false
  readBuf : UInt8 := 0
  ppuLatch : UInt8 := 0
  vram : ByteArray
  pal : ByteArray
  -- crude APU frame counter
  frameCyc : UInt32 := 0
  frameMode5 : Bool := false
  irqInhibit : Bool := false
  frameIrq : Bool := false
  /-- Pulse 1 length counter (the only channel modelled: blargg's timing tests sync on it). -/
  len1 : UInt8 := 0
  halt1 : Bool := false
  en1 : Bool := false
  /-- Cycles until a pending `$4017` sequencer reset (0 = none). -/
  frameResetIn : UInt8 := 0
  -- OAM DMA
  dmaPending : Bool := false
  dmaPage : UInt8 := 0
  -- bookkeeping
  cycles : UInt64 := 0
  /-- Set by a write to `$6000`; the run loop stops so the driver can inspect it. -/
  statusEvent : Bool := false

private def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Parse an iNES image (mappers 0, 1, 3). -/
def load (rom : ByteArray) : Except String Bus := do
  if rom.size < 16 || rom.get! 0 != 0x4E || rom.get! 1 != 0x45 || rom.get! 2 != 0x53
      || rom.get! 3 != 0x1A then
    throw "not an iNES file"
  let nPrg := (rom.get! 4).toNat
  let nChr := (rom.get! 5).toNat
  let f6 := rom.get! 6
  let mapper := (f6 >>> 4) ||| (rom.get! 7 &&& 0xF0)
  unless mapper == 0 || mapper == 1 || mapper == 3 do throw s!"unsupported mapper {mapper}"
  let base := 16 + (if f6 &&& 0x04 != 0 then 512 else 0)
  let prgEnd := base + nPrg * 0x4000
  let chrEnd := prgEnd + nChr * 0x2000
  if nPrg == 0 || rom.size < chrEnd then throw "truncated image"
  let prg := rom.extract base prgEnd
  let chr := if nChr == 0 then zeros 0x2000 else rom.extract prgEnd chrEnd
  pure { ram := zeros 0x800, prgRam := zeros 0x2000, prg, chr, chrIsRam := nChr == 0,
         mapper, prgBanks := nPrg.toUInt32, mirror := if f6 &&& 1 != 0 then 2 else 3,
         oam := zeros 256, vram := zeros 0x800, pal := zeros 32 }

/-! ### Cartridge -/

@[inline] def prgOffset (b : Bus) (a : UInt16) : Nat :=
  if b.mapper == 1 then
    let mode := (b.mmcCtrl >>> 2) &&& 3
    let bank := (b.mmcPrg &&& 0x0F).toUInt32
    let lo := (a &&& 0x3FFF).toUInt32
    let hiHalf := a ≥ 0xC000
    let bk : UInt32 :=
      if mode < 2 then (bank &&& 0x0E) + (if hiHalf then 1 else 0)
      else if mode == 2 then (if hiHalf then bank else 0)
      else (if hiHalf then b.prgBanks - 1 else bank)
    ((bk % b.prgBanks) * 0x4000 + lo).toNat
  else
    (a - 0x8000).toNat % b.prg.size

@[inline] def mmc1Write (b : Bus) (a : UInt16) (v : UInt8) : Bus :=
  if b.lastWriteCyc + 1 == b.cycles then b
  else if v &&& 0x80 != 0 then
    { b with shift := 0, shiftCount := 0, mmcCtrl := b.mmcCtrl ||| 0x0C }
  else
    let sh := (b.shift >>> 1) ||| ((v &&& 1) <<< 4)
    if b.shiftCount < 4 then { b with shift := sh, shiftCount := b.shiftCount + 1 }
    else
      let b := { b with shift := 0, shiftCount := 0 }
      match ((a >>> 13) &&& 3).toNat with
      | 0 => { b with mmcCtrl := sh, mirror := sh &&& 3 }
      | 1 => { b with chrBank := sh }
      | 2 => b
      | _ => { b with mmcPrg := sh }

/-! ### Crude PPU memory -/

@[inline] def ntIndex (b : Bus) (a : UInt16) : Nat :=
  let a := a &&& 0x0FFF
  let i : UInt16 := match b.mirror with
    | 0 => a &&& 0x3FF
    | 1 => 0x400 ||| (a &&& 0x3FF)
    | 2 => a &&& 0x7FF
    | _ => ((a >>> 1) &&& 0x400) ||| (a &&& 0x3FF)
  i.toNat

@[inline] def palIndex (a : UInt16) : Nat :=
  let i := a &&& 0x1F
  (if i &&& 0x13 == 0x10 then i &&& 0x0F else i).toNat

@[inline] def chrIndex (b : Bus) (a : UInt16) : Nat :=
  if b.mapper == 3 then (b.chrBank.toNat * 0x2000 + a.toNat) % b.chr.size
  else a.toNat % b.chr.size

@[inline] def ppuRead (b : Bus) (a : UInt16) : UInt8 :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then b.chr.get! (chrIndex b a)
  else if a < 0x3F00 then b.vram.get! (ntIndex b a)
  else b.pal.get! (palIndex a)

@[inline] def ppuWrite (b : Bus) (a : UInt16) (v : UInt8) : Bus :=
  let a := a &&& 0x3FFF
  if a < 0x2000 then
    if b.chrIsRam then { b with chr := b.chr.set! (chrIndex b a) v } else b
  else if a < 0x3F00 then { b with vram := b.vram.set! (ntIndex b a) v }
  else { b with pal := b.pal.set! (palIndex a) (v &&& 0x3F) }

/-- APU length-counter load table. -/
def lengthTable : Array UInt8 := #[
  10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
  12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30]

@[inline] def vInc (b : Bus) : UInt16 := if b.pctrl &&& 0x04 != 0 then 32 else 1

/-! ### Clock -/

def frameDots : UInt32 := 341 * 262
def vblSetDot : UInt32 := 241 * 341 + 1
def vblClrDot : UInt32 := 261 * 341 + 1

/-- Advance the crude PPU by `n ≤ 3` dots (vblank set/clear, `$2002` race suppression). -/
@[inline] def advDots (b : Bus) (n : UInt32) : Bus :=
  let d0 := b.dot
  let d1 := d0 + n
  let d := if d1 ≥ frameDots then d1 - frameDots else d1
  -- did we cross x in (d0, d0+n]?
  let crosses (x : UInt32) : Bool :=
    (d0 < x && x ≤ d1) || (d1 ≥ frameDots && x ≤ d1 - frameDots)
  if crosses vblSetDot then { b with dot := d, vbl := !b.vblSuppress, vblSuppress := false }
  else if crosses vblClrDot then { b with dot := d, vbl := false }
  else { b with dot := d }

/-- Start one CPU cycle: `ppuPre` PPU dots happen before the CPU's bus access (the remaining
`3 - ppuPre` after it, `tickPost`), and one APU frame-counter cycle. -/
@[inline] def tick (b : Bus) : Bus :=
  let b := advDots b b.ppuPre
  let (fc, fr) :=
    if b.frameResetIn == 0 then (b.frameCyc + 1, (0 : UInt8))
    else if b.frameResetIn == 1 then (0, 0)
    else (b.frameCyc + 1, b.frameResetIn - 1)
  let irqStep := !b.frameMode5 && (fc == 29828 || fc == 29829 || fc == 29830)
  let frameIrq := b.frameIrq || (irqStep && !b.irqInhibit)
  let half := fc == 14913 || (if b.frameMode5 then fc == 37281 else fc == 29829)
  let len1 := if half && !b.halt1 && b.len1 != 0 then b.len1 - 1 else b.len1
  let fc := if b.frameMode5 then (if fc ≥ 37282 then 0 else fc)
    else if fc ≥ 29830 then 0 else fc
  { b with frameCyc := fc, frameResetIn := fr, frameIrq, len1, cycles := b.cycles + 1 }

/-- Finish one CPU cycle: the PPU dots after the bus access. -/
@[inline] def tickPost (b : Bus) : Bus := advDots b (3 - b.ppuPre)

/-! ### CPU bus access -/

/-- CPU read; the value read is left in `openBus`. -/
@[inline] def read (b : Bus) (a : UInt16) : Bus :=
  if a < 0x2000 then { b with openBus := b.ram.get! (a &&& 0x7FF).toNat }
  else if a < 0x4000 then
    match (a &&& 7).toNat with
    | 2 =>
      let v := (if b.vbl then 0x80 else 0) ||| (b.ppuLatch &&& 0x1F)
      { b with openBus := v, ppuLatch := v, vbl := false, wtog := false,
               vblSuppress := b.dot + 1 == vblSetDot }
    | 4 =>
      let i := b.oamAddr
      let x := b.oam.get! i.toNat
      let v := if i &&& 3 == 2 then x &&& 0xE3 else x
      { b with openBus := v, ppuLatch := v }
    | 7 =>
      let pa := b.vaddr &&& 0x3FFF
      let (v, buf) :=
        if pa ≥ 0x3F00 then
          ((ppuRead b pa) ||| (b.ppuLatch &&& 0xC0), ppuRead b (pa - 0x1000))
        else (b.readBuf, ppuRead b pa)
      { b with openBus := v, ppuLatch := v, readBuf := buf, vaddr := b.vaddr + vInc b }
    | _ => { b with openBus := b.ppuLatch }
  else if a < 0x4020 then
    if a == 0x4015 then
      let v := (if b.frameIrq then 0x40 else 0) ||| (b.openBus &&& 0x20) |||
        (if b.len1 != 0 then 1 else 0)
      { b with openBus := v, frameIrq := false }
    else if a == 0x4016 || a == 0x4017 then { b with openBus := b.openBus &&& 0xE0 }
    else b
  else if a < 0x6000 then b
  else if a < 0x8000 then { b with openBus := b.prgRam.get! (a - 0x6000).toNat }
  else { b with openBus := b.prg.get! (prgOffset b a) }

/-- CPU write. -/
@[inline] def write (b : Bus) (a : UInt16) (v : UInt8) : Bus :=
  let b' :=
    if a < 0x2000 then { b with ram := b.ram.set! (a &&& 0x7FF).toNat v }
    else if a < 0x4000 then
      let b := { b with ppuLatch := v }
      match (a &&& 7).toNat with
      | 0 => { b with pctrl := v,
                      taddr := (b.taddr &&& (0xF3FF : UInt16)) ||| ((v &&& 3).toUInt16 <<< 10) }
      | 1 => { b with pmask := v }
      | 3 => { b with oamAddr := v }
      | 4 => { b with oam := b.oam.set! b.oamAddr.toNat v, oamAddr := b.oamAddr + 1 }
      | 5 => { b with wtog := !b.wtog }
      | 6 =>
        if !b.wtog then
          { b with wtog := true,
                   taddr := (b.taddr &&& (0x00FF : UInt16)) ||| ((v &&& 0x3F).toUInt16 <<< 8) }
        else
          let t := (b.taddr &&& 0xFF00) ||| v.toUInt16
          { b with wtog := false, taddr := t, vaddr := t }
      | 7 => { ppuWrite b b.vaddr v with vaddr := b.vaddr + vInc b }
      | _ => b
    else if a < 0x4020 then
      if a == 0x4014 then { b with dmaPending := true, dmaPage := v }
      else if a == 0x4000 then { b with halt1 := v &&& 0x20 != 0 }
      else if a == 0x4003 then
        if b.en1 then { b with len1 := lengthTable[(v >>> 3).toNat]! } else b
      else if a == 0x4015 then
        { b with en1 := v &&& 1 != 0, len1 := if v &&& 1 != 0 then b.len1 else 0 }
      else if a == 0x4017 then
        { b with frameMode5 := v &&& 0x80 != 0, irqInhibit := v &&& 0x40 != 0,
                 frameIrq := if v &&& 0x40 != 0 then false else b.frameIrq,
                 frameResetIn := if b.cycles % 2 == 0 then 3 else 4,
                 len1 := if v &&& 0x80 != 0 && !b.halt1 && b.len1 != 0 then b.len1 - 1
                   else b.len1 }
      else b
    else if a < 0x6000 then b
    else if a < 0x8000 then
      { b with prgRam := b.prgRam.set! (a - 0x6000).toNat v, statusEvent := a == 0x6000 }
    else if b.mapper == 1 then mmc1Write b a v
    else if b.mapper == 3 then { b with chrBank := v }
    else b
  { b' with openBus := v, lastWriteCyc := b.cycles }

/-! ### Run loop -/

@[inline] def lines (b : Bus) (reset : Bool) : IntLines :=
  { nmi := b.vbl && b.pctrl &&& 0x80 != 0, irq := b.frameIrq, reset }

/-- OAM DMA: `n` remaining DMA cycles (`n = 512 … 1` copy, odd = read, even = write). -/
def dmaLoop : Nat → UInt16 → Bus → Bus
  | 0, _, b => b
  | n + 1, src, b =>
    let b := tick b
    if n % 2 == 1 then dmaLoop n src (tickPost (read b src))
    else
      let v := b.openBus
      let b := tickPost { b with oam := b.oam.set! b.oamAddr.toNat v, oamAddr := b.oamAddr + 1 }
      dmaLoop n (src + 1) b

@[inline] def doDma (b : Bus) : Bus :=
  let b := { b with dmaPending := false }
  let b := tickPost (tick b)
  let b := if b.cycles % 2 == 1 then tickPost (tick b) else b
  dmaLoop 512 (b.dmaPage.toUInt16 <<< 8) b

/-- Run up to `fuel` CPU cycles, stopping early after a write to `$6000`. -/
def runLoop : Nat → Core → Bus → Core × Bus
  | 0, c, b => (c, b)
  | fuel + 1, c, b =>
    if b.statusEvent then (c, b)
    else
      let b := if b.dmaPending then doDma b else b
      let b := tick b
      match c.busOp with
      | .read a =>
        let b := tickPost (read b a)
        runLoop fuel (c.complete (lines b false) b.openBus) b
      | .write a v =>
        let b := tickPost (write b a v)
        runLoop fuel (c.complete (lines b false) v) b

/-- One cycle with the RESET line asserted. -/
def resetCycle (c : Core) (b : Bus) : Core × Bus :=
  let b := tick b
  match c.busOp with
  | .read a => let b := tickPost (read b a); (c.complete (lines b true) b.openBus, b)
  | .write a v => let b := tickPost (write b a v); (c.complete (lines b true) v, b)

/-! ## Driver -/

def hexByte (b : UInt8) : String :=
  let d (n : Nat) := Char.ofNat (if n < 10 then 48 + n else 55 + n)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

def hex16 (w : UInt16) : String := hexByte (w >>> 8).toUInt8 ++ hexByte w.toUInt8

def statusText (b : Bus) : String := Id.run do
  let mut s := ""
  for i in [4:0x2000] do
    let c := b.prgRam.get! i
    if c == 0 then break
    s := s.push (Char.ofNat c.toNat)
  return s

/-- Side-effect-free read of RAM / PRG-RAM / PRG-ROM (for hang detection). -/
def peek (b : Bus) (a : UInt16) : UInt8 :=
  if a < 0x2000 then b.ram.get! (a &&& 0x7FF).toNat
  else if a < 0x6000 then 0
  else if a < 0x8000 then b.prgRam.get! (a - 0x6000).toNat
  else b.prg.get! (prgOffset b a)

/-- Is the CPU (PC = `pc`) inside a short `t: … JMP t` loop with no exit (how the old blargg
shells end: `forever: sei; lda #0; sta PPUCTRL; jmp forever`)? Heuristic: confirmed by the
screen text before it is believed. -/
def spinning (b : Bus) (pc : UInt16) : Bool :=
  (List.range 10).any fun k =>
    let q := pc + k.toUInt16
    let t := (peek b (q + 1)).toUInt16 ||| ((peek b (q + 2)).toUInt16 <<< 8)
    peek b q == 0x4C && t ≤ pc && q - t ≤ 8

/-- Screen text: nametable 0 (32×30 tiles) read as ASCII — the old blargg shells (no `$6000`
output) print with an ASCII tile set. -/
def screenText (b : Bus) : String := Id.run do
  let mut out := ""
  for row in [0:30] do
    let mut line := ""
    for col in [0:32] do
      let t := b.vram.get! (row * 32 + col)
      line := line.push (if 0x20 ≤ t && t < 0x7F then Char.ofNat t.toNat else ' ')
    let l := line.trimAsciiEnd.toString
    unless l.isEmpty do out := out ++ l ++ "\n"
  return out

/-- Verdict scraped from the screen of a ROM without the `$6000` protocol: `some 0` pass,
`some 1` fail, `none` undecided. -/
def screenVerdict (txt : String) : Option UInt8 :=
  let has (w : String) := (txt.splitOn w).length > 1
  if has "Passed" || has "PASSED" || has "All tests complete" then some 0
  else if has "Failed" || has "FAILED" || has "Error" then some 1
  else none

def signatureOk (b : Bus) : Bool :=
  b.prgRam.get! 1 == 0xDE && b.prgRam.get! 2 == 0xB0 && b.prgRam.get! 3 == 0x61

/-- Cycles to wait after a `$81` reset request (≈ 112 ms at 1.79 MHz). -/
def resetDelay : Nat := 200000

/-- Run a ROM until it reports a final status at `$6000` or `maxCycles` elapse. Returns the
status (`$FF` with a note on timeout/load error) and the text output at `$6004`. -/
def runRom (path : System.FilePath) (maxCycles : Nat) (ppuPre : UInt32 := 2) :
    IO (UInt8 × String) := do
  let b ← match load (← IO.FS.readBinFile path) with
    | .ok b => pure { b with ppuPre }
    | .error e => return (0xFF, s!"load error: {e}")
  let mut c := Core.powerOn State.init
  let mut b := b
  let mut resetAt : Option UInt64 := none
  while b.cycles.toNat < maxCycles do
    let budget := match resetAt with
      | some t => if t > b.cycles then (t - b.cycles).toNat else 0
      | none => 1000000
    let (c', b') := runLoop budget c b
    c := c'; b := b'
    if b.statusEvent then
      b := { b with statusEvent := false }
    -- inspect status (on any $6000 write or chunk end)
    if let some t := resetAt then
      if b.cycles ≥ t then
        let (c', b') := resetCycle c b
        c := c'; b := b'; resetAt := none
      continue
    if signatureOk b then
      let st := b.prgRam.get! 0
      if st == 0x81 then
        resetAt := some (b.cycles + resetDelay.toUInt64)
      else if st != 0x80 then
        -- let the ROM finish printing (it writes the text before the status)
        let (c', b') := runLoop 1000 c { b with statusEvent := false }
        c := c'; b := b'
        return (st, statusText b)
    else if spinning b c.ms.cpu.pc then
      -- no $6000 protocol and the program has ended: scrape the screen
      let txt := screenText b
      if let some v := screenVerdict txt then return (v, "[screen] " ++ txt)
  if !signatureOk b then
    -- no $6000 protocol (e.g. cpu_timing_test6 loops forever after printing): screen verdict
    let txt := screenText b
    if let some v := screenVerdict txt then
      return (v, s!"[screen after {b.cycles} cycles] " ++ txt)
  return (0xFF, s!"TIMEOUT after {b.cycles} cycles at PC ${hex16 c.ms.cpu.pc}; " ++
    s!"text so far: {statusText b}; screen: {screenText b}")

def romDir : System.FilePath := "testdata/nes-test-roms"

/-- ROMs that pass with the CPU core and this scaffolding, with their cycle budget.
Not listed: `instr_test-v5/all_instrs.nes`, `rom_singles/03-immediate.nes` and
`blargg_nes_cpu_test5/cpu.nes` fail only on `$AB` (ATX/LXA #imm): the core uses the
SingleStepTests magic constant `A, X := (A | $EE) & #`, blargg's checksums expect `$FF`
(`A, X := #`). -/
def passing : List (String × Nat) := [
  ("instr_test-v5/official_only.nes", 60000000),
  ("instr_test-v5/rom_singles/01-basics.nes", 10000000),
  ("instr_test-v5/rom_singles/02-implied.nes", 10000000),
  ("instr_test-v5/rom_singles/04-zero_page.nes", 10000000),
  ("instr_test-v5/rom_singles/05-zp_xy.nes", 20000000),
  ("instr_test-v5/rom_singles/06-absolute.nes", 10000000),
  ("instr_test-v5/rom_singles/07-abs_xy.nes", 20000000),
  ("instr_test-v5/rom_singles/08-ind_x.nes", 10000000),
  ("instr_test-v5/rom_singles/09-ind_y.nes", 10000000),
  ("instr_test-v5/rom_singles/10-branches.nes", 10000000),
  ("instr_test-v5/rom_singles/11-stack.nes", 10000000),
  ("instr_test-v5/rom_singles/12-jmp_jsr.nes", 10000000),
  ("instr_test-v5/rom_singles/13-rts.nes", 10000000),
  ("instr_test-v5/rom_singles/14-rti.nes", 10000000),
  ("instr_test-v5/rom_singles/15-brk.nes", 10000000),
  ("instr_test-v5/rom_singles/16-special.nes", 10000000),
  ("instr_misc/instr_misc.nes", 20000000),
  ("instr_timing/instr_timing.nes", 60000000),
  ("cpu_dummy_reads/cpu_dummy_reads.nes", 20000000),
  ("cpu_dummy_writes/cpu_dummy_writes_oam.nes", 20000000),
  ("cpu_dummy_writes/cpu_dummy_writes_ppumem.nes", 20000000),
  ("cpu_exec_space/test_cpu_exec_space_apu.nes", 20000000),
  ("cpu_exec_space/test_cpu_exec_space_ppuio.nes", 20000000),
  ("cpu_interrupts_v2/cpu_interrupts.nes", 40000000),
  ("cpu_reset/ram_after_reset.nes", 20000000),
  ("cpu_reset/registers.nes", 20000000),
  ("blargg_nes_cpu_test5/official.nes", 60000000),
  ("cpu_timing_test6/cpu_timing_test.nes", 35000000)
]

/-- Last non-empty line of the ROM's text, ANSI colour codes stripped. -/
def lastLine (txt : String) : String :=
  let noEsc := (txt.splitOn "\x1b[").map (fun s => (s.dropWhile (· != 'm')).drop 1 |>.toString)
  let clean := match txt.splitOn "\x1b[" with
    | first :: _ => first ++ String.join (noEsc.drop 1)
    | [] => txt
  let ls := (clean.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  ls.getLastD ""

/-- Run `passing`; returns the number of failing ROMs. -/
def run : IO UInt32 := do
  unless ← romDir.pathExists do
    IO.println "blargg: SKIPPED (no testdata; run scripts/fetch-testdata.sh)"
    return 0
  let mut fails : UInt32 := 0
  for (r, maxCycles) in passing do
    let (st, txt) ← runRom (romDir / r) maxCycles
    let ok := st == 0
    unless ok do fails := fails + 1
    IO.println s!"blargg {r}: {if ok then "PASS" else s!"FAIL ${hexByte st}"} ({lastLine txt})"
  IO.println s!"blargg: {passing.length - fails.toNat}/{passing.length} passed"
  return fails

end Test.Blargg
