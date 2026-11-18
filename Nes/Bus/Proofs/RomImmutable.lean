import Nes.Cart.Mapper

/-!
# T-BUS-2 — ROM immutability

PRG-ROM and CHR-ROM are not fields of the mutable cartridge state: they live in `Rom`, which
every cartridge operation takes read-only (`CartState.cpuWrite : Rom → CartState → … →
CartState`). So the structural half of T-BUS-2 holds by the types; the theorems below make
it explicit for the bundled `Cart` and add the observable consequence for NROM.

## Spec

* `Cart.cpuWrite_rom`, `ppuWrite_rom`, `ppuA12_rom`: a CPU write, PPU write or A12 edge
  leaves `c.rom` unchanged (for every mapper constructor, since dispatch only rewrites
  `c.st`).
* `Cart.run_rom`: after any sequence of bus operations, `rom` is unchanged.
* `Cart.run_kind`: every cartridge keeps its mapper (constructor of `MapperState`: NROM,
  CNROM, MMC1, UxROM, AxROM) under any sequence of operations.
* `Cart.run_cpuRead_prg`: for every mapper, after any sequence of bus operations, a CPU read
  of `$8000–$FFFF` returns a byte of the original PRG-ROM (at the current bank offset);
  `Cart.run_ppuRead_chr`: likewise for PPU pattern reads on a CHR-ROM cartridge.
* `Cart.run_mapper_nrom`: an NROM cartridge stays NROM under any sequence of operations.
* `Cart.run_cpuRead_prg_nrom`: on an NROM cartridge, after any sequence of bus operations, a
  CPU read of `$8000–$FFFF` returns the original PRG-ROM byte at NROM's offset.
* `Cart.run_ppuRead_chr_nrom`: on an NROM cartridge with CHR-ROM, after any sequence of
  bus operations, a PPU read of the pattern tables returns the original CHR-ROM byte.
-/

namespace Nes.Cart

/-- A state-changing cartridge bus operation (reads do not change a `Cart`). -/
inductive BusOp where
  | cpuWrite (a : UInt16) (v : UInt8) (cyc : UInt64 := 0)
  | ppuWrite (a : UInt16) (v : UInt8)
  | ppuA12 (b : Bool)

namespace Cart

/-- Apply one bus operation. -/
def step (c : Cart) : BusOp → Cart
  | .cpuWrite a v cyc => c.cpuWrite a v cyc
  | .ppuWrite a v => c.ppuWrite a v
  | .ppuA12 b => c.ppuA12 b

/-- Apply a sequence of bus operations, left to right. -/
def run (c : Cart) (ops : List BusOp) : Cart := ops.foldl step c

theorem cpuWrite_rom (c : Cart) (a : UInt16) (v : UInt8) (cyc : UInt64 := 0) :
    (c.cpuWrite a v cyc).rom = c.rom := rfl
theorem ppuWrite_rom (c : Cart) (a : UInt16) (v : UInt8) : (c.ppuWrite a v).rom = c.rom := rfl
theorem ppuA12_rom (c : Cart) (b : Bool) : (c.ppuA12 b).rom = c.rom := rfl

theorem step_rom (c : Cart) (op : BusOp) : (c.step op).rom = c.rom := by
  cases op <;> rfl

theorem run_rom (c : Cart) (ops : List BusOp) : (c.run ops).rom = c.rom := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih => simp only [run, List.foldl_cons] at *; rw [ih, step_rom]

/-- The mapper constructor (which board the cartridge is). -/
def _root_.Nes.Cart.MapperState.kind : MapperState → Nat
  | .nrom _ => 0
  | .cnrom _ => 3
  | .mmc1 _ => 1
  | .uxrom _ => 2
  | .axrom _ => 7
  | .mmc3 _ => 4

theorem _root_.Nes.Cart.MapperState.kind_regWrite (rom : Rom) (m : MapperState) (a : UInt16)
    (v : UInt8) (cyc : UInt64) : (m.regWrite rom a v cyc).kind = m.kind := by
  cases m <;> rfl

theorem _root_.Nes.Cart.MapperState.kind_ppuA12 (b : Bool) (m : MapperState) :
    (m.ppuA12 b).kind = m.kind := by
  cases m <;> rfl

theorem step_kind (c : Cart) (op : BusOp) : (c.step op).st.mapper.kind = c.st.mapper.kind := by
  cases op with
  | cpuWrite a v cyc =>
    simp only [step, cpuWrite, CartState.cpuWrite, MapperState.kind_regWrite]
    split <;> rfl
  | ppuWrite a v =>
    simp only [step, ppuWrite, CartState.ppuWrite]
    split <;> rfl
  | ppuA12 b => exact MapperState.kind_ppuA12 b _

theorem run_kind (c : Cart) (ops : List BusOp) :
    (c.run ops).st.mapper.kind = c.st.mapper.kind := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih => simp only [run, List.foldl_cons] at *; rw [ih, step_kind]

private theorem cpuRead_prg_of_rom (d c : Cart) (hr : d.rom = c.rom) (a : UInt16)
    (ha : 0x8000 ≤ a) (ob : UInt8) :
    d.cpuRead a ob = c.rom.prg[d.st.mapper.prgOffset c.rom a] := by
  obtain ⟨drom, dst⟩ := d
  obtain ⟨crom, cst⟩ := c
  simp only at hr
  subst hr
  simp [cpuRead, CartState.cpuRead, ha]

theorem run_cpuRead_prg (c : Cart) (ops : List BusOp) (a : UInt16) (ha : 0x8000 ≤ a)
    (ob : UInt8) :
    (c.run ops).cpuRead a ob = c.rom.prg[(c.run ops).st.mapper.prgOffset c.rom a] :=
  cpuRead_prg_of_rom _ _ (run_rom c ops) a ha ob

private theorem ppuRead_chr_of_rom (d c : Cart) (hr : d.rom = c.rom)
    (hchr : c.rom.chr.size ≠ 0) (a : UInt16) :
    d.ppuRead a =
      c.rom.chr[(d.st.mapper.chrOffset c.rom a).val]'
        (Rom.chrLen_of_ne_zero hchr ▸ (d.st.mapper.chrOffset c.rom a).isLt) := by
  obtain ⟨drom, dst⟩ := d
  obtain ⟨crom, cst⟩ := c
  simp only at hr hchr
  subst hr
  simp [ppuRead, CartState.ppuRead, hchr]

theorem run_ppuRead_chr (c : Cart) (ops : List BusOp) (hchr : c.rom.chr.size ≠ 0)
    (a : UInt16) :
    (c.run ops).ppuRead a =
      c.rom.chr[((c.run ops).st.mapper.chrOffset c.rom a).val]'
        (Rom.chrLen_of_ne_zero hchr ▸ ((c.run ops).st.mapper.chrOffset c.rom a).isLt) :=
  ppuRead_chr_of_rom _ _ (run_rom c ops) hchr a

theorem step_mapper_nrom (c : Cart) (op : BusOp) (s : Nrom.State)
    (hm : c.st.mapper = .nrom s) : ∃ s', (c.step op).st.mapper = .nrom s' := by
  cases op <;>
    simp only [step, cpuWrite, ppuWrite, ppuA12, CartState.cpuWrite, CartState.ppuWrite,
      CartState.ppuA12] <;>
    (try split) <;> simp [hm, MapperState.regWrite, MapperState.ppuA12]

theorem run_mapper_nrom (c : Cart) (ops : List BusOp) (s : Nrom.State)
    (hm : c.st.mapper = .nrom s) : ∃ s', (c.run ops).st.mapper = .nrom s' := by
  induction ops generalizing c s with
  | nil => exact ⟨s, hm⟩
  | cons op ops ih =>
    obtain ⟨s', h'⟩ := step_mapper_nrom c op s hm
    exact ih (c.step op) s' h'

theorem run_cpuRead_prg_nrom (c : Cart) (ops : List BusOp) (s : Nrom.State)
    (hm : c.st.mapper = .nrom s) (a : UInt16) (ha : 0x8000 ≤ a) (ob : UInt8) :
    (c.run ops).cpuRead a ob = c.rom.prg[Nrom.prgOffset c.rom s a] := by
  obtain ⟨s', h'⟩ := run_mapper_nrom c ops s hm
  have hr := run_rom c ops
  simp only [cpuRead, CartState.cpuRead, ha, ↓reduceIte]
  generalize c.run ops = d at h' hr
  obtain ⟨drom, dst⟩ := d
  simp only at hr h' ⊢
  subst hr
  simp [h', MapperState.prgOffset, Mapper.prgOffset, Nrom.prgOffset]

theorem run_ppuRead_chr_nrom (c : Cart) (ops : List BusOp) (s : Nrom.State)
    (hm : c.st.mapper = .nrom s) (hchr : c.rom.chr.size ≠ 0) (a : UInt16) :
    (c.run ops).ppuRead a =
      c.rom.chr[(Nrom.chrOffset c.rom s a).val]'
        (Rom.chrLen_of_ne_zero hchr ▸ (Nrom.chrOffset c.rom s a).isLt) := by
  obtain ⟨s', h'⟩ := run_mapper_nrom c ops s hm
  have hr := run_rom c ops
  simp only [ppuRead, CartState.ppuRead]
  generalize c.run ops = d at h' hr
  obtain ⟨drom, dst⟩ := d
  simp only at hr h' ⊢
  subst hr
  simp [h', hchr, MapperState.chrOffset, Mapper.chrOffset, Nrom.chrOffset]

end Cart

end Nes.Cart
