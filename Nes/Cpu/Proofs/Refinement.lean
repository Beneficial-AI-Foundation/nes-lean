import Nes.Cpu.Proofs.Refinement.Prefix

/-!
# `Nes.Cpu.Proofs.Refinement` — T-REF-1: the cycle model refines the ISA model

## Spec

* `T_REF_1_stmt`: for every CPU state `s` that is not halted and every memory `m`,
  `microStep s m = step s m`: running the micro-machine from the boundary `ofState s` (no
  pending interrupt) to the next boundary against flat memory yields exactly `Isa.step`'s
  registers, memory, and cycle count. `microStep` counts one cycle per bus operation, so the
  cycle equality says the micro-machine emits exactly `cycles(op)` + page-cross/branch penalty
  bus operations.
* `ClassRefines c`: the same, restricted to opcodes of instruction class `c`.
  `T_REF_1_of_classes`: `(∀ c, ClassRefines c) → T_REF_1_stmt`.
* Proved so far: `T_REF_1_read` (86 opcodes), `T_REF_1_imm` (24), `T_REF_1_imp` (28),
  `T_REF_1_write` (22, including the unstable `SHY/SHX/AHX/TAS` stores): 160 of the 256
  opcodes, every addressing mode they use, page-cross cycles included. Remaining classes:
  `rmw` (66), `jam` (12), `branch` (8), `push`, `pull` (2 each), `jsr`, `rts`, `rti`, `brk`,
  `jmpAbs`, `jmpInd` (1 each).

## Method (compositional)

`runInstr_prefix` = opcode fetch (`runInstr_fetch`) + the addressing prefix lemma for the
opcode's mode (`prefix_spec`, file `Refinement/Prefix`), leaving an explicit machine at the
start of the class suffix. A class proof then runs the suffix (`runInstr_last` for the final
cycle), and matches `Isa.step` using: an `exec_<class>` lemma (`Isa.exec` = the micro
`exec*` helper for the instructions of that class), and a `<class>_table` fact over all 256
opcodes (`decide +kernel`): which instructions/modes occur in the class, and the cycle-count
identity `1 + prefixCycles + suffix cycles = cycles + extraCycles`.
-/

set_option linter.unusedSimpArgs false

namespace Nes.Cpu.Proofs.Refinement
open Nes Nes.Cpu MicroState

/-- **T-REF-1** (statement). -/
def T_REF_1_stmt : Prop :=
  ∀ (s : State) (m : Mem), s.halted = false → microStep s m = step s m

/-- T-REF-1 restricted to the opcodes of one instruction class. -/
def ClassRefines (c : Cls) : Prop :=
  ∀ (s : State) (m : Mem), s.halted = false → classify (decode (m.read s.pc)) = c →
    microStep s m = step s m

theorem T_REF_1_of_classes (h : ∀ c, ClassRefines c) : T_REF_1_stmt :=
  fun s m hs => h _ s m hs rfl

/-- Instructions whose `Isa.exec` is "read the operand, apply `execRead`" (read and immediate
classes). -/
def readOk : Instr → Bool
  | .LDA | .LDX | .LDY | .LAX | .ADC | .SBC | .AND | .ORA | .EOR | .CMP | .CPX | .CPY | .BIT
  | .ANC | .ALR | .ARR | .SBX | .LAS | .XAA | .NOP => true
  | _ => false

theorem exec_read (e : Entry) (hr : readOk e.instr = true) (s : State) (m : Mem) (ea : UInt16)
    (cr : Bool) :
    exec e s m ea cr = (execRead e { s with pc := s.pc + e.mode.len } (m.read ea), m) := by
  obtain ⟨i, mode, cy, pcr, off⟩ := e
  cases i <;> simp only [readOk] at hr <;>
    first | (exact absurd hr (by decide)) | (simp only [exec, execRead] <;> rfl)

theorem decode_eq_decodeFin (op : UInt8) : decode op = decodeFin ⟨op.toNat, op.toNat_lt⟩ := rfl

/-- Every suffix is non-empty and starts with an unconditional micro-op. -/
theorem suffix_head : ∀ c : Cls, (suffix c).size ≠ 0 ∧ isCond ((suffix c).getD 0 .jamHalt) = false := by
  intro c; cases c <;> decide

theorem prefixCycles_le (mode : AddrMode) (pc cr : Bool) : prefixCycles mode pc cr ≤ 4 := by
  cases mode <;> cases pc <;> cases cr <;> decide

/-- Classes whose program starts with the shared addressing prefix (all but `JSR`, `JMP abs`). -/
def usesPrefix : Cls → Bool
  | .jsr | .jmpAbs => false
  | _ => true

theorem uops_split (op : UInt8) (h : usesPrefix (classify (decode op)) = true) :
    uops op = modePrefix (decode op).mode ++ suffix (classify (decode op)) := by
  rw [uops_eq]; simp only [program, prefixFor]; split <;> simp_all [usesPrefix]

theorem bump_bump (a b : Nat) (r : MicroState × Mem × Nat) : bump a (bump b r) = bump (b + a) r := by
  simp [bump, Nat.add_assoc, Nat.add_comm a b]

/-- Composition, fetch + prefix: from a non-halted boundary, `microStep`'s run is the opcode
fetch, the addressing prefix (`k` cycles, memory untouched), then the suffix from an explicit
machine whose `addr`/`crossed` are `Isa.resolve`'s (see `PrefixSpec`). -/
theorem runInstr_prefix (s : State) (m : Mem) (h : s.halted = false)
    (hp : usesPrefix (classify (decode (m.read s.pc))) = true) :
    let e := decode (m.read s.pc)
    ∃ base data,
      let r := if resolvesAddr e.mode then prefixAddr s m e.mode else (0, false)
      let k := prefixCycles e.mode e.pageCross r.2
      runInstr maxCycles (ofState s) m =
        bump (k + 1) (runInstr (7 - k)
          { cpu := { s with pc := s.pc + 1 + prefixPcInc e.mode }, op := m.read s.pc,
            pos := (modePrefix e.mode).size.toUInt8 + 1, addr := r.1, crossed := r.2,
            base := base, data := data } m) ∧
      (hasFixup e.mode = true → base = r.1 - (indexReg s e.mode).toUInt16) := by
  intro e
  have hctx : PreCtx s (fetched s (m.read s.pc)) e.mode (suffix (classify e)) :=
    ⟨rfl, rfl, rfl, uops_split _ hp, (suffix_head _).1, (suffix_head _).2⟩
  have hk := prefixCycles_le e.mode e.pageCross
    (if resolvesAddr e.mode then prefixAddr s m e.mode else (0, false)).2
  obtain ⟨base, data, h1, h2⟩ := prefix_spec e.mode s m _ _
    (7 - prefixCycles e.mode e.pageCross
      (if resolvesAddr e.mode then prefixAddr s m e.mode else (0, false)).2) hctx
  refine ⟨base, data, ?_, h2⟩
  dsimp only [fetched] at h1
  generalize prefixCycles e.mode e.pageCross
    (if resolvesAddr e.mode then prefixAddr s m e.mode else (0, false)).2 = K at h1 hk ⊢
  rw [show maxCycles = (7 - K + K) + 1 by simp only [maxCycles]; omega, runInstr_fetch _ _ _ h]
  dsimp only [fetched]
  rw [h1, bump_bump]

/-! ## Glue facts -/

theorem prefixAddr_eq (s : State) (m : Mem) (mode : AddrMode) (h : mode ≠ .ind) :
    prefixAddr s m mode = resolve s m mode := by
  cases mode <;> simp_all [prefixAddr]

theorem prefixPcInc_len (mode : AddrMode) (h : resolvesAddr mode = true) :
    1 + prefixPcInc mode = mode.len := by
  cases mode <;> simp_all [resolvesAddr] <;> decide

theorem prefix_pos (mode : AddrMode) :
    ((modePrefix mode).size.toUInt8 + 1).toNat = (modePrefix mode).size + 1 := by
  cases mode <;> decide

theorem prefix_pos_ne (mode : AddrMode) : (modePrefix mode).size.toUInt8 + 1 ≠ 0 := by
  cases mode <;> decide

theorem extraCycles_nonrel (e : Entry) (s : State) (cr : Bool) (h : e.mode ≠ .rel) :
    extraCycles e s cr = if e.pageCross && cr then 1 else 0 := by
  simp [extraCycles, h]

/-! ## Class `read` (`readExec`): suffix lemma and end-to-end refinement -/

/-- The last cycle of an instruction: the micro-op `u` ends the program. -/
theorem runInstr_last (f : Nat) (ms : MicroState) (m : Mem) (p : MicroProgram) (u : MicroOp)
    (hu : uops ms.op = p ++ #[u]) (hpos : ms.pos.toNat = p.size + 1) :
    runInstr (f + 1) ms m =
      match ms.busOp with
      | .read a => ({ ms.exec u (m.read a) with pos := 0 }, m, 1)
      | .write a v => ({ ms.exec u v with pos := 0 }, m.write a v, 1) := by
  have hp0 : ms.pos ≠ 0 := by intro h0; simp [h0] at hpos
  have hcur : ms.curOp = u := by simp [curOp, hu, hpos, Array.getElem?_append]
  have hend : (uops ms.op).size ≤ ms.pos.toNat := by simp [hu, hpos]
  rw [runInstr_succ]
  simp only [cycle, complete, hp0, beq_iff_eq, ↓reduceIte, Bool.false_eq_true, hcur]
  rcases ms.busOp with a | ⟨a, v⟩ <;> simp only <;>
    rw [advance_end _ (by simpa using hend)] <;> simp

/-- The read suffix: one cycle reading `addr` and executing; the instruction ends. -/
theorem suffix_read (f : Nat) (ms : MicroState) (m : Mem) (p : MicroProgram)
    (hu : uops ms.op = p ++ #[.readExec]) (hpos : ms.pos.toNat = p.size + 1) :
    runInstr (f + 1) ms m =
      ({ ms with cpu := execRead (decode ms.op) ms.cpu (m.read ms.addr), pos := 0 }, m, 1) := by
  have hp0 : ms.pos ≠ 0 := by intro h0; simp [h0] at hpos
  have hcur : ms.curOp = .readExec := by simp [curOp, hu, hpos, Array.getElem?_append]
  rw [runInstr_last f ms m p _ hu hpos]
  simp [busOp, hcur, hp0, MicroState.exec]

/-- Table facts for the read class, over all 256 opcodes. -/
theorem read_table : ∀ i : Fin 256, classify (decodeFin i) = .read →
    readOk (decodeFin i).instr = true ∧ resolvesAddr (decodeFin i).mode = true ∧
    (decodeFin i).mode ≠ .ind ∧ (decodeFin i).mode ≠ .rel ∧
    ∀ c : Bool, prefixCycles (decodeFin i).mode (decodeFin i).pageCross c + 2 =
      (decodeFin i).cycles.toNat + (if (decodeFin i).pageCross && c then 1 else 0) := by
  decide +kernel

/-- T-REF-1 for every read-class opcode (loads, ALU ops, BIT, compares, NOP with an operand,
the stable unofficial reads): the micro-machine computes `Isa.step`'s registers, memory and
cycle count, page-cross penalty included. -/
theorem T_REF_1_read (s : State) (m : Mem) (h : s.halted = false)
    (hc : classify (decode (m.read s.pc)) = .read) : microStep s m = step s m := by
  obtain ⟨hr, hres, hind, hrel, hcyc⟩ := read_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hr hres hind hrel hcyc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hres, ↓reduceIte, prefixAddr_eq s m _ hind] at h1
  have hk := prefixCycles_le (decode (m.read s.pc)).mode (decode (m.read s.pc)).pageCross
    (resolve s m (decode (m.read s.pc)).mode).2
  have hcy := hcyc (resolve s m (decode (m.read s.pc)).mode).2
  generalize prefixCycles (decode (m.read s.pc)).mode (decode (m.read s.pc)).pageCross
    (resolve s m (decode (m.read s.pc)).mode).2 = K at h1 hk hcy
  rw [show 7 - K = (6 - K) + 1 by omega, suffix_read (p := modePrefix (decode (m.read s.pc)).mode)]
    at h1
  rotate_left
  · exact hu
  · exact prefix_pos _
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, exec_read _ hr,
    extraCycles_nonrel _ _ _ hrel, bump]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · simp only [UInt16.add_assoc, prefixPcInc_len _ hres]
  · simp only; omega

/-! ## Class `imm` (`immExec`) -/

theorem imm_table : ∀ i : Fin 256, classify (decodeFin i) = .imm →
    readOk (decodeFin i).instr = true ∧ (decodeFin i).mode = .imm ∧
    (decodeFin i).cycles.toNat = 2 ∧ (decodeFin i).pageCross = false := by
  decide +kernel

/-- T-REF-1 for every immediate-mode opcode. -/
theorem T_REF_1_imm (s : State) (m : Mem) (h : s.halted = false)
    (hc : classify (decode (m.read s.pc)) = .imm) : microStep s m = step s m := by
  obtain ⟨hr, hmode, hcy, hpc⟩ := imm_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hr hmode hcy hpc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc, hmode] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
    List.length_nil, suffix] at h1 hu
  rw [show (7 : Nat) = 6 + 1 from rfl,
    runInstr_last (p := #[]) (u := .immExec)] at h1
  rotate_left
  · exact hu
  · rfl
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, exec_read _ hr,
    extraCycles_nonrel (decode (m.read s.pc)) s _ (by simp [hmode]), bump, busOp, curOp, hu, hmode, hcy, hpc]
  simp [MicroState.exec, resolve, AddrMode.len, UInt16.add_assoc]

/-! ## Class `imp` (`impExec`: implied and accumulator) -/

/-- Opcodes whose `Isa.exec` is `execImp` on the implied/accumulator operand. -/
def impOk (e : Entry) : Bool :=
  match e.instr with
  | .ASL | .LSR | .ROL | .ROR => e.mode == .acc
  | .INX | .INY | .DEX | .DEY | .TAX | .TAY | .TXA | .TYA | .TSX | .TXS
  | .CLC | .SEC | .CLI | .SEI | .CLV | .CLD | .SED | .NOP => e.mode == .imp
  | _ => false

theorem exec_imp (e : Entry) (hi : impOk e = true) (s : State) (m : Mem) (ea : UInt16)
    (cr : Bool) : exec e s m ea cr = (execImp e.instr { s with pc := s.pc + 1 }, m) := by
  obtain ⟨i, mode, cy, pcr, off⟩ := e
  cases i <;> simp only [impOk, beq_iff_eq] at hi <;>
    first
      | (exact absurd hi (by decide))
      | (subst hi; simp only [exec, execImp, shiftOp, AddrMode.len, beq_self_eq_true,
          ↓reduceIte] <;> rfl)

theorem imp_table : ∀ i : Fin 256, classify (decodeFin i) = .imp →
    impOk (decodeFin i) = true ∧ ((decodeFin i).mode = .imp ∨ (decodeFin i).mode = .acc) ∧
    (decodeFin i).cycles.toNat = 2 ∧ (decodeFin i).pageCross = false := by
  decide +kernel

/-- T-REF-1 for every implied / accumulator opcode. -/
theorem T_REF_1_imp (s : State) (m : Mem) (h : s.halted = false)
    (hc : classify (decode (m.read s.pc)) = .imp) : microStep s m = step s m := by
  obtain ⟨hi, hmode, hcy, hpc⟩ := imp_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hi hmode hcy hpc
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc] at hu
  obtain ⟨base, data, h1, -⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  rcases hmode with hmode | hmode <;>
  · rw [hmode] at hu
    simp only [hmode, resolvesAddr, prefixCycles, hasFixup, modePrefix, prefixPcInc,
      Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.sub_zero, List.size_toArray,
      List.length_nil, suffix] at h1 hu
    rw [show (7 : Nat) = 6 + 1 from rfl,
      runInstr_last (p := #[]) (u := .impExec)] at h1
    rotate_left
    · exact hu
    · rfl
    simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte, exec_imp _ hi,
      extraCycles_nonrel (decode (m.read s.pc)) s _ (by simp [hmode]), bump, busOp, curOp, hu, hmode, hcy, hpc]
    simp [MicroState.exec]

/-! ## Class `write` (stores, including the unstable `SHY/SHX/AHX/TAS`) -/

/-- Store instructions. -/
def writeOk : Instr → Bool
  | .STA | .STX | .STY | .SAX | .SHY | .SHX | .AHX | .TAS => true
  | _ => false

theorem write_table : ∀ i : Fin 256, classify (decodeFin i) = .write →
    writeOk (decodeFin i).instr = true ∧ resolvesAddr (decodeFin i).mode = true ∧
    (decodeFin i).mode ≠ .ind ∧ (decodeFin i).mode ≠ .rel ∧ (decodeFin i).pageCross = false ∧
    (∀ c : Bool, prefixCycles (decodeFin i).mode false c + 2 = (decodeFin i).cycles.toNat) ∧
    (unstable (decodeFin i).instr = true →
      ((decodeFin i).instr = .SHY ∧ (decodeFin i).mode = .absx) ∨
      ((decodeFin i).instr ≠ .SHY ∧ ((decodeFin i).mode = .absy ∨ (decodeFin i).mode = .indy))) := by
  decide +kernel

/-- T-REF-1 for every store opcode. -/
theorem T_REF_1_write (s : State) (m : Mem) (h : s.halted = false)
    (hc : classify (decode (m.read s.pc)) = .write) : microStep s m = step s m := by
  obtain ⟨hw, hres, hind, hrel, hpc, hcyc, hun⟩ := write_table ⟨_, (m.read s.pc).toNat_lt⟩ hc
  rw [← decode_eq_decodeFin] at hw hres hind hrel hpc hcyc hun
  have hu := uops_split (m.read s.pc) (by rw [hc]; rfl)
  rw [hc] at hu
  obtain ⟨base, data, h1, h2⟩ := runInstr_prefix s m h (by rw [hc]; rfl)
  simp only [hres, ↓reduceIte, prefixAddr_eq s m _ hind, hpc] at h1 h2
  have hk := prefixCycles_le (decode (m.read s.pc)).mode false
    (resolve s m (decode (m.read s.pc)).mode).2
  have hcy := hcyc (resolve s m (decode (m.read s.pc)).mode).2
  generalize prefixCycles (decode (m.read s.pc)).mode false
    (resolve s m (decode (m.read s.pc)).mode).2 = K at h1 hk hcy
  rw [show 7 - K = (6 - K) + 1 by omega, runInstr_last (p := modePrefix (decode (m.read s.pc)).mode)
    (u := .write)] at h1
  rotate_left
  · exact hu
  · exact prefix_pos _
  simp only [suffix] at hu
  simp only [busOp, curOp, hu, prefix_pos, Nat.add_sub_cancel, Array.getD_eq_getD_getElem?,
    Array.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, beq_iff_eq, prefix_pos_ne,
    List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some] at h1
  simp only [MicroState.exec, storeAddr, storeByte] at h1
  simp only [microStep, h1, step, h, Bool.false_eq_true, ↓reduceIte,
    extraCycles_nonrel _ _ _ hrel, bump, hpc]
  clear h1 hu
  generalize resolve s m (decode (m.read s.pc)).mode = R at *
  generalize decode (m.read s.pc) = E at *
  obtain ⟨i, mode, cy, pcr, off⟩ := E
  obtain ⟨ea, cr⟩ := R
  simp only at *
  cases i <;> simp only [writeOk] at hw <;> (try exact absurd hw (by decide)) <;>
    simp [MicroState.exec, exec, storeAddr, storeByte, storeVal, unstable, unstableStore,
      AddrMode.len, UInt16.add_assoc, prefixPcInc_len _ hres] at hun ⊢ <;>
    (try rcases hun with hun | hun) <;> (try subst hun) <;>
    simp_all [hasFixup, indexReg] <;> omega

end Nes.Cpu.Proofs.Refinement
