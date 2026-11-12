import Lean

set_option warningAsError true

namespace N2MachineSlice

abbrev Word := BitVec 64

def signedMax : Word := 0x7fffffffffffffff
def zero : Word := 0

-- Entry at aa96: r12 holds the count and rbp the increment. CMP/SETG
-- and CMP/SETL are signed. TEST/SETS and TEST/SETG classify rbp.
def refuses (count increment : Word) : Bool :=
  let upper := signedMax - increment
  let lower := upper + 1#64
  (zero.slt increment && upper.slt count) ||
    (increment.msb && count.slt lower)

-- Both rejecting branch paths converge before the store. The accepted ADD
-- at ab17 has its two operands preserved by the intervening stack loads.
def execute (count increment : Word) : Option Word :=
  if refuses count increment then none else some (increment + count)

private theorem upper_exact (b : Word) (hb : 0 ≤ b.toInt) :
    (signedMax - b).toInt = 9223372036854775807 - b.toInt := by
  have hmax : signedMax.toInt = 9223372036854775807 := by decide
  have hu := BitVec.toInt_lt (x := b)
  change b.toInt < 9223372036854775808 at hu
  rw [BitVec.toInt_sub, hmax]
  apply Int.bmod_eq_of_le <;> omega

theorem branch_iff_overflow (a b : Word) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt) :
    refuses a b = true ↔ 9223372036854775807 < a.toInt + b.toInt := by
  have hzero : zero.toInt = 0 := by decide
  have hsign : b.msb = false := by
    rw [← BitVec.slt_zero_eq_msb, BitVec.slt_eq_decide]
    simp [Int.not_lt.mpr hb]
  have hu := BitVec.toInt_lt (x := a)
  change a.toInt < 9223372036854775808 at hu
  simp only [refuses, hsign, Bool.false_and, Bool.or_false, BitVec.slt_eq_decide,
    hzero, upper_exact b hb, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem accepted_register_exact (a b : Word) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt)
    (h : refuses a b = false) : (b + a).toInt = a.toInt + b.toInt := by
  have hfit : ¬ 9223372036854775807 < a.toInt + b.toInt := by
    intro hov
    have ht := (branch_iff_overflow a b ha hb).mpr hov
    simp [h] at ht
  rw [BitVec.toInt_add, Int.add_comm b.toInt]
  apply Int.bmod_eq_of_le <;> omega

theorem execute_exact (a b : Word) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt) :
    (execute a b).map BitVec.toInt =
      if 9223372036854775807 < a.toInt + b.toInt then none else some (a.toInt + b.toInt) := by
  by_cases h : 9223372036854775807 < a.toInt + b.toInt
  · simp [execute, h, (branch_iff_overflow a b ha hb).mpr h]
  · have hf : refuses a b = false := by
      cases he : refuses a b
      · rfl
      · exact (h ((branch_iff_overflow a b ha hb).mp he)).elim
    simp [execute, h, hf, accepted_register_exact a b ha hb hf]

def guardBytes : ByteArray := ⟨#[
  0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x29, 0xe8,
  0x49, 0x39, 0xc4, 0x0f, 0x9f, 0xc1, 0x48, 0xff, 0xc0, 0x49, 0x39, 0xc4, 0x0f,
  0x9c, 0xc0, 0x48, 0x85, 0xed, 0x41, 0x0f, 0x98, 0xc5, 0x0f, 0x9f, 0xc3, 0x41,
  0x20, 0xc5, 0x20, 0xcb, 0x75, 0x05, 0x45, 0x84, 0xed, 0x74, 0x39]⟩

def acceptedBytes : ByteArray := ⟨#[
  0x44, 0x08, 0xeb, 0x0f, 0x85, 0xb3, 0x01, 0x00, 0x00, 0x4c, 0x8b, 0xac, 0x24,
  0xb0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x54, 0x24, 0x60, 0x4c, 0x01, 0xe5]⟩

-- Only the encodings used by these two slices are supported.
inductive Op where
  | movMax | sub | cmp | setGCl | inc | setLAl | testRbp
  | setSR13 | setGBl | andR13Al | andBlCl | testR13 | orBlR13
  | jne (disp : Nat) | je (disp : Nat)
  | loadR13 | loadRdx | add
  deriving DecidableEq, Repr

def encodings : List (List UInt8 × Op) := [
  ([0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f], .movMax),
  ([0x48, 0x29, 0xe8], .sub),
  ([0x49, 0x39, 0xc4], .cmp),
  ([0x0f, 0x9f, 0xc1], .setGCl),
  ([0x48, 0xff, 0xc0], .inc),
  ([0x0f, 0x9c, 0xc0], .setLAl),
  ([0x48, 0x85, 0xed], .testRbp),
  ([0x41, 0x0f, 0x98, 0xc5], .setSR13),
  ([0x0f, 0x9f, 0xc3], .setGBl),
  ([0x41, 0x20, 0xc5], .andR13Al),
  ([0x20, 0xcb], .andBlCl),
  ([0x75, 0x05], .jne 5),
  ([0x45, 0x84, 0xed], .testR13),
  ([0x74, 0x39], .je 0x39),
  ([0x44, 0x08, 0xeb], .orBlR13),
  ([0x0f, 0x85, 0xb3, 0x01, 0x00, 0x00], .jne 0x1b3),
  ([0x4c, 0x8b, 0xac, 0x24, 0xb0, 0x00, 0x00, 0x00], .loadR13),
  ([0x48, 0x8b, 0x54, 0x24, 0x60], .loadRdx),
  ([0x4c, 0x01, 0xe5], .add)]

def decode (bytes : List UInt8) : Option (Nat × Op) :=
  (encodings.find? fun (encoding, _) => bytes.take encoding.length == encoding).map
    fun (encoding, op) => (encoding.length, op)

structure State where
  pc : Nat := 0xaa96
  r12 : Word
  rbp : Word
  rax : Word := 0
  al : Bool := false
  cl : Bool := false
  bl : Bool := false
  r13b : Bool := false
  r13 : Word := 0
  rdx : Word := 0
  stackB0 : Word
  stack60 : Word
  less : Bool := false
  greater : Bool := false
  sign : Bool := false
  zf : Bool := false

-- The byte operations read only bytes set to 0 or 1 by SETcc. AL is
-- observed after the last read of the full RAX, and R13B is dead after reload.
-- Only flags observed before the next flag-setting instruction are recorded.
def step (width : Nat) (op : Op) (s : State) : State :=
  let next := { s with pc := s.pc + width }
  match op with
  | .movMax => { next with rax := signedMax }
  | .sub => { next with rax := s.rax - s.rbp }
  | .cmp => { next with less := s.r12.slt s.rax, greater := s.rax.slt s.r12 }
  | .setGCl => { next with cl := s.greater }
  | .inc => { next with rax := s.rax + 1#64 }
  | .setLAl => { next with al := s.less }
  | .testRbp => { next with sign := s.rbp.msb, greater := zero.slt s.rbp }
  | .setSR13 => { next with r13b := s.sign }
  | .setGBl => { next with bl := s.greater }
  | .andR13Al => { next with r13b := s.r13b && s.al }
  | .andBlCl =>
      let byte := s.bl && s.cl
      { next with bl := byte, zf := !byte }
  | .jne d => if s.zf then next else { next with pc := next.pc + d }
  | .testR13 => { next with zf := !s.r13b }
  | .je d => if s.zf then { next with pc := next.pc + d } else next
  | .orBlR13 =>
      let byte := s.bl || s.r13b
      { next with bl := byte, zf := !byte }
  | .loadR13 => { next with r13 := s.stackB0 }
  | .loadRdx => { next with rdx := s.stack60 }
  | .add => { next with rbp := s.rbp + s.r12 }

def fetch (guard accepted : List UInt8) (pc : Nat) : List UInt8 :=
  if 0xaa96 ≤ pc && pc < 0xaac8 then guard.drop (pc - 0xaa96)
  else if 0xab01 ≤ pc && pc < 0xab1a then accepted.drop (pc - 0xab01)
  else []

inductive Exit where
  | reject | sum (value : Word) | invalid
  deriving DecidableEq, Repr

def run (guard accepted : List UInt8) : Nat → State → Exit
  | 0, _ => .invalid
  | fuel + 1, s =>
      if s.pc == 0xaac8 then .reject
      else if s.pc == 0xab1a then .sum s.rbp
      else match decode (fetch guard accepted s.pc) with
      | none => .invalid
      | some (width, op) => run guard accepted fuel (step width op s)

def runRecorded (a b stackB0 stack60 : Word) : Exit :=
  run guardBytes.data.toList acceptedBytes.data.toList 21
    { r12 := a, rbp := b, stackB0, stack60 }

@[simp] private theorem decode_aa96 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaa96) =
      some (10, .movMax) := by decide

@[simp] private theorem decode_aaa0 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaa0) =
      some (3, .sub) := by decide

@[simp] private theorem decode_aaa3 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaa3) =
      some (3, .cmp) := by decide

@[simp] private theorem decode_aaa6 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaa6) =
      some (3, .setGCl) := by decide

@[simp] private theorem decode_aaa9 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaa9) =
      some (3, .inc) := by decide

@[simp] private theorem decode_aaac :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaac) =
      some (3, .cmp) := by decide

@[simp] private theorem decode_aaaf :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaaaf) =
      some (3, .setLAl) := by decide

@[simp] private theorem decode_aab2 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaab2) =
      some (3, .testRbp) := by decide

@[simp] private theorem decode_aab5 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaab5) =
      some (4, .setSR13) := by decide

@[simp] private theorem decode_aab9 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaab9) =
      some (3, .setGBl) := by decide

@[simp] private theorem decode_aabc :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaabc) =
      some (3, .andR13Al) := by decide

@[simp] private theorem decode_aabf :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaabf) =
      some (2, .andBlCl) := by decide

@[simp] private theorem decode_aac1 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaac1) =
      some (2, .jne 5) := by decide

@[simp] private theorem decode_aac3 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaac3) =
      some (3, .testR13) := by decide

@[simp] private theorem decode_aac6 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xaac6) =
      some (2, .je 0x39) := by decide

@[simp] private theorem decode_ab01 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xab01) =
      some (3, .orBlR13) := by decide

@[simp] private theorem decode_ab04 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xab04) =
      some (6, .jne 0x1b3) := by decide

@[simp] private theorem decode_ab0a :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xab0a) =
      some (8, .loadR13) := by decide

@[simp] private theorem decode_ab12 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xab12) =
      some (5, .loadRdx) := by decide

@[simp] private theorem decode_ab17 :
    decode (fetch guardBytes.data.toList acceptedBytes.data.toList 0xab17) =
      some (3, .add) := by decide

theorem recorded_run_exact (a b stackB0 stack60 : Word) :
    runRecorded a b stackB0 stack60 = if refuses a b then .reject else .sum (b + a) := by
  cases hgt : (signedMax - b).slt a <;>
  cases hlt : a.slt (signedMax - b + 1#64) <;>
  cases hsign : b.msb <;> cases hpositive : zero.slt b <;>
    simp [runRecorded, run, step, refuses, hgt, hlt, hsign, hpositive]

-- For the recorded ELF, the executable LOAD segment has equal file and
-- virtual offsets. The recorded full-file digest is separate from this check.
def checkSlices (binary : ByteArray) : Bool :=
  (binary.extract 0xaa96 0xaac8).data == guardBytes.data &&
    (binary.extract 0xab01 0xab1a).data == acceptedBytes.data

def runBinary (binary : ByteArray) (a b stackB0 stack60 : Word) : Exit :=
  run (binary.extract 0xaa96 0xaac8).data.toList
    (binary.extract 0xab01 0xab1a).data.toList 21 { r12 := a, rbp := b, stackB0, stack60 }

theorem checked_binary_exact (binary : ByteArray) (h : checkSlices binary = true)
    (a b stackB0 stack60 : Word) :
    runBinary binary a b stackB0 stack60 =
      if refuses a b then .reject else .sum (b + a) := by
  simp only [checkSlices, Bool.and_eq_true, beq_iff_eq] at h
  unfold runBinary
  rw [h.1, h.2]
  exact recorded_run_exact a b stackB0 stack60

def Exit.observed : Exit → Option Int
  | .sum value => some value.toInt
  | _ => none

theorem checked_binary_count (binary : ByteArray) (h : checkSlices binary = true)
    (a b stackB0 stack60 : Word) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt) :
    (runBinary binary a b stackB0 stack60).observed =
      if 9223372036854775807 < a.toInt + b.toInt then none else some (a.toInt + b.toInt) := by
  rw [checked_binary_exact binary h]
  have he := execute_exact a b ha hb
  cases hr : refuses a b <;> simpa [hr, execute, Exit.observed] using he

abbrev Memory := Word → UInt8

opaque readWord (mem : Memory) (addr : Word) : Word :=
  BitVec.ofNat 64 ((List.range 8).foldl
    (fun n i => n + (mem (addr + BitVec.ofNat 64 i)).toNat * 256 ^ i) 0)

def writeWord (mem : Memory) (addr value : Word) : Memory :=
  fun byte =>
    let i := (byte - addr).toNat
    if i < 8 then UInt8.ofNat (value.toNat / 256 ^ i % 256) else mem byte

theorem writeWord_outside (mem : Memory) (addr value byte : Word)
    (h : 8 ≤ (byte - addr).toNat) : writeWord mem addr value byte = mem byte := by
  unfold writeWord
  exact ite_eq_right (Nat.not_lt.mpr h)

opaque indexed (base index : Word) : Word := base + 8#64 * index

structure MemoryState where
  mem : Memory
  rdi : Word
  r9 : Word
  r13 : Word
  r15 : Word
  rsp : Word
  rbp : Word := 0
  r12 : Word := 0

-- Dead registers are omitted at the observation point immediately after
-- the store. In particular, the LEAs and the loop-index updates are decoded
-- but do not affect the projected memory, source operands, or store address.
inductive MemoryOp where
  | loadIncrement | loadCount | saveIndex | nextIndex | setR12
  | leaRbx | leaRcx | restoreIndex | store
  deriving DecidableEq

def memoryEncodings : List (List UInt8 × MemoryOp) := [
  ([0x4a, 0x8b, 0x2c, 0xcf], .loadIncrement),
  ([0x4f, 0x8b, 0x64, 0xfd, 0x00], .loadCount),
  ([0x49, 0x89, 0xc6], .saveIndex),
  ([0x49, 0x8d, 0x46, 0x01], .nextIndex),
  ([0x49, 0xbc, 0, 0, 0, 0, 0, 0, 0, 0x20], .setR12),
  ([0x48, 0x8d, 0x1d, 0xe1, 0x2a, 0, 0], .leaRbx),
  ([0x48, 0x8d, 0x0d, 0xaa, 0x2a, 0, 0], .leaRcx),
  ([0x4d, 0x89, 0xf1], .restoreIndex),
  ([0x4b, 0x89, 0x6c, 0xfd, 0x00], .store)]

def decodeLinear (encodings : List (List UInt8 × α)) :
    Nat → List UInt8 → Option (List α)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes => do
      let (encoding, op) ← encodings.find? fun (encoding, _) =>
        bytes.take encoding.length == encoding
      let remaining ← decodeLinear encodings fuel (bytes.drop encoding.length)
      return op :: remaining

def decodeMemory := decodeLinear memoryEncodings

def stepMemory (s : MemoryState) (op : MemoryOp) : MemoryState :=
  match op with
  | .loadIncrement => { s with rbp := readWord s.mem (indexed s.rdi s.r9) }
  | .loadCount => { s with r12 := readWord s.mem (indexed s.r13 s.r15) }
  | .setR12 => { s with r12 := 0x2000000000000000 }
  | .store => { s with mem := writeWord s.mem (indexed s.r13 s.r15) s.rbp }
  | .saveIndex | .nextIndex | .leaRbx | .leaRcx | .restoreIndex => s

def loadBytes : List UInt8 :=
  [0x4a, 0x8b, 0x2c, 0xcf, 0x4f, 0x8b, 0x64, 0xfd, 0x00, 0x49, 0x89, 0xc6]

def storeBytes : List UInt8 :=
  [0x49, 0x8d, 0x46, 0x01, 0x49, 0xbc, 0, 0, 0, 0, 0, 0, 0, 0x20,
   0x48, 0x8d, 0x1d, 0xe1, 0x2a, 0, 0, 0x48, 0x8d, 0x0d, 0xaa, 0x2a, 0, 0,
   0x4d, 0x89, 0xf1, 0x4b, 0x89, 0x6c, 0xfd, 0x00]

private theorem decode_loads :
    decodeMemory 3 loadBytes = some [.loadIncrement, .loadCount, .saveIndex] := by decide

private theorem decode_store :
    decodeMemory 6 storeBytes =
      some [.nextIndex, .setR12, .leaRbx, .leaRcx, .restoreIndex, .store] := by decide

def loadSlice (binary : ByteArray) : List UInt8 :=
  (binary.extract 0xaa8a 0xaa96).data.toList
def storeSlice (binary : ByteArray) : List UInt8 :=
  (binary.extract 0xab1a 0xab3e).data.toList

def checkUpdate (binary : ByteArray) : Bool :=
  checkSlices binary && (loadSlice binary == loadBytes && storeSlice binary == storeBytes)

inductive MemoryExit where
  | reject (mem : Memory) | stored (mem : Memory) | invalid

def commitStore (loaded : MemoryState) (restored value : Word) :
    Option (List MemoryOp) → MemoryExit
  | none => .invalid
  | some stores =>
      .stored (stores.foldl stepMemory { loaded with rbp := value, r13 := restored }).mem

def finishUpdate (binary : ByteArray) (loaded : MemoryState) (restored : Word) :
    Exit → MemoryExit
  | .reject => .reject loaded.mem
  | .invalid => .invalid
  | .sum value => commitStore loaded restored value (decodeMemory 6 (storeSlice binary))

def startUpdate (binary : ByteArray) (arithmetic : Word → Word → Word → Word → Exit)
    (s : MemoryState) : Option (List MemoryOp) → MemoryExit
  | none => .invalid
  | some loads =>
      let loaded := loads.foldl stepMemory s
      let restored := readWord loaded.mem (loaded.rsp + 0xb0#64)
      finishUpdate binary loaded restored
        (arithmetic loaded.r12 loaded.rbp restored
          (readWord loaded.mem (loaded.rsp + 0x60#64)))

-- The arithmetic slice reloads r13 from [rsp+0xb0] on success, preserves
-- r15, and does not write memory. It stops before the rejection routine.
def runUpdate (binary : ByteArray) (s : MemoryState) : MemoryExit :=
  startUpdate binary (runBinary binary) s (decodeMemory 3 (loadSlice binary))

abbrev countAddress (s : MemoryState) : Word := indexed s.r13 s.r15
abbrev oldCount (s : MemoryState) : Word := readWord s.mem (countAddress s)
abbrev increment (s : MemoryState) : Word := readWord s.mem (indexed s.rdi s.r9)

private def loadedState (s : MemoryState) : MemoryState :=
  { s with rbp := increment s, r12 := oldCount s }

private theorem start_loaded (binary : ByteArray)
    (arithmetic : Word → Word → Word → Word → Exit) (s : MemoryState) :
    startUpdate binary arithmetic s (some [.loadIncrement, .loadCount, .saveIndex]) =
      finishUpdate binary (loadedState s) (readWord s.mem (s.rsp + 0xb0#64))
        (arithmetic (oldCount s) (increment s) (readWord s.mem (s.rsp + 0xb0#64))
          (readWord s.mem (s.rsp + 0x60#64))) := rfl

private theorem runUpdate_loaded (binary : ByteArray) (s : MemoryState)
    (h : loadSlice binary = loadBytes) :
    runUpdate binary s = finishUpdate binary (loadedState s)
      (readWord s.mem (s.rsp + 0xb0#64))
      (runBinary binary (oldCount s) (increment s) (readWord s.mem (s.rsp + 0xb0#64))
        (readWord s.mem (s.rsp + 0x60#64))) :=
  (congrArg (startUpdate binary (runBinary binary) s)
    ((congrArg (decodeMemory 3) h).trans decode_loads)).trans
    (start_loaded binary (runBinary binary) s)

private theorem store_fold (s : MemoryState) (value restored : Word) :
    commitStore (loadedState s) restored value
      (some [.nextIndex, .setR12, .leaRbx, .leaRcx, .restoreIndex, .store]) =
      .stored (writeWord s.mem (indexed restored s.r15) value) := rfl

private theorem finish_store (binary : ByteArray) (s : MemoryState) (value restored : Word)
    (h : storeSlice binary = storeBytes) :
    finishUpdate binary (loadedState s) restored (.sum value) =
      .stored (writeWord s.mem (indexed restored s.r15) value) :=
  (congrArg (commitStore (loadedState s) restored value)
    ((congrArg (decodeMemory 6) h).trans decode_store)).trans (store_fold s value restored)

private theorem finish_reject (binary : ByteArray) (s : MemoryState) (restored : Word) :
    finishUpdate binary (loadedState s) restored .reject = .reject s.mem := rfl

private theorem finish_correct (binary : ByteArray) (s : MemoryState) (restored : Word)
    (hstore : storeSlice binary = storeBytes) (restore : restored = s.r13)
    (ha : 0 ≤ (oldCount s).toInt) (hb : 0 ≤ (increment s).toInt)
    (result : Exit)
    (hr : result = if refuses (oldCount s) (increment s) then .reject
      else .sum (increment s + oldCount s)) :
    finishUpdate binary (loadedState s) restored result =
      if 9223372036854775807 < (oldCount s).toInt + (increment s).toInt
      then .reject s.mem else .stored (writeWord s.mem (countAddress s)
        (BitVec.ofInt 64 ((oldCount s).toInt + (increment s).toInt))) := by
  rw [hr]
  by_cases hov : 9223372036854775807 < (oldCount s).toInt + (increment s).toInt
  · simp only [ite_eq_left hov, ite_eq_left ((branch_iff_overflow _ _ ha hb).mpr hov),
      finish_reject]
  · have hf : refuses (oldCount s) (increment s) = false := by
      cases he : refuses (oldCount s) (increment s)
      · rfl
      · exact (hov ((branch_iff_overflow _ _ ha hb).mp he)).elim
    have he := accepted_register_exact _ _ ha hb hf
    have hword : BitVec.ofInt 64 ((oldCount s).toInt + (increment s).toInt) =
        increment s + oldCount s := by
      rw [← he, BitVec.ofInt_toInt]
    have hfalse : ¬ refuses (oldCount s) (increment s) = true := by simp [hf]
    rw [ite_eq_right hov, ite_eq_right hfalse, finish_store binary s _ _ hstore, restore, hword]

theorem checked_binary_update (binary : ByteArray) (h : checkUpdate binary = true)
    (s : MemoryState) (restore : readWord s.mem (s.rsp + 0xb0#64) = s.r13)
    (ha : 0 ≤ (oldCount s).toInt) (hb : 0 ≤ (increment s).toInt) :
    runUpdate binary s =
      if 9223372036854775807 < (oldCount s).toInt + (increment s).toInt
      then .reject s.mem else .stored (writeWord s.mem (countAddress s)
        (BitVec.ofInt 64 ((oldCount s).toInt + (increment s).toInt))) := by
  simp only [checkUpdate, Bool.and_eq_true, beq_iff_eq] at h
  exact (runUpdate_loaded binary s h.2.1).trans
    (finish_correct binary s _ h.2.2 restore ha hb _
      (checked_binary_exact binary h.1 _ _ _ _))

-- The caller-visible projection of the overflow return record. Unobserved
-- fields use different offsets in the valid, non-overlapping ABI buffer.
structure ErrorResult where
  tag : UInt8
  length : Word
  message : Word
  resultPointer : Word
  returnAddress : Word
  consumedStackBytes : Nat
  deriving DecidableEq

structure CleanupInputs where
  ownership : UInt8 := 0
  secondCount : Word := 0
  firstBase : Word := 0
  secondBase : Word := 0

structure ErrorState where
  imageBase : Word
  buffer : Word
  caller : Word
  cleanup : CleanupInputs := {}
  freeCalls : List Word := []
  rax : Word := 0
  r11 : Word := 0
  bl : UInt8 := 0
  stackLength : Word := 0
  stackMessage : Word := 0
  resultTag : UInt8 := 0
  resultLength : Word := 0
  resultMessage : Word := 0
  stackOffset : Nat := 0
  returned : Bool := false

inductive ErrorOp where
  | setLength
  | setMessage
  | saveTraceFlag
  | saveLength
  | saveMessage
  | setTag
  | readTraceFlag
  | storeAuxiliary
  | storeTraceFlag
  | storeTrace
  | storeCapacity
  | maskTag
  | readLength
  | storeLength
  | readMessage
  | storeMessage
  | storeExtra
  | storeTag
  | storeTrailing
  | returnBuffer
  | dropFrame
  | popSaved
  | ret
  | testOwnership
  | readSecondBase
  | skipFirst
  | saveFirstTrace
  | freeFirst
  | restoreFirstTrace
  | testSecondCount
  | reloadBuffer
  | setCapacity
  | skipSecond
  | setSecondArgument
  | saveSecondTrace
  | freeSecond
  | restoreSecondTrace
  deriving DecidableEq

def errorEncodings : List (List UInt8 × ErrorOp) := [
  ([0xb8, 0x21, 0x00, 0x00, 0x00], .setLength),
  ([0x4c, 0x8d, 0x1d, 0xbd, 0x2a, 0x00, 0x00], .setMessage),
  ([0x88, 0x54, 0x24, 0x0f], .saveTraceFlag),
  ([0x48, 0x89, 0x44, 0x24, 0x50], .saveLength),
  ([0x4c, 0x89, 0x5c, 0x24, 0x58], .saveMessage),
  ([0xb3, 0x01], .setTag),
  ([0x0f, 0xb6, 0x54, 0x24, 0x0f], .readTraceFlag),
  ([0x4d, 0x89, 0x6f, 0x30], .storeAuxiliary),
  ([0x41, 0x88, 0x57, 0x28], .storeTraceFlag),
  ([0x49, 0x89, 0x77, 0x20], .storeTrace),
  ([0x4d, 0x89, 0x67, 0x18], .storeCapacity),
  ([0x80, 0xe3, 0x01], .maskTag),
  ([0x48, 0x8b, 0x44, 0x24, 0x50], .readLength),
  ([0x49, 0x89, 0x47, 0x10], .storeLength),
  ([0x48, 0x8b, 0x44, 0x24, 0x58], .readMessage),
  ([0x49, 0x89, 0x47, 0x08], .storeMessage),
  ([0x4d, 0x89, 0x57, 0x38], .storeExtra),
  ([0x41, 0x88, 0x1f], .storeTag),
  ([0x49, 0x89, 0x6f, 0x40], .storeTrailing),
  ([0x4c, 0x89, 0xf8], .returnBuffer),
  ([0x48, 0x81, 0xc4, 0xc8, 0x00, 0x00, 0x00], .dropFrame),
  ([0x5b], .popSaved),
  ([0x41, 0x5c], .popSaved),
  ([0x41, 0x5d], .popSaved),
  ([0x41, 0x5e], .popSaved),
  ([0x41, 0x5f], .popSaved),
  ([0x5d], .popSaved),
  ([0xc3], .ret),
  ([0x80, 0x7c, 0x24, 0x48, 0x00], .testOwnership),
  ([0x4c, 0x8b, 0xb4, 0x24, 0xb0, 0x00, 0x00, 0x00], .readSecondBase),
  ([0x74, 0x0b], .skipFirst),
  ([0x49, 0x89, 0xf4], .saveFirstTrace),
  ([0xe8, 0x7c, 0x63, 0xff, 0xff], .freeFirst),
  ([0x4c, 0x89, 0xe6], .restoreFirstTrace),
  ([0x48, 0x83, 0xbc, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00], .testSecondCount),
  ([0x4c, 0x8b, 0xbc, 0x24, 0x90, 0x00, 0x00, 0x00], .reloadBuffer),
  ([0x49, 0xbc, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20], .setCapacity),
  ([0x7e, 0x0e], .skipSecond),
  ([0x4c, 0x89, 0xf7], .setSecondArgument),
  ([0x48, 0x89, 0xf5], .saveSecondTrace),
  ([0xe8, 0x4f, 0x63, 0xff, 0xff], .freeSecond),
  ([0x48, 0x89, 0xee], .restoreSecondTrace)]

def decodeError := decodeLinear errorEncodings

def stepError (s : ErrorState) (op : ErrorOp) : ErrorState :=
  match op with
  | .setLength => { s with rax := 33 }
  | .setMessage => { s with r11 := s.imageBase + 0xaaf3#64 + 0x2abd#64 }
  | .saveLength => { s with stackLength := s.rax }
  | .saveMessage => { s with stackMessage := s.r11 }
  | .freeFirst => { s with freeCalls := s.freeCalls ++ [s.cleanup.firstBase] }
  | .freeSecond => { s with freeCalls := s.freeCalls ++ [s.cleanup.secondBase] }
  | .testOwnership | .readSecondBase | .skipFirst | .saveFirstTrace | .restoreFirstTrace |
    .testSecondCount | .reloadBuffer | .setCapacity | .skipSecond | .setSecondArgument |
    .saveSecondTrace | .restoreSecondTrace => s
  | .setTag => { s with bl := 1 }
  | .maskTag => { s with bl := s.bl &&& 1 }
  | .readLength => { s with rax := s.stackLength }
  | .readMessage => { s with rax := s.stackMessage }
  | .storeLength => { s with resultLength := s.rax }
  | .storeMessage => { s with resultMessage := s.rax }
  | .storeTag => { s with resultTag := s.bl }
  | .returnBuffer => { s with rax := s.buffer }
  | .dropFrame => { s with stackOffset := s.stackOffset + 0xc8 }
  | .popSaved => { s with stackOffset := s.stackOffset + 8 }
  | .ret => { s with returned := true, stackOffset := s.stackOffset + 8 }
  | .saveTraceFlag | .readTraceFlag | .storeAuxiliary | .storeTraceFlag |
    .storeTrace | .storeCapacity | .storeExtra | .storeTrailing => s

def prepareErrorBytes : List UInt8 :=
  [0xb8, 0x21, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x1d, 0xbd, 0x2a, 0x00, 0x00,
   0x88, 0x54, 0x24, 0x0f, 0x48, 0x89, 0x44, 0x24, 0x50, 0x4c, 0x89, 0x5c,
   0x24, 0x58]

private theorem decode_error_prepare :
    decodeError 5 prepareErrorBytes =
      some [.setLength, .setMessage, .saveTraceFlag, .saveLength, .saveMessage] := by decide

def cleanupEnterBytes : List UInt8 :=
  [0x80, 0x7c, 0x24, 0x48, 0x00, 0x4c, 0x8b, 0xb4, 0x24, 0xb0, 0x00, 0x00,
   0x00, 0x74, 0x0b]

def cleanupEnterSlice (binary : ByteArray) :=
  (binary.extract 0xacbd 0xaccc).data.toList

private theorem decode_cleanup_enter :
    decodeError 3 cleanupEnterBytes =
      some [.testOwnership, .readSecondBase, .skipFirst] := by decide

def cleanupFirstBytes : List UInt8 :=
  [0x49, 0x89, 0xf4, 0xe8, 0x7c, 0x63, 0xff, 0xff, 0x4c, 0x89, 0xe6]

def cleanupFirstSlice (binary : ByteArray) :=
  (binary.extract 0xaccc 0xacd7).data.toList

private theorem decode_cleanup_first :
    decodeError 3 cleanupFirstBytes =
      some [.saveFirstTrace, .freeFirst, .restoreFirstTrace] := by decide

def cleanupMiddleBytes : List UInt8 :=
  [0x48, 0x83, 0xbc, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x8b, 0xbc,
   0x24, 0x90, 0x00, 0x00, 0x00, 0xb3, 0x01, 0x49, 0xbc, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x20, 0x7e, 0x0e]

def cleanupMiddleSlice (binary : ByteArray) :=
  (binary.extract 0xacd7 0xacf6).data.toList

private theorem decode_cleanup_middle :
    decodeError 5 cleanupMiddleBytes =
      some [.testSecondCount, .reloadBuffer, .setTag, .setCapacity, .skipSecond] := by decide

def cleanupSecondBytes : List UInt8 :=
  [0x4c, 0x89, 0xf7, 0x48, 0x89, 0xf5, 0xe8, 0x4f, 0x63, 0xff, 0xff, 0x48,
   0x89, 0xee]

def cleanupSecondSlice (binary : ByteArray) :=
  (binary.extract 0xacf6 0xad04).data.toList

private theorem decode_cleanup_second :
    decodeError 4 cleanupSecondBytes =
      some [.setSecondArgument, .saveSecondTrace, .freeSecond, .restoreSecondTrace] := by decide

def returnErrorBytes : List UInt8 :=
  [0x0f, 0xb6, 0x54, 0x24, 0x0f, 0x4d, 0x89, 0x6f, 0x30, 0x41, 0x88, 0x57,
   0x28, 0x49, 0x89, 0x77, 0x20, 0x4d, 0x89, 0x67, 0x18, 0x80, 0xe3, 0x01,
   0x48, 0x8b, 0x44, 0x24, 0x50, 0x49, 0x89, 0x47, 0x10, 0x48, 0x8b, 0x44,
   0x24, 0x58, 0x49, 0x89, 0x47, 0x08, 0x4d, 0x89, 0x57, 0x38, 0x41, 0x88,
   0x1f, 0x49, 0x89, 0x6f, 0x40, 0x4c, 0x89, 0xf8, 0x48, 0x81, 0xc4, 0xc8,
   0x00, 0x00, 0x00, 0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f,
   0x5d, 0xc3]

private theorem decode_error_return :
    decodeError 22 returnErrorBytes =
      some [.readTraceFlag, .storeAuxiliary, .storeTraceFlag, .storeTrace, .storeCapacity, .maskTag, .readLength, .storeLength, .readMessage, .storeMessage, .storeExtra, .storeTag, .storeTrailing, .returnBuffer, .dropFrame, .popSaved, .popSaved, .popSaved, .popSaved, .popSaved, .popSaved, .ret] := by decide

def prepareErrorSlice (binary : ByteArray) := (binary.extract 0xaae7 0xab01).data.toList
def returnErrorSlice (binary : ByteArray) := (binary.extract 0xad04 0xad4e).data.toList

def overflowMessage : ByteArray := "checked integer addition overflow".toUTF8

private def relativeTarget (next : Nat) (displacement : List UInt8) : Int :=
  let magnitude := (displacement.zipIdx).foldl
    (fun n (byte, i) => n + byte.toNat * 256 ^ i) 0
  (next : Int) + (BitVec.ofNat (8 * displacement.length) magnitude).toInt

theorem cleanup_targets :
    relativeTarget 0xaccc (cleanupEnterBytes.drop 14) = 0xacd7 ∧
    relativeTarget 0xacf6 (cleanupMiddleBytes.drop 30) = 0xad04 ∧
    relativeTarget 0xacd4 ((cleanupFirstBytes.drop 4).take 4) = 0x1050 ∧
    relativeTarget 0xad01 ((cleanupSecondBytes.drop 7).take 4) = 0x1050 := by decide

def checkCleanup (binary : ByteArray) : Bool :=
  (cleanupEnterSlice binary == cleanupEnterBytes) &&
  (cleanupFirstSlice binary == cleanupFirstBytes) &&
  (cleanupMiddleSlice binary == cleanupMiddleBytes) &&
  (cleanupSecondSlice binary == cleanupSecondBytes)

def checkErrorReturn (binary : ByteArray) : Bool :=
  (prepareErrorSlice binary == prepareErrorBytes) &&
  (checkCleanup binary) &&
  (returnErrorSlice binary == returnErrorBytes) &&
  ((binary.extract 0xd5b0 0xd5d1).data == overflowMessage.data)

-- JE at acca skips the first free to acd7 if ownership is zero.
-- JLE at acf4 skips the second free to ad04 if the signed count is
-- nonpositive. Both calls are summarized as returning with preserved
-- projected fields and the original stack pointer.
def executeCleanup (binary : ByteArray) (s : ErrorState) : Option ErrorState := do
  let enter ← decodeError 3 (cleanupEnterSlice binary)
  let first ← decodeError 3 (cleanupFirstSlice binary)
  let middle ← decodeError 5 (cleanupMiddleSlice binary)
  let second ← decodeError 4 (cleanupSecondSlice binary)
  let entered := enter.foldl stepError s
  let afterFirst := if entered.cleanup.ownership == 0 then entered
    else first.foldl stepError entered
  let afterMiddle := middle.foldl stepError afterFirst
  return if zero.slt afterMiddle.cleanup.secondCount then second.foldl stepError afterMiddle
    else afterMiddle

def cleanupCalls (inputs : CleanupInputs) : List Word :=
  (if inputs.ownership == 0 then [] else [inputs.firstBase]) ++
    (if zero.slt inputs.secondCount then [inputs.secondBase] else [])

theorem checked_cleanup (binary : ByteArray) (h : checkCleanup binary = true) (s : ErrorState) :
    executeCleanup binary s =
      some { s with bl := 1, freeCalls := s.freeCalls ++ cleanupCalls s.cleanup } := by
  simp only [checkCleanup, Bool.and_eq_true, beq_iff_eq] at h
  unfold executeCleanup
  rw [h.1.1.1, h.1.1.2, h.1.2, h.2, decode_cleanup_enter, decode_cleanup_first,
    decode_cleanup_middle, decode_cleanup_second]
  cases hFirst : s.cleanup.ownership == 0 <;> cases hSecond : zero.slt s.cleanup.secondCount <;>
    simp [Bind.bind, Option.bind, List.foldl, stepError, cleanupCalls, hFirst, hSecond,
      List.append_assoc]

def finishError (binary : ByteArray) (cleaned : ErrorState) : Option ErrorResult :=
  (decodeError 22 (returnErrorSlice binary)).bind fun tail =>
    let final := tail.foldl stepError cleaned
    if final.returned then
      some ⟨final.resultTag, final.resultLength, final.resultMessage, final.rax,
        final.caller, final.stackOffset⟩
    else none

-- The earlier stack-trace call remains a summary boundary. The valid frame
-- supplies the caller address at offset 0xf8.
def afterPrepare (binary : ByteArray) (s : ErrorState) :
    Option (List ErrorOp) → Option ErrorResult
  | none => none
  | some prepare =>
      (executeCleanup binary (prepare.foldl stepError s)).bind (finishError binary)

def executeError (binary : ByteArray) (s : ErrorState) : Option ErrorResult :=
  afterPrepare binary s (decodeError 5 (prepareErrorSlice binary))

def expectedError (base buffer caller : Word) : ErrorResult :=
  ⟨1, 33, base + 0xd5b0#64, buffer, caller, 0x100⟩

private def preparedError (base buffer caller : Word) (cleanup : CleanupInputs) : ErrorState :=
  { imageBase := base, buffer, caller, cleanup, rax := 33,
    r11 := base + 0xaaf3#64 + 0x2abd#64, stackLength := 33,
    stackMessage := base + 0xaaf3#64 + 0x2abd#64 }

private theorem prepared_fold (binary : ByteArray) (base buffer caller : Word)
    (cleanup : CleanupInputs) :
    afterPrepare binary { imageBase := base, buffer, caller, cleanup }
      (some [.setLength, .setMessage, .saveTraceFlag, .saveLength, .saveMessage]) =
      (executeCleanup binary (preparedError base buffer caller cleanup)).bind (finishError binary) := rfl

private theorem execute_prepared (binary : ByteArray) (h : prepareErrorSlice binary = prepareErrorBytes)
    (base buffer caller : Word) (cleanup : CleanupInputs) :
    executeError binary { imageBase := base, buffer, caller, cleanup } =
      (executeCleanup binary (preparedError base buffer caller cleanup)).bind (finishError binary) :=
  (congrArg (afterPrepare binary { imageBase := base, buffer, caller, cleanup })
    ((congrArg (decodeError 5) h).trans decode_error_prepare)).trans
    (prepared_fold binary base buffer caller cleanup)

private theorem finish_prepared (binary : ByteArray) (h : returnErrorSlice binary = returnErrorBytes)
    (base buffer caller : Word) (cleanup : CleanupInputs) (calls : List Word) :
    finishError binary { preparedError base buffer caller cleanup with bl := 1, freeCalls := calls } =
      some (expectedError base buffer caller) := by
  unfold finishError
  rw [h, decode_error_return]
  simp [Option.bind, List.foldl, stepError, preparedError, expectedError, BitVec.add_assoc]

attribute [local irreducible] executeCleanup finishError executeError

set_option maxRecDepth 8192 in
theorem checked_error_return (binary : ByteArray) (h : checkErrorReturn binary = true)
    (base buffer caller : Word) (cleanup : CleanupInputs) :
    executeError binary { imageBase := base, buffer, caller, cleanup } =
        some (expectedError base buffer caller) ∧
      (binary.extract 0xd5b0 0xd5d1).data = overflowMessage.data := by
  simp only [checkErrorReturn, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨?_, h.2⟩
  rw [execute_prepared binary h.1.1.1]
  rw [checked_cleanup binary h.1.1.2]
  exact finish_prepared binary h.1.2 base buffer caller cleanup _


-- Compose the already checked update with the projected error epilogue.
theorem overflow_produces_error (binary : ByteArray) (hUpdate : checkUpdate binary = true)
    (hReturn : checkErrorReturn binary = true) (s : MemoryState)
    (restore : readWord s.mem (s.rsp + 0xb0#64) = s.r13)
    (ha : 0 ≤ (oldCount s).toInt) (hb : 0 ≤ (increment s).toInt)
    (overflow : 9223372036854775807 < (oldCount s).toInt + (increment s).toInt)
    (base buffer caller : Word) (cleanup : CleanupInputs) :
    (match runUpdate binary s with
      | .reject _ => executeError binary { imageBase := base, buffer, caller, cleanup }
      | _ => none) = some (expectedError base buffer caller) := by
  rw [checked_binary_update binary hUpdate s restore ha hb, ite_eq_left overflow]
  exact (checked_error_return binary hReturn base buffer caller cleanup).1

end N2MachineSlice

#print axioms N2MachineSlice.checked_binary_update
#print axioms N2MachineSlice.checked_cleanup
#print axioms N2MachineSlice.overflow_produces_error

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected path to recorded counter ELF")
  let binary ← IO.FS.readBinFile path
  unless N2MachineSlice.checkUpdate binary && N2MachineSlice.checkErrorReturn binary do
    throw (IO.userError "counter instruction bytes differ")
  IO.println "N2 update, overflow return and error-message bytes matched"
