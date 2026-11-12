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

end N2MachineSlice

#print axioms N2MachineSlice.checked_binary_count

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected path to recorded counter ELF")
  let binary ← IO.FS.readBinFile path
  unless N2MachineSlice.checkSlices binary do
    throw (IO.userError "counter instruction bytes differ")
  IO.println "N2 checked-add instruction bytes matched"
