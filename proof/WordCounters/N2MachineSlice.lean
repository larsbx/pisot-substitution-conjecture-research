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
  let lower := upper + 1
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

-- For the recorded ELF, the executable LOAD segment has equal file and
-- virtual offsets. The replay pins the complete ELF before this check.
def checkSlices (binary : ByteArray) : Bool :=
  (binary.extract 0xaa96 0xaac8).data == guardBytes.data &&
    (binary.extract 0xab01 0xab1a).data == acceptedBytes.data

end N2MachineSlice

#print axioms N2MachineSlice.execute_exact

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected path to recorded counter ELF")
  let binary ← IO.FS.readBinFile path
  unless N2MachineSlice.checkSlices binary do
    throw (IO.userError "counter instruction bytes differ")
  IO.println "N2 checked-add instruction bytes matched"
