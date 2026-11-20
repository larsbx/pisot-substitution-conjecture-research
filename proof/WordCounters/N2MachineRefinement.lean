import WordCounters.N2MachineSlice
import WordCounters.Refinement

set_option warningAsError true
set_option maxRecDepth 8192

namespace N2MachineRefinement

open N2MachineSlice
abbrev limit : Nat := 9223372036854775807

-- These are effective addresses at the entry of the recorded slice.
structure Update where
  seenBase : Word
  seenIndex : Word
  countBase : Word
  countIndex : Word

def Update.entry (u : Update) (mem : Memory) (rsp : Word) : MemoryState :=
  { mem, rsp, rdi := u.seenBase, r9 := u.seenIndex, r13 := u.countBase,
    r15 := u.countIndex }

def outside (address byte : Word) : Prop := 8 ≤ (byte - address).toNat

-- Require disjointness of every store byte and the protected range.
def protects (address base : Word) (size : Nat) : Prop :=
  ∀ i : Nat, i < size → outside address (base + BitVec.ofNat 64 i)

def validRange (base : Word) (size : Nat) : Prop := base.toNat + size ≤ 2^64

structure Frame where
  rsp : Word
  result : Word
  imageBase : Word
  caller : Word
  cleanup : CleanupInputs

-- The six pops occupy rsp+c8 through rsp+f7. RET reads rsp+f8.
-- The modeled frame covers this interval and the local spill area.
def Frame.valid (f : Frame) : Prop :=
  validRange f.rsp 0x100 ∧ validRange f.result 0x48 ∧
  (f.rsp.toNat + 0x100 ≤ f.result.toNat ∨ f.result.toNat + 0x48 ≤ f.rsp.toNat)

def Update.framed (u : Update) (f : Frame) (mem : Memory) : Prop :=
  let s := u.entry mem f.rsp
  f.valid ∧ readWord mem (f.rsp + 0xb0#64) = u.countBase ∧
    readWord mem (f.rsp + 0xf8#64) = f.caller ∧
    validRange (countAddress s) 8 ∧ validRange (indexed s.rdi s.r9) 8 ∧
    protects (countAddress s) f.rsp 0x100 ∧
    protects (countAddress s) f.result 0x48 ∧
    protects (countAddress s) (indexed s.rdi s.r9) 8

structure PendingUpdate where
  target : Update
  old : Nat
  addend : Nat

-- The planner must establish these relations from the compiled loop's
-- initialization, address arithmetic and back edges at each reached step.
def PendingUpdate.ready (p : PendingUpdate) (f : Frame) (mem : Memory) : Prop :=
  let s := p.target.entry mem f.rsp
  p.target.framed f mem ∧ (oldCount s).toInt = (p.old : Int) ∧
    (increment s).toInt = (p.addend : Int)

inductive Outcome where
  | complete (mem : Memory)
  | refused (mem : Memory) (error : ErrorResult)
  | invalid

def run (update : MemoryState → MemoryExit) (error : Option ErrorResult)
    (f : Frame) : List PendingUpdate → Memory → Outcome
  | [], mem => .complete mem
  | p :: rest, mem =>
      match update (p.target.entry mem f.rsp) with
      | .stored next => run update error f rest next
      | .reject unchanged =>
          match error with
          | some result => .refused unchanged result
          | none => .invalid
      | .invalid => .invalid

def runBinaryTrace (binary : ByteArray) (f : Frame) :=
  run (runUpdate binary) (executeError binary
    { imageBase := f.imageBase, buffer := f.result, caller := f.caller,
      cleanup := f.cleanup }) f

def sourceStore (f : Frame) (p : PendingUpdate) (mem : Memory) : Memory :=
  writeWord mem (countAddress (p.target.entry mem f.rsp))
    (BitVec.ofNat 64 (p.old + p.addend))

-- Exact checked additions on the planned source operands. On refusal the
-- memory observation is the state immediately before the failing store.
def sourceRun (f : Frame) : List PendingUpdate → Memory → Outcome
  | [], mem => .complete mem
  | p :: rest, mem =>
      if PscWordCounters.addGuard limit p.old p.addend then
        .refused mem (expectedError f.imageBase f.result f.caller)
      else sourceRun f rest (sourceStore f p mem)

def Ready (f : Frame) : List PendingUpdate → Memory → Prop
  | [], _ => True
  | p :: rest, mem =>
      p.ready f mem ∧
      (PscWordCounters.addGuard limit p.old p.addend = false →
        Ready f rest (sourceStore f p mem))

theorem step_exact (binary : ByteArray) (checked : checkUpdate binary = true)
    (f : Frame) (p : PendingUpdate) (mem : Memory) (ready : p.ready f mem) :
    runUpdate binary (p.target.entry mem f.rsp) =
      if PscWordCounters.addGuard limit p.old p.addend then .reject mem
      else .stored (sourceStore f p mem) := by
  let s := p.target.entry mem f.rsp
  have ha : 0 ≤ (oldCount s).toInt := by rw [ready.2.1]; omega
  have hb : 0 ≤ (increment s).toInt := by rw [ready.2.2]; omega
  have h := checked_binary_update binary checked s ready.1.2.1 ha hb
  change runUpdate binary s = _
  rw [h, ready.2.1, ready.2.2]
  have hold := BitVec.toInt_lt (x := oldCount s)
  rw [ready.2.1] at hold
  change (p.old : Int) < 9223372036854775808 at hold
  have fits : p.old ≤ limit := by change p.old ≤ 9223372036854775807; omega
  have guard := PscWordCounters.guard_exact limit p.old p.addend fits
  cases hg : PscWordCounters.addGuard limit p.old p.addend
  · have hn := guard.mp hg
    change p.old + p.addend ≤ 9223372036854775807 at hn
    have hfit : ¬ 9223372036854775807 < (p.old : Int) + (p.addend : Int) := by omega
    rw [ite_eq_right hfit, ← Int.natCast_add]
    rfl
  · have hn : ¬ p.old + p.addend ≤ limit := by
      intro he
      have hf := guard.mpr he
      rw [hg] at hf
      exact Bool.noConfusion hf
    change ¬ p.old + p.addend ≤ 9223372036854775807 at hn
    have hov : 9223372036854775807 < (p.old : Int) + (p.addend : Int) := by omega
    rw [ite_eq_left hov]
    rfl

private theorem trace_from_step (update : MemoryState → MemoryExit) (f : Frame)
    (step : ∀ p mem, p.ready f mem →
      update (p.target.entry mem f.rsp) =
        if PscWordCounters.addGuard limit p.old p.addend then .reject mem
        else .stored (sourceStore f p mem))
    (plan : List PendingUpdate) (mem : Memory) (ready : Ready f plan mem) :
    run update (some (expectedError f.imageBase f.result f.caller)) f plan mem =
      sourceRun f plan mem := by
  induction plan generalizing mem with
  | nil => rfl
  | cons p rest ih =>
    have hu := step p mem ready.1
    rw [run, sourceRun, hu]
    cases hg : PscWordCounters.addGuard limit p.old p.addend
    · exact ih _ (ready.2 hg)
    · rfl

theorem trace_exact (binary : ByteArray) (checked : checkUpdate binary = true)
    (returns : checkErrorReturn binary = true) (f : Frame)
    (plan : List PendingUpdate) (mem : Memory) (ready : Ready f plan mem) :
    runBinaryTrace binary f plan mem = sourceRun f plan mem := by
  unfold runBinaryTrace
  rw [(checked_error_return binary returns f.imageBase f.result f.caller f.cleanup).1]
  exact trace_from_step (runUpdate binary) f (step_exact binary checked f) plan mem ready

theorem store_preserves_frame (f : Frame) (p : PendingUpdate) (mem : Memory)
    (ready : p.ready f mem) :
    (∀ i : Nat, i < 0x100 →
      sourceStore f p mem (f.rsp + BitVec.ofNat 64 i) = mem (f.rsp + BitVec.ofNat 64 i)) ∧
    (∀ i : Nat, i < 0x48 →
      sourceStore f p mem (f.result + BitVec.ofNat 64 i) =
        mem (f.result + BitVec.ofNat 64 i)) := by
  exact ⟨fun i hi => writeWord_outside _ _ _ _ (ready.1.2.2.2.2.2.1 i hi),
    fun i hi => writeWord_outside _ _ _ _ (ready.1.2.2.2.2.2.2.1 i hi)⟩

-- The error branch never executes the remainder of the plan.
theorem refusal_stops (binary : ByteArray) (checked : checkUpdate binary = true)
    (returns : checkErrorReturn binary = true) (f : Frame)
    (p : PendingUpdate) (rest : List PendingUpdate) (mem : Memory)
    (ready : p.ready f mem)
    (overflow : PscWordCounters.addGuard limit p.old p.addend = true) :
    runBinaryTrace binary f (p :: rest) mem =
      .refused mem (expectedError f.imageBase f.result f.caller) := by
  have schedule : Ready f (p :: rest) mem :=
    ⟨ready, fun accepted => Bool.noConfusion (overflow.symm.trans accepted)⟩
  rw [trace_exact binary checked returns f _ mem schedule, sourceRun, ite_eq_left overflow]

-- A store into the protected range itself violates the byte frame.
theorem overlapping_store_rejected (address : Word) (size : Nat) (nonempty : 0 < size) :
    ¬ protects address address size := by
  intro framed
  have overlap := framed 0 nonempty
  simp [outside] at overlap

theorem incorrect_spill_rejected (u : Update) (f : Frame) (mem : Memory)
    (wrong : readWord mem (f.rsp + 0xb0#64) ≠ u.countBase) :
    ¬ u.framed f mem :=
  fun framed => wrong framed.2.1

#print axioms refusal_stops
#print axioms step_exact
#print axioms trace_exact
#print axioms store_preserves_frame

end N2MachineRefinement
