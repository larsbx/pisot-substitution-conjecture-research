import Lean

set_option warningAsError true

namespace PscWordCounters

abbrev Letter := Fin 3
abbrev Slot := List Letter
abbrev Counts := Slot → Nat

def initial : Counts
  | [] => 1
  | _ :: _ => 0

-- A slot is stored last letter first. Updates read the previous prefix.
def increment (counts : Counts) (letter : Letter) : Slot → Nat
  | [] => 0
  | head :: tail => if head = letter then counts tail else 0

def step (counts : Counts) (letter : Letter) : Counts :=
  fun slot => counts slot + increment counts letter slot

def exact (counts : Counts) (word : List Letter) : Counts :=
  word.foldl step counts

-- This is the positive-addend guard in checked_int.mojo, with subtraction
-- interpreted in Int. Zero increments can also represent untouched slots.
def addGuard (limit a b : Nat) : Bool :=
  decide (0 < b ∧ (limit : Int) - (b : Int) < (a : Int))

theorem guard_exact (limit a b : Nat) (ha : a ≤ limit) :
    addGuard limit a b = false ↔ a + b ≤ limit := by
  unfold addGuard
  simp only [decide_eq_false_iff_not]
  omega

def checkedStep (limit : Nat) (slots : List Slot) (counts : Counts) (letter : Letter) :
    Option Counts :=
  if slots.all (fun slot => !addGuard limit (counts slot) (increment counts letter slot))
  then some (step counts letter) else none

def run (limit : Nat) (slots : List Slot) (counts : Counts) : List Letter → Option Counts
  | [] => some counts
  | letter :: rest => (checkedStep limit slots counts letter).bind
      (fun next => run limit slots next rest)

def Fits (limit : Nat) (slots : List Slot) (counts : Counts) : Prop :=
  ∀ slot ∈ slots, counts slot ≤ limit

def PrefixesFit (limit : Nat) (slots : List Slot) (counts : Counts) : List Letter → Prop
  | [] => True
  | letter :: rest => Fits limit slots (step counts letter) ∧
      PrefixesFit limit slots (step counts letter) rest

theorem checked_step_exact (limit : Nat) (slots : List Slot) (counts : Counts)
    (letter : Letter) (h : Fits limit slots counts) :
    checkedStep limit slots counts letter = some (step counts letter) ↔
      Fits limit slots (step counts letter) := by
  simp only [checkedStep, ite_eq_left_iff, reduceCtorEq, imp_false, Classical.not_not,
    List.all_eq_true, Bool.not_eq_true']
  unfold Fits step
  exact forall_congr' fun slot => forall_congr' fun hs => guard_exact _ _ _ (h slot hs)

open scoped Classical in
theorem run_exact (limit : Nat) (slots : List Slot) (counts : Counts)
    (word : List Letter) (h : Fits limit slots counts) :
    run limit slots counts word =
      if _ : PrefixesFit limit slots counts word then some (exact counts word) else none := by
  classical
  induction word generalizing counts with
  | nil => simp [run, exact, PrefixesFit]
  | cons letter rest ih =>
    have hs := checked_step_exact limit slots counts letter h
    by_cases hf : Fits limit slots (step counts letter)
    · have hp : PrefixesFit limit slots counts (letter :: rest) ↔
          PrefixesFit limit slots (step counts letter) rest :=
        ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
      simp only [run, hs.mpr hf, Option.bind, ih _ hf, hp, exact, List.foldl_cons]
    · have hn : checkedStep limit slots counts letter = none := by
        unfold checkedStep
        split
        · rename_i guard
          have he : checkedStep limit slots counts letter = some (step counts letter) := by
            simp [checkedStep, guard]
          exact (hf (hs.mp he)).elim
        · rfl
      simp [run, hn, PrefixesFit, hf]

-- Enumeration retains each choice of positions, including repeated words.
def extendDeck (deck : List Slot) (letter : Letter) : List Slot :=
  deck ++ deck.map (List.cons letter)

def deck (word : List Letter) : List Slot :=
  word.foldl extendDeck [[]]

theorem deck_step (previous : List Slot) (letter : Letter) (slot : Slot) :
    (extendDeck previous letter).count slot =
      step (fun pattern => previous.count pattern) letter slot := by
  cases slot with
  | nil =>
    simp [extendDeck, step, increment, List.count_eq_countP,
      List.countP_map, Function.comp_def]
  | cons head tail =>
    by_cases h : head = letter
    · subst head
      simp [extendDeck, step, increment, List.count_eq_countP,
        List.countP_map, Function.comp_def]
    · have h' : letter ≠ head := Ne.symm h
      simp [extendDeck, step, increment, h, h', List.count_eq_countP,
        List.countP_map, Function.comp_def]

theorem fold_exact_deck (word : List Letter) (previous : List Slot) :
    exact (fun slot => previous.count slot) word =
      fun slot => (word.foldl extendDeck previous).count slot := by
  induction word generalizing previous with
  | nil => rfl
  | cons letter rest ih =>
    have hs : step (fun slot => previous.count slot) letter =
        fun slot => (extendDeck previous letter).count slot := funext fun slot =>
      (deck_step previous letter slot).symm
    simpa only [exact, List.foldl_cons, hs] using ih (extendDeck previous letter)

theorem initial_deck : initial = fun slot => ([[]] : List Slot).count slot := by
  funext slot
  cases slot <;> simp [initial]

theorem successful_count_exact (limit : Nat) (slots : List Slot) (word : List Letter)
    (counts : Counts) (hi : Fits limit slots initial)
    (h : run limit slots initial word = some counts) :
    ∀ slot, counts slot = (deck word).count slot := by
  classical
  rw [run_exact _ _ _ _ hi] at h
  split at h
  · have he : exact initial word = counts := Option.some.inj h
    rw [← he, initial_deck, fold_exact_deck]
    exact fun _ => rfl
  · contradiction

theorem refusal_iff_prefix_overflow (limit : Nat) (slots : List Slot) (word : List Letter)
    (hi : Fits limit slots initial) :
    run limit slots initial word = none ↔ ¬ PrefixesFit limit slots initial word := by
  classical
  rw [run_exact _ _ _ _ hi]
  by_cases h : PrefixesFit limit slots initial word <;> simp [h]

def alphabet : List Letter := [0, 1, 2]

def slotsOfLength : Nat → List Slot
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun letter => (slotsOfLength n).map (List.cons letter)

theorem mem_alphabet (letter : Letter) : letter ∈ alphabet := by
  have h : letter.val = 0 ∨ letter.val = 1 ∨ letter.val = 2 := by omega
  rcases h with h | h | h
  · have he : letter = 0 := Fin.ext h
    simp [he, alphabet]
  · have he : letter = 1 := Fin.ext h
    simp [he, alphabet]
  · have he : letter = 2 := Fin.ext h
    simp [he, alphabet]

theorem mem_slotsOfLength (n : Nat) (slot : Slot) :
    slot ∈ slotsOfLength n ↔ slot.length = n := by
  induction n generalizing slot with
  | zero => cases slot <;> simp [slotsOfLength]
  | succ n ih =>
    cases slot with
    | nil => simp [slotsOfLength]
    | cons letter tail =>
      simp [slotsOfLength, mem_alphabet, ih]

def trackedSlots : Nat → List Slot
  | 0 => []
  | degree + 1 => slotsOfLength (degree + 1) ++ trackedSlots degree

theorem mem_trackedSlots (degree : Nat) (slot : Slot) :
    slot ∈ trackedSlots degree ↔ 0 < slot.length ∧ slot.length ≤ degree := by
  induction degree with
  | zero => cases slot <;> simp [trackedSlots]
  | succ n ih =>
    simp only [trackedSlots, List.mem_append, mem_slotsOfLength, ih]
    omega

theorem initial_tracked_fits (limit degree : Nat) : Fits limit (trackedSlots degree) initial := by
  intro slot hs
  have h := ((mem_trackedSlots degree slot).mp hs).1
  cases slot with
  | nil => simp at h
  | cons => simp [initial]

-- A fitting degree-four count, and refusal caused by a shorter prefix counter.
private def zeros : List Letter := [0, 0, 0, 0, 0]

example : (run 10 (trackedSlots 4) initial zeros).map (fun s => s [0, 0, 0, 0]) =
    some 5 := by decide

example : (run 9 (trackedSlots 4) initial zeros).isNone = true := by decide

example : (run 5 (trackedSlots 4) initial [0, 0, 0, 0]).isNone = true := by decide

example : (run 84 (trackedSlots 3) initial (List.replicate 9 0)).isSome = true := by decide

example : (run 84 (trackedSlots 4) initial (List.replicate 9 0)).isNone = true := by decide

-- Extending a row-major index remains in the checked next dimension.
theorem extend_index_lt {size slot letter slots : Nat}
    (hl : letter < size) (hs : slot < slots) :
    slot * size + letter < slots * size := by
  calc
    slot * size + letter < (slot + 1) * size := by rw [Nat.add_mul]; simp; omega
    _ ≤ slots * size := Nat.mul_le_mul_right _ (by omega)

theorem difference_fits (limit a b : Nat) (ha : a ≤ limit) (hb : b ≤ limit) :
    -(limit : Int) ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ (limit : Int) := by
  omega

end PscWordCounters

#print axioms PscWordCounters.successful_count_exact
#print axioms PscWordCounters.refusal_iff_prefix_overflow
#print axioms PscWordCounters.mem_trackedSlots
#print axioms PscWordCounters.extend_index_lt
#print axioms PscWordCounters.difference_fits
