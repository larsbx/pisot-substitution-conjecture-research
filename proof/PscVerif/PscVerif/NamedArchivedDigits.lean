import PscVerif.NamedInverseDecoder
import PscVerif.OccurrenceAdmissibility

/-!
# Complete computable digits for the two original archived overlap graphs

The native digit IDs enumerate the actual squared words in parent order:
three positions for parent zero, seven for parent one, and five for parent
two. Every ID decodes to a full literal mark, and every full mark has a
unique ID. The additional outer/local address is authenticated by the
existing `Mark.inflate`, retaining both levels of the original substitution.

This is an occurrence enumeration, not a graph-completeness assertion.
Pre-code gate: `docs/c4-archived-payload-import-literature-2026-11-12.md`.
-/

namespace Psc.NamedArchivedDigits

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceInverse Psc.OccurrenceCover Psc.NamedPrefixCompact

/-- Exact lengths of the three original squared image words. -/
def lengths : Fin 3 → ℕ := ![3, 7, 5]

theorem length_two (fixture : Fin 2) (a : Fin 3) :
    (iterateImages (substitution fixture) 2 a).length = lengths a := by
  fin_cases fixture <;> fin_cases a <;> decide +kernel

/-- The original parent-major ID ordering, before selecting an occurrence. -/
def parent (k : Fin 15) : Fin 3 :=
  if k.val < 3 then 0 else if k.val < 10 then 1 else 2

/-- The zero-based position within the complete squared parent word. -/
def flat (k : Fin 15) : ℕ :=
  if k.val < 3 then k.val else if k.val < 10 then k.val - 3 else k.val - 10

def start : Fin 3 → ℕ := ![0, 3, 10]

theorem flat_lt (fixture : Fin 2) (k : Fin 15) :
    flat k < (iterateImages (substitution fixture) 2 (parent k)).length := by
  rw [length_two]
  fin_cases k <;> decide +kernel

theorem start_add_flat (k : Fin 15) : start (parent k) + flat k = k.val := by
  fin_cases k <;> decide +kernel

/-- The stored digit is the entire actual mark, including prefix and suffix. -/
def digit (fixture : Fin 2) (k : Fin 15) :
    Digit (iterateImages (substitution fixture) 2) :=
  ⟨parent k, markAt _ ⟨flat k, flat_lt fixture k⟩⟩

theorem digit_parent (fixture : Fin 2) (k : Fin 15) :
    (digit fixture k).1 = parent k := rfl

theorem digit_flat (fixture : Fin 2) (k : Fin 15) :
    (digit fixture k).2.index = flat k :=
  markAt_index _ _

/-- Recover the archived ID from the parent and the full mark's position. -/
def index (fixture : Fin 2) (d : Digit (iterateImages (substitution fixture) 2)) :
    Fin 15 :=
  ⟨start d.1 + d.2.index, by
    rcases d with ⟨a, m⟩
    have hi := m.index_lt
    rw [length_two] at hi
    fin_cases a <;> simp [start, lengths] at * <;> omega⟩

theorem parent_index (fixture : Fin 2)
    (d : Digit (iterateImages (substitution fixture) 2)) :
    parent (index fixture d) = d.1 := by
  apply Fin.ext
  rcases d with ⟨a, m⟩
  have hi := m.index_lt
  rw [length_two] at hi
  fin_cases a
  · have hcut : m.index < 3 := by simpa [lengths] using hi
    simp [index, parent, start, hcut]
  · have hbound : m.index < 7 := by simpa [lengths] using hi
    have hfirst : ¬ 3 + m.index < 3 := by omega
    have hsecond : 3 + m.index < 10 := by omega
    simp [index, parent, start, hfirst, hsecond]
  · have hfirst : ¬ 10 + m.index < 3 := by omega
    have hsecond : ¬ 10 + m.index < 10 := by omega
    simp [index, parent, start, hfirst, hsecond]

theorem flat_index (fixture : Fin 2)
    (d : Digit (iterateImages (substitution fixture) 2)) :
    flat (index fixture d) = d.2.index := by
  rcases d with ⟨a, m⟩
  have hi := m.index_lt
  rw [length_two] at hi
  fin_cases a <;> simp [index, flat, start, lengths] at * <;> omega

/-- A complete parent/flat address identifies the full literal digit. -/
theorem address_injective (fixture : Fin 2) :
    Function.Injective (fun d : Digit (iterateImages (substitution fixture) 2) =>
      (d.1, d.2.index)) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  have hab : a = b := congrArg Prod.fst h
  subst b
  have hm : m.index = n.index := congrArg Prod.snd h
  have he : m = n := mark_index_injective _ hm
  subst n
  rfl

/-- Exhaustiveness for every full original mark, not merely sampled digits. -/
theorem digit_index (fixture : Fin 2)
    (d : Digit (iterateImages (substitution fixture) 2)) :
    digit fixture (index fixture d) = d := by
  apply address_injective fixture
  exact Prod.ext (parent_index fixture d)
    ((digit_flat fixture (index fixture d)).trans (flat_index fixture d))

/-- No two archived digit IDs identify the same literal occurrence. -/
theorem index_digit (fixture : Fin 2) (k : Fin 15) :
    index fixture (digit fixture k) = k := by
  apply Fin.ext
  change start (parent k) + (digit fixture k).2.index = k.val
  rw [digit_flat]
  exact start_add_flat k

theorem digit_injective (fixture : Fin 2) : Function.Injective (digit fixture) :=
  Function.LeftInverse.injective (index_digit fixture)

theorem digit_surjective (fixture : Fin 2) : Function.Surjective (digit fixture) :=
  fun d => ⟨index fixture d, digit_index fixture d⟩

/-- A computable equivalence, with neither choice nor a noncomputable inventory. -/
def digitEquiv (fixture : Fin 2) :
    Fin 15 ≃ Digit (iterateImages (substitution fixture) 2) where
  toFun := digit fixture
  invFun := index fixture
  left_inv := index_digit fixture
  right_inv := digit_index fixture

/-- First-level position in the original parent image. -/
def outerIndex (k : Fin 15) : ℕ :=
  ![0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 1, 2, 2, 2] k

/-- Position within the image of the actual selected first-level letter. -/
def localIndex (k : Fin 15) : ℕ :=
  ![0, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 2] k

theorem outerIndex_lt (fixture : Fin 2) (k : Fin 15) :
    outerIndex k < (substitution fixture (parent k)).length := by
  fin_cases fixture <;> fin_cases k <;> decide +kernel

def outerMark (fixture : Fin 2) (k : Fin 15) :
    Mark (substitution fixture (parent k)) :=
  markAt _ ⟨outerIndex k, outerIndex_lt fixture k⟩

theorem localIndex_lt (fixture : Fin 2) (k : Fin 15) :
    localIndex k < (substitution fixture (outerMark fixture k).letter).length := by
  fin_cases fixture <;> fin_cases k <;> decide +kernel

def localMark (fixture : Fin 2) (k : Fin 15) :
    Mark (substitution fixture (outerMark fixture k).letter) :=
  markAt _ ⟨localIndex k, localIndex_lt fixture k⟩

theorem outerMark_index (fixture : Fin 2) (k : Fin 15) :
    (outerMark fixture k).index = outerIndex k := markAt_index _ _

theorem localMark_index (fixture : Fin 2) (k : Fin 15) :
    (localMark fixture k).index = localIndex k := markAt_index _ _

/-- The source of inflation is the original squared word, not a reordered image. -/
theorem square_word (fixture : Fin 2) (a : Fin 3) :
    iterateImages (substitution fixture) 2 a =
      subst (substitution fixture) (substitution fixture a) := by
  fin_cases fixture <;> fin_cases a <;> rfl

/-- Full parent/outer/local authentication through literal inflation.
`HEq` retains the word index on each mark without inserting casts in the
computational digit decoder. Both word indices agree by `square_word`. -/
theorem digit_inflate (fixture : Fin 2) (k : Fin 15) :
    HEq (digit fixture k).2
      ((outerMark fixture k).inflate (substitution fixture) (localMark fixture k)) := by
  fin_cases fixture <;> fin_cases k <;> rfl

/-- The complete nested prefix, not only its Parikh vector, is preserved. -/
theorem digit_before_inflate (fixture : Fin 2) (k : Fin 15) :
    (digit fixture k).2.before =
      subst (substitution fixture) (outerMark fixture k).before ++
        (localMark fixture k).before := by
  fin_cases fixture <;> fin_cases k <;> rfl

theorem digit_letter_inflate (fixture : Fin 2) (k : Fin 15) :
    (digit fixture k).2.letter = (localMark fixture k).letter := by
  fin_cases fixture <;> fin_cases k <;> rfl

theorem digit_after_inflate (fixture : Fin 2) (k : Fin 15) :
    (digit fixture k).2.after = (localMark fixture k).after ++
      subst (substitution fixture) (outerMark fixture k).after := by
  fin_cases fixture <;> fin_cases k <;> rfl

/-- The flat index is recovered from the complete outer prefix and local index. -/
theorem flat_eq_nested_index (fixture : Fin 2) (k : Fin 15) :
    flat k = (subst (substitution fixture) (outerMark fixture k).before).length +
      localIndex k := by
  fin_cases fixture <;> fin_cases k <;> decide +kernel

/-- Equal selected letters do not identify their distinct positional marks. -/
theorem repeated_letters_retain_positions :
    (digit 0 4).2.letter = (digit 0 5).2.letter ∧ digit 0 4 ≠ digit 0 5 := by
  refine ⟨by decide +kernel, ?_⟩
  intro h
  exact (by decide : (4 : Fin 15) ≠ 5) (digit_injective 0 h)

/-- The two common-incidence sources select different letters at the same ID. -/
theorem source_order_matters :
    (digit 0 1).2.letter = 2 ∧ (digit 1 1).2.letter = 1 := by
  constructor <;> decide +kernel

end Psc.NamedArchivedDigits
