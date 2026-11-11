import PscVerif.OccurrenceFinite
import PscVerif.FixedPointLimit

/-!
# Actual prefix positions and their complete substitution addresses

The dependent address retains the parent ordinal and its full literal mark.
The forward index is injective even with erasures. Cofinality of substituted
prefix lengths supplies surjectivity; nonerasing is a sufficient condition.
The full fixed-prefix equation then identifies the addressed output with the
original word, including its entire prefix and selected letter.

An actual productive prolongable seed instantiates the infinite word using
`FixedPointLimit.limit`. A bounded fixed-prefix check is not substituted for
that construction. Pre-code gate:
`docs/c4-prefix-closure-literature-2026-11-11.md`.
-/

namespace Psc.PrefixAddress

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceAddress Matrix

def wordPrefix (w : ℕ → Fin 3) (n : ℕ) : Word := List.ofFn (fun i : Fin n => w i)

@[simp]
theorem prefix_length (w : ℕ → Fin 3) (n : ℕ) : (wordPrefix w n).length = n := by
  simp [wordPrefix]

@[simp]
theorem prefix_zero (w : ℕ → Fin 3) : wordPrefix w 0 = [] := by simp [wordPrefix]

@[simp]
theorem prefix_getElem (w : ℕ → Fin 3) (n i : ℕ) (h : i < (wordPrefix w n).length) :
    (wordPrefix w n)[i]'h = w i := by simp [wordPrefix]

theorem prefix_take (w : ℕ → Fin 3) {m n : ℕ} (h : m ≤ n) :
    (wordPrefix w n).take m = wordPrefix w m := by
  apply List.ext_getElem
  · simp [wordPrefix, Nat.min_eq_left h]
  · intro i hi hj
    simp [wordPrefix]

theorem prefix_mono (w : ℕ → Fin 3) {m n : ℕ} (h : m ≤ n) :
    wordPrefix w m <+: wordPrefix w n := by
  apply List.prefix_iff_eq_take.mpr
  simpa only [prefix_length] using (prefix_take w h).symm

theorem prefix_succ (w : ℕ → Fin 3) (n : ℕ) :
    wordPrefix w (n + 1) = wordPrefix w n ++ [w n] := by
  simpa [wordPrefix, List.concat_eq_append] using
    List.ofFn_succ' (fun i : Fin (n + 1) => w i)

/-- The complete fixed-word identity, quantified over every finite prefix. -/
def FixedPrefix (τ : Fin 3 → Word) (w : ℕ → Fin 3) : Prop :=
  ∀ n, wordPrefix w (subst τ (wordPrefix w n)).length = subst τ (wordPrefix w n)

/-- Every output position occurs in some actual substituted prefix. -/
def CofinalImages (τ : Fin 3 → Word) (w : ℕ → Fin 3) : Prop :=
  ∀ n, ∃ N, n < (subst τ (wordPrefix w N)).length

theorem cofinalImages_of_nonerasing (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (nonerasing : ∀ a, τ a ≠ []) : CofinalImages τ w := by
  intro n
  refine ⟨n + 1, ?_⟩
  have h := Psc.FixedPointLimit.length_le_subst τ nonerasing (wordPrefix w (n + 1))
  rw [prefix_length] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self n) h

/-- The source ordinal is retained even when different source letters or
different positions have equal projected data. -/
abbrev Address (τ : Fin 3 → Word) (w : ℕ → Fin 3) :=
  Σ i : ℕ, Mark (τ (w i))

def childIndex (τ : Fin 3 → Word) (w : ℕ → Fin 3) (e : Address τ w) : ℕ :=
  (subst τ (wordPrefix w e.1)).length + e.2.index

def parentMark (w : ℕ → Fin 3) (i : ℕ) : Mark (wordPrefix w (i + 1)) where
  before := wordPrefix w i
  letter := w i
  after := []
  split := prefix_succ w i

theorem inflated_index (τ : Fin 3 → Word) (w : ℕ → Fin 3) (e : Address τ w) :
    ((parentMark w e.1).inflate τ e.2).index = childIndex τ w e := by
  simp [parentMark, Mark.inflate, Mark.index, childIndex]

/-- A forward address already fits into the image of the prefix ending
at its own parent. No nonerasing assumption is needed. -/
theorem childIndex_lt (τ : Fin 3 → Word) (w : ℕ → Fin 3) (e : Address τ w) :
    childIndex τ w e < (subst τ (wordPrefix w (e.1 + 1))).length := by
  rw [← inflated_index]
  exact Mark.index_lt _

theorem childIndex_parent_le (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (nonerasing : ∀ a, τ a ≠ []) (e : Address τ w) :
    e.1 ≤ childIndex τ w e := by
  have h := Psc.FixedPointLimit.length_le_subst τ nonerasing (wordPrefix w e.1)
  rw [prefix_length] at h
  exact h.trans (Nat.le_add_right _ _)

/-- The existing finite lookup returns the full forward numeric address
inside any larger source window. -/
theorem childIndex_locate (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (e : Address τ w) (N : ℕ) (h : e.1 < N) :
    locate ((wordPrefix w N).map τ) (childIndex τ w e) = some (e.1, e.2.index) := by
  have hi : e.1 < (wordPrefix w N).length := by simpa using h
  have hd : e.2.index < (τ ((wordPrefix w N)[e.1]'hi)).length := by
    simpa only [prefix_getElem] using e.2.index_lt
  have hl := locate_subst_position τ (wordPrefix w N) e.1 e.2.index hi hd
  simpa only [prefix_take w h.le, childIndex] using hl

/-- Different full parent/local marks never share an output index, even
if there are empty image blocks between their parents. -/
theorem childIndex_injective (τ : Fin 3 → Word) (w : ℕ → Fin 3) :
    Function.Injective (childIndex τ w) := by
  rintro ⟨i, d⟩ ⟨j, e⟩ h
  let N := max i j + 1
  have hi : i < N := lt_of_le_of_lt (le_max_left i j) (Nat.lt_succ_self _)
  have hj : j < N := lt_of_le_of_lt (le_max_right i j) (Nat.lt_succ_self _)
  have hd := childIndex_locate τ w ⟨i, d⟩ N hi
  have he := childIndex_locate τ w ⟨j, e⟩ N hj
  rw [h] at hd
  have hp : (i, d.index) = (j, e.index) := Option.some.inj (hd.symm.trans he)
  have hij : i = j := congrArg Prod.fst hp
  subst j
  have hde : d = e := mark_index_injective _ (congrArg Prod.snd hp)
  subst e
  rfl

/-- Cofinal output windows cover every natural-number output position. -/
theorem childIndex_surjective (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (cofinal : CofinalImages τ w) : Function.Surjective (childIndex τ w) := by
  intro n
  obtain ⟨N, hn⟩ := cofinal n
  let o := locateSubst τ (wordPrefix w N) n hn
  obtain ⟨ho, hf⟩ := List.getElem?_eq_some_iff.mp o.atOrdinal
  have hoN : o.ordinal < N := by simpa only [prefix_length] using ho
  have hw : w o.ordinal = o.factor := by simpa only [prefix_getElem] using hf
  let d : Mark (τ (w o.ordinal)) :=
    ⟨o.before, o.letter, o.after, by rw [hw]; exact o.split⟩
  refine ⟨⟨o.ordinal, d⟩, ?_⟩
  have he := locateSubst_index τ (wordPrefix w N) n hn
  change n = (subst τ ((wordPrefix w N).take o.ordinal)).length + o.localIndex at he
  rw [prefix_take w hoN.le] at he
  change (subst τ (wordPrefix w o.ordinal)).length + o.before.length = n
  rw [o.local_length]
  exact he.symm

theorem childIndex_bijective (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (cofinal : CofinalImages τ w) : Function.Bijective (childIndex τ w) :=
  ⟨childIndex_injective τ w, childIndex_surjective τ w cofinal⟩

/-- This equivalence preserves actual marks. It does not assert that their
Parikh vectors or projected prefix points are distinct. -/
noncomputable def addressEquiv (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (cofinal : CofinalImages τ w) : Address τ w ≃ ℕ :=
  Equiv.ofBijective (childIndex τ w) (childIndex_bijective τ w cofinal)

theorem prefix_childIndex (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix τ w) (e : Address τ w) :
    wordPrefix w (childIndex τ w e) = subst τ (wordPrefix w e.1) ++ e.2.before := by
  have h := ((parentMark w e.1).inflate τ e.2).take_index
  rw [inflated_index, ← fixed (e.1 + 1), prefix_take w (childIndex_lt τ w e).le] at h
  exact h

theorem letter_childIndex (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix τ w) (e : Address τ w) :
    w (childIndex τ w e) = e.2.letter := by
  have h := ((parentMark w e.1).inflate τ e.2).selected
  rw [inflated_index, ← fixed (e.1 + 1), prefix_getElem] at h
  exact h

/-- The affine prefix formula is derived from the complete literal prefix
identity, retaining its actual addressed occurrence. -/
theorem parikhZ_prefix_childIndex (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix τ w) (e : Address τ w) :
    parikhZ (wordPrefix w (childIndex τ w e)) =
      incidenceZ τ *ᵥ parikhZ (wordPrefix w e.1) + parikhZ e.2.before := by
  rw [prefix_childIndex τ w fixed, parikhZ_append, parikhZ_subst]

/-- Every actual position has a unique full address; the prefix and letter
identities refer to that address, not merely an equal projected label. -/
theorem complete_address (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix τ w) (cofinal : CofinalImages τ w) (n : ℕ) :
    ∃! e : Address τ w, childIndex τ w e = n ∧
      wordPrefix w n = subst τ (wordPrefix w e.1) ++ e.2.before ∧ w n = e.2.letter := by
  obtain ⟨e, he⟩ := childIndex_surjective τ w cofinal n
  refine ⟨e, ⟨he, ?_, ?_⟩, ?_⟩
  · simpa only [he] using prefix_childIndex τ w fixed e
  · simpa only [he] using letter_childIndex τ w fixed e
  · intro f hf
    exact childIndex_injective τ w (hf.1.trans he.symm)

/-- An actual infinite word constructed from a nonerasing, strictly growing
prolongable seed. Growth is proved by the existing fixed-point module. -/
noncomputable def seedWord (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length) : ℕ → Fin 3 :=
  Psc.FixedPointLimit.limit τ u 1
    (Psc.FixedPointLimit.grow_of_nonerasing τ nonerasing (p := 1) prolongable grows)

theorem seedWord_fixedPrefix (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length) :
    FixedPrefix τ (seedWord τ u nonerasing prolongable grows) := by
  intro n
  simpa only [wordPrefix, seedWord, Function.iterate_one] using
    Psc.FixedPointLimit.limit_fixed_eq τ (u := u) (p := 1) prolongable
      (Psc.FixedPointLimit.grow_of_nonerasing τ nonerasing (p := 1) prolongable grows) n

theorem seedWord_cofinalImages (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length) :
    CofinalImages τ (seedWord τ u nonerasing prolongable grows) :=
  cofinalImages_of_nonerasing τ _ nonerasing

/-- Finite iterated seed windows are authenticated prefixes of the actual
constructed word, rather than independent samples of an arbitrary word. -/
theorem seedWord_spec (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length) (j i : ℕ)
    (h : i < ((subst τ)^[j] u).length) :
    seedWord τ u nonerasing prolongable grows i = ((subst τ)^[j] u)[i]'h := by
  simpa only [seedWord, Nat.one_mul, List.get_eq_getElem] using
    Psc.FixedPointLimit.limit_spec τ (u := u) (p := 1) prolongable
      (Psc.FixedPointLimit.grow_of_nonerasing τ nonerasing (p := 1) prolongable grows)
      j i (by simpa only [Nat.one_mul] using h)

theorem subst_erasing (u : Word) : subst (fun _ : Fin 3 => []) u = [] := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa only [subst, List.map_cons, List.flatten_cons, List.nil_append] using ih

/-- The fixed-prefix identity is vacuous for complete erasure. -/
theorem erasing_fixedPrefix :
    FixedPrefix (fun _ : Fin 3 => []) (fun _ : ℕ => (0 : Fin 3)) := by
  intro n
  simp only [subst_erasing, List.length_nil, prefix_zero]

/-- Cofinality is the additional condition excluding that vacuous identity. -/
theorem erasing_not_cofinalImages :
    ¬ CofinalImages (fun _ : Fin 3 => []) (fun _ : ℕ => (0 : Fin 3)) := by
  intro h
  obtain ⟨N, hN⟩ := h 0
  simpa only [subst_erasing, List.length_nil, Nat.lt_irrefl] using hN

end Psc.PrefixAddress
