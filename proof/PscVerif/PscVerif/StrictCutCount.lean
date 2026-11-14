import PscVerif.OccurrenceTransport
import Mathlib.Order.Interval.Set.Monotone

/-! Count actual reduction starts in the original integer Parikh space. -/

namespace Psc.StrictCutCount

open Psc.Binomial Psc.Reduction Psc.OccurrenceNewborn Psc.OccurrenceTransport

/-- The original prefix vector before a factor occurrence. -/
def factorStart (bs : List WordPair) (j : Fin bs.length) : Fin 3 → ℤ :=
  parikhZ (((bs.take j.val).map Prod.fst).flatten)

/-- Factor starts include the initial position of a nonempty reduction and
exclude the terminal position. -/
def startVectors (bs : List WordPair) : Finset (Fin 3 → ℤ) :=
  Finset.univ.image (factorStart bs)

theorem factorStart_injective {bs : List WordPair}
    (hne : ∀ B ∈ bs, B.1 ≠ []) : Function.Injective (factorStart bs) := by
  let prefixLength := fun j : ℕ => (((bs.take j).map Prod.fst).flatten).length
  have hmono : StrictMonoOn prefixLength (Set.Iic bs.length) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro j hj
    have hj' : j < bs.length := hj
    have hget : bs[j]? = some (bs[j]'hj') := List.getElem?_eq_getElem hj'
    have hnonempty := hne (bs[j]'hj') (List.getElem_mem hj')
    have hpositive : 0 < (bs[j]'hj').1.length := List.length_pos_iff.mpr hnonempty
    simpa [prefixLength, List.take_add_one, hget] using
      Nat.lt_add_of_pos_right (n := prefixLength j) hpositive
  intro i j h
  apply Fin.ext
  apply hmono.injOn (show i.val ≤ bs.length from i.isLt.le)
    (show j.val ≤ bs.length from j.isLt.le)
  exact (equiv1_of_parikhZ_eq h).length_eq

theorem card_startVectors {bs : List WordPair}
    (hne : ∀ B ∈ bs, B.1 ≠ []) : (startVectors bs).card = bs.length := by
  rw [startVectors, Finset.card_image_of_injective _ (factorStart_injective hne)]
  simp

private theorem markAtFactorStart (bs : List WordPair) (j : Fin bs.length)
    (track : WordPair → Word) (hne : track bs[j.val] ≠ []) :
    ∃ mark : Mark (bs.map track).flatten,
      mark.before = ((bs.take j.val).map track).flatten := by
  have hsplit := List.take_append_drop j.val bs
  have hdrop : bs.drop j.val = bs[j.val] :: bs.drop (j.val + 1) :=
    List.drop_eq_getElem_cons j.isLt
  rw [hdrop] at hsplit
  cases htrack : track bs[j.val] with
  | nil => exact (hne htrack).elim
  | cons letter tail =>
    refine ⟨⟨_, letter, tail ++ ((bs.drop (j.val + 1)).map track).flatten, ?_⟩, rfl⟩
    have h := congrArg (fun xs : List WordPair => (xs.map track).flatten) hsplit
    simpa only [List.map_append, List.flatten_append, List.map_cons,
      List.flatten_cons, htrack, List.cons_append] using h.symm

/-- Each counted vector has two literal proper marks with equal prefixes in
Parikh space. -/
theorem exists_balanced_marks_of_mem {u v : Word} (hbal : Equiv1 u v)
    {z : Fin 3 → ℤ} (hz : z ∈ startVectors (red u v)) :
    ∃ top : Mark u, ∃ bottom : Mark v,
      parikhZ top.before = z ∧ parikhZ bottom.before = z := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  have hblock := red_isBlock hbal _ (List.getElem_mem j.isLt)
  have hbottom : ((red u v)[j.val]).2 ≠ [] := by
    intro h
    exact hblock.1 (List.length_eq_zero_iff.mp (by simpa [h] using hblock.2.1.length_eq))
  obtain ⟨top, ht⟩ := markAtFactorStart (red u v) j Prod.fst hblock.1
  obtain ⟨bottom, hb⟩ := markAtFactorStart (red u v) j Prod.snd hbottom
  have hp := equiv1_join ((red u v).take j.val)
    (fun B hB => (red_isBlock hbal B (List.mem_of_mem_take hB)).2.1)
  let top' : Mark u := ⟨top.before, top.letter, top.after,
    (red_top hbal.length_eq).symm.trans top.split⟩
  let bottom' : Mark v := ⟨bottom.before, bottom.letter, bottom.after,
    (red_bot hbal.length_eq).symm.trans bottom.split⟩
  refine ⟨top', bottom', ?_, ?_⟩
  · exact congrArg parikhZ ht
  · exact (congrArg parikhZ hb).trans (parikhZ_eq_of_equiv1 hp).symm

private theorem physicalLength_le_mul_length (ℓ : Fin 3 → ℝ) (L : ℝ)
    (bs : List WordPair) (hbound : ∀ B ∈ bs, physicalLength ℓ B.1 ≤ L) :
    physicalLength ℓ (bs.map Prod.fst).flatten ≤ L * (bs.length : ℝ) := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    have hhead := hbound B (by simp)
    have htail := ih (fun U hU => hbound U (by simp [hU]))
    simp only [List.map_cons, List.flatten_cons, physicalLength_append,
      List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    linarith

/-- Each factor contributes a distinct start, even when factor labels repeat. -/
theorem physicalLength_le_card_reduction_starts (ℓ : Fin 3 → ℝ) (L : ℝ)
    {u v : Word} (hbal : Equiv1 u v)
    (hbound : ∀ B ∈ red u v, physicalLength ℓ B.1 ≤ L) :
    physicalLength ℓ u ≤ L * ((startVectors (red u v)).card : ℝ) := by
  rw [card_startVectors (fun B hB => (red_isBlock hbal B hB).1)]
  simpa only [red_top hbal.length_eq] using
    physicalLength_le_mul_length ℓ L (red u v) hbound

/-- The physical coordinate of every counted vector lies in the strip
starting at the original origin and ending before the terminal cut. -/
theorem offset_mem_strip_of_mem (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    {u v : Word} (hbal : Equiv1 u v) {z : Fin 3 → ℤ}
    (hz : z ∈ startVectors (red u v)) :
    0 ≤ offset ℓ z ∧ offset ℓ z < physicalLength ℓ u := by
  obtain ⟨top, _, ht, _⟩ := exists_balanced_marks_of_mem hbal hz
  rw [← ht]
  have hoff : offset ℓ (parikhZ top.before) = physicalLength ℓ top.before := by
    simp [offset, parikhZ, physicalLength, dotProduct]
  rw [hoff]
  have hnonneg := physicalLength_nonneg ℓ (fun a => (hℓ a).le)
  refine ⟨hnonneg _, ?_⟩
  conv_rhs => rw [top.split, physicalLength_append, physicalLength_cons]
  linarith [hℓ top.letter, hnonneg top.after]

/-- Repeating one factor twice yields two distinct proper starts, even
though the two factor labels are identical. -/
theorem repeated_factor_control :
    (startVectors [([0], [1]), ([0], [1])]).card = 2 := by
  rw [card_startVectors]
  · rfl
  · intro B hB
    simp at hB
    subst B
    simp

theorem empty_startVectors : startVectors [] = ∅ := by
  simp [startVectors]

end Psc.StrictCutCount
