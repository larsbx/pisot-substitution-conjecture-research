/- The cycle and crossing calculations for the grouped eventual range. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Defs

public section

namespace Psc.PeriodicPartner

open scoped BigOperators

private def groupCycle {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (u v : Bool) : A :=
  ∑ i, ∑ j, if p i = u ∧ q j = v then w i j else 0

private theorem groupCycle_row {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (h : ∀ i, ∑ j, w i j = 0)
    (u : Bool) : groupCycle p q w u false + groupCycle p q w u true = 0 := by
  unfold groupCycle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hp : p i = u
  · rw [← Finset.sum_add_distrib]
    refine Eq.trans ?_ (h i)
    apply Finset.sum_congr rfl
    intro j _
    cases q j <;> simp [hp]
  · simp [hp]

private theorem groupCycle_swap {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A) (u v : Bool) :
    groupCycle p q w u v = groupCycle q p (fun j i => w i j) v u := by
  unfold groupCycle
  rw [Finset.sum_comm]
  simp only [and_comm]

/-- Push a cycle by summing edge coefficients on its grouped endpoints.
Each side has at most two groups, encoded by `Bool`. Zero edge weights
cover missing seams. The grouped cycle has one free entry. -/
theorem grouped_cycle_entries {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0) :
    let x (u v : Bool) := ∑ i, ∑ j, if p i = u ∧ q j = v then w i j else 0
    ∀ u v, x u v = if u = v then x false false else -x false false := by
  change ∀ u v, groupCycle p q w u v =
    if u = v then groupCycle p q w false false else -groupCycle p q w false false
  let x := groupCycle p q w
  change ∀ u v, x u v = if u = v then x false false else -x false false
  have hLeft (u : Bool) := groupCycle_row p q w hrow u
  have hRight (v : Bool) : x false v + x true v = 0 := by
    change groupCycle p q w false v + groupCycle p q w true v = 0
    rw [groupCycle_swap p q w false v, groupCycle_swap p q w true v]
    exact groupCycle_row q p (fun j i => w i j) hcol v
  have hft : x false true = -x false false := eq_neg_of_add_eq_zero_right (hLeft false)
  have htf : x true false = -x false false := eq_neg_of_add_eq_zero_right (hRight false)
  have htt : x true true = x false false := by
    have h : x true false + x true true = 0 := hLeft true
    rw [htf] at h
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_right h
  intro u v
  cases u <;> cases v <;> simp [hft, htf, htt]

/-- A nonzero cycle on two groups per side needs a seam of nonzero weight
over each of the four grouped edges. -/
theorem grouped_cycle_support {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (hne : ∃ u v, (∑ i, ∑ j, if p i = u ∧ q j = v then w i j else 0) ≠ 0) :
    ∀ u v, ∃ i j, p i = u ∧ q j = v ∧ w i j ≠ 0 := by
  classical
  let x := groupCycle p q w
  have hshape : ∀ u v, x u v = if u = v then x false false else -x false false :=
    grouped_cycle_entries p q w hrow hcol
  change ∃ u v, x u v ≠ 0 at hne
  intro u v
  by_contra hmissing
  have hzero : x u v = 0 := by
    unfold x groupCycle
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hgroup : p i = u ∧ q j = v
    · have hw : w i j = 0 := by
        by_contra hn
        exact hmissing ⟨i, j, hgroup.1, hgroup.2, hn⟩
      simp [hgroup, hw]
    · simp [hgroup]
  have hfirst : x false false = 0 := by
    rw [hshape u v] at hzero
    split at hzero <;> simpa using hzero
  obtain ⟨u', v', hnonzero⟩ := hne
  exact hnonzero (by rw [hshape u' v', hfirst]; simp)

/-- A nonzero grouped entry picks out an original row meeting both column
groups, since that row has zero total weight. -/
theorem grouped_row_crosses {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A)
    (hrow : ∀ i, ∑ j, w i j = 0) {u : Bool}
    (hentry : (∑ i, ∑ j, if p i = u ∧ q j = false then w i j else 0) ≠ 0) :
    ∃ i j k, p i = u ∧ q j = false ∧ q k = true ∧ w i j ≠ 0 ∧ w i k ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hp : p i = u := by
    by_contra h
    exact hi (by simp [h])
  simp only [hp, true_and] at hi
  have hadd : (∑ j, if q j = false then w i j else 0) +
      (∑ j, if q j = true then w i j else 0) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Eq.trans ?_ (hrow i)
    apply Finset.sum_congr rfl
    intro j _
    cases q j <;> simp
  have hsecond : (∑ j, if q j = true then w i j else 0) ≠ 0 :=
    fun h => hi (by simpa only [h, add_zero] using hadd)
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsecond
  split at hj
  · rename_i hqj
    split at hk
    · rename_i hqk
      exact ⟨i, j, k, hp, hqj, hqk, hj, hk⟩
    · exact (hk rfl).elim
  · exact (hj rfl).elim

end Psc.PeriodicPartner
