import Mathlib

/-!
# Route R2: positive-mass obstruction from oriented discrepancies

Finite and exact. This does NOT establish that a strict PIP component
admits a common nonnegative separating functional or positive-density
good returns. Those are adversarially tested open hypotheses.
-/
namespace PscRoutes.R2

variable {ι : Type*} [DecidableEq ι]

/-- A nonnegative family with `good` coordinates at least delta
has total mass at least card(good)*delta. The density limit and the
orientation functional are intentionally outside this theorem. -/
theorem good_mass_lower_bound
    (allIndices good : Finset ι) (value : ι → ℚ) (delta : ℚ)
    (hsub : good ⊆ allIndices)
    (hnonneg : ∀ i ∈ allIndices, 0 ≤ value i)
    (hgood : ∀ i ∈ good, delta ≤ value i) :
    (good.card : ℚ) * delta ≤ ∑ i ∈ allIndices, value i := by
  calc
    (good.card : ℚ) * delta = ∑ _i ∈ good, delta := by simp
    _ ≤ ∑ i ∈ good, value i :=
      Finset.sum_le_sum (by intro i hi; exact hgood i hi)
    _ ≤ ∑ i ∈ allIndices, value i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro i hi _; exact hnonneg i hi)

/-- Algebraic contradiction once an independently proved lower
density bound exceeds a certified upper bound for the average. -/
theorem positive_density_contradiction
    (rho delta mean : ℚ) (hpositive : 0 < rho * delta)
    (hlower : rho * delta ≤ mean)
    (hupper : mean < rho * delta) : False := by
  linarith

end PscRoutes.R2

#print axioms PscRoutes.R2.good_mass_lower_bound
#print axioms PscRoutes.R2.positive_density_contradiction
