import Mathlib

/-!
# Route R1: correction-free ancestry rigidity

Only the explicitly quantified height-growth and bounded-orbit exclusion
are proved here. The nonvanishing height of an actual integral ancestry
defect, and production of long zero-correction stretches from strictness,
remain separate open bindings. No universal PSC claim is discharged.
-/
namespace PscRoutes.R1

variable {State : Type*}

/-- Iterating a Perron-height recurrence on a correction-free orbit. -/
theorem height_on_orbit (beta : ℝ) (x : ℕ → State) (height : State → ℝ)
    (hstep : ∀ k, height (x (k + 1)) = beta * height (x k))
    (n : ℕ) :
    height (x n) = beta ^ n * height (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hstep n, ih, pow_succ]
      ring

/-- A finite-state height cap forbids an excessively long
correction-free segment with nonzero initial Perron height.
The explicit separation epsilon and cap B are assumptions, not
a Pisot/irreducibility theorem. -/
theorem correction_free_run_exclusion
    (beta epsilon cap : ℝ) (x : ℕ → State) (height : State → ℝ)
    (n : ℕ)
    (hbeta : 1 < beta)
    (hstep : ∀ k, height (x (k + 1)) = beta * height (x k))
    (hseparated : epsilon ≤ |height (x 0)|)
    (hcap : |height (x n)| ≤ cap)
    (hlarge : cap < beta ^ n * epsilon) : False := by
  have hnonneg : 0 ≤ beta ^ n := pow_nonneg (by linarith) n
  have hgrowth := height_on_orbit beta x height hstep n
  rw [hgrowth, abs_mul, abs_of_nonneg hnonneg] at hcap
  have hbound : beta ^ n * epsilon ≤ beta ^ n * |height (x 0)| :=
    mul_le_mul_of_nonneg_left hseparated hnonneg
  linarith

end PscRoutes.R1

#print axioms PscRoutes.R1.height_on_orbit
#print axioms PscRoutes.R1.correction_free_run_exclusion
