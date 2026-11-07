import Mathlib

/-!
# Route R4: conditional separation certificates

This proves only that an offset inside a **certified separating radius**
must be zero. Actual Rauzy overlap offsets, the common vertex-to-common
tile bridge, and a uniform window separation radius are open bindings.
-/
namespace PscRoutes.R4

variable {Offset : Type*} [Zero Offset]

/-- Exact abstract separation interface. Never infer its premise
from Pisot contraction alone. -/
theorem separated_window_forces_zero
    (distance : Offset → ℝ) (radius : ℝ)
    (hseparation : ∀ x : Offset, x ≠ 0 → radius ≤ distance x)
    (x : Offset) (hinside : distance x < radius) : x = 0 := by
  by_contra hx
  have hfar := hseparation x hx
  linarith

/-- Integer toy control: a nonzero integral scalar offset cannot have
absolute value less than one. This says nothing about nonintegral
physical offsets in the Pisot embedding without an independent
trace-dual coordinate certificate. -/
theorem integer_offset_small_implies_zero (z : ℤ)
    (hsmall : |(z : ℝ)| < 1) : z = 0 := by
  have hbounds := abs_lt.mp hsmall
  have hlow : (-1 : ℤ) < z := by exact_mod_cast hbounds.1
  have hhigh : z < (1 : ℤ) := by exact_mod_cast hbounds.2
  omega

end PscRoutes.R4

#print axioms PscRoutes.R4.separated_window_forces_zero
#print axioms PscRoutes.R4.integer_offset_small_implies_zero
