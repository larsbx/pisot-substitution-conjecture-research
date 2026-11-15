/-
Elementary modulus comparisons for candidate degree-five sectors.
The spectral application also needs transport of the relevant Galois orbit
into the spectrum of the signed quotient.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Psc.Degree5Sector

/-- Nonzero integral determinant and two contracting conjugates give
both contracting moduli strictly above the reciprocal Perron modulus. -/
theorem reciprocal_lt (b x y : ℝ) (hb : 1 < b) (hx : 0 < x)
    (hy : y < 1) (hd : 1 ≤ b * x * y) : 1 < b * x := by
  exact lt_of_le_of_lt hd (by simpa using mul_lt_mul_of_pos_left hy (mul_pos (by linarith) hx))

/-- With the Perron root assigned the largest exponent, each of the three
indicated contents has a weight strictly above the Perron bound. -/
theorem excluded_weights (b x y : ℝ) (hb : 1 < b) (hx : 0 < x)
    (hy : y < 1) (hd : 1 ≤ b * x * y) :
    b < b^4 * x ∧ b < b^3 * x^2 ∧ b < b^3 * x * y := by
  have hbp : 0 < b := by linarith
  have hbx := reciprocal_lt b x y hb hx hy hd
  have hb2 : 1 < b^2 := by nlinarith
  have hsq : 1 < (b * x)^2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc
      b = b * 1 := by ring
      _ < b * (b^2 * (b * x)) := by
        apply mul_lt_mul_of_pos_left _ hbp
        nlinarith [mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hbx)]
      _ = b^4 * x := by ring
  · calc
      b = b * 1 := by ring
      _ < b * (b * x)^2 := mul_lt_mul_of_pos_left hsq hbp
      _ = b^3 * x^2 := by ring
  · calc
      b < b^2 := by nlinarith
      _ = b^2 * 1 := by ring
      _ ≤ b^2 * (b * x * y) := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ = b^3 * x * y := by ring

/-- Every placement of content (2,2,1) lies below the Perron bound when
the determinant modulus is one. -/
theorem weight_221_unit (b x y : ℝ) (hb : 1 < b)
    (hx : 0 < x) (hx1 : x < 1) (_hy : 0 < y) (hy1 : y < 1)
    (hd : b * x * y = 1) :
    b^2 * x^2 * y < b ∧ b^2 * x * y^2 < b ∧ b * x^2 * y^2 < b := by
  have hbp : 0 < b := by linarith
  have hx' := mul_lt_mul_of_pos_left hx1 hbp
  have hy' := mul_lt_mul_of_pos_left hy1 hbp
  have hxy : x * y < 1 :=
    (by simpa using mul_lt_mul_of_pos_left hy1 hx : x * y < x).trans hx1
  constructor
  · calc
      b^2 * x^2 * y = (b * x * y) * (b * x) := by ring
      _ < b := by simpa [hd] using hx'
  constructor
  · calc
      b^2 * x * y^2 = (b * x * y) * (b * y) := by ring
      _ < b := by simpa [hd] using hy'
  · calc
      b * x^2 * y^2 = (b * x * y) * (x * y) := by ring
      _ < b := by simpa [hd] using hxy.trans hb

end Psc.Degree5Sector
