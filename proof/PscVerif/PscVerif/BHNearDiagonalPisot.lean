import PscVerif.BHDiagonalParameters
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Primitive irreducible Pisot arithmetic in the two adjacent BH bands

The actual words `(1, 0 1^k 2, 0^r 1)` have incidence characteristic
polynomial `X^3-k*X^2-2*X-r` and determinant `r`. For every `r ≥ 12`
and `r+1 ≤ k ≤ r+2`, the bracketed real root is constructed. Its two
other complex roots have squared norm exactly `r/beta < 1`, and the
actual characteristic polynomial is irreducible over the rationals.

The same-session extension of the standard arithmetic source decision is
`docs/bh-diagonal-arithmetic-stop-go-2026-11-27.md`. No spectral conclusion
or unimodular hypothesis is introduced.
-/

namespace Psc.BHNearDiagonalPisot

open Matrix Polynomial
open Psc.Incidence (inc)
open Psc.BHNearDiagonalLiteral

/-- Original image-letter counts, with source letters indexing columns. -/
theorem incidence_eq (r k : ℕ) :
    inc (sigma r k) = !![0,1,r; 1,k,1; 0,1,0] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Psc.Incidence.inc_apply, sigma, List.count_replicate]

theorem incidence_sq (r k : ℕ) :
    inc (sigma r k)^2 = !![1,k+r,1; k,k^2+2,k+r; 1,k,1] := by
  rw [incidence_eq, pow_two]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The square is strictly positive whenever the literal run is nonempty. -/
theorem primitive (r k : ℕ) (hk : 0 < k) :
    ∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c := by
  refine ⟨2, by omega, ?_⟩
  rw [incidence_sq]
  intro a c
  fin_cases a <;> fin_cases c <;> simp <;> omega

noncomputable def incidenceQ (r k : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (inc (sigma r k)).map (Nat.cast : ℕ → ℚ)

theorem incidenceQ_eq (r k : ℕ) :
    incidenceQ r k = !![0,1,(r : ℚ); 1,k,1; 0,1,0] := by
  rw [incidenceQ, incidence_eq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp

/-- The determinant is r in both bands; the matrices are not unimodular. -/
theorem determinant (r k : ℕ) : (incidenceQ r k).det = r := by
  rw [incidenceQ_eq, Matrix.det_fin_three]
  simp

noncomputable def polynomial (r k : ℕ) : ℚ[X] :=
  X^3-C (k : ℚ)*X^2-C 2*X-C (r : ℚ)

noncomputable def integerPolynomial (r k : ℕ) : ℤ[X] :=
  X^3-C (k : ℤ)*X^2-C 2*X-C (r : ℤ)

theorem charpoly_eq (r k : ℕ) :
    (incidenceQ r k).charpoly = polynomial r k := by
  rw [incidenceQ_eq, Matrix.charpoly, Matrix.det_fin_three]
  simp [polynomial, map_ofNat]
  ring

theorem polynomial_natDegree (r k : ℕ) : (polynomial r k).natDegree = 3 := by
  unfold polynomial
  compute_degree!

theorem integerPolynomial_monic (r k : ℕ) : (integerPolynomial r k).Monic := by
  unfold integerPolynomial
  monicity!

theorem polynomial_eq_map (r k : ℕ) :
    polynomial r k = (integerPolynomial r k).map (Int.castRingHom ℚ) := by
  simp [polynomial, integerPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_ofNat]

theorem polynomial_monic (r k : ℕ) : (polynomial r k).Monic := by
  rw [polynomial_eq_map]
  exact (integerPolynomial_monic r k).map _

theorem aeval_polynomial {A : Type*} [CommRing A] [Algebra ℚ A]
    (r k : ℕ) (z : A) :
    aeval z (polynomial r k) = z^3-(k : A)*z^2-2*z-r := by
  simp [polynomial, map_ofNat]

theorem aeval_integerPolynomial {A : Type*} [CommRing A] [Algebra ℤ A]
    (r k : ℕ) (z : A) :
    aeval z (integerPolynomial r k) = z^3-(k : A)*z^2-2*z-r := by
  simp [integerPolynomial, map_ofNat]

theorem a_identity {r k : ℕ} {β : ℝ} (h : Family r k β) :
    (β-k)*β = 2+r/β := by
  nlinarith only [h.toRunFamily.quadratic_eq]

theorem cubic_factor {r k : ℕ} {β : ℝ} (h : Family r k β) (x : ℝ) :
    (x-β)*(x^2+(β-k)*x+r/β) = x^3-(k : ℝ)*x^2-2*x-r := by
  have ha := a_identity h
  have hb : β*((r : ℝ)/β) = r := mul_div_cancel₀ _ h.toRunFamily.beta_pos.ne'
  have hax := congrArg (fun v : ℝ => v*x) ha
  nlinarith only [hb, hax]

/-- The remaining quadratic has negative discriminant, uniformly in the
two adjacent bands. Its coefficients come from the exact family bounds. -/
theorem quadratic_factor_pos {r k : ℕ} {β : ℝ} (h : Family r k β) (x : ℝ) :
    0 < x^2+(β-k)*x+r/β := by
  have hw := family_window h
  have ha : 0 < β-k := sub_pos.mpr h.lower
  have hs := mul_pos ha (sub_pos.mpr hw.a_small)
  nlinarith only [hs, hw.a_small, hw.b_large, sq_nonneg (x+(β-k)/2)]

/-- The root in (k,k+1) is the only real root of the actual cubic. -/
theorem real_root_unique {r k : ℕ} {β : ℝ} (h : Family r k β) {x : ℝ}
    (hroot : x^3-(k : ℝ)*x^2-2*x-r = 0) : x = β := by
  have hfactor : (x-β)*(x^2+(β-k)*x+r/β) = 0 := by
    rw [cubic_factor h, hroot]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_right (quadratic_factor_pos h x).ne')

theorem family_root_unique {r k : ℕ} {β γ : ℝ}
    (hβ : Family r k β) (hγ : Family r k γ) : γ = β :=
  real_root_unique hβ (by linarith [hγ.cubic])

theorem root_not_integer {r k : ℕ} {β : ℝ} (h : Family r k β) (z : ℤ) :
    (z : ℝ) ≠ β := by
  intro hz
  have hlo : (k : ℤ) < z := by exact_mod_cast (hz ▸ h.lower)
  have hhi : z < (k : ℤ)+1 := by exact_mod_cast (hz ▸ h.upper)
  omega

theorem no_integer_root {r k : ℕ} {β : ℝ} (h : Family r k β) (z : ℤ) :
    (z : ℝ)^3-(k : ℝ)*(z : ℝ)^2-2*(z : ℝ)-r ≠ 0 := by
  intro hz
  exact root_not_integer h z (real_root_unique h hz)

/-- A rational root of the monic integer cubic would be integral, while
the unique real root is strictly between the consecutive integers k,k+1. -/
theorem no_rational_root (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) (x : ℚ) :
    ¬ (polynomial r k).IsRoot x := by
  intro hx
  obtain ⟨β, hβ⟩ := BHDiagonalParameters.near_diagonal_root_exists r k hr hklo hkhi
  have hx' : aeval x (integerPolynomial r k) = 0 := by
    have h0 : eval x (polynomial r k) = 0 := hx
    rw [aeval_integerPolynomial]
    simpa [polynomial] using h0
  obtain ⟨n, rfl, _⟩ := exists_integer_of_is_root_of_monic
    (integerPolynomial_monic r k) hx'
  have hn : (n : ℝ)^3-(k : ℝ)*(n : ℝ)^2-2*(n : ℝ)-r = 0 := by
    rw [aeval_integerPolynomial, algebraMap_int_eq, eq_intCast] at hx'
    exact_mod_cast hx'
  exact no_integer_root hβ n hn

theorem polynomial_irreducible (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) : Irreducible (polynomial r k) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]; decide
  · exact no_rational_root r k hr hklo hkhi

/-- Irreducibility is attached to the original incidence characteristic polynomial. -/
theorem irreducible (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) : Irreducible (incidenceQ r k).charpoly := by
  rw [charpoly_eq]
  exact polynomial_irreducible r k hr hklo hkhi

theorem complex_cubic_factor {r k : ℕ} {β : ℝ} (h : Family r k β) (z : ℂ) :
    (z-(β : ℂ))*(z^2+((β-k : ℝ) : ℂ)*z+(((r : ℝ)/β : ℝ) : ℂ)) =
      z^3-(k : ℂ)*z^2-2*z-r := by
  have ha : ((β-k : ℝ) : ℂ)*(β : ℂ) = 2+(((r : ℝ)/β : ℝ) : ℂ) := by
    exact_mod_cast a_identity h
  have hb : (β : ℂ)*(((r : ℝ)/β : ℝ) : ℂ) = (r : ℂ) := by
    exact_mod_cast (mul_div_cancel₀ (r : ℝ) h.toRunFamily.beta_pos.ne')
  push_cast at ha hb ⊢
  linear_combination -z*ha-hb

/-- Every other complex root is nonreal and has squared norm r/beta<1. -/
theorem other_root {r k : ℕ} {β : ℝ} (h : Family r k β) {z : ℂ}
    (hz : z^3-(k : ℂ)*z^2-2*z-r = 0) (hzb : z ≠ (β : ℂ)) :
    ‖z‖^2 = (r : ℝ)/β ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  let a : ℝ := β-k
  let b : ℝ := r/β
  have hw := family_window h
  have ha : 0 < a := sub_pos.mpr h.lower
  have ha' : a < 1/4 := hw.a_small
  have hb : 4/5 < b := hw.b_large
  have hb' : b < 1 := hw.b_lt_one
  have hdisc : a^2 < 4*b := by
    nlinarith only [mul_pos ha (sub_pos.mpr ha'), hb]
  have hquad : z^2+(a : ℂ)*z+(b : ℂ) = 0 := by
    have hf : (z-(β : ℂ))*(z^2+(a : ℂ)*z+(b : ℂ)) = 0 := by
      rw [complex_cubic_factor h, hz]
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hzb)
  have hre := congrArg Complex.re hquad
  have him := congrArg Complex.im hquad
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
  set x := z.re
  set y := z.im
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2*x+a)]
  have hx : 2*x+a = 0 := by
    have hp : y*(2*x+a) = 0 := by linarith
    exact (mul_eq_zero.mp hp).resolve_left hy
  have hn : ‖z‖^2 = b := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ)*hre+x*hx
  refine ⟨hn, hy, ?_⟩
  nlinarith [norm_nonneg z]

/-- The expanding real root is constructed from the natural parameter
bounds; all other roots of this same actual incidence contract. -/
theorem pisot (r k : ℕ) (hr : 12 ≤ r) (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r k).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1 := by
  obtain ⟨β, hβ⟩ := BHDiagonalParameters.near_diagonal_root_exists r k hr hklo hkhi
  refine ⟨β, hβ, ?_, ?_, ?_⟩
  · linarith [beta_gt_thirteen hβ]
  · rw [charpoly_eq, aeval_polynomial]
    exact_mod_cast (show β^3-(k : ℝ)*β^2-2*β-r = 0 by linarith [hβ.cubic])
  · intro z hz hzb
    rw [charpoly_eq, aeval_polynomial] at hz
    exact (other_root hβ hz hzb).2.2

theorem root_not_rational {r k : ℕ} {β : ℝ} (h : Family r k β) (q : ℚ) :
    (q : ℝ) ≠ β := by
  intro hq
  apply no_rational_root r k h.large h.above h.below q
  change eval q (polynomial r k) = 0
  simp only [polynomial, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  have hb : β^3-(k : ℝ)*β^2-2*β-r = 0 := by linarith [h.cubic]
  rw [← hq] at hb
  exact_mod_cast hb

/-- A positive left eigenvector of the original incidence: beta times the
literal length vector, with no division in its displayed coordinates. -/
theorem positive_left_eigenvector {r k : ℕ} {β : ℝ} (h : Family r k β) :
    ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
      w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w := by
  refine ⟨![β,β^2,β+r], ?_, ?_⟩
  · intro a
    fin_cases a <;> simp <;>
      nlinarith [h.toRunFamily.beta_pos, show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  · rw [incidence_eq]
    ext c
    fin_cases c <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      nlinarith [h.cubic]

/-- Constructor for primitive irreducible Pisot arithmetic on the actual
two-band substitution. Only the three natural parameter bounds are inputs. -/
theorem primitive_irreducible_pisot (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c) ∧
    Irreducible (incidenceQ r k).charpoly ∧
    ∃ β : ℝ, Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r k).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
        w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w := by
  obtain ⟨β, hβ, hβ1, hroot, hother⟩ := pisot r k hr hklo hkhi
  exact ⟨primitive r k (by omega), irreducible r k hr hklo hkhi,
    β, hβ, hβ1, hroot, hother, positive_left_eigenvector hβ⟩

end Psc.BHNearDiagonalPisot
