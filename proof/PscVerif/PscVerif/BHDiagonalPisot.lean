import PscVerif.BHDiagonalParameters
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Primitive irreducible Pisot arithmetic for the diagonal literal family

For every `r ≥ 12`, the actual words `(1, 0 1^r 2, 0^r 1)` have a positive
incidence square and irreducible rational characteristic polynomial
`X^3-r*X^2-2*X-r`. The expanding real root is constructed, and every other
complex root has squared norm exactly `r/beta < 1`.

The standard rational-root and quadratic-factor argument specializes the
method of `C4ParameterFamilyPisot` to the actual diagonal incidence. Its
source decision is `docs/bh-diagonal-arithmetic-stop-go-2026-11-27.md`.
There is no spectral conclusion or unimodular assumption here.
-/

namespace Psc.BHDiagonalPisot

open Matrix Polynomial
open Psc.Incidence (inc)
open Psc.BHNearDiagonalLiteral (sigma)
open Psc.BHDiagonalLiteral

/-- The original image-letter counts, with source letters indexing columns. -/
theorem incidence_eq (r : ℕ) :
    inc (sigma r r) = !![0,1,r; 1,r,1; 0,1,0] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Psc.Incidence.inc_apply,sigma,List.count_replicate]

/-- The square is computed on the actual incidence, not an independently
specified matrix with the same characteristic polynomial. -/
theorem incidence_sq (r : ℕ) :
    inc (sigma r r)^2 = !![1,2*r,1; r,r^2+2,2*r; 1,r,1] := by
  rw [incidence_eq,pow_two]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem primitive (r : ℕ) (hr : 12 ≤ r) :
    ∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r r)^n) a c := by
  refine ⟨2,by omega,?_⟩
  rw [incidence_sq]
  intro a c
  fin_cases a <;> fin_cases c <;> simp <;> omega

/-- Rational cast of the original incidence matrix. -/
noncomputable def incidenceQ (r : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (inc (sigma r r)).map (Nat.cast : ℕ → ℚ)

theorem incidenceQ_eq (r : ℕ) :
    incidenceQ r = !![0,1,(r : ℚ); 1,r,1; 0,1,0] := by
  rw [incidenceQ,incidence_eq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp

/-- The determinant is the parameter, so this family is nonunit. -/
theorem determinant (r : ℕ) : (incidenceQ r).det = r := by
  rw [incidenceQ_eq,Matrix.det_fin_three]
  simp

noncomputable def polynomial (r : ℕ) : ℚ[X] :=
  X^3-C (r : ℚ)*X^2-C 2*X-C (r : ℚ)

noncomputable def integerPolynomial (r : ℕ) : ℤ[X] :=
  X^3-C (r : ℤ)*X^2-C 2*X-C (r : ℤ)

theorem charpoly_eq (r : ℕ) : (incidenceQ r).charpoly = polynomial r := by
  rw [incidenceQ_eq,Matrix.charpoly,Matrix.det_fin_three]
  simp [polynomial,map_ofNat]
  ring

theorem polynomial_natDegree (r : ℕ) : (polynomial r).natDegree = 3 := by
  unfold polynomial
  compute_degree!

theorem integerPolynomial_monic (r : ℕ) : (integerPolynomial r).Monic := by
  unfold integerPolynomial
  monicity!

theorem polynomial_eq_map (r : ℕ) :
    polynomial r = (integerPolynomial r).map (Int.castRingHom ℚ) := by
  simp [polynomial,integerPolynomial,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,map_ofNat]

theorem polynomial_monic (r : ℕ) : (polynomial r).Monic := by
  rw [polynomial_eq_map]
  exact (integerPolynomial_monic r).map _

theorem aeval_polynomial {A : Type*} [CommRing A] [Algebra ℚ A]
    (r : ℕ) (z : A) :
    aeval z (polynomial r) = z^3-(r : A)*z^2-2*z-r := by
  simp [polynomial,map_ofNat]

theorem aeval_integerPolynomial {A : Type*} [CommRing A] [Algebra ℤ A]
    (r : ℕ) (z : A) :
    aeval z (integerPolynomial r) = z^3-(r : A)*z^2-2*z-r := by
  simp [integerPolynomial,map_ofNat]

/-- A rational root of this monic integer cubic would be integral. The
constructed real root lies strictly between consecutive integers and is
its only real root, so no candidate integer can occur. -/
theorem no_rational_root (r : ℕ) (hr : 12 ≤ r) (x : ℚ) :
    ¬ (polynomial r).IsRoot x := by
  intro hx
  obtain ⟨β,hβ⟩ := BHDiagonalParameters.family_root_exists r hr
  have hx' : aeval x (integerPolynomial r) = 0 := by
    have h0 : eval x (polynomial r) = 0 := hx
    rw [aeval_integerPolynomial]
    simpa [polynomial] using h0
  obtain ⟨n,rfl,_⟩ := exists_integer_of_is_root_of_monic
    (integerPolynomial_monic r) hx'
  have hn : (n : ℝ)^3-(r : ℝ)*(n : ℝ)^2-2*(n : ℝ)-r = 0 := by
    rw [aeval_integerPolynomial,algebraMap_int_eq,eq_intCast] at hx'
    exact_mod_cast hx'
  exact BHDiagonalParameters.no_integer_root hβ n hn

theorem polynomial_irreducible (r : ℕ) (hr : 12 ≤ r) :
    Irreducible (polynomial r) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]; decide
  · exact no_rational_root r hr

/-- Irreducibility belongs to the original incidence characteristic polynomial. -/
theorem irreducible (r : ℕ) (hr : 12 ≤ r) :
    Irreducible (incidenceQ r).charpoly := by
  rw [charpoly_eq]
  exact polynomial_irreducible r hr

/-- Exact factorization at the constructed real root, now over the complexes. -/
theorem complex_cubic_factor {r β} (h : Family r β) (z : ℂ) :
    (z-(β : ℂ))*(z^2+((β-r : ℝ) : ℂ)*z+(((r : ℝ)/β : ℝ) : ℂ)) =
      z^3-(r : ℂ)*z^2-2*z-r := by
  have ha : ((β-r : ℝ) : ℂ)*(β : ℂ) = 2+(((r : ℝ)/β : ℝ) : ℂ) := by
    exact_mod_cast a_identity h
  have hb : (β : ℂ)*(((r : ℝ)/β : ℝ) : ℂ) = (r : ℂ) := by
    exact_mod_cast (mul_div_cancel₀ (r : ℝ) (beta_pos h).ne')
  push_cast at ha hb ⊢
  linear_combination -z*ha-hb

/-- Every other complex root has squared modulus `r/beta < 1` and is nonreal.
The expanding root and all coefficient bounds are those of `Family`. -/
theorem other_root {r β} (h : Family r β) {z : ℂ}
    (hz : z^3-(r : ℂ)*z^2-2*z-r = 0) (hzb : z ≠ (β : ℂ)) :
    ‖z‖^2 = (r : ℝ)/β ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  let a : ℝ := β-r
  let b : ℝ := r/β
  have ha : 0 < a := a_pos h
  have ha' : a < 1/4 := a_small h
  have hb : 48/49 < b := b_large h
  have hb' : b < 1 := b_lt_one h
  have hdisc : a^2 < 4*b := by
    nlinarith only [mul_pos ha (sub_pos.mpr ha'),hb]
  have hquad : z^2+(a : ℂ)*z+(b : ℂ) = 0 := by
    have hf : (z-(β : ℂ))*(z^2+(a : ℂ)*z+(b : ℂ)) = 0 := by
      rw [complex_cubic_factor h,hz]
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hzb)
  have hre := congrArg Complex.re hquad
  have him := congrArg Complex.im hquad
  simp only [pow_two,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.zero_re,Complex.add_im,Complex.mul_im,Complex.zero_im] at hre him
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
    rw [Complex.sq_norm,Complex.normSq_apply]
    linear_combination (-1 : ℝ)*hre+x*hx
  refine ⟨hn,hy,?_⟩
  nlinarith [norm_nonneg z]

/-- The root is constructed for each integer parameter. Every other root of
that same actual incidence has modulus strictly below one. -/
theorem pisot (r : ℕ) (hr : 12 ≤ r) :
    ∃ β : ℝ, Family r β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (incidenceQ r).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1 := by
  obtain ⟨β,hβ⟩ := BHDiagonalParameters.family_root_exists r hr
  refine ⟨β,hβ,?_,?_,?_⟩
  · have hr' : (12 : ℝ) ≤ r := by exact_mod_cast hr
    linarith [hβ.lower]
  · rw [charpoly_eq,aeval_polynomial]
    exact_mod_cast (show β^3-(r : ℝ)*β^2-2*β-r = 0 by linarith [hβ.cubic])
  · intro z hz hzb
    rw [charpoly_eq,aeval_polynomial] at hz
    exact (other_root hβ hz hzb).2.2

/-- Irrationality of the actual expanding root follows from the same monic
integer arithmetic, without a further existence or independence premise. -/
theorem root_not_rational {r β} (h : Family r β) (q : ℚ) : (q : ℝ) ≠ β := by
  intro hq
  apply no_rational_root r h.large q
  change eval q (polynomial r) = 0
  simp only [polynomial,eval_sub,eval_pow,eval_X,eval_mul,eval_C]
  have hb : β^3-(r : ℝ)*β^2-2*β-r = 0 := by linarith [h.cubic]
  rw [← hq] at hb
  exact_mod_cast hb

/-- A positive left eigenvector with no divisions, tied to the original
incidence. It is beta times the literal length vector `(1,beta,1+r/beta)`. -/
theorem positive_left_eigenvector {r β} (h : Family r β) :
    ∃ w : Fin 3 → ℝ, (∀ a,0 < w a) ∧
      w ᵥ* (inc (sigma r r)).map (Nat.cast : ℕ → ℝ) = β • w := by
  refine ⟨![β,β^2,β+r],?_,?_⟩
  · intro a
    fin_cases a <;> simp <;> nlinarith [beta_pos h,show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  · rw [incidence_eq]
    ext c
    fin_cases c <;> simp [Matrix.vecMul,dotProduct,Fin.sum_univ_succ] <;>
      nlinarith [h.cubic]

/-- The primitive, irreducible, expanding-root and contracting-conjugate
claims are assembled on exactly the original incidence, for all `r>=12`. -/
theorem primitive_irreducible_pisot (r : ℕ) (hr : 12 ≤ r) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r r)^n) a c) ∧
    Irreducible (incidenceQ r).charpoly ∧
    ∃ β : ℝ, Family r β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (incidenceQ r).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → ℝ, (∀ a,0 < w a) ∧
        w ᵥ* (inc (sigma r r)).map (Nat.cast : ℕ → ℝ) = β • w := by
  obtain ⟨β,hβ,hβ1,hroot,hother⟩ := pisot r hr
  exact ⟨primitive r hr,irreducible r hr,β,hβ,hβ1,hroot,hother,positive_left_eigenvector hβ⟩

end Psc.BHDiagonalPisot
