import PscVerif.Degree5Completion

/-!
# The degree-five reciprocal cubic as a determinant-twisted exterior square

The source gate is `docs/c4-degree-five-exterior-literature-2026-11-11.md`.
Here `wedge2` is the repository's explicit three-by-three matrix of minors.
The coefficient identity is valid over every commutative ring, including
singular matrices. The rational image statements retain all hypotheses of
`Degree5Completion`; they do not construct a word realization or an
isomorphism from the degree-five image to copies of an exterior module.
-/

namespace Psc.Degree5Exterior

open Matrix Polynomial Psc.Cyclicity Psc.Binomial Psc.SignedCocycle
open Psc.ParikhRank Psc.Incidence Psc.Defect5 Psc.Degree5Transport
open Psc.Degree5Completion
open scoped BigOperators

/-- Every two-by-two minor is homogeneous of degree two. -/
theorem wedge2_smul {R : Type*} [CommRing R] (c : R)
    (M : Matrix (Fin 3) (Fin 3) R) :
    wedge2 (c • M) = c ^ 2 • wedge2 M := by
  ext i j
  simp only [wedge2, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The determinant twist gives exactly the degree-five reciprocal coefficients.
No nonzero determinant or field hypothesis is needed. -/
theorem charpoly_det_smul_wedge2 {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    (M.det • wedge2 M).charpoly =
      X ^ 3 - C (M.det * (wedge2 M).trace) * X ^ 2 +
        C (M.det ^ 3 * M.trace) * X - C (M.det ^ 5) := by
  rw [charpoly_fin_three, trace_smul, wedge2_smul, trace_smul,
    trace_wedge2_wedge2, det_smul, det_wedge2]
  simp only [Fintype.card_fin, smul_eq_mul, map_mul, map_pow]
  ring

/-- The accepted rational reciprocal cubic is the characteristic polynomial
of the determinant-twisted matrix of exterior-square minors. -/
theorem reciprocal_eq_charpoly_det_wedge (M : Matrix (Fin 3) (Fin 3) ℚ) :
    reciprocal M = (M.det • wedge2 M).charpoly :=
  (charpoly_det_smul_wedge2 M).symm

/-- Positive unit determinant removes the twist. -/
theorem reciprocal_eq_charpoly_wedge_of_det_one
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hd : M.det = 1) :
    reciprocal M = (wedge2 M).charpoly := by
  simpa only [hd, one_smul] using reciprocal_eq_charpoly_det_wedge M

/-- Negative unit determinant keeps a minus sign on the exterior action. -/
theorem reciprocal_eq_charpoly_neg_wedge_of_det_neg_one
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hd : M.det = -1) :
    reciprocal M = (-wedge2 M).charpoly := by
  simpa only [hd, neg_one_smul] using reciprocal_eq_charpoly_det_wedge M

/-- The polynomial identity still applies when the exterior square is nonzero
but the determinant twist vanishes. -/
theorem reciprocal_eq_X_pow_three_of_det_zero
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hd : M.det = 0) :
    reciprocal M = X ^ 3 := by
  simp [reciprocal, hd]

section Image

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)

-- These hypotheses do not occur in the image-polynomial conclusion itself.
-- Retain them explicitly in every wrapper's declaration.
include hM hprim hβ hβ1 hpisot

/-- The actual image polynomial is a power of the twisted exterior polynomial;
the zero image and exponent zero remain included. -/
theorem q5_eq_exterior_pow_rank :
    ∃ k : ℕ, q5 P hbal = ((incQ S).det • wedge2 (incQ S)).charpoly ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  simpa only [reciprocal_eq_charpoly_det_wedge] using
    q5_eq_pow_rank P hbal hM hprim hβ hβ1 hpisot

/-- A nonzero actual defect column supplies a positive exponent. -/
theorem q5_eq_exterior_pow_rank_of_nonzero
    (hne : ∃ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 ≠ 0) :
    ∃ k : ℕ, 0 < k ∧
      q5 P hbal = ((incQ S).det • wedge2 (incQ S)).charpoly ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  simpa only [reciprocal_eq_charpoly_det_wedge] using
    q5_eq_pow_rank_of_nonzero P hbal hM hprim hne hβ hβ1 hpisot

/-- The determinant-one specialization preserves the actual image rank. -/
theorem q5_eq_wedge_pow_rank_of_det_one (hd : (incQ S).det = 1) :
    ∃ k : ℕ, q5 P hbal = (wedge2 (incQ S)).charpoly ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  simpa only [hd, one_smul] using
    q5_eq_exterior_pow_rank P hbal hM hprim hβ hβ1 hpisot

/-- The determinant-minus-one specialization retains the sign. -/
theorem q5_eq_neg_wedge_pow_rank_of_det_neg_one (hd : (incQ S).det = -1) :
    ∃ k : ℕ, q5 P hbal = (-wedge2 (incQ S)).charpoly ^ k ∧
      Module.finrank ℚ (LinearMap.range (columns P)) = 3 * k := by
  simpa only [hd, neg_one_smul] using
    q5_eq_exterior_pow_rank P hbal hM hprim hβ hβ1 hpisot

end Image

section ImageLength

/-- Counting every occurrence in an image gives its incidence column sum. -/
theorem incidence_column_sum {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → List α) (a : α) : ∑ b, inc s b a = (s a).length := by
  rw [← List.sum_toFinset_count_eq_length]
  simp only [inc_apply]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  exact List.count_eq_zero.mpr (by simpa using hb)

/-- Every complex incidence root is bounded by any common image-length bound.
This uses actual column counts and needs no Pisot or primitivity hypothesis. -/
theorem incidence_root_norm_le_image_bound
    {α : Type*} [Fintype α] [DecidableEq α] (s : α → List α) (B : ℕ)
    (hlen : ∀ a, (s a).length ≤ B) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) :
    ‖β‖ ≤ (B : ℝ) := by
  let A : Matrix α α ℚ := (inc s).map (Nat.cast : ℕ → ℚ)
  have hroot : (A.map (algebraMap ℚ ℂ)).charpoly.eval β = 0 := by
    rw [Matrix.charpoly_map, eval_map_algebraMap]
    exact hβ
  obtain ⟨v, hv0, hv⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
    (A.map (algebraMap ℚ ℂ)) β hroot
  apply Psc.ParikhIntertwiner.spectral_bound_of_subinvariant
    ((inc s).map (Nat.cast : ℕ → ℝ)) (fun _ => 1) (fun _ => by norm_num)
    (B : ℝ) ?_ (A.map (algebraMap ℚ ℂ)) ?_ v hv0 β hv
  · intro a
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, one_mul, mul_one]
    rw [← Nat.cast_sum, incidence_column_sum]
    exact_mod_cast hlen a
  · intro i j
    simp [A]

/-- For images of length at most three, a nonunit determinant excludes the
degree-five image whenever every state satisfies degree-four balance.
This does not exclude degree-six defects or assert absence of strict systems. -/
theorem columns_eq_zero_of_nonunit_short_images
    {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incQ S).charpoly)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) {β : ℂ}
    (hβ : aeval β (incQ S).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1)
    (hd2 : 2 ≤ ‖(((incQ S).det : ℚ) : ℂ)‖)
    (hlen : ∀ a, (S.s a).length ≤ 3) : columns P = 0 := by
  apply columns_eq_zero_of_nonunit_small_perron P hbal hM hprim hβ hβ1 hpisot hd2
  have hle := incidence_root_norm_le_image_bound S.s 3 hlen hβ
  norm_num at hle
  linarith

end ImageLength

namespace Controls

def singular : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- A singular matrix can have a nonzero exterior square while the twisted
characteristic polynomial is still exactly `X³`. -/
theorem singular_control :
    singular.det = 0 ∧ wedge2 singular ≠ 0 ∧ reciprocal singular = X ^ 3 := by
  have hd : singular.det = 0 := by norm_num [singular, Matrix.det_fin_three]
  refine ⟨hd, ?_, reciprocal_eq_X_pow_three_of_det_zero singular hd⟩
  intro hz
  have := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => A 0 0) hz
  norm_num [wedge2, singular, pairFst, pairSnd] at this

/-- On `-I`, omitting the determinant sign changes the constant coefficient. -/
theorem negative_unit_sign_needed :
    reciprocal (-1 : Matrix (Fin 3) (Fin 3) ℚ) ≠
      (wedge2 (-1 : Matrix (Fin 3) (Fin 3) ℚ)).charpoly := by
  intro h
  have he := congrArg (fun p : ℚ[X] => p.eval 0) h
  norm_num [reciprocal, charpoly_wedge2, Matrix.det_fin_three] at he

/-- On `2I`, omitting the determinant scale changes the constant coefficient. -/
theorem nonunit_scale_needed :
    reciprocal ((2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ)) ≠
      (wedge2 ((2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ))).charpoly := by
  intro h
  have he := congrArg (fun p : ℚ[X] => p.eval 0) h
  norm_num [reciprocal, charpoly_wedge2, Matrix.det_smul] at he

end Controls

end Psc.Degree5Exterior
