/- Transport a root of the actual degree-five quotient to its Lie eigenvector. -/
import PscVerif.Degree5Transport
import PscVerif.Degree5Weights

namespace Psc.Degree5RootLift

open Psc.Binomial Psc.SignedCocycle Psc.Defect5 Psc.Lie5 Psc.LieWeights
open Psc.Degree5Transport Psc.Degree5Weights Matrix Polynomial
open scoped BigOperators Kronecker

theorem power5_map {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 3) (Fin 3) ℚ) :
    (tensorMatrix M).map (algebraMap ℚ K) = power5 (M.map (algebraMap ℚ K)) := by
  ext ⟨a,b,c,d,e⟩ ⟨x,y,z,r,t⟩
  simp only [tensorMatrix, power5, Matrix.map_apply, kroneckerMap_apply, map_mul]
  ring

/-- The lift is a linear combination of scalar extensions of vectors in the
actual rational image. Its nonvanishing follows from a rational left inverse,
whose matrix remains a left inverse after scalar extension. -/
theorem exists_image_eigenvector {K : Type*} [Field K] [CharZero K]
    {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) {z : K}
    (hz : aeval z (q5 P hbal) = 0) :
    ∃ f : Word5 → K, f ≠ 0 ∧
      f ∈ Submodule.span K (Set.range fun u : LinearMap.range (columns P) =>
        fun w => algebraMap ℚ K (u.val w)) ∧
      power5 ((incidence S).map (algebraMap ℚ K)) *ᵥ f = z • f ∧
      (∃ c : Fin 48 → K, f = ∑ j, c j • (fun w => (coeff (bracket5 j) w : K))) := by
  classical
  let W := LinearMap.range (columns P)
  let b := Module.finBasis ℚ W
  let e := Pi.basisFun ℚ Word5
  let A := LinearMap.toMatrix b b (Psc.SectorBridge.imRestrict (intertwine P hbal))
  let B := LinearMap.toMatrix b e W.subtype
  let T := LinearMap.toMatrix e e (tensor (incidence S))
  have hT : T = tensorMatrix (incidence S) := by
    ext w v
    simp only [T, e, LinearMap.toMatrix_apply, tensor, Matrix.toLin'_apply, Pi.basisFun_repr,
      Pi.basisFun_apply, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply]
  have hTB : T * B = B * A := by
    dsimp only [T, B, A]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]; rfl
  obtain ⟨R, hR⟩ := LinearMap.exists_leftInverse_of_injective W.subtype
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  let C := LinearMap.toMatrix e b R
  have hCB : C * B = 1 := by
    dsimp only [C, B]
    rw [← LinearMap.toMatrix_comp, hR, LinearMap.toMatrix_id]
  let ρ := algebraMap ℚ K
  have hroot : (A.map ρ).charpoly.eval z = 0 := by
    rw [Matrix.charpoly_map, eval_map_algebraMap]
    rw [show A.charpoly = q5 P hbal from LinearMap.charpoly_toMatrix _ b]
    exact hz
  obtain ⟨v, hv, he⟩ :=
    Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot (A.map ρ) z hroot
  let f := B.map ρ *ᵥ v
  have hf0 : f ≠ 0 := by
    intro hf
    have h := congrArg (fun w => C.map ρ *ᵥ w) hf
    apply hv
    simpa only [f, mulVec_mulVec, ← Matrix.map_mul, hCB, Matrix.map_one, map_zero, map_one, one_mulVec,
      mulVec_zero] using h
  have hfE : power5 ((incidence S).map ρ) *ᵥ f = z • f := by
    dsimp only [f]
    rw [← power5_map, ← hT, mulVec_mulVec, ← Matrix.map_mul, hTB, Matrix.map_mul,
      ← mulVec_mulVec, he, mulVec_smul]
  have hf : f = ∑ i, v i • (fun w => ρ ((b i).val w)) := by
    funext w
    simp [f, B, e, Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, mul_comm]
  refine ⟨f, hf0, ?_, hfE, ?_⟩
  · rw [hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, rfl⟩)
  · have h (i : Fin (Module.finrank ℚ W)) := cast_bracket_combination (K := K)
      (range_le_lie P hbal (b i).property)
    choose c hc using h
    refine ⟨fun j => ∑ i, v i * c i j, ?_⟩
    rw [hf]
    simp_rw [show ∀ i, (fun w => ρ ((b i).val w)) =
      ∑ j, c i j • (fun w => (coeff (bracket5 j) w : K)) from hc,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]

/-- Every root of the actual degree-five image polynomial has a mixed
degree-five weight once three distinct incidence roots are supplied. -/
theorem root_q5_is_mixed {K : Type*} [Field K] [CharZero K]
    {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) (x : Fin 3 → K)
    (hx : Function.Injective x) (hroots : ∀ i, aeval (x i) (incidence S).charpoly = 0)
    {z : K} (hz : aeval z (q5 P hbal) = 0) :
    ∃ κ, Mixed κ ∧ z = mono x κ := by
  obtain ⟨f, hf, -, he, hLie⟩ := exists_image_eigenvector P hbal hz
  obtain ⟨Q, hQ, hMQ⟩ := Psc.SectorBridge.exists_conj_diagonal (incidence S) x hx hroots
  apply mixed_of_lie_eigen _ Q⁻¹ Q x _ _ hf hLie he
  · rw [hMQ, ← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hQ, one_mul]
  · exact Matrix.mul_nonsing_inv _ hQ

/-- A nonzero actual column under irreducible incidence supplies a common
root of the image and signed characteristic polynomials with mixed weight. -/
theorem exists_signed_mixed_weight {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hM : Irreducible (incidence S).charpoly)
    (hne : ∃ j : P.Rep, Psc.Defect5Lie.k5Vec j.1.1 j.1.2 ≠ 0) :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧
      (∀ i, aeval (x i) (incidence S).charpoly = 0) ∧
      ∃ z : ℂ, aeval z (q5 P hbal) = 0 ∧
        aeval z (P.Ssign.map (Int.cast : ℤ → ℚ)).charpoly = 0 ∧
        ∃ κ, Mixed κ ∧ z = mono x κ := by
  obtain ⟨x, hx, hroots, -⟩ := Psc.SectorBridge.exists_distinct_roots (L := ℂ) (incidence S) hM
  obtain ⟨z, hz⟩ := exists_root_q5 P hbal hne
  exact ⟨x, hx, hroots, z, hz, aeval_eq_zero_of_dvd_aeval_eq_zero (q5_dvd_signed P hbal) hz,
    root_q5_is_mixed P hbal x hx hroots hz⟩

end Psc.Degree5RootLift
