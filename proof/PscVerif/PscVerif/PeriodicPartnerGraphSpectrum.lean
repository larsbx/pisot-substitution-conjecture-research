/- The edge and cycle spectra of a finite graph with a commuting vertex map. -/
import PscVerif.SectorBridge
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

namespace Psc.PeriodicPartnerGraphSpectrum

section Boundary

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V] {edge : Module.End K E} {vertex : Module.End K V}
  {boundary : E →ₗ[K] V}

/-- The image of the boundary is invariant under the vertex operator. -/
theorem boundary_range_invariant (commutes : boundary.comp edge = vertex.comp boundary) :
    ∀ x ∈ LinearMap.range boundary, vertex x ∈ LinearMap.range boundary := by
  rintro _ ⟨e, rfl⟩
  exact ⟨edge e, LinearMap.congr_fun commutes e⟩

variable [FiniteDimensional K E]

/-- The two factors are the boundary image and the cycle space, with their induced actions. -/
theorem edge_charpoly_factor (commutes : boundary.comp edge = vertex.comp boundary) :
    edge.charpoly = (vertex.restrict (boundary_range_invariant commutes)).charpoly *
      (edge.restrict (Psc.KernelCofactor.ker_invariant commutes)).charpoly := by
  have ontoCommutes : boundary.rangeRestrict.comp edge =
      (vertex.restrict (boundary_range_invariant commutes)).comp boundary.rangeRestrict :=
    LinearMap.ext fun e => Subtype.ext (LinearMap.congr_fun commutes e)
  have h := Psc.KernelCofactor.charpoly_eq_mul_restrict boundary.rangeRestrict
    boundary.surjective_rangeRestrict edge _ ontoCommutes
  have sameKernel : LinearMap.ker boundary.rangeRestrict = LinearMap.ker boundary :=
    LinearMap.ker_rangeRestrict boundary
  have sameRestriction {U W : Submodule K E} (hUW : U = W)
      (hU : ∀ x ∈ U, edge x ∈ U) (hW : ∀ x ∈ W, edge x ∈ W) :
      (edge.restrict hU).charpoly = (edge.restrict hW).charpoly := by
    subst W
    rfl
  rwa [sameRestriction sameKernel _ (Psc.KernelCofactor.ker_invariant commutes)] at h

/-- The boundary can add only roots present in the vertex operator, with multiplicity. -/
theorem edge_charpoly_dvd_vertex_mul_cycles [FiniteDimensional K V]
    (commutes : boundary.comp edge = vertex.comp boundary) :
    edge.charpoly ∣ vertex.charpoly *
      (edge.restrict (Psc.KernelCofactor.ker_invariant commutes)).charpoly := by
  rw [edge_charpoly_factor commutes]
  exact mul_dvd_mul_right (Psc.SectorBridge.charpoly_restrict_dvd vertex _
    (boundary_range_invariant commutes)) _

end Boundary

section FiniteVertices

variable {K α : Type*} [Field K] [Finite α]

/-- Linearizing a finite vertex function preserves its eventual repetition. -/
theorem vertex_power_repeat (f : α → α) :
    ∃ m n : ℕ, m < n ∧ (Finsupp.lmapDomain K K f : Module.End K (α →₀ K)) ^ m =
      (Finsupp.lmapDomain K K f) ^ n := by
  have iterateLinear (k : ℕ) :
      Finsupp.lmapDomain K K (f^[k]) = (Finsupp.lmapDomain K K f) ^ k := by
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih =>
        rw [Function.iterate_succ, Finsupp.lmapDomain_comp, ih, pow_succ, Module.End.mul_eq_comp]
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k])
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨a, b, hlt, by simpa only [iterateLinear] using congrArg (Finsupp.lmapDomain K K) h⟩
  · exact ⟨b, a, hlt, by simpa only [iterateLinear] using congrArg (Finsupp.lmapDomain K K) h.symm⟩

/-- Every root of a finite vertex operator is zero or a root of unity. -/
theorem vertex_charpoly_root (f : α → α) {z : K}
    (hz : (Finsupp.lmapDomain K K f).charpoly.IsRoot z) :
    z = 0 ∨ ∃ k : ℕ, 0 < k ∧ z ^ k = 1 := by
  by_cases hzero : z = 0
  · exact Or.inl hzero
  have eigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ z).mpr hz
  obtain ⟨x, hx⟩ := eigen.exists_hasEigenvector
  obtain ⟨m, n, hmn, hrepeats⟩ := vertex_power_repeat (K := K) f
  have hsmul : z ^ m • x = z ^ n • x := by rw [← hx.pow_apply m, ← hx.pow_apply n, hrepeats]
  have hpow : z ^ m = z ^ n := (smul_left_injective K hx.2) hsmul
  refine Or.inr ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero m hzero)
  rw [← pow_add, Nat.add_sub_of_le hmn.le, mul_one, hpow]

end FiniteVertices

end Psc.PeriodicPartnerGraphSpectrum
