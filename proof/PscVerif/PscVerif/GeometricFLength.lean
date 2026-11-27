/-
# Length data from a positive left eigenvector

This module exposes the length-functional binding without importing the strict-system
or spectral applications. The declarations are extracted unchanged from
`GeometricFStrict`; that module continues to import and re-export them.
-/
import PscVerif.GeometricFInclusion

namespace Psc.GeometricF

open Matrix Psc.Binomial Psc.Incidence Psc.BPrimeBinding

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The additive functional `v ↦ ℓ·v` on integer vectors. -/
def lenHom (ℓ : α → ℝ) : (α → ℤ) →+ ℝ where
  toFun v := ∑ a, ℓ a * (v a : ℝ)
  map_zero' := by simp
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]

omit [DecidableEq α] in
theorem lenHom_apply (ℓ : α → ℝ) (v : α → ℤ) : lenHom ℓ v = ∑ a, ℓ a * (v a : ℝ) := rfl

theorem lenHom_single (ℓ : α → ℝ) (a : α) : lenHom ℓ (pvec [a]) = ℓ a := by
  rw [lenHom_apply, Finset.sum_eq_single a]
  · simp [pvec]
  · intro b _ hb
    simp [pvec, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem lengthData_of_left_eigen {s : α → List α} {ℓ : α → ℝ} {β : ℝ} (hβ : 0 < β)
    (hℓ : ∀ a, 0 < ℓ a) (h : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    LengthData s (lenHom ℓ) β where
  beta_pos := hβ
  pos a := by rw [lenHom_single]; exact hℓ a
  eigen v := by
    have hc : ∀ c, ∑ a, ℓ a * ((inc s a c : ℕ) : ℝ) = β * ℓ c := fun c => by
      have := congrFun h c
      simpa [Matrix.vecMul, dotProduct] using this
    simp only [lenHom_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ← hc c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => by ring

end Psc.GeometricF
