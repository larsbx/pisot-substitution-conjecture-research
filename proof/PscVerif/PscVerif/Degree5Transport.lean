/- The signed quotient and the actual degree-five defect image. -/
import PscVerif.Defect5Lie
import PscVerif.SectorBridge
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

namespace Psc.Degree5Transport

open Psc.Defect5 Psc.Defect5Lie Psc.Lie5 Psc.SignedCocycle Psc.Incidence
open scoped BigOperators

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- The actual defect columns, extended linearly from the representatives. -/
noncomputable def columns : (P.Rep → ℚ) →ₗ[ℚ] Vec5 :=
  Fintype.linearCombination ℚ fun j => k5Vec j.1.1 j.1.2

noncomputable def signed : (P.Rep → ℚ) →ₗ[ℚ] (P.Rep → ℚ) :=
  Matrix.toLin' (P.Ssign.map (Int.cast : ℤ → ℚ))

def tensorMatrix (M : Matrix (Fin 3) (Fin 3) ℚ) : Matrix Word5 Word5 ℚ :=
  fun ⟨a,b,c,d,e⟩ ⟨x,y,z,r,t⟩ => M a x * M b y * M c z * M d r * M e t

noncomputable def tensor (M : Matrix (Fin 3) (Fin 3) ℚ) : Vec5 →ₗ[ℚ] Vec5 :=
  Matrix.toLin' (tensorMatrix M)

theorem tensor_apply (M : Matrix (Fin 3) (Fin 3) ℚ) (v : Vec5) :
    tensor M v = phi5 M v := by
  funext w
  rcases w with ⟨a,b,c,d,e⟩
  simp only [tensor, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    tensorMatrix, phi5]

abbrev incidence (S : ChildSystem (Fin 3)) : Matrix (Fin 3) (Fin 3) ℚ :=
  (inc S.s).map (Nat.cast : ℕ → ℚ)

theorem intertwine (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    columns P ∘ₗ signed P = tensor (incidence S) ∘ₗ columns P := by
  apply Psc.SectorBridge.linearCombination_intertwine
  intro j
  simpa only [tensor_apply, Matrix.map_apply] using phi5_k5Vec_rep P hbal j

theorem kernel_invariant (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    LinearMap.ker (columns P) ≤ (LinearMap.ker (columns P)).comap (signed P) := by
  intro v hv
  change columns P v = 0 at hv
  change columns P (signed P v) = 0
  rw [show columns P (signed P v) = tensor (incidence S) (columns P v) from
    LinearMap.congr_fun (intertwine P hbal) v, hv, map_zero]

theorem range_invariant (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    ∀ v ∈ LinearMap.range (columns P), tensor (incidence S) v ∈ LinearMap.range (columns P) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨signed P u, LinearMap.congr_fun (intertwine P hbal) u⟩

/-- The first isomorphism transports the quotient action to the actual defect image. -/
theorem quotient_intertwines_range (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (x : (P.Rep → ℚ) ⧸ LinearMap.ker (columns P)) :
    (columns P).quotKerEquivRange
      ((LinearMap.ker (columns P)).mapQ _ (signed P) (kernel_invariant P hbal) x) =
      (tensor (incidence S)).restrict (range_invariant P hbal) ((columns P).quotKerEquivRange x) := by
  obtain ⟨u, rfl⟩ := (LinearMap.ker (columns P)).mkQ_surjective x
  apply Subtype.ext
  change columns P (signed P u) = tensor (incidence S) (columns P u)
  exact LinearMap.congr_fun (intertwine P hbal) u

open Polynomial Psc.SectorBridge

/-- The rational characteristic polynomial of the actual defect image. -/
noncomputable def q5 (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) : ℚ[X] :=
  imCharpoly (intertwine P hbal)

theorem q5_dvd_signed (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    q5 P hbal ∣ (P.Ssign.map (Int.cast : ℤ → ℚ)).charpoly :=
  imCharpoly_dvd_left (intertwine P hbal)

theorem q5_dvd_tensor (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    q5 P hbal ∣ (tensor (incidence S)).charpoly :=
  imCharpoly_dvd_right (intertwine P hbal)

theorem exists_root_q5 (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    (hK : ∃ j : P.Rep, k5Vec j.1.1 j.1.2 ≠ 0) :
    ∃ z : ℂ, aeval z (q5 P hbal) = 0 := by
  obtain ⟨j, hj⟩ := hK
  exact exists_root_imCharpoly (intertwine P hbal)
    (range_linearCombination_ne_bot (j := j) hj) ℂ

/-- A known weight root in the image has its exponent placements in the
signed spectrum, via the rational image polynomial and the cubic orbit lemma. -/
theorem weight_orbit_signed (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2)
    {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (a b c : ℕ)
    (hweight : aeval (β ^ a * α ^ b * γ ^ c) (q5 P hbal) = 0) :
    let q := (P.Ssign.map (Int.cast : ℤ → ℚ)).charpoly
    (∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧ aeval (β ^ b * x ^ a * y ^ c) q = 0) ∧
    (∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧ aeval (β ^ c * x ^ a * y ^ b) q = 0) := by
  exact Psc.GaloisOrbit.orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ _ a b c
    (aeval_eq_zero_of_dvd_aeval_eq_zero (q5_dvd_signed P hbal) hweight)

end Psc.Degree5Transport
