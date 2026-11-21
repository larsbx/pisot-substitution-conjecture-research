/-
# Continuity of the concrete geometric realization

The existing stable-coordinate series has a uniform geometric majorant over
the whole exact hull.  Local constancy of origin data, together with exact
desubstitution continuity, makes each term continuous.  Uniform summation
then proves continuity of the actual real lift on the exact hull, its torus
projection and the full solenoid history.  The ordinary-hull conclusion uses
the proved equivariance and target flow from `PeriodicPartnerLocalRealization`.

The intermediate lemmas state the role of inverse continuity explicitly.
The final concrete theorems discharge it through the finite-parent compactness
argument; recognizability itself remains the original bijectivity premise.
Source decision: `docs/c4-realization-continuity-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerOriginContinuity
import PscVerif.PeriodicPartnerLocalRealization
import PscVerif.PeriodicPartnerDesubContinuity
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace Psc.PeriodicPartnerRealizationContinuity

open Function Filter Set Matrix Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerOriginContinuity
open Psc.PeriodicPartnerLocalRealization
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- The same geometric majorant controls every tiling, including when `ρ = 0`. -/
theorem realization_term_norm_le (k : ℕ) (T : S.Hull) :
    ‖(mat S ^ k) *ᵥ P.proj (cs hR T k)‖ ≤ P.C * P.offsetBound * P.ρ ^ k := by
  calc
    ‖(mat S ^ k) *ᵥ P.proj (cs hR T k)‖ ≤ P.C * P.ρ ^ k * ‖P.proj (cs hR T k)‖ :=
      P.norm_pow_proj_le _ k
    _ ≤ P.C * P.ρ ^ k * P.offsetBound :=
      mul_le_mul_of_nonneg_left (cs_bound P hR T k)
        (mul_nonneg P.C_nonneg (pow_nonneg P.ρ_nonneg k))
    _ = P.C * P.offsetBound * P.ρ ^ k := by ring

omit [Nonempty α] in
theorem summable_realization_majorant :
    Summable (fun k : ℕ => P.C * P.offsetBound * P.ρ ^ k) :=
  (summable_geometric_of_lt_one P.ρ_nonneg P.ρ_lt_one).mul_left _

/-- The stable series converges uniformly on the entire exact hull; no
compactness or continuity of desubstitution is used in this tail estimate. -/
theorem tendstoUniformly_realization_series :
    TendstoUniformly
      (fun n : ℕ => fun T : S.Hull =>
        ∑ k ∈ Finset.range n, (mat S ^ k) *ᵥ P.proj (cs hR T k))
      (fun T : S.Hull => ∑' k, (mat S ^ k) *ᵥ P.proj (cs hR T k)) atTop :=
  tendstoUniformly_tsum_nat (summable_realization_majorant P)
    (realization_term_norm_le P hR)

omit [Fintype α] [DecidableEq α] in
theorem continuous_level_of_continuous_desub
    (hdesub : Continuous (desub hR)) (n : ℕ) : Continuous (level hR n) :=
  hdesub.iterate n

theorem isLocallyConstant_xs_of_continuous_desub
    (hdesub : Continuous (desub hR)) (n : ℕ) :
    IsLocallyConstant (fun T : S.Hull => xs hR T n) := by
  simpa only [xs, Function.comp_def] using
    ((isLocallyConstant_origin (S := S)).comp Prod.snd).comp_continuous
      (continuous_level_of_continuous_desub hR hdesub n)

theorem isLocallyConstant_cs_of_continuous_desub
    (hdesub : Continuous (desub hR)) (n : ℕ) :
    IsLocallyConstant (fun T : S.Hull => cs hR T n) := by
  simpa only [cs, Function.comp_def] using
    (isLocallyConstant_offset (S := S)).comp_continuous
      (continuous_level_of_continuous_desub hR hdesub (n + 1))

/-- The actual vector lift is continuous for exact agreement.  This theorem
does not claim that the vector lift is continuous on the ordinary hull. -/
theorem continuous_realVec_of_continuous_desub
    (hdesub : Continuous (desub hR)) : Continuous (realVec P hR) := by
  have hterm (k : ℕ) :
      Continuous (fun T : S.Hull => (mat S ^ k) *ᵥ P.proj (cs hR T k)) :=
    ((isLocallyConstant_cs_of_continuous_desub hR hdesub k).comp
      (fun v : α → ℝ => (mat S ^ k) *ᵥ P.proj v)).continuous
  have hsum := continuous_tsum hterm (summable_realization_majorant P)
    (realization_term_norm_le P hR)
  have hx : Continuous (fun T : S.Hull => xs hR T 0) :=
    (isLocallyConstant_xs_of_continuous_desub hR hdesub 0).continuous
  exact ((hx.smul continuous_const).neg).sub hsum

theorem continuous_torusRealize_of_continuous_desub
    (hdesub : Continuous (desub hR)) : Continuous (torusRealize P hR) :=
  QuotientAddGroup.continuous_mk.comp
    (continuous_realVec_of_continuous_desub P hR hdesub)

/-- Continuity of every compatible coordinate gives continuity of the existing
solenoid-valued map, not merely its depth-zero projection. -/
theorem continuous_realize_of_continuous_desub
    (hdesub : Continuous (desub hR)) : Continuous (realize P hR) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun n =>
    (continuous_torusRealize_of_continuous_desub P hR hdesub).comp
      (continuous_level_of_continuous_desub hR hdesub n)

theorem continuous_realizeLocal_of_continuous_desub (hβ : 1 < S.β)
    (hdesub : Continuous (desub hR)) : Continuous (realizeLocal P hR) :=
  (continuous_realizeLocal_iff P hR hβ).mpr
    (continuous_realize_of_continuous_desub P hR hdesub)

/-! ## Concrete theorems with inverse continuity discharged -/

/-- Every desubstitution depth is continuous, using compact anchored fibres
to derive continuity of the existing inverse of bijective inflation. -/
theorem continuous_level (n : ℕ) : Continuous (level hR n) :=
  continuous_level_of_continuous_desub hR
    (Psc.PeriodicPartnerDesubContinuity.continuous_desub hR) n

/-- Continuity of the existing vector lift on the exact hull, with no added
inverse-continuity or local-recognition hypothesis. -/
theorem continuous_realVec : Continuous (realVec P hR) :=
  continuous_realVec_of_continuous_desub P hR
    (Psc.PeriodicPartnerDesubContinuity.continuous_desub hR)

theorem continuous_torusRealize : Continuous (torusRealize P hR) :=
  continuous_torusRealize_of_continuous_desub P hR
    (Psc.PeriodicPartnerDesubContinuity.continuous_desub hR)

/-- The actual compatible-history realization is continuous on the exact hull. -/
theorem continuous_realize : Continuous (realize P hR) :=
  continuous_realize_of_continuous_desub P hR
    (Psc.PeriodicPartnerDesubContinuity.continuous_desub hR)

/-- The actual geometric realization is continuous for the ordinary local hull
topology.  Its only nonstructural inputs are the existing Pisot data, bijective
inflation and strict expansion used by the proved flow equivariance. -/
theorem continuous_realizeLocal (hβ : 1 < S.β) : Continuous (realizeLocal P hR) :=
  (continuous_realizeLocal_iff P hR hβ).mpr (continuous_realize P hR)

end Psc.PeriodicPartnerRealizationContinuity
