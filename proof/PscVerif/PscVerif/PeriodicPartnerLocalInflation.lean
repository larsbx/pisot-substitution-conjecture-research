/-
# Inflation as a homeomorphism of the ordinary legal hull

The inverse already defined from bijective inflation is now continuous in
the exact presentation by the finite-parent compactness argument. Its
translation identity descends that continuity through the ordinary-hull
open quotient. The resulting homeomorphism uses the original bijectivity
hypothesis only; no continuous inverse or globally compact hull is assumed.

Source decision: `docs/c4-realization-continuity-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerDesubContinuity
import PscVerif.PeriodicPartnerLocalTopology

namespace Psc.PeriodicPartnerLocalInflation

open Function Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerLocalTopology
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α}
variable (hR : Bijective (inflateH (S := S)))

/-- The existing exact inverse, on the same carrier with the ordinary topology. -/
noncomputable def desubLocal (T : LocalHull S) : LocalHull S :=
  ofExact S (desub hR T.toHull)

/-- Desubstitution scales the translation coordinate of every quotient chart. -/
theorem desubLocal_chart (p : ℝ × S.Hull) :
    desubLocal hR (chart S p) = chart S (p.1 / S.β, desub hR p.2) := by
  apply LocalHull.ext
  exact desub_translate hR p.1 p.2

/-- Ordinary-hull inverse continuity follows from proved exact continuity. -/
theorem continuous_desubLocal : Continuous (desubLocal hR) := by
  apply (isOpenQuotientMap_chart S).isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun p : ℝ × S.Hull => (p.1 / S.β, desub hR p.2)) :=
    (continuous_fst.div_const S.β).prodMk
      ((Psc.PeriodicPartnerDesubContinuity.continuous_desub hR).comp continuous_snd)
  simpa only [Function.comp_def, desubLocal_chart] using (continuous_chart S).comp h

/-- The ordinary inverse retains the same translation covariance. -/
theorem desubLocal_translate (t : ℝ) (T : LocalHull S) :
    desubLocal hR (Psc.PeriodicPartnerLocalTopology.translate S t T) =
      Psc.PeriodicPartnerLocalTopology.translate S (t / S.β) (desubLocal hR T) := by
  apply LocalHull.ext
  exact desub_translate hR t T.toHull

@[simp] theorem inflate_desubLocal (T : LocalHull S) :
    Psc.PeriodicPartnerLocalTopology.inflate S (desubLocal hR T) = T := by
  apply LocalHull.ext
  exact inflateH_desub hR T.toHull

@[simp] theorem desubLocal_inflate (T : LocalHull S) :
    desubLocal hR (Psc.PeriodicPartnerLocalTopology.inflate S T) = T := by
  apply LocalHull.ext
  exact desub_inflateH hR T.toHull

/-- Literal inflation is a homeomorphism under the existing recognizability
input. Bijectivity itself is not proved by this construction. -/
noncomputable def inflateHomeomorph : LocalHull S ≃ₜ LocalHull S where
  toFun := Psc.PeriodicPartnerLocalTopology.inflate S
  invFun := desubLocal hR
  left_inv := desubLocal_inflate hR
  right_inv := inflate_desubLocal hR
  continuous_toFun := Psc.PeriodicPartnerLocalTopology.continuous_inflate S
  continuous_invFun := continuous_desubLocal hR

end Psc.PeriodicPartnerLocalInflation
