/-
# The σₖ family hull as a flow with a homeomorphic inflation

Instantiates `PeriodicPartnerLocalAction` on the literal family hull: inflation of
`LocalHull (geometry k hk)` is a homeomorphism for every `k ≥ 1`, from the proved bijectivity
`ParameterFamilyRecognizability.inflateH_bijective`, compactness and Hausdorffness.

Source decision: `docs/c4-hull-flow-homeomorphism-stop-go-2026-11-22.md`.
-/
import PscVerif.PeriodicPartnerLocalAction
import PscVerif.C4ParameterFamilyRecognizability

namespace Psc.ParameterFamilyFlow

open Psc.ParameterFamilyTiling (geometry)
open Psc.PeriodicPartnerLocalTopology

/-- Inflation of the σₖ ordinary hull, as a homeomorphism. -/
noncomputable def inflateHomeomorph (k : ℕ) (hk : 1 ≤ k) :
    LocalHull (geometry k hk) ≃ₜ LocalHull (geometry k hk) :=
  Psc.PeriodicPartnerLocalTopology.inflateHomeomorph _
    (Psc.ParameterFamilyRecognizability.inflateH_bijective k hk)

/-- Inflation of the σₖ ordinary hull is a homeomorphism for every `k ≥ 1`. -/
theorem inflate_isHomeomorph (k : ℕ) (hk : 1 ≤ k) : IsHomeomorph (inflate (geometry k hk)) :=
  (inflateHomeomorph k hk).isHomeomorph

end Psc.ParameterFamilyFlow
