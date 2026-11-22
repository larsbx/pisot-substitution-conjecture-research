import PscVerif.C4FamilyFiniteZeroFibre
import PscVerif.C4ParameterFamilyEquicontinuousFactor

/-!
# Ordinary proximality and maximality from finite automaton witnesses

The finite signed tile automaton supplies exact common-shift witnesses
for every zero-fibre pair. These discharge the anchor hypotheses of the
already verified ordinary-hull transport and factor-descent interfaces.
The compactness and local-topology arguments in those interfaces are
reused unchanged; this module adds no limit construction.

Every concrete solenoid fibre is ordinarily proximal, the fibre relation
is exactly ordinary proximality, and its finite nonproximal rank is one.
Every continuous equivariant map to a Hausdorff uniform equicontinuous
action descends uniquely through the actual solenoid. These statements
do not assert singleton fibres almost everywhere or an invariant-measure
spectral conclusion.

Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.C4FamilyFiniteProximal

open Function Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyZeroFibreWitnesses Psc.C4FamilyFiniteZeroFibre
open Psc.PeriodicPartnerLocalTopology (LocalHull)
open Psc.PeriodicPartnerOrdinaryProximal (TopologicallyProximal)

variable (k : ℕ) (hk : 1 ≤ k)

/-- Ordinary proximality holds throughout every concrete solenoid fibre.
The finite automaton discharges the universal witness premise of the
existing compact-transport wrapper. -/
theorem same_fibre_topologicallyProximal (hk₂ : 2 ≤ k)
    {T U : LocalHull (geometry k hk)}
    (hTU : solenoidRealize k hk T = solenoidRealize k hk U) :
    TopologicallyProximal
      (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U :=
  Psc.ParameterFamilyOrdinaryProximal.same_fibre_proximal_of_zero_fibre_witnesses
    k hk hk₂
    (fun _ _ hT hU => zero_fibre_windowWitnesses k hk hk₂ hT hU (by norm_num)) hTU

/-- Ordinary proximality is exactly the concrete solenoid fibre relation. -/
theorem same_fibre_iff_topologicallyProximal (hk₂ : 2 ≤ k)
    (T U : LocalHull (geometry k hk)) :
    solenoidRealize k hk T = solenoidRealize k hk U ↔
      TopologicallyProximal
        (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U :=
  ⟨same_fibre_topologicallyProximal k hk hk₂,
    Psc.ParameterFamilyRotationFactor.solenoidRealize_eq_of_topologicallyProximal k hk⟩

/-- The ordinary proximal relation is closed in the product of ordinary
local hulls, because it is the equality relation of a continuous factor. -/
theorem isClosed_topologicallyProximal (hk₂ : 2 ≤ k) :
    IsClosed {p : LocalHull (geometry k hk) × LocalHull (geometry k hk) |
      TopologicallyProximal
        (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) p.1 p.2} := by
  let : T2Space (Psc.PeriodicPartnerRealization.Solenoid (geometry k hk)) :=
    Psc.PeriodicPartnerRealization.solenoid_t2Space _
  have hset : {p : LocalHull (geometry k hk) × LocalHull (geometry k hk) |
      TopologicallyProximal
        (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) p.1 p.2} =
      {p | solenoidRealize k hk p.1 = solenoidRealize k hk p.2} := by
    ext p
    exact (same_fibre_iff_topologicallyProximal k hk hk₂ p.1 p.2).symm
  rw [hset]
  exact isClosed_eq ((continuous_solenoidRealize k hk).comp continuous_fst)
    ((continuous_solenoidRealize k hk).comp continuous_snd)

/-- Every concrete factor fibre has nonproximal rank exactly one. The
definition is the supremum of cardinalities of finite pairwise nonproximal
subsets, not the number of points in the fibre. -/
theorem concreteFibreRank_eq_one (hk₂ : 2 ≤ k)
    (z : Psc.PeriodicPartnerRealization.Solenoid (geometry k hk)) :
    Psc.ParameterFamilyRotationFactor.concreteFibreRank k hk z = 1 :=
  Psc.PeriodicPartnerRotationFactor.fibreNonproximalRank_eq_one_of_surjective
    (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
    (solenoidRealize k hk) (solenoidRealize_surjective k hk)
    (fun _ _ h => same_fibre_topologicallyProximal k hk hk₂ h) z

/-- Every continuous map intertwining the hull flow with a Hausdorff
topological-group rotation factors uniquely, continuously and equivariantly
through the concrete solenoid. The finite common-tile theorem supplies the
anchor premise. -/
theorem rotation_factor_descent (hk₂ : 2 ≤ k)
    {G : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [T2Space G]
    (ρ : ℝ → G) (f : LocalHull (geometry k hk) → G) (hf : Continuous f)
    (hf_equiv : ∀ t T,
      f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) = ρ t + f T) :
    ∃! d : Psc.PeriodicPartnerRealization.Solenoid (geometry k hk) → G,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (Psc.PeriodicPartnerRealization.flow (pisotData k hk) t z) = ρ t + d z := by
  obtain ⟨V, _, hV⟩ := fixed_tiling_over_zero k hk
  exact Psc.ParameterFamilyRotationFactor.rotation_descent_of_zero_anchor_common_tile
    k hk hV (fun W hW => zero_fibre_common_tile k hk hk₂ hV hW) ρ f hf hf_equiv

/-- The defining maximal-equicontinuous-factor universal property for the
actual solenoid map. Its own flow is equicontinuous by the inherited
uniformity theorem, and every equicontinuous Hausdorff uniform target
factors through it uniquely. No published factor identification is assumed. -/
theorem equicontinuous_factor_descent (hk₂ : 2 ≤ k)
    {Z : Type*} [UniformSpace Z] [T2Space Z]
    (act : ℝ → Z → Z) (hzero : ∀ z, act 0 z = z)
    (hadd : ∀ s t z, act s (act t z) = act (s + t) z)
    (hequi : Equicontinuous act)
    (f : LocalHull (geometry k hk) → Z) (hf : Continuous f)
    (hf_equiv : ∀ t T,
      f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) = act t (f T)) :
    ∃! d : Psc.PeriodicPartnerRealization.Solenoid (geometry k hk) → Z,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (Psc.PeriodicPartnerRealization.flow (pisotData k hk) t z) = act t (d z) := by
  obtain ⟨V, _, hV⟩ := fixed_tiling_over_zero k hk
  exact Psc.ParameterFamilyEquicontinuousFactor.equicontinuous_factor_descent_of_zero_anchor_common_tile
    k hk hV (fun W hW => zero_fibre_common_tile k hk hk₂ hV hW)
    act hzero hadd hequi f hf hf_equiv

end Psc.C4FamilyFiniteProximal
