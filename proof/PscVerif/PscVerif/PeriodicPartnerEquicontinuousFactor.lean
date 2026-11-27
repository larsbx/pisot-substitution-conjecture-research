import PscVerif.PeriodicPartnerRotationFactor
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# Equicontinuous actions have diagonal proximality

The ordinary `Equicontinuous` family of time maps suffices. Applying an
inverse-time map near a diagonal orbit-limit point puts the original pair
in every entourage. The compact quotient-descent theorem therefore applies
to arbitrary Hausdorff uniform equicontinuous targets, without presenting
them first as group rotations.

Source decision: `docs/c4-rotation-factor-rank-stop-go-2026-11-21.md`,
follow-up on the abstract equicontinuous universal property.
-/

namespace Psc.PeriodicPartnerEquicontinuousFactor

open Function Filter Set Topology
open Psc.PeriodicPartnerOrdinaryProximal Psc.PeriodicPartnerRotationFactor
open scoped Uniformity Topology

section EquicontinuousActions

variable {Z : Type*} [UniformSpace Z] [T2Space Z]

/-- Ordinary equicontinuity and the real-action inverse laws imply that
common-orbit-closure proximality is diagonal. Uniform equicontinuity is
not assumed. -/
theorem eq_of_topologicallyProximal_of_equicontinuous (act : ℝ → Z → Z)
    (hzero : ∀ z, act 0 z = z)
    (hadd : ∀ s t z, act s (act t z) = act (s + t) z)
    (hequi : Equicontinuous act) {x y : Z}
    (h : TopologicallyProximal act x y) : x = y := by
  obtain ⟨z, hz⟩ := h
  apply eq_of_uniformity
  intro U hU
  obtain ⟨V, hV, hVV⟩ := equicontinuousAt_iff_pair.mp (hequi z) U hU
  obtain ⟨_, hp, t, rfl⟩ := mem_closure_iff_nhds.mp hz (V ×ˢ V) (prod_mem_nhds hV hV)
  have hxy := hVV (act t x) hp.1 (act t y) hp.2 (-t)
  simpa only [hadd, neg_add_cancel, hzero] using hxy

end EquicontinuousActions

section Descent

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [T2Space Y] [UniformSpace Z] [T2Space Z]

/-- Every continuous equivariant map to an equicontinuous Hausdorff uniform
action descends uniquely through a compact-to-Hausdorff factor with proximal
fibres. No group-rotation representation of the target is required. -/
theorem existsUnique_equicontinuous_descent
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (actZ : ℝ → Z → Z)
    (g : X → Y) (hg : Continuous g) (honto : Surjective g)
    (hg_equiv : ∀ t x, g (act t x) = actY t (g x))
    (hprox : ∀ x y, g x = g y → TopologicallyProximal act x y)
    (hzero : ∀ z, actZ 0 z = z)
    (hadd : ∀ s t z, actZ s (actZ t z) = actZ (s + t) z)
    (hequi : Equicontinuous actZ)
    (f : X → Z) (hf : Continuous f)
    (hf_equiv : ∀ t x, f (act t x) = actZ t (f x)) :
    ∃! d : Y → Z, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = actZ t (d y) :=
  existsUnique_continuous_equivariant_descent act actY actZ g hg honto hg_equiv hprox
    (fun _ _ h => eq_of_topologicallyProximal_of_equicontinuous actZ hzero hadd hequi h)
    f hf hf_equiv

end Descent

section UniformRotations

/-- Common right translations preserve the relative element defining the
right group uniformity, uniformly over every translating element. -/
@[to_additive uniformEquicontinuous_add_right_rotations]
theorem uniformEquicontinuous_right_rotations {ι G : Type*}
    [UniformSpace G] [Group G] [IsRightUniformGroup G] (ρ : ι → G) :
    UniformEquicontinuous (fun i z => z * ρ i) := by
  intro U hU
  rw [uniformity_eq_comap_nhds_one] at hU
  obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
  have hpre : {p : G × G | p.2 / p.1 ∈ V} ∈ 𝓤 G := by
    rw [uniformity_eq_comap_nhds_one]
    exact preimage_mem_comap hV
  filter_upwards [hpre] with p hp i
  apply hVU
  change (p.2 * ρ i) / (p.1 * ρ i) ∈ V
  simpa only [mul_div_mul_right_eq_div] using hp

end UniformRotations

end Psc.PeriodicPartnerEquicontinuousFactor
