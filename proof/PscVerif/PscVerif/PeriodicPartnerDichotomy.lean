/-
# The exact branch-origin dichotomy

This module binds the same ray and endpoint predicates in the periodicity and collapse
theorems.  Its only additional local input is that a common ray plus a shared labelled
origin tile supplies a common metric patch of that tile's positive length.

For a branch-normalized ternary pair, endpoint merging after two steps is equivalent to
metric collapse under unshifted inflation.  Endpoint separation is equivalent to the
absence of collapse and, under the named realization inputs, to the zero fibre.

For a same-fibre partner triple the successful case gives a common positive period in
the distinguished fibre.  In the merging case all three points lie outside that fibre
at this branch origin.  This does not exclude another translating periodicization from
landing in the zero fibre; the origin is fixed throughout these statements.

No theorem selects a witness satisfying the successful case from NM_V, and no theorem
asserts a rank-two contradiction or a concrete tiling-space realization.
-/
import PscVerif.PeriodicPartnerDynamics
import PscVerif.PeriodicPartnerCollapse

namespace Psc.PeriodicPartnerDichotomy

open Function Filter Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerCollapse
open scoped Topology

section Adapter

variable {X α : Type*} [MetricSpace X]
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}

/-- Bind the endpoint-collapse interface to exactly the predicates used by the branch
criterion.  The `common_patch` argument is primitive local geometry, not convergence. -/
def endpointDataOfBranch
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (D : AgreementData X f β) (tileLength : α → ℝ)
    (hpos : ∀ a, 0 < tileLength a)
    (hpatch : ∀ {x y a}, AgreeRight x y 0 → EndsAt x 0 a → EndsAt y 0 a →
      D.Agree (tileLength a) x y) : RightEndpointData D α g where
  CommonRightRay x y := AgreeRight x y 0
  EndsAtZero x a := EndsAt x 0 a
  tileLength := tileLength
  tileLength_pos := hpos
  ray_inflate h := by simpa only [mul_zero] using laws.agree_inflate h
  endpoint_inflate h := by simpa only [mul_zero] using laws.endpoint_inflate h
  common_patch := hpatch

end Adapter

section Ternary

variable {X Y : Type*} [MetricSpace X]
    {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}

/-- The branch-origin metric collapse criterion is itself an exact two-step test.
The forward implication needs only local common-patch geometry; the converse uses
the separately supplied BDS periodicization input through the periodicity criterion. -/
theorem ternary_endpoint_merge_iff_collapse
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (D : AgreementData X f β) (tileLength : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < tileLength a)
    (hpatch : ∀ {x y a}, AgreeRight x y 0 → EndsAt x 0 a → EndsAt y 0 a →
      D.Agree (tileLength a) x y)
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b = g^[2] c ↔
      Tendsto (fun n : ℕ => dist (f^[n] S) (f^[n] U)) atTop (𝓝 0) := by
  constructor
  · intro hmerge
    let E := endpointDataOfBranch laws D tileLength hpos hpatch
    exact E.distance_tendsto_zero_of_endpoint_merge
      hβ hbranch.1 hbranch.2.1 hbranch.2.2.1 2 hmerge
  · intro hcollapse
    by_contra hseparate
    have hperiod := (ternary_two_step_iff_pairPeriodic laws hβ hBDS hbranch).mp hseparate
    exact laws.branch_ne hbranch
      (eq_of_periodic_of_distance_tendsto_zero hperiod.mem_left hperiod.mem_right hcollapse)

/-- Persistent ternary branch endpoints exactly exclude metric collapse. -/
theorem ternary_endpoint_separation_iff_not_collapse
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (D : AgreementData X f β) (tileLength : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < tileLength a)
    (hpatch : ∀ {x y a}, AgreeRight x y 0 → EndsAt x 0 a → EndsAt y 0 a →
      D.Agree (tileLength a) x y)
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔
      ¬ Tendsto (fun n : ℕ => dist (f^[n] S) (f^[n] U)) atTop (𝓝 0) :=
  not_congr (ternary_endpoint_merge_iff_collapse laws hβ hBDS D tileLength hpos hpatch hbranch)

/-- Under the explicit geometric-realization inputs, absence of branch-origin collapse
is equivalent to membership of the two leaves in the distinguished fibre. -/
theorem ternary_zero_fibre_iff_not_collapse
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (D : AgreementData X f β) (tileLength : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < tileLength a)
    (hpatch : ∀ {x y a}, AgreeRight x y 0 → EndsAt x 0 a → EndsAt y 0 a →
      D.Agree (tileLength a) x y)
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    (h S = q₀ ∧ h U = q₀) ↔
      ¬ Tendsto (fun n : ℕ => dist (f^[n] S) (f^[n] U)) atTop (𝓝 0) :=
  (ternary_two_step_iff_zero_fibre laws hβ hBDS A h q₀ hf hsem hfinite hfixed hR4 hbranch).symm.trans
    (ternary_endpoint_separation_iff_not_collapse laws hβ hBDS D tileLength hpos hpatch hbranch)

/-- Complete conditional classification of a branch-normalized same-fibre triple.
The two cases use the same points and origin.  No witness selection is assumed or proved.
The common partner need not have an endpoint at the origin. -/
theorem ternary_branch_triple_dichotomy
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (D : AgreementData X f β) (tileLength : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < tileLength a)
    (hpatch : ∀ {x y a}, AgreeRight x y 0 → EndsAt x 0 a → EndsAt y 0 a →
      D.Agree (tileLength a) x y)
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {T S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hTS : h T = h S) (hTU : h T = h U) :
    (g^[2] b ≠ g^[2] c ∧ h T = q₀ ∧ h S = q₀ ∧ h U = q₀ ∧
      ∃ n > 0, f^[n] T = T ∧ f^[n] S = S ∧ f^[n] U = U) ∨
    (g^[2] b = g^[2] c ∧ h T ≠ q₀ ∧ h S ≠ q₀ ∧ h U ≠ q₀ ∧
      ¬ PairPeriodic f S U ∧
      Tendsto (fun n : ℕ => dist (f^[n] S) (f^[n] U)) atTop (𝓝 0)) := by
  by_cases hmerge : g^[2] b = g^[2] c
  · have hS : h S ≠ q₀ := by
      intro hSz
      have hUz : h U = q₀ := hTU.symm.trans (hTS.trans hSz)
      exact ((ternary_two_step_iff_zero_fibre laws hβ hBDS A h q₀ hf hsem
        hfinite hfixed hR4 hbranch).mpr ⟨hSz, hUz⟩) hmerge
    have hT : h T ≠ q₀ := fun hTz => hS (hTS.symm.trans hTz)
    have hU : h U ≠ q₀ := fun hUz => hT (hTU.trans hUz)
    have hnotperiod : ¬ PairPeriodic f S U := fun hp =>
      ((ternary_two_step_iff_pairPeriodic laws hβ hBDS hbranch).mpr hp) hmerge
    exact Or.inr ⟨hmerge, hT, hS, hU, hnotperiod,
      (ternary_endpoint_merge_iff_collapse laws hβ hBDS D tileLength hpos hpatch hbranch).mp hmerge⟩
  · exact Or.inl ⟨hmerge, ternary_zero_fibre_periodic_triple laws hβ hBDS A h q₀
      hf hsem hfinite hfixed hR4 hbranch hmerge hTS⟩

end Ternary

end Psc.PeriodicPartnerDichotomy
