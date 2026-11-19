/-
# Exact right rays imply metric translation-asymptoticity

The direction used in periodic-partner extraction is proved from local geometric inputs:
translation transports a right ray from `y` to `y - t`; a ray starting at or before `-R`
contains a centred agreement window of radius `R`; and the metric is uniformly controlled
by such windows.  For a fixed window the sufficient translation threshold is `t ≥ y + R`.

The Barge--Diamond--Swanson metric periodicization theorem remains an explicit input.
This module converts that input to the exact-ray predicate used by the endpoint theorems;
it does not prove BDS, construct a tiling hull, or establish the local window law for one.
No expansion, compactness, or continuity assumption is needed for the metric conversion.

See `docs/c4-periodic-partner-formalization-stop-go-2026-11-19.md` for the extended
pre-code source decision.
-/
import PscVerif.PeriodicPartnerDynamics
import PscVerif.PeriodicPartnerCollapse

namespace Psc.PeriodicPartnerAsymptotic

open Function Filter Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerCollapse
open scoped Topology

/-- Metric right asymptoticity for the convention `translate t S = S - t`.
The translation parameter tends to positive infinity, with no discrete reindexing. -/
def TranslationRightAsymptotic {X : Type*} [MetricSpace X]
    (translate : ℝ → X → X) (S U : X) : Prop :=
  Tendsto (fun t : ℝ => dist (translate t S) (translate t U)) atTop (𝓝 0)

section Conversion

variable {X : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
    {translate : ℝ → X → X} {AgreeRight : X → X → ℝ → Prop}

/-- Exact agreement on one right ray implies metric asymptoticity of the translated pair.
Only the metric-modulus field of `D` is used; the ray transport hypothesis stands alone
and does not require the endpoint or inflation laws. -/
theorem translationRightAsymptotic_of_rightAsymptotic
    (D : AgreementData X f β)
    (htranslate : ∀ {S U y} (t : ℝ), AgreeRight S U y →
      AgreeRight (translate t S) (translate t U) (y - t))
    (hwindow : ∀ {R r : ℝ} {S U : X}, 0 < R → r ≤ -R →
      AgreeRight S U r → D.Agree R S U)
    {S U : X} (h : RightAsymptotic AgreeRight S U) :
    TranslationRightAsymptotic translate S U := by
  obtain ⟨y, hagree⟩ := h
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hR, hclose⟩ := D.controls_dist ε hε
  refine ⟨y + R, fun t ht => ?_⟩
  have hstart : y - t ≤ -R := by
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using sub_le_sub_left ht y
  have hpatch := hwindow hR hstart (htranslate t hagree)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
    hclose (translate t S) (translate t U) hpatch

/-- A named BDS input stated with metric translation-asymptoticity supplies the
exact-ray BDS input required by the existing extraction theorems.  BDS itself is
neither proved nor inserted as an axiom. -/
theorem bdsPeriodicization_of_translationRightAsymptotic
    (D : AgreementData X f β)
    (htranslate : ∀ {S U y} (t : ℝ), AgreeRight S U y →
      AgreeRight (translate t S) (translate t U) (y - t))
    (hwindow : ∀ {R r : ℝ} {S U : X}, 0 < R → r ≤ -R →
      AgreeRight S U r → D.Agree R S U)
    (hBDS : BDSPeriodicization f translate (TranslationRightAsymptotic translate)) :
    BDSPeriodicization f translate (RightAsymptotic AgreeRight) := by
  intro S U hne hright
  exact hBDS hne
    (translationRightAsymptotic_of_rightAsymptotic D htranslate hwindow hright)

end Conversion

section BranchConsumers

variable {X α : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
    {translate : ℝ → X → X} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}

/-- Convenience wrapper using the translation law from the existing branch contract. -/
theorem translationRightAsymptotic_of_branch_laws
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (D : AgreementData X f β)
    (hwindow : ∀ {R r : ℝ} {S U : X}, 0 < R → r ≤ -R →
      AgreeRight S U r → D.Agree R S U)
    {S U : X} (h : RightAsymptotic AgreeRight S U) :
    TranslationRightAsymptotic translate S U :=
  translationRightAsymptotic_of_rightAsymptotic D laws.agree_translate hwindow h

end BranchConsumers

section TernaryConsumers

variable {X Y : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
    {translate : ℝ → X → X} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}

/-- The two-step endpoint criterion with BDS stated in its metric asymptotic form.
The exact-ray-to-metric correspondence is discharged by the local window input. -/
theorem ternary_two_step_iff_pairPeriodic_of_metric_BDS
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (D : AgreementData X f β)
    (hwindow : ∀ {R r : ℝ} {S U : X}, 0 < R → r ≤ -R →
      AgreeRight S U r → D.Agree R S U)
    (hBDS : BDSPeriodicization f translate (TranslationRightAsymptotic translate))
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ PairPeriodic f S U :=
  ternary_two_step_iff_pairPeriodic laws hβ
    (bdsPeriodicization_of_translationRightAsymptotic D laws.agree_translate hwindow hBDS)
    hbranch

/-- The identity-fibre endpoint criterion after deriving the exact-ray BDS input.
The realization map, finite fixed fibre, and origin/fibre theorem remain explicit. -/
theorem ternary_two_step_iff_zero_fibre_of_metric_BDS
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    (D : AgreementData X f β)
    (hwindow : ∀ {R r : ℝ} {S U : X}, 0 < R → r ≤ -R →
      AgreeRight S U r → D.Agree R S U)
    (hBDS : BDSPeriodicization f translate (TranslationRightAsymptotic translate))
    (A : Y → Y) (h : X → Y) (q₀ : Y)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : {x | h x = q₀}.Finite) (hfixed : A q₀ = q₀)
    (hR4 : R4ZeroFibre f h q₀ EndsAt)
    {S U : X} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt S U 0 b c) :
    g^[2] b ≠ g^[2] c ↔ h S = q₀ ∧ h U = q₀ :=
  ternary_two_step_iff_zero_fibre laws hβ
    (bdsPeriodicization_of_translationRightAsymptotic D laws.agree_translate hwindow hBDS)
    A h q₀ hf hsem hfinite hfixed hR4 hbranch

end TernaryConsumers

end Psc.PeriodicPartnerAsymptotic
