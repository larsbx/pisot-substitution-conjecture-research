import PscVerif.C4FamilyMeasuredRealization

/-! The full-history characters generate the measured L² space of the
ordinary legal hull and give its joint translation eigenvectors. -/

namespace Psc.C4FamilyMeasuredSpectrum

open Function Filter MeasureTheory Set
open scoped InnerProductSpace Psc.PeriodicPartnerSolenoidHaar Psc.C4FamilyMeasuredRealization
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate translate_translate translate_zero)
open Psc.PeriodicPartnerSolenoidCharacters (Certificate character character_norm frequency)
open Psc.PeriodicPartnerSolenoidHaar (haar)
open Psc.C4FamilyHaarErgodicity (characterLp haar_inner_self span_characterLp_closure_eq_top)
open Psc.C4FamilySolenoidCharacters (eigenfunction eigenfunction_translate)
open Psc.C4FamilyMeasuredRealization

private theorem compL2_surjective_of_ae_leftInverse
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} {g : β → α} (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g ν μ)
    (h : (g ∘ f) =ᵐ[μ] id) :
    Surjective (Lp.compMeasurePreservingₗᵢ ℂ f hf : Lp ℂ 2 ν → Lp ℂ 2 μ) := by
  intro u
  let v := Lp.compMeasurePreserving g hg u
  refine ⟨v, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving v hf,
    hf.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u hg), h] with x hx hy hgf
  exact hx.trans (hy.trans (congrArg (fun a : α => u a) hgf))

variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)

local notation "X" => LocalHull (geometry k hk)
local notation "μₛ" => haar (geometry k hk)
local notation "νₕ" => hullMeasure k hk hk₂
local notation "π" => solenoidRealize k hk

/-- Pullback along the actual geometric realization is a complex linear isometry. -/
noncomputable def pullback : Lp ℂ 2 μₛ →ₗᵢ[ℂ] Lp ℂ 2 νₕ :=
  Lp.compMeasurePreservingₗᵢ ℂ π (measurePreserving_factor k hk hk₂)

/-- The measurable inverse realizes every L² class as an actual factor pullback. -/
theorem pullback_surjective : Surjective (pullback k hk hk₂) :=
  compL2_surjective_of_ae_leftInverse (measurePreserving_factor k hk hk₂)
    (measurePreserving_inverse k hk hk₂) (inverse_factor_ae k hk hk₂)

/-- The pullback is a unitary equivalence of the two complex L² spaces. -/
noncomputable def l2Equiv : Lp ℂ 2 μₛ ≃ₗᵢ[ℂ] Lp ℂ 2 νₕ :=
  LinearIsometryEquiv.ofSurjective (pullback k hk hk₂) (pullback_surjective k hk hk₂)

/-- Koopman composition for the actual ordinary-hull translation at time t. -/
noncomputable def translationKoopman (t : ℝ) : Lp ℂ 2 νₕ →ₗᵢ[ℂ] Lp ℂ 2 νₕ :=
  Lp.compMeasurePreservingₗᵢ ℂ (translate (geometry k hk) t)
    (measurePreserving_translate k hk hk₂ t)

theorem translationKoopman_surjective (t : ℝ) : Surjective (translationKoopman k hk hk₂ t) :=
  compL2_surjective_of_ae_leftInverse (measurePreserving_translate k hk hk₂ t)
    (measurePreserving_translate k hk hk₂ (-t)) <| Eventually.of_forall fun T => by
      change translate (geometry k hk) (-t) (translate (geometry k hk) t T) = T
      rw [translate_translate, neg_add_cancel, translate_zero]

/-- The existing continuous eigenfunction, represented in the specified hull L² space. -/
noncomputable def eigenfunctionLp (c : Certificate (Fin 3)) : Lp ℂ 2 νₕ :=
  pullback k hk hk₂ (characterLp k hk c)

theorem eigenfunctionLp_ae (c : Certificate (Fin 3)) :
    (eigenfunctionLp k hk hk₂ c : X → ℂ) =ᵐ[νₕ] eigenfunction k hk c := by
  have hπ := measurePreserving_factor k hk hk₂
  have hc := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μₛ (character (geometry k hk) c)
  exact (Lp.coeFn_compMeasurePreserving (characterLp k hk c) hπ).trans
    (hπ.quasiMeasurePreserving.ae hc)

theorem eigenfunctionLp_inner_self (c : Certificate (Fin 3)) :
    ⟪eigenfunctionLp k hk hk₂ c, eigenfunctionLp k hk hk₂ c⟫_ℂ = 1 :=
  ((pullback k hk hk₂).inner_map_map _ _).trans
    (haar_inner_self k hk (character_norm (geometry k hk) c))

theorem eigenfunctionLp_ne_zero (c : Certificate (Fin 3)) : eigenfunctionLp k hk hk₂ c ≠ 0 := by
  intro he
  have h := eigenfunctionLp_inner_self k hk hk₂ c
  rw [he, inner_zero_left] at h
  exact zero_ne_one h

/-- The translation phase uses the sign convention of Koopman composition. -/
noncomputable def translationPhase (t ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (t * ξ) : ℝ) : ℂ) * Complex.I)

theorem eigenfunctionLp_translate (c : Certificate (Fin 3)) (t : ℝ) :
    translationKoopman k hk hk₂ t (eigenfunctionLp k hk hk₂ c) =
      translationPhase t (frequency (geometry k hk) (pisotData k hk) c) •
        eigenfunctionLp k hk hk₂ c := by
  let phase := translationPhase t (frequency (geometry k hk) (pisotData k hk) c)
  let v := eigenfunctionLp k hk hk₂ c
  have hp := measurePreserving_translate k hk hk₂ t
  have he := eigenfunctionLp_ae k hk hk₂ c
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v hp, hp.quasiMeasurePreserving.ae he, he,
    Lp.coeFn_smul phase v] with T h₁ h₂ h₃ h₄
  calc
    _ = eigenfunction k hk c (translate (geometry k hk) t T) := h₁.trans h₂
    _ = phase * eigenfunction k hk c T := eigenfunction_translate k hk c t T
    _ = _ := by
      rw [h₄]
      change phase * eigenfunction k hk c T = phase * v T
      rw [h₃]

/-- The finite-certificate eigenfunctions span a dense subspace of actual hull L². -/
theorem span_eigenfunctionLp_closure_eq_top :
    (Submodule.span ℂ (range (eigenfunctionLp k hk hk₂))).topologicalClosure = ⊤ := by
  have hd : DenseRange (pullback k hk hk₂).toContinuousLinearMap :=
    (pullback_surjective k hk hk₂).denseRange
  have h := hd.topologicalClosure_map_submodule (span_characterLp_closure_eq_top k hk)
  rw [Submodule.map_span, ← range_comp] at h
  exact h

/-- A nonzero L² vector with one real frequency for all translations. -/
def IsTranslationEigenvector (v : Lp ℂ 2 νₕ) : Prop :=
  v ≠ 0 ∧ ∃ ξ : ℝ, ∀ t : ℝ,
    translationKoopman k hk hk₂ t v = translationPhase t ξ • v

/-- The measured translation action of the literal σₖ family has pure discrete spectrum. -/
theorem pureDiscrete_translation :
    (Submodule.span ℂ {v | IsTranslationEigenvector k hk hk₂ v}).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← span_eigenfunctionLp_closure_eq_top k hk hk₂]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨c, rfl⟩
  exact ⟨eigenfunctionLp_ne_zero k hk hk₂ c, frequency (geometry k hk) (pisotData k hk) c,
    eigenfunctionLp_translate k hk hk₂ c⟩

end Psc.C4FamilyMeasuredSpectrum
