import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Pure discrete spectrum of a measured real flow

The measured endpoint of the family roadmap, stated once and for an arbitrary
measure-preserving real flow.

* `MeasuredFlow μ`: a family `φ t` of `μ`-preserving maps indexed by real time.
* `koopman F t`: composition with `φ t` on `L²(μ; ℂ)`.
* `IsEigen F f`: `f ∘ φ t = e^{2πiωt} f` in `L²` for one real frequency `ω` and all `t`.
* `PureDiscrete F`: the complex span of the eigenfunctions is dense in `L²(μ; ℂ)`.

Three implications are proved, each with its hypotheses visible.

* `pureDiscrete_of_continuous_eigen`: on a compact Hausdorff space with a finite weakly regular
  measure, continuous pointwise eigenfunctions whose span is dense in `C(Y, ℂ)` give
  pure discreteness.
* `pureDiscrete_of_denseRange`: pure discreteness lifts along a measure-preserving,
  almost everywhere equivariant map whose pullback has dense range.
* `surjective_pullback_of_ae_inverse`: a measurable almost everywhere left inverse makes
  that pullback surjective.

No hull, solenoid, invariant measure or singleton-fibre statement is made here.

Source decision: `docs/c4-measured-pure-discrete-2026-11-22.md`.
-/

namespace Psc.MeasuredPureDiscrete

open MeasureTheory Function Filter
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- A real-time family of measure-preserving maps. No group law or continuity is assumed;
the statements below do not use them. -/
structure MeasuredFlow (μ : Measure X) where
  φ : ℝ → X → X
  mp : ∀ t, MeasurePreserving (φ t) μ μ

/-- The phase `e^{2πiωt}`. -/
noncomputable def phase (ω t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ω * t)

/-- The Koopman operator at time `t` on `L²(μ; ℂ)`. -/
noncomputable def koopman (F : MeasuredFlow μ) (t : ℝ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗ ℂ (F.φ t) (F.mp t)

theorem coeFn_koopman (F : MeasuredFlow μ) (t : ℝ) (f : Lp ℂ 2 μ) :
    koopman F t f =ᵐ[μ] f ∘ F.φ t :=
  Lp.coeFn_compMeasurePreserving f (F.mp t)

/-- An `L²` eigenfunction of the flow, with a real frequency. -/
def IsEigen (F : MeasuredFlow μ) (f : Lp ℂ 2 μ) : Prop :=
  ∃ ω : ℝ, ∀ t, koopman F t f = phase ω t • f

/-- The complex span of the eigenfunctions. -/
noncomputable def eigenSpan (F : MeasuredFlow μ) : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ {f | IsEigen F f}

/-- Pure discrete spectrum: the eigenfunctions span a dense subspace of `L²(μ; ℂ)`. -/
def PureDiscrete (F : MeasuredFlow μ) : Prop :=
  Dense (eigenSpan F : Set (Lp ℂ 2 μ))

theorem pureDiscrete_iff_closure (F : MeasuredFlow μ) :
    PureDiscrete F ↔ (eigenSpan F).topologicalClosure = ⊤ := by
  rw [PureDiscrete, ← Submodule.dense_iff_topologicalClosure_eq_top]

/-! ## Continuous eigenfunctions -/

section Continuous

variable [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y]
  [SecondCountableTopologyEither Y ℂ] [IsFiniteMeasure ν]

/-- A continuous function that is a pointwise eigenfunction is an `L²` eigenfunction. -/
theorem isEigen_toLp (G : MeasuredFlow ν) (f : C(Y, ℂ)) {ω : ℝ}
    (hf : ∀ t y, f (G.φ t y) = phase ω t * f y) :
    IsEigen G (ContinuousMap.toLp 2 ν ℂ f) := by
  refine ⟨ω, fun t => Lp.ext ?_⟩
  have h₁ := coeFn_koopman G t (ContinuousMap.toLp 2 ν ℂ f)
  have h₂ : (ContinuousMap.toLp 2 ν ℂ f : Y → ℂ) ∘ G.φ t =ᵐ[ν] f ∘ G.φ t :=
    (G.mp t).quasiMeasurePreserving.ae_eq_comp (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) ν f)
  have h₃ := Lp.coeFn_smul (phase ω t) (ContinuousMap.toLp 2 ν ℂ f)
  have h₄ := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) ν f
  filter_upwards [h₁, h₂, h₃, h₄] with y e₁ e₂ e₃ e₄
  rw [e₁, e₂, e₃, Pi.smul_apply, e₄, smul_eq_mul]
  exact hf t y

/-- **Continuous eigenfunctions with dense uniform span give pure discrete spectrum.**
The measure is finite and weakly regular; no invariance beyond `MeasuredFlow` is used. -/
theorem pureDiscrete_of_continuous_eigen [T2Space Y] [ν.WeaklyRegular] (G : MeasuredFlow ν)
    (E : Set C(Y, ℂ))
    (hE : ∀ f ∈ E, ∃ ω : ℝ, ∀ t y, f (G.φ t y) = phase ω t * f y)
    (hdense : Dense (Submodule.span ℂ E : Set C(Y, ℂ))) :
    PureDiscrete G := by
  let L : C(Y, ℂ) →L[ℂ] Lp ℂ 2 ν := ContinuousMap.toLp 2 ν ℂ
  have hL : DenseRange L := ContinuousMap.toLp_denseRange ℂ ν ℂ (by norm_num)
  have himage : Dense (L '' (Submodule.span ℂ E : Set C(Y, ℂ))) :=
    hL.dense_image L.continuous hdense
  have hle : Submodule.span ℂ E ≤ (eigenSpan G).comap L.toLinearMap :=
    Submodule.span_le.2 fun f hf => by
      obtain ⟨ω, hω⟩ := hE f hf
      exact Submodule.subset_span (isEigen_toLp G f hω)
  refine himage.mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact hle hf

end Continuous

/-! ## Transfer along a factor map -/

/-- The pullback of `L²` functions along a measure-preserving map. -/
noncomputable def pullback {g : X → Y} (hg : MeasurePreserving g μ ν) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ g hg

theorem coeFn_pullback {g : X → Y} (hg : MeasurePreserving g μ ν) (f : Lp ℂ 2 ν) :
    pullback hg f =ᵐ[μ] f ∘ g :=
  Lp.coeFn_compMeasurePreserving f hg

/-- Pullback along an almost everywhere equivariant map intertwines the Koopman operators. -/
theorem koopman_pullback (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (hg : MeasurePreserving g μ ν) (heq : ∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g)
    (t : ℝ) (f : Lp ℂ 2 ν) :
    koopman F t (pullback hg f) = pullback hg (koopman G t f) := by
  refine Lp.ext ?_
  have h₁ := coeFn_koopman F t (pullback hg f)
  have h₂ : (pullback hg f : X → ℂ) ∘ F.φ t =ᵐ[μ] (f ∘ g) ∘ F.φ t :=
    (F.mp t).quasiMeasurePreserving.ae_eq_comp (coeFn_pullback hg f)
  have h₃ := coeFn_pullback hg (koopman G t f)
  have h₄ : (koopman G t f : Y → ℂ) ∘ g =ᵐ[μ] (f ∘ G.φ t) ∘ g :=
    hg.quasiMeasurePreserving.ae_eq_comp (coeFn_koopman G t f)
  filter_upwards [h₁, h₂, h₃, h₄, heq t] with x e₁ e₂ e₃ e₄ e₅
  rw [e₁, e₂, e₃, e₄]
  simp only [comp_apply] at e₅ ⊢
  rw [e₅]

theorem isEigen_pullback (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (hg : MeasurePreserving g μ ν) (heq : ∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g)
    {f : Lp ℂ 2 ν} (hf : IsEigen G f) : IsEigen F (pullback hg f) := by
  obtain ⟨ω, hω⟩ := hf
  exact ⟨ω, fun t => by rw [koopman_pullback F G hg heq, hω, map_smul]⟩

/-- **Transfer.** Pure discreteness of the target lifts to the source when the pullback has
dense range. Density is a hypothesis; `surjective_pullback_of_ae_inverse` supplies it from an
almost everywhere inverse. -/
theorem pureDiscrete_of_denseRange (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (hg : MeasurePreserving g μ ν) (heq : ∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g)
    (hdense : DenseRange (pullback hg)) (hG : PureDiscrete G) : PureDiscrete F := by
  have himage : Dense (pullback hg '' (eigenSpan G : Set (Lp ℂ 2 ν))) :=
    hdense.dense_image (pullback hg).continuous hG
  have hle : eigenSpan G ≤ (eigenSpan F).comap (pullback hg).toLinearMap :=
    Submodule.span_le.2 fun f hf =>
      Submodule.subset_span (isEigen_pullback F G hg heq hf)
  refine himage.mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact hle hf

/-- A measurable almost everywhere left inverse of `g` preserves the measures backwards. -/
theorem measurePreserving_of_ae_inverse {g : X → Y} (hg : MeasurePreserving g μ ν)
    {h : Y → X} (hh : Measurable h) (hinv : h ∘ g =ᵐ[μ] id) : MeasurePreserving h ν μ := by
  refine ⟨hh, ?_⟩
  rw [← hg.map_eq, Measure.map_map hh hg.measurable, Measure.map_congr hinv, Measure.map_id]

/-- **Almost everywhere invertibility makes the pullback onto.** -/
theorem surjective_pullback_of_ae_inverse {g : X → Y} (hg : MeasurePreserving g μ ν)
    {h : Y → X} (hh : Measurable h) (hinv : h ∘ g =ᵐ[μ] id) :
    Surjective (pullback hg) := by
  have hmp := measurePreserving_of_ae_inverse hg hh hinv
  intro f
  refine ⟨pullback hmp f, Lp.ext ?_⟩
  have h₁ := coeFn_pullback hg (pullback hmp f)
  have h₂ : (pullback hmp f : Y → ℂ) ∘ g =ᵐ[μ] (f ∘ h) ∘ g :=
    hg.quasiMeasurePreserving.ae_eq_comp (coeFn_pullback hmp f)
  filter_upwards [h₁, h₂, hinv] with x e₁ e₂ e₃
  rw [e₁, e₂]
  simp only [comp_apply, id_eq] at e₃ ⊢
  rw [e₃]

/-- **The assembled implication.** A measure-preserving, almost everywhere equivariant map
with a measurable almost everywhere inverse carries pure discreteness from target to source. -/
theorem pureDiscrete_of_ae_inverse (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (hg : MeasurePreserving g μ ν) (heq : ∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g)
    {h : Y → X} (hh : Measurable h) (hinv : h ∘ g =ᵐ[μ] id) (hG : PureDiscrete G) :
    PureDiscrete F :=
  pureDiscrete_of_denseRange F G hg heq
    (surjective_pullback_of_ae_inverse hg hh hinv).denseRange hG

/-- The image measure under a map that intertwines `φ` with `ψ` is preserved by `ψ`. -/
theorem measurePreserving_map_of_semiconj {g : X → Y} (hg : Measurable g) {φ : X → X}
    {ψ : Y → Y} (hφ : MeasurePreserving φ μ μ) (hψ : Measurable ψ)
    (h : ∀ x, g (φ x) = ψ (g x)) : MeasurePreserving ψ (μ.map g) (μ.map g) := by
  refine ⟨hψ, ?_⟩
  have hc : ψ ∘ g = g ∘ φ := funext fun x => (h x).symm
  rw [Measure.map_map hψ hg, hc, ← Measure.map_map hg hφ.measurable, hφ.map_eq]

/-! ## Controls -/

/-- The stationary flow. -/
def stationary (μ : Measure X) : MeasuredFlow μ where
  φ _ := id
  mp _ := MeasurePreserving.id μ

theorem koopman_stationary (t : ℝ) (f : Lp ℂ 2 μ) : koopman (stationary μ) t f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_koopman (stationary μ) t f] with x hx
  simpa [stationary] using hx

/-- Positive control: for the stationary flow every function has frequency zero. -/
theorem pureDiscrete_stationary : PureDiscrete (stationary μ) := by
  have h : eigenSpan (stationary μ) = ⊤ := by
    refine top_unique fun f _ => Submodule.subset_span ⟨0, fun t => ?_⟩
    rw [koopman_stationary, phase]
    simp
  rw [PureDiscrete, h]
  exact dense_univ

theorem phase_one_half : phase 1 (1 / 2) = -1 := by
  rw [phase]
  have : (2 * Real.pi * Complex.I * (1 : ℝ) * ((1 / 2 : ℝ) : ℂ) : ℂ) = Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

/-- Negative control: the frequency is a real constraint. Under the stationary flow a
function with frequency one vanishes. -/
theorem eq_zero_of_stationary_frequency_one {f : Lp ℂ 2 μ}
    (hf : ∀ t, koopman (stationary μ) t f = phase 1 t • f) : f = 0 := by
  have h := hf (1 / 2)
  rw [koopman_stationary, phase_one_half, neg_one_smul] at h
  have h2 : (2 : ℂ) • f = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel f
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Psc.MeasuredPureDiscrete
