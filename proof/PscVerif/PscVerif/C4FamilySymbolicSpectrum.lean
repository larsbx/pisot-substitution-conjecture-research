import PscVerif.C4FamilyMeasuredSpectrum
import PscVerif.C4FamilySymbolicLanguage
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Transfer of the actual ordinary-hull spectrum to its next-tile symbolic
return map. The transverse probability is induced by the measured constant
strip of the very same legal tilings. -/

namespace Psc.C4FamilySymbolicSpectrum

open Function Filter MeasureTheory Set ContinuousLinearMap
open scoped InnerProductSpace Psc.C4FamilyMeasuredRealization
open Psc.ParameterFamilyTiling (geometry)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.C4FamilyMeasuredRealization (hullMeasure measurePreserving_translate)
open Psc.C4FamilyMeasuredSpectrum (translationKoopman translationPhase
  pureDiscrete_translation)
open Psc.C4FamilySymbolicSection

noncomputable scoped instance transversalMeasurableSpace {k : ℕ} {hk : 1 ≤ k} :
    MeasurableSpace (Transversal k hk) := borel _

scoped instance transversalBorelSpace {k : ℕ} {hk : 1 ≤ k} :
    BorelSpace (Transversal k hk) := ⟨rfl⟩

private noncomputable def equivOfEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) (hs : Surjective f) :
    α ≃ᵐ β where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hs⟩
  measurable_toFun := hf.measurable
  measurable_invFun := by
    let e := Equiv.ofBijective f ⟨hf.injective, hs⟩
    intro s h
    change MeasurableSet (e.symm ⁻¹' s)
    have hs' : (e.symm : β → α) ⁻¹' s = f '' s := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        exact show e.symm (e x) ∈ s by simpa using hx
    rw [hs']
    exact hf.measurableSet_image' h

variable (k : ℕ) (hk : 1 ≤ k)

local notation "G" => geometry k hk
local notation "B" => Transversal k hk
local notation "X" => LocalHull G

/-- Unique measurable coordinates in the half-open physical suspension. -/
noncomputable def physicalStripEquiv : PhysicalStrip k hk ≃ᵐ X := by
  have hm : MeasurableSet (PhysicalStrip k hk) :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (continuous_roof.comp continuous_fst).measurable)
  exact equivOfEmbedding (continuous_physical.continuousOn.measurableEmbedding hm physical_injOn)
    (fun T => by obtain ⟨p, hp, he⟩ := exists_physical T; exact ⟨⟨p, hp⟩, he⟩)

/-- Unique measurable coordinates in the half-open constant suspension. -/
noncomputable def constantStripEquiv : ConstantStrip k hk ≃ᵐ X := by
  have hm : MeasurableSet (ConstantStrip k hk) := measurable_snd measurableSet_Ico
  exact equivOfEmbedding (continuous_strip.continuousOn.measurableEmbedding hm strip_injOn)
    (fun T => by obtain ⟨p, hp, he⟩ := exists_strip T; exact ⟨⟨p, hp⟩, he⟩)

/-- The base coordinate of the constant suspension, a factor at time equal
to the mean roof. -/
noncomputable def symbolicFactor (T : X) : B := ((constantStripEquiv k hk).symm T).1.1

theorem measurable_symbolicFactor : Measurable (symbolicFactor k hk) :=
  measurable_fst.comp (measurable_subtype_coe.comp (constantStripEquiv k hk).symm.measurable)

theorem symbolicFactor_translate (T : X) :
    symbolicFactor k hk (translate G (meanRoof k hk) T) = next (symbolicFactor k hk T) := by
  let p := (constantStripEquiv k hk).symm T
  have hp : strip p.1 = T := (constantStripEquiv k hk).apply_symm_apply T
  let q : ConstantStrip k hk := ⟨(next p.1.1, p.1.2), p.2⟩
  have hq : constantStripEquiv k hk q = translate G (meanRoof k hk) T := by
    change strip (next p.1.1, p.1.2) = _
    rw [← hp, translate_mean_strip]
  change ((constantStripEquiv k hk).symm (translate G (meanRoof k hk) T)).1.1 = q.1.1
  rw [← hq, MeasurableEquiv.symm_apply_apply]

variable (hk₂ : 2 ≤ k)

local notation "ν" => hullMeasure k hk hk₂

/-- The transverse probability attached to the measured ordinary hull. -/
noncomputable def symbolicMeasure : Measure B := (ν).map (symbolicFactor k hk)

instance : IsProbabilityMeasure (symbolicMeasure k hk hk₂) :=
  inferInstanceAs (IsProbabilityMeasure ((ν).map (symbolicFactor k hk)))

theorem measurePreserving_symbolicFactor :
    MeasurePreserving (symbolicFactor k hk) ν (symbolicMeasure k hk hk₂) :=
  ⟨measurable_symbolicFactor k hk, rfl⟩

theorem measurePreserving_next :
    MeasurePreserving (next (k := k) (hk := hk))
      (symbolicMeasure k hk hk₂) (symbolicMeasure k hk hk₂) := by
  have h := measurePreserving_translate k hk hk₂ (meanRoof k hk)
  have hf := measurable_symbolicFactor k hk
  refine ⟨continuous_next.measurable, ?_⟩
  change ((ν).map (symbolicFactor k hk)).map next = (ν).map (symbolicFactor k hk)
  have hq : symbolicFactor k hk ∘ translate G (meanRoof k hk) = next ∘ symbolicFactor k hk :=
    funext (symbolicFactor_translate k hk)
  rw [Measure.map_map continuous_next.measurable hf, ← hq, ← Measure.map_map hf h.measurable, h.map_eq]

local notation "μ" => symbolicMeasure k hk hk₂

/-- Koopman composition by the forward one-tile shift. -/
noncomputable def shiftKoopman : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ next (measurePreserving_next k hk hk₂)

private theorem compLp_surjective {α : Type*} [MeasurableSpace α] {m : Measure α}
    (e : α ≃ᵐ α) (hf : MeasurePreserving e m m) :
    Surjective (Lp.compMeasurePreservingₗᵢ ℂ e hf (E := ℂ) (p := 2)) := by
  have hg := hf.symm e
  intro v
  refine ⟨Lp.compMeasurePreserving e.symm hg v, Lp.ext ?_⟩
  change (Lp.compMeasurePreserving e hf (Lp.compMeasurePreserving e.symm hg v) : α → ℂ)
    =ᵐ[m] v
  rw [← Lp.compMeasurePreserving_comp_apply v hg hf]
  have hcomp : (e.symm : α → α) ∘ e = id := funext e.symm_apply_apply
  generalize (hg.comp hf) = h
  revert h
  rw [hcomp]
  intro h
  rw [Lp.compMeasurePreserving_id_apply]

private theorem compLp_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m₁ : Measure α} {m₂ : Measure β} {f g : α → β} (h : f = g)
    (hf : MeasurePreserving f m₁ m₂) (hg : MeasurePreserving g m₁ m₂)
    (v : Lp ℂ 2 m₂) :
    Lp.compMeasurePreserving f hf v = Lp.compMeasurePreserving g hg v := by
  subst g
  rfl

private theorem adjoint_intertwines {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℂ] F) (U : F →ₗᵢ[ℂ] F) (R : E →ₗᵢ[ℂ] E) (hR : Surjective R)
    (h : U.toContinuousLinearMap ∘L J.toContinuousLinearMap =
      J.toContinuousLinearMap ∘L R.toContinuousLinearMap) :
    J.toContinuousLinearMap.adjoint ∘L U.toContinuousLinearMap =
      R.toContinuousLinearMap ∘L J.toContinuousLinearMap.adjoint := by
  let j := J.toContinuousLinearMap
  let u := U.toContinuousLinearMap
  let r := R.toContinuousLinearMap
  have hr : r ∘L r.adjoint = 1 := by
    ext1 v
    obtain ⟨w, rfl⟩ := hR v
    change r (r.adjoint (r w)) = r w
    congr 1
    exact congrArg (fun A : E →L[ℂ] E => A w) R.adjoint_comp_self
  have hback : u.adjoint ∘L j = j ∘L r.adjoint := by
    calc
      u.adjoint ∘L j = u.adjoint ∘L ((j ∘L r) ∘L r.adjoint) := by
        rw [ContinuousLinearMap.comp_assoc j, hr, one_def, ContinuousLinearMap.comp_id]
      _ = (u.adjoint ∘L u) ∘L (j ∘L r.adjoint) := by
        rw [← h]
        change u.adjoint ∘L ((u ∘L j) ∘L r.adjoint) = _
        simp only [ContinuousLinearMap.comp_assoc]
      _ = j ∘L r.adjoint := by
        rw [show u.adjoint ∘L u = 1 from U.adjoint_comp_self, one_def, ContinuousLinearMap.id_comp]
  simpa only [adjoint_comp, adjoint_adjoint] using
    congrArg (fun A : E →L[ℂ] F => A.adjoint) hback

private theorem compLp_intertwines {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m₁ : Measure α} {m₂ : Measure β} {f : α → β} {t : α → α} {r : β → β}
    (hf : MeasurePreserving f m₁ m₂) (ht : MeasurePreserving t m₁ m₁)
    (hr : MeasurePreserving r m₂ m₂) (h : f ∘ t = r ∘ f) :
    (Lp.compMeasurePreservingₗᵢ ℂ t ht (E := ℂ) (p := 2)).toContinuousLinearMap ∘L
        (Lp.compMeasurePreservingₗᵢ ℂ f hf).toContinuousLinearMap =
      (Lp.compMeasurePreservingₗᵢ ℂ f hf).toContinuousLinearMap ∘L
        (Lp.compMeasurePreservingₗᵢ ℂ r hr).toContinuousLinearMap := by
  ext1 v
  change Lp.compMeasurePreserving t ht (Lp.compMeasurePreserving f hf v) =
    Lp.compMeasurePreserving f hf (Lp.compMeasurePreserving r hr v)
  rw [← Lp.compMeasurePreserving_comp_apply v hf ht,
    ← Lp.compMeasurePreserving_comp_apply v hr hf]
  exact compLp_congr h _ _ _

private theorem pureDiscrete_factor {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℂ] F) (U : F →ₗᵢ[ℂ] F) (R : E →ₗᵢ[ℂ] E) (hR : Surjective R)
    (h : U.toContinuousLinearMap ∘L J.toContinuousLinearMap =
      J.toContinuousLinearMap ∘L R.toContinuousLinearMap)
    (hU : (Submodule.span ℂ {v | v ≠ 0 ∧ ∃ z : ℂ, U v = z • v}).topologicalClosure = ⊤) :
    (Submodule.span ℂ {v | v ≠ 0 ∧ ∃ z : ℂ, R v = z • v}).topologicalClosure = ⊤ := by
  let j := J.toContinuousLinearMap
  have hproj := adjoint_intertwines J U R hR h
  have hj : DenseRange j.adjoint := by
    apply Surjective.denseRange
    intro y
    exact ⟨J y, congrArg (fun A : E →L[ℂ] E => A y) J.adjoint_comp_self⟩
  have hspan := hj.topologicalClosure_map_submodule hU
  rw [Submodule.map_span] at hspan
  apply top_unique
  rw [← hspan]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨v, ⟨_, z, he⟩, rfl⟩
  change j.adjoint v ∈ Submodule.span ℂ {v | v ≠ 0 ∧ ∃ z : ℂ, R v = z • v}
  by_cases hv : j.adjoint v = 0
  · rw [hv]
    exact zero_mem _
  apply Submodule.subset_span
  refine ⟨hv, z, ?_⟩
  have hh := congrArg (fun A : F →L[ℂ] E => A v) hproj
  change j.adjoint (U v) = R (j.adjoint v) at hh
  rw [← hh, he, map_smul]

/-- A nonzero complex L² eigenvector for the next-tile return. -/
def IsShiftEigenvector (v : Lp ℂ 2 μ) : Prop :=
  v ≠ 0 ∧ ∃ z : ℂ, shiftKoopman k hk hk₂ v = z • v

/-- Pure discrete spectrum for the actual legal next-tile shift with its
transverse probability. -/
theorem pureDiscrete_next :
    (Submodule.span ℂ {v | IsShiftEigenvector k hk hk₂ v}).topologicalClosure = ⊤ := by
  let c := meanRoof k hk
  have hf := measurePreserving_symbolicFactor k hk hk₂
  have hs := measurePreserving_next k hk hk₂
  have ht := measurePreserving_translate k hk hk₂ c
  have hq : symbolicFactor k hk ∘ translate G c = next ∘ symbolicFactor k hk :=
    funext (symbolicFactor_translate k hk)
  have hsurj : Surjective (shiftKoopman k hk hk₂) :=
    compLp_surjective (nextHomeomorph (k := k) (hk := hk)).toMeasurableEquiv hs
  let J := Lp.compMeasurePreservingₗᵢ ℂ (symbolicFactor k hk) hf (E := ℂ) (p := 2)
  refine pureDiscrete_factor J
    (translationKoopman k hk hk₂ c) (shiftKoopman k hk hk₂) hsurj
    (compLp_intertwines hf ht hs hq) ?_
  apply top_unique
  rw [← pureDiscrete_translation k hk hk₂]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro v ⟨hv, ξ, he⟩
  exact ⟨hv, translationPhase c ξ, he c⟩

open Psc.C4FamilySymbolicLanguage (SymbolicHull itineraryHomeomorph
  shift continuous_shift itineraryHomeomorph_next)

local notation "W" => SymbolicHull k hk

noncomputable scoped instance wordMeasurableSpace {j : ℕ} {hj : 1 ≤ j} :
    MeasurableSpace (SymbolicHull j hj) := borel _

scoped instance wordBorelSpace {j : ℕ} {hj : 1 ≤ j} :
    BorelSpace (SymbolicHull j hj) := ⟨rfl⟩

private noncomputable def wordConjugacy : B ≃ᵐ W :=
  (itineraryHomeomorph (k := k) (hk := hk)).toMeasurableEquiv

/-- The invariant probability on the actual bi-infinite legal words. -/
noncomputable def wordMeasure : Measure W := (μ).map (wordConjugacy k hk)

instance : IsProbabilityMeasure (wordMeasure k hk hk₂) :=
  inferInstanceAs (IsProbabilityMeasure ((μ).map (wordConjugacy k hk)))

theorem measurePreserving_itinerary :
    MeasurePreserving (itineraryHomeomorph (k := k) (hk := hk)) μ (wordMeasure k hk hk₂) :=
  ⟨(wordConjugacy k hk).measurable, rfl⟩

theorem measurePreserving_wordShift :
    MeasurePreserving (shift (k := k) (hk := hk)) (wordMeasure k hk hk₂) (wordMeasure k hk hk₂) := by
  let e := wordConjugacy k hk
  have hq : shift ∘ e = e ∘ next := (funext itineraryHomeomorph_next).symm
  have hs := measurePreserving_next k hk hk₂
  refine ⟨continuous_shift.measurable, ?_⟩
  change ((μ).map e).map shift = (μ).map e
  rw [Measure.map_map continuous_shift.measurable e.measurable, hq,
    ← Measure.map_map e.measurable hs.measurable, hs.map_eq]

/-- Koopman composition by the left shift of the actual legal sequence. -/
noncomputable def wordShiftKoopman :
    Lp ℂ 2 (wordMeasure k hk hk₂) →ₗᵢ[ℂ] Lp ℂ 2 (wordMeasure k hk hk₂) :=
  Lp.compMeasurePreservingₗᵢ ℂ shift (measurePreserving_wordShift k hk hk₂)

private noncomputable def wordShiftEquiv : W ≃ᵐ W :=
  (wordConjugacy k hk).symm.trans
    ((nextHomeomorph (k := k) (hk := hk)).toMeasurableEquiv.trans (wordConjugacy k hk))

private theorem wordShiftEquiv_apply (x : W) : wordShiftEquiv k hk x = shift x := by
  let y := (wordConjugacy k hk).symm x
  change itineraryHomeomorph (next y) = shift x
  rw [itineraryHomeomorph_next]
  exact congrArg shift ((wordConjugacy k hk).apply_symm_apply x)

/-- The literal family has pure discrete complex L² spectrum for the
left shift on the two-sided legal symbolic hull, for every k ≥ 2. -/
theorem pureDiscrete_shift :
    (Submodule.span ℂ {v : Lp ℂ 2 (wordMeasure k hk hk₂) |
      v ≠ 0 ∧ ∃ z : ℂ, wordShiftKoopman k hk hk₂ v = z • v}).topologicalClosure = ⊤ := by
  have hf := measurePreserving_itinerary k hk hk₂
  have ht := measurePreserving_next k hk hk₂
  have hs := measurePreserving_wordShift k hk hk₂
  have he : (wordShiftEquiv k hk : W → W) = shift := funext (wordShiftEquiv_apply k hk)
  have hs' : MeasurePreserving (wordShiftEquiv k hk) (wordMeasure k hk hk₂)
      (wordMeasure k hk hk₂) := he.symm ▸ hs
  have hsurj : Surjective (wordShiftKoopman k hk hk₂) := by
    intro v
    obtain ⟨w, hw⟩ := compLp_surjective (wordShiftEquiv k hk) hs' v
    refine ⟨w, ?_⟩
    change Lp.compMeasurePreserving shift hs w = v
    rw [← compLp_congr he hs' hs w]
    exact hw
  let J := Lp.compMeasurePreservingₗᵢ ℂ itineraryHomeomorph hf (E := ℂ) (p := 2)
  exact pureDiscrete_factor J
    (shiftKoopman k hk hk₂) (wordShiftKoopman k hk hk₂) hsurj
    (compLp_intertwines hf ht hs (funext itineraryHomeomorph_next))
    (pureDiscrete_next k hk hk₂)

end Psc.C4FamilySymbolicSpectrum
