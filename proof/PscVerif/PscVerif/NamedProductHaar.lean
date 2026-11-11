import PscVerif.MadicHaar
import PscVerif.NamedStableChart
import PscVerif.OccurrenceResidue
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.Discrete

/-! Product-Haar image scaling for the two named actual substitutions. -/

open Set MeasureTheory Topology
open MeasureTheory.Measure
open scoped ENNReal
open Psc.NamedStableChart Psc.OccurrenceResidue Psc.OccurrenceTransport
namespace Psc.NamedProductHaar

abbrev M (σ : Fin 3 → Word) := incidenceLinear σ
abbrev H (σ : Fin 3 → Word) := MadicResidue.Carrier (M σ)
abbrev G (σ : Fin 3 → Word) := Ambient σ Stable

theorem integral_injective (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ) :
    Function.Injective (M σ) := by
  intro x y h
  apply MZ_mulVec_injective
  simpa only [M, incidenceLinear_apply, hM] using h

theorem first_residue_card (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ) :
    Nat.card (MadicResidue.Residue (M σ) 1) = 2 := by
  let e := LinearEquiv.ofInjective (M σ ^ 1) (by
    simpa only [pow_one] using integral_injective σ hM)
  have h := Submodule.natAbs_det_equiv (MadicResidue.powerRange (M σ) 1) e
  change (LinearMap.det (M σ ^ 1)).natAbs = _ at h
  rw [← h, pow_one]
  unfold M incidenceLinear
  rw [hM, ← Matrix.toLin'_apply', LinearMap.det_toLin', MZ_det] <;> rfl

theorem action_index (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ) :
    Nat.card (H σ ⧸ LinearMap.range (MadicResidue.action (M σ))) = 2 :=
  (Nat.card_congr (MadicResidue.actionCokernelEquiv (M σ)
    (integral_injective σ hM)).toEquiv).trans (first_residue_card σ hM)

theorem measure_compact_action (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ)
    (ν : Measure (H σ)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (s : Set (H σ)) :
    ν (MadicResidue.action (M σ) '' s) = (2 : ℝ≥0∞)⁻¹ * ν s := by
  letI := MadicResidue.residue_finite (M σ) (integral_injective σ hM) 1
  letI : Fintype (MadicResidue.Residue (M σ) 1) := Fintype.ofFinite _
  have hcard : Fintype.card (MadicResidue.Residue (M σ) 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, first_residue_card σ hM]
  rw [MadicResidue.measure_action_image _ (integral_injective σ hM), hcard] <;> norm_num

theorem measure_product_action (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ)
    (ν : Measure (H σ)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (s : Set (G σ)) :
    (volume.prod ν) (ambientAction σ B '' s) =
      ENNReal.ofReal beta⁻¹ * (volume.prod ν) s := by
  letI := MadicResidue.carrier_compactSpace (M σ) (integral_injective σ hM)
  letI : ∀ q, Finite (MadicResidue.Residue (M σ) q) :=
    MadicResidue.residue_finite (M σ) (integral_injective σ hM)
  letI : ∀ q, SecondCountableTopology (MadicResidue.Residue (M σ) q) :=
    fun q => DiscreteTopology.secondCountableTopology_of_countable
  letI : SecondCountableTopology (H σ) := by
    change SecondCountableTopology (↥(MadicResidue.compatibleSequences (M σ)))
    infer_instance
  letI : SecondCountableTopology (G σ) := by
    change SecondCountableTopology (Stable × H σ)
    infer_instance
  let T := ambientAction σ B
  let μ : Measure (G σ) := volume.prod ν
  have hdet : LinearMap.det Blinear = 2 / beta := by
    rw [Blinear, ← Matrix.toLin'_apply', LinearMap.det_toLin', Bmat_det, b_eq_inv_beta]
    ring
  have hdetpos : 0 < LinearMap.det Blinear := by
    rw [hdet]
    exact div_pos (by norm_num) beta_pos
  let e := (Blinear.equivOfDetNeZero hdetpos.ne').toContinuousLinearEquiv
  have hB : IsOpenEmbedding B := e.toHomeomorph.isOpenEmbedding
  have hT : IsOpenEmbedding T := hB.prodMap
    (MadicResidue.action_isOpenEmbedding (M σ) (integral_injective σ hM))
  letI : (μ.comap T).IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hT
  have h := isAddLeftInvariant_eq_smul (μ.comap T) μ
  let cube : Set Stable := Icc 0 1
  let rect : Set (G σ) := cube ×ˢ univ
  have hcube : volume cube = 1 := by simp [cube, Real.volume_Icc_pi]
  have hrect : μ rect = 1 := by simp [μ, rect, Measure.prod_prod, hcube]
  have himage : T '' rect = (Blinear '' cube) ×ˢ (MadicResidue.action (M σ) '' univ) := by
    change (Prod.map (Blinear : Stable → Stable)
      (MadicResidue.action (M σ) : H σ → H σ)) '' (cube ×ˢ univ) = _
    exact prodMap_image_prod _ _ _ _
  have hc : (addHaarScalarFactor (μ.comap T) μ : ℝ≥0∞) = ENNReal.ofReal beta⁻¹ := by
    have hr := congrArg (fun m : Measure (G σ) => m rect) h
    rw [hT.measurableEmbedding.comap_apply, himage, Measure.smul_apply, hrect] at hr
    simp only [ENNReal.smul_def, smul_eq_mul, mul_one] at hr
    rw [← hr]
    change (volume.prod ν) _ = _
    rw [Measure.prod_prod, addHaar_image_linearMap, hcube, mul_one, abs_of_pos hdetpos, hdet,
      measure_compact_action σ hM, measure_univ, mul_one]
    rw [show ((2 : ℝ≥0∞)⁻¹) = ENNReal.ofReal ((2 : ℝ)⁻¹) by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (div_nonneg (by norm_num) beta_pos.le)]
    congr 1
    ring
  have hs := congrArg (fun m : Measure (G σ) => m s) h
  rw [hT.measurableEmbedding.comap_apply, Measure.smul_apply] at hs
  change μ (T '' s) = _
  simpa only [ENNReal.smul_def, smul_eq_mul, hc] using hs

theorem measure_affine_power (σ : Fin 3 → Word) (hM : incidenceZ σ = MZ)
    (ν : Measure (H σ)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (k : ℕ) (t : G σ) (s : Set (G σ)) :
    (volume.prod ν) ((fun x => (ambientAction σ B ^ k) x + t) '' s) =
      (ENNReal.ofReal beta⁻¹) ^ k * (volume.prod ν) s := by
  have scale (k : ℕ) :
      (volume.prod ν) ((ambientAction σ B ^ k) '' s) =
        (ENNReal.ofReal beta⁻¹) ^ k * (volume.prod ν) s := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      let T := ambientAction σ B
      change (volume.prod ν) ((T ∘ (T ^ k : AddMonoid.End (G σ))) '' s) = _
      rw [← Set.image_image T (T ^ k : AddMonoid.End (G σ)) s]
      change (volume.prod ν) (ambientAction σ B '' ((ambientAction σ B ^ k) '' s)) = _
      rw [measure_product_action σ hM, ih, pow_succ', mul_assoc]
  calc
    _ = (volume.prod ν) ((fun y => y + t) '' ((ambientAction σ B ^ k) '' s)) := by
      simp only [Set.image_image]
    _ = _ := by rw [Set.image_add_right, measure_preimage_add_right, scale]

end Psc.NamedProductHaar
