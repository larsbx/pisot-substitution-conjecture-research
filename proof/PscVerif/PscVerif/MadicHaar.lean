import PscVerif.MadicActionRange
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Haar image scaling on the original compact carrier. -/

open Set MeasureTheory Topology
open MeasureTheory.Measure
open scoped ENNReal
namespace Psc.MadicResidue

variable {V : Type*} [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V]
variable (M : V →ₗ[ℤ] V)

instance : MeasurableSpace (Carrier M) := borel _
instance : BorelSpace (Carrier M) := ⟨rfl⟩

theorem action_isOpenEmbedding (hinj : Function.Injective M) :
    IsOpenEmbedding (action M) := by
  let := carrier_compactSpace M hinj
  have he := (continuous_action M).isClosedEmbedding (action_injective M hinj)
  refine ⟨he.isEmbedding, ?_⟩
  have hr : Set.range (action M) = (eval M 1) ⁻¹' {0} := by
    exact congrArg (fun p : Submodule ℤ (Carrier M) => (p : Set (Carrier M)))
      (action_range_eq_ker_eval_one M hinj)
  rw [hr]
  exact (isOpen_discrete _).preimage (continuous_eval M 1)

omit [Module.Free ℤ V] [Module.Finite ℤ V] in
/-- For any normalized Haar measure, every first-residue fiber has the
same mass. Its value is the inverse of the actual quotient cardinality. -/
theorem measure_first_kernel [Fintype (Residue M 1)]
    (μ : Measure (Carrier M)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    μ ((eval M 1) ⁻¹' {0}) = (Fintype.card (Residue M 1) : ℝ≥0∞)⁻¹ := by
  let fiber (a : Residue M 1) := (eval M 1) ⁻¹' {a}
  have hm (a) : MeasurableSet (fiber a) :=
    ((isOpen_discrete _).preimage (continuous_eval M 1)).measurableSet
  have hd : Pairwise (fun a b => Disjoint (fiber a) (fiber b)) := by
    intro a b hab
    exact Set.disjoint_left.mpr fun x ha hb => hab (ha.symm.trans hb)
  have hu : (⋃ a, fiber a) = univ := by
    ext x
    simp [fiber]
  have hsame (a) : μ (fiber a) = μ (fiber 0) := by
    obtain ⟨x, hx⟩ := eval_surjective M 1 a
    have hpre : (fun y => x + y) ⁻¹' fiber a = fiber 0 := by
      ext y
      simp [fiber, map_add, hx]
    rw [← hpre, measure_preimage_add]
  have hsum : (Fintype.card (Residue M 1) : ℝ≥0∞) * μ (fiber 0) = 1 := by
    simpa [hsame] using (measure_iUnion hd hm (μ := μ)).symm.trans
      (by rw [hu, measure_univ])
  have hn : (Fintype.card (Residue M 1) : ℝ≥0∞) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  calc
    _ = (Fintype.card (Residue M 1) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Residue M 1) : ℝ≥0∞) * μ (fiber 0)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hn (by simp), one_mul]
    _ = _ := by rw [hsum, mul_one]

theorem measure_action_image (hinj : Function.Injective M) [Fintype (Residue M 1)]
    (μ : Measure (Carrier M)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (s : Set (Carrier M)) :
    μ (action M '' s) = (Fintype.card (Residue M 1) : ℝ≥0∞)⁻¹ * μ s := by
  let := carrier_compactSpace M hinj
  let f := (action M).toAddMonoidHom
  have he : IsOpenEmbedding f := action_isOpenEmbedding M hinj
  letI : (μ.comap f).IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ he
  have h := isAddInvariant_eq_smul_of_compactSpace (μ.comap f) μ
  have hc : (addHaarScalarFactor (μ.comap f) μ : ℝ≥0∞) =
      (Fintype.card (Residue M 1) : ℝ≥0∞)⁻¹ := by
    have hr : f '' univ = (eval M 1) ⁻¹' {0} := by
      rw [image_univ]
      exact congrArg (fun p : Submodule ℤ (Carrier M) => (p : Set (Carrier M)))
        (action_range_eq_ker_eval_one M hinj)
    have hu := congrArg (fun ν : Measure (Carrier M) => ν univ) h
    rw [he.measurableEmbedding.comap_apply, hr, measure_first_kernel M μ,
      Measure.smul_apply, measure_univ] at hu
    simpa using hu.symm
  have hs := congrArg (fun ν : Measure (Carrier M) => ν s) h
  rw [he.measurableEmbedding.comap_apply, Measure.smul_apply] at hs
  change μ (f '' s) = _
  simpa only [ENNReal.smul_def, smul_eq_mul, hc] using hs

end Psc.MadicResidue
