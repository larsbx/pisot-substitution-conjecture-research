import PscVerif.NamedStableChart

/-!
# The named full real chart and nonsingular real incidence

The physical row and both stable coordinates together form a continuous
linear equivalence. This packages the existing reconstruction identities;
the stable projection alone is not used as an invertible chart. The actual
real incidence is likewise packaged as an equivalence and remains bound to
the original integer matrix by the existing cast identity.

No assertion that the chart preserves canonical volume is made.
Pre-code gate: the following-increment section of
`docs/c4-finite-cut-count.md`, committed in `d6d6ba2331bc`.
-/

namespace Psc.NamedFullChart

open Matrix Psc.NamedStableChart

noncomputable def fullChartLinear : AmbientReal →ₗ[ℝ] (ℝ × Stable) where
  toFun x := (physical x, W *ᵥ x)
  map_add' x y := by
    exact Prod.ext (physical_add x y) (Matrix.mulVec_add W x y)
  map_smul' t x := by
    change (physical (t • x), W *ᵥ (t • x)) = (t * physical x, t • (W *ᵥ x))
    rw [physical_smul, Matrix.mulVec_smul]

theorem fullChartLinear_injective : Function.Injective fullChartLinear := by
  intro x y h
  have hp : physical x = physical y := congrArg Prod.fst h
  have hw : W *ᵥ x = W *ᵥ y := congrArg Prod.snd h
  calc
    x = L (W *ᵥ x) + (physical x / kappa) • r := reconstruction x
    _ = L (W *ᵥ y) + (physical y / kappa) • r := by rw [hp, hw]
    _ = y := (reconstruction y).symm

theorem fullChart_inverse_formula (y : ℝ × Stable) :
    fullChartLinear (L y.2 + (y.1 / kappa) • r) = y := by
  apply Prod.ext
  · change physical (L y.2 + (y.1 / kappa) • r) = y.1
    rw [physical_add, physical_L, physical_smul, physical_r_eq_kappa,
      zero_add, div_mul_cancel₀ _ kappa_ne_zero]
  · change W *ᵥ (L y.2 + (y.1 / kappa) • r) = y.2
    rw [Matrix.mulVec_add, W_L, Matrix.mulVec_smul, W_r_zero, smul_zero, add_zero]

theorem fullChartLinear_surjective : Function.Surjective fullChartLinear := by
  intro y
  exact ⟨L y.2 + (y.1 / kappa) • r, fullChart_inverse_formula y⟩

/-- The original full physical/stable chart, with its actual inverse. -/
noncomputable def fullChart : AmbientReal ≃L[ℝ] (ℝ × Stable) :=
  (LinearEquiv.ofBijective fullChartLinear
    ⟨fullChartLinear_injective, fullChartLinear_surjective⟩).toContinuousLinearEquiv

@[simp] theorem fullChart_apply (x : AmbientReal) :
    fullChart x = (physical x, W *ᵥ x) := rfl

theorem fullChart_symm_apply (y : ℝ × Stable) :
    fullChart.symm y = L y.2 + (y.1 / kappa) • r := by
  apply fullChart.injective
  rw [fullChart.apply_symm_apply]
  exact (fullChart_inverse_formula y).symm

theorem realIncidence_det : MR.det = 2 := by
  norm_num [MR_eq, Matrix.det_fin_three]

theorem realIncidence_injective : Function.Injective MR.mulVecLin :=
  Matrix.mulVec_injective_of_det_ne_zero (by rw [realIncidence_det]; norm_num)

theorem realIncidence_surjective : Function.Surjective MR.mulVecLin := by
  intro y
  refine ⟨![y 1 - (y 0 + y 2) / 2, y 2, (y 0 - y 2) / 2], ?_⟩
  change MR *ᵥ _ = y
  rw [MR_mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- This is the real extension of the same determinant-two integer matrix. -/
noncomputable def realIncidence : AmbientReal ≃L[ℝ] AmbientReal :=
  (LinearEquiv.ofBijective MR.mulVecLin
    ⟨realIncidence_injective, realIncidence_surjective⟩).toContinuousLinearEquiv

@[simp] theorem realIncidence_apply (x : AmbientReal) :
    realIncidence x = MR *ᵥ x := rfl

theorem realIncidence_castZ (z : Fin 3 → ℤ) :
    realIncidence (castZ z) = castZ (MZ *ᵥ z) :=
  (castZ_mulVec z).symm

end Psc.NamedFullChart
