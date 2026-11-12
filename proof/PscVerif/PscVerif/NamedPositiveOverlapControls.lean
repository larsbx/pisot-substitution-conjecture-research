import PscVerif.NamedPositiveOverlap
import PscVerif.MadicFundamentalCellControls

/-! Calibrations for the fixed-depth limit and the measure transfer. -/

open Set Filter MeasureTheory
open scoped Topology

namespace Psc.NamedPositiveOverlapControls

-- A positive constant strip can hide a strict density deficit forever.
theorem bounded_strip_counterexample :
    (∀ᶠ _n : ℕ in atTop, (2 : ℝ) * 1 ≤ (1 + 1) * 1) ∧
      ¬ (2 : ℝ) ≤ 1 := by
  exact ⟨Eventually.of_forall (fun _ => by norm_num), by norm_num⟩

-- A moving width can hide the same deficit even along a diverging strip.
theorem moving_width_counterexample :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, (2 : ℝ) * n ≤ ((n : ℝ) + n) * 1) ∧
      ¬ (2 : ℝ) ≤ 1 := by
  refine ⟨tendsto_natCast_atTop_atTop, Eventually.of_forall (fun n => ?_), by norm_num⟩
  linarith

-- The compact set and open target alone do not imply an additive tube.
theorem missing_containment_counterexample :
    IsCompact ({0} : Set ℝ) ∧ IsOpen (Set.Ioi (0 : ℝ)) ∧
      ¬ ∃ U V : Set ℝ, ({0} : Set ℝ) ⊆ U ∧ V ∈ 𝓝 0 ∧
        ∀ u ∈ U, ∀ v ∈ V, u + v ∈ Set.Ioi (0 : ℝ) := by
  refine ⟨isCompact_singleton, isOpen_Ioi, ?_⟩
  rintro ⟨U, V, hU, hV, hUV⟩
  have h := hUV 0 (hU (mem_singleton 0)) 0 (mem_of_mem_nhds hV)
  simpa using h

-- A positive-measure open superset alone gives no lower bound on the compact set.
theorem one_open_superset_counterexample :
    ({0} : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 ∧
      0 < (volume : Measure ℝ) (Set.Ioo (-1) 1) ∧
      (volume : Measure ℝ) {0} = 0 := by
  refine ⟨?_, ?_, measure_singleton 0⟩
  · intro x hx
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    norm_num
  · rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    norm_num

-- The original mismatched-depth controls are compiled by this import:
-- coarser_residue_translates_overlap and finer_residue_loses_coverage.

end Psc.NamedPositiveOverlapControls
