import PscVerif.NamedStrictExclusion

/-! Independent finite controls for distinct-label and complete-root coverage. -/

open Set MeasureTheory

namespace Psc.NamedStrictExclusionControls

open Psc.OccurrencePiece Psc.ArchivedGraphRefinement

def diagonalTiles (a : Fin 3) : Set ℤ := if a = 0 then {0} else ∅

/-- If equal labels are admitted, all three archived root intersections
can be null while the diagonal intersection has positive measure. -/
theorem dropping_distinct_labels_counterexample :
    (∀ k : Fin 3, (Measure.dirac (0 : ℤ))
      (overlap (0 : (Fin 3 → ℤ) →+ ℤ) diagonalTiles (archivedRoot k)) = 0) ∧
      0 < (Measure.dirac (0 : ℤ)) (diagonalTiles 0 ∩ diagonalTiles 0) := by
  constructor
  · intro k
    fin_cases k <;> simp [overlap, archivedRoot, diagonalTiles]
  · simp [diagonalTiles]

def omittedRootTiles (a : Fin 3) : Set ℤ := if a = 0 then ∅ else {0}

/-- Nullity at roots 01 and 02 does not control the missing root 12.
The source of its positive measure is entirely independent of strict systems. -/
theorem omitting_root_counterexample :
    (Measure.dirac (0 : ℤ))
        (overlap (0 : (Fin 3 → ℤ) →+ ℤ) omittedRootTiles (archivedRoot 0)) = 0 ∧
      (Measure.dirac (0 : ℤ))
        (overlap (0 : (Fin 3 → ℤ) →+ ℤ) omittedRootTiles (archivedRoot 1)) = 0 ∧
      0 < (Measure.dirac (0 : ℤ))
        (overlap (0 : (Fin 3 → ℤ) →+ ℤ) omittedRootTiles (archivedRoot 2)) := by
  simp [overlap, archivedRoot, omittedRootTiles]

end Psc.NamedStrictExclusionControls
