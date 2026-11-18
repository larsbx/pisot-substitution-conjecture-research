import PscVerif.MadicFundamentalCell
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact cell boundaries: coordinate faces and matched depths

The product-order interval `Ico 0 1` admits an upper-face integer vector and
therefore cannot replace the coordinatewise half-open cube. The remaining
controls use multiplication by two on the original three-dimensional integer
lattice and its genuine matrix-adic inverse limit. A real cell of depth one
with residue depth zero overlaps its nonzero translate; a real cell of depth
zero with residue depth one misses an explicit point.

The doubling map is an elementary calibration of the cell construction, not
a Pisot substitution or a new C4 specimen. These controls do not assert any
positive-measure overlap of named tiles.
Pre-code GO: `docs/c4-finite-cut-count.md`, following-increment decision,
and its linked cell-packing literature review.
-/

noncomputable section

open Set Psc.MadicFundamentalCell

namespace Psc.MadicFundamentalCellControls

/-- The first original integer basis vector. -/
def firstBasis : Int3 := ![1, 0, 0]

/-- The product-order interval is bounded, but its upper coordinate faces
give two distinct original integer representatives and overlapping translates. -/
theorem product_order_interval_loses_uniqueness :
    intCast firstBasis ∈ Set.Ico (0 : Real3) 1 ∧
      intCast firstBasis ∉ coordinateCube ∧ firstBasis ≠ 0 ∧
      ¬ Disjoint (Set.Ico (0 : Real3) 1)
        ((fun x : Real3 => intCast firstBasis + x) '' Set.Ico (0 : Real3) 1) := by
  have hmem : intCast firstBasis ∈ Set.Ico (0 : Real3) 1 := by
    constructor
    · intro i
      fin_cases i <;> norm_num [firstBasis, intCast]
    · apply lt_of_le_not_ge
      · intro i
        fin_cases i <;> norm_num [firstBasis, intCast]
      · intro h
        have hi := h (1 : Fin 3)
        norm_num [firstBasis, intCast] at hi
  have hzero : (0 : Real3) ∈ Set.Ico (0 : Real3) 1 := by
    refine ⟨le_rfl, lt_of_le_not_ge ?_ ?_⟩
    · intro i
      norm_num
    · intro h
      have hi := h (0 : Fin 3)
      norm_num at hi
  refine ⟨hmem, ?_, ?_, ?_⟩
  · intro h
    have hi := (mem_coordinateCube _).mp h (0 : Fin 3)
    norm_num [firstBasis, intCast] at hi
  · intro h
    have hi := congrFun h (0 : Fin 3)
    norm_num [firstBasis] at hi
  · intro h
    exact Set.disjoint_left.mp h hmem ⟨0, hzero, add_zero _⟩

/-- Multiplication by two on the actual original integer lattice. -/
def doubling : Int3 →ₗ[ℤ] Int3 := (2 : ℤ) • LinearMap.id

/-- Its invertible real extension, with inverse multiplication by one half. -/
def realDoubling : Real3 ≃L[ℝ] Real3 :=
  Units.mk0 (2 : ℝ) (by norm_num) • ContinuousLinearEquiv.refl ℝ Real3

/-- The calibration preserves the required original integer/real binding. -/
theorem doubling_compatible (z : Int3) :
    realDoubling (intCast z) = intCast (doubling z) := by
  ext i
  simp [realDoubling, doubling, intCast]

/-- The deliberately mismatched version of the actual cell. When `r = q`,
this is definitionally `cell doubling realDoubling (refl ...) q`. -/
def mixedDepthCell (r q : ℕ) : Set (Real3 × MadicResidue.Carrier doubling) :=
  ((ContinuousLinearEquiv.refl ℝ Real3) '' ((realDoubling ^ r) '' coordinateCube)) ×ˢ
    ((MadicResidue.eval doubling q) ⁻¹' {0})

/-- Keeping a depth-one real cell but dropping the depth-one residue condition
causes an overlap by the nonzero original vector `(1,0,0)`. -/
theorem coarser_residue_translates_overlap :
    firstBasis ≠ 0 ∧
      ¬ Disjoint (mixedDepthCell 1 0)
        ((fun x => diagonal doubling (ContinuousLinearEquiv.refl ℝ Real3) firstBasis + x) ''
          mixedDepthCell 1 0) := by
  have hzeroCube : (0 : Real3) ∈ coordinateCube := by
    simp
  have hzero : (0 : Real3 × MadicResidue.Carrier doubling) ∈ mixedDepthCell 1 0 := by
    refine ⟨⟨0, ⟨0, hzeroCube, by simp⟩, by simp⟩, ?_⟩
    change MadicResidue.eval doubling 0 0 = 0
    exact map_zero _
  have hhalf : (fun i => (intCast firstBasis i) / 2) ∈ coordinateCube := by
    rw [mem_coordinateCube]
    intro i
    fin_cases i <;> norm_num [firstBasis, intCast]
  have hreal : realDoubling (fun i => (intCast firstBasis i) / 2) =
      intCast firstBasis := by
    ext i
    simp [realDoubling]
    ring
  have hmem : diagonal doubling (ContinuousLinearEquiv.refl ℝ Real3) firstBasis ∈
      mixedDepthCell 1 0 := by
    refine ⟨⟨intCast firstBasis, ⟨_, hhalf, ?_⟩, rfl⟩, ?_⟩
    · simpa only [pow_one] using hreal
    · exact MadicResidue.quotient_zero_level doubling firstBasis
  refine ⟨?_, ?_⟩
  · intro h
    have hi := congrFun h (0 : Fin 3)
    norm_num [firstBasis] at hi
  · intro h
    exact Set.disjoint_left.mp h hmem ⟨0, hzero, add_zero _⟩

/-- The basis vector is nonzero in the genuine depth-one quotient of `2I`. -/
theorem firstBasis_nonzero_depth_one :
    MadicResidue.eval doubling 1 (MadicResidue.star doubling firstBasis) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := (MadicResidue.eval_one_star_eq_zero_iff doubling firstBasis).mp h
  have hi := congrFun hz (0 : Fin 3)
  change 2 * z 0 = 1 at hi
  omega

/-- Keeping the unit real cube but imposing the depth-one residue kernel
loses coverage of `(0, star (1,0,0))` under the original diagonal action. -/
theorem finer_residue_loses_coverage :
    ¬ ∃ z : Int3,
      (0, MadicResidue.star doubling firstBasis) -
          diagonal doubling (ContinuousLinearEquiv.refl ℝ Real3) z ∈ mixedDepthCell 0 1 := by
  rintro ⟨z, hz⟩
  have hreal : -intCast z ∈ coordinateCube := by
    rcases hz.1 with ⟨_, ⟨u, hu, rfl⟩, heq⟩
    rw [pow_zero] at heq
    have hu_eq : u = -intCast z := by
      simpa [show (1 : Real3 ≃L[ℝ] Real3) = ContinuousLinearEquiv.refl ℝ Real3 from rfl]
        using heq
    exact hu_eq ▸ hu
  have hzeroCube : (0 : Real3) ∈ coordinateCube := by simp
  have hz0 : z = 0 := by
    have hneg : -z = 0 := cube_integer_difference_zero hreal hzeroCube (by simp)
    simpa using hneg
  have hres := hz.2
  change MadicResidue.eval doubling 1
    (MadicResidue.star doubling firstBasis - MadicResidue.star doubling z) = 0 at hres
  rw [hz0, map_zero, sub_zero] at hres
  exact firstBasis_nonzero_depth_one hres

end Psc.MadicFundamentalCellControls
