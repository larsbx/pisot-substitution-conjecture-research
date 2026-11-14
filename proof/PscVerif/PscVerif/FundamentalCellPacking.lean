import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Finite packing of additive fundamental cells

The acting indices are retained throughout the finite count.  Equal mass comes
from fundamental domains for one invariant action; the rectangle estimate uses
an explicit measurable containing set, with no measurability requirement on an
intermediate sum of internal sets.  A measure-preserving coordinate view allows
the physical/stable product to be reassociated without changing the action.
-/

namespace Psc.FundamentalCellPacking

open MeasureTheory Set Function
open scoped ENNReal Pointwise

section InvariantAction

variable {Γ α ι : Type*} [AddGroup Γ] [MeasurableSpace α] [AddAction Γ α]
    [MeasurableConstVAdd Γ α] {μ : Measure α} [VAddInvariantMeasure Γ α μ]

/-- Finite additivity for the original acting indices and one translated cell.
Only the translates indexed by `Z` need to be almost everywhere disjoint. -/
theorem measure_finite_vadd (Z : Finset Γ) {F : Set α}
    (hF : NullMeasurableSet F μ)
    (hd : Set.Pairwise (Z : Set Γ) (AEDisjoint μ on fun z => z +ᵥ F)) :
    μ (⋃ z ∈ Z, z +ᵥ F) = (Z.card : ℝ≥0∞) * μ F := by
  rw [measure_biUnion_finset₀ hd (fun z _ => hF.vadd z)]
  simp [measure_vadd, nsmul_eq_mul]

/-- A reference fundamental domain supplies the exact common mass at every
finite set of indices. Coverage is used in the equality of domain measures. -/
theorem measure_finite_fundamentalDomains [Countable Γ] (Z : Finset Γ)
    {F F₀ : Set α} (hF : IsAddFundamentalDomain Γ F μ)
    (hF₀ : IsAddFundamentalDomain Γ F₀ μ) :
    μ (⋃ z ∈ Z, z +ᵥ F) = (Z.card : ℝ≥0∞) * μ F₀ := by
  rw [measure_finite_vadd Z hF.nullMeasurableSet
    (fun _ _ _ _ hne => hF.aedisjoint hne), hF.measure_eq hF₀]

/-- For one nonzero invariant measure, a family of fundamental domains has a
positive finite common real mass as soon as one reference domain has finite
mass. No determinant or normalization of that mass is asserted. -/
theorem exists_positive_common_mass [Countable Γ] (F : ι → Set α) (q₀ : ι)
    (hF : ∀ q, IsAddFundamentalDomain Γ (F q) μ) (hμ : μ ≠ 0)
    (hfinite : μ (F q₀) ≠ ∞) :
    ∃ c : ℝ, 0 < c ∧ ∀ q, μ (F q) = ENNReal.ofReal c := by
  refine ⟨μ.real (F q₀), ?_, ?_⟩
  · exact ENNReal.toReal_pos
      (IsAddFundamentalDomain.measure_ne_zero hμ (hF q₀)) hfinite
  · intro q
    rw [(hF q).measure_eq (hF q₀), measureReal_def,
      ENNReal.ofReal_toReal hfinite]

/-- A finite family of disjoint translates cannot have greater total mass
than its containing set. The bound is on the original index cardinality. -/
theorem card_mul_mass_le_of_enclosure (Z : Finset Γ) {F R : Set α}
    (hF : NullMeasurableSet F μ)
    (hd : Set.Pairwise (Z : Set Γ) (AEDisjoint μ on fun z => z +ᵥ F))
    {c : ℝ} (hc : 0 ≤ c) (hmass : μ F = ENNReal.ofReal c)
    (hfinite : μ R ≠ ∞) (henclose : ∀ z ∈ Z, z +ᵥ F ⊆ R) :
    c * (Z.card : ℝ) ≤ μ.real R := by
  have hsubset : (⋃ z ∈ Z, z +ᵥ F) ⊆ R := by
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨z, hz, hzx⟩
    exact henclose z hz hzx
  have hbound := ENNReal.toReal_mono hfinite (measure_mono hsubset)
  rw [measure_finite_vadd Z hF hd, hmass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] at hbound
  simpa [measureReal_def, mul_comm] using hbound

end InvariantAction

section Rectangle

variable {Γ α Y : Type*} [AddGroup Γ] [MeasurableSpace α] [AddAction Γ α]
    [MeasurableConstVAdd Γ α] {μa : Measure α} [VAddInvariantMeasure Γ α μa]
    [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

/-- Rectangle packing after any measure-preserving coordinate view. In the
matrix-adic application the view only reassociates the physical, stable and
compact coordinates. The target `O` is fixed and measurable of finite mass. -/
theorem card_mul_mass_le_rectangle (Z : Finset Γ) {F : Set α}
    (hF : IsAddFundamentalDomain Γ F μa) {c : ℝ} (hc : 0 ≤ c)
    (hmass : μa F = ENNReal.ofReal c) {view : α → ℝ × Y}
    (hview : MeasurePreserving view μa (volume.prod μ))
    {X L : ℝ} (hX : 0 ≤ X) (hL : 0 ≤ L) {O : Set Y}
    (hO : MeasurableSet O) (hOfinite : μ O ≠ ∞)
    (henclose : ∀ z ∈ Z, z +ᵥ F ⊆ view ⁻¹' (Icc 0 (X + L) ×ˢ O)) :
    c * (Z.card : ℝ) ≤ (X + L) * μ.real O := by
  have hrect : MeasurableSet (Icc (0 : ℝ) (X + L) ×ˢ O) :=
    measurableSet_Icc.prod hO
  have hfinite : μa (view ⁻¹' (Icc 0 (X + L) ×ˢ O)) ≠ ∞ := by
    rw [hview.measure_preimage hrect.nullMeasurableSet,
      Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOfinite
  have hbound := card_mul_mass_le_of_enclosure Z hF.nullMeasurableSet
    (fun _ _ _ _ hne => hF.aedisjoint hne) hc hmass hfinite henclose
  rw [hview.measureReal_preimage hrect.nullMeasurableSet, measureReal_prod_prod,
    Real.volume_real_Icc_of_le (add_nonneg hX hL), sub_zero] at hbound
  exact hbound

end Rectangle

section Strip

variable {Γ α Y : Type*} [AddGroup Γ] [AddAction Γ α] [AddCommGroup Y]

/-- The strip and cell-width hypotheses establish the rectangle enclosure
pointwise. `U` and `V` need not be measurable, and their sum is never measured. -/
theorem finite_vadd_subset_rectangle (Z : Finset Γ) {F : Set α}
    {view : α → ℝ × Y} {diagonal : Γ → ℝ × Y}
    (hview_add : ∀ z x, view (z +ᵥ x) = diagonal z + view x)
    {X L : ℝ} {U V O : Set Y}
    (hstrip : ∀ z ∈ Z, 0 ≤ (diagonal z).1 ∧ (diagonal z).1 < X ∧
      (diagonal z).2 ∈ U)
    (hcell : ∀ x ∈ F, 0 ≤ (view x).1 ∧ (view x).1 ≤ L ∧ (view x).2 ∈ V)
    (hinside : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ O) :
    ∀ z ∈ Z, z +ᵥ F ⊆ view ⁻¹' (Icc 0 (X + L) ×ˢ O) := by
  intro z hz y hy
  rcases hy with ⟨x, hx, rfl⟩
  obtain ⟨hz0, hzX, hzU⟩ := hstrip z hz
  obtain ⟨hx0, hxL, hxV⟩ := hcell x hx
  change view (z +ᵥ x) ∈ Icc 0 (X + L) ×ˢ O
  rw [hview_add]
  exact ⟨⟨add_nonneg hz0 hx0, (add_le_add hzX.le hxL)⟩,
    hinside _ hzU _ hxV⟩

variable [MeasurableSpace α] [MeasurableConstVAdd Γ α] {μa : Measure α}
    [VAddInvariantMeasure Γ α μa] [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

/-- The finite rectangle estimate with the actual point-strip and cell-width
premises exposed. In particular, no count of the image under `diagonal` or
`view` is substituted for the original finite index count. -/
theorem card_mul_mass_le_rectangle_of_strip (Z : Finset Γ) {F : Set α}
    (hF : IsAddFundamentalDomain Γ F μa) {c : ℝ} (hc : 0 ≤ c)
    (hmass : μa F = ENNReal.ofReal c) {view : α → ℝ × Y}
    (hview : MeasurePreserving view μa (volume.prod μ)) {diagonal : Γ → ℝ × Y}
    (hview_add : ∀ z x, view (z +ᵥ x) = diagonal z + view x)
    {X L : ℝ} (hX : 0 ≤ X) (hL : 0 ≤ L) {U V O : Set Y}
    (hO : MeasurableSet O) (hOfinite : μ O ≠ ∞)
    (hstrip : ∀ z ∈ Z, 0 ≤ (diagonal z).1 ∧ (diagonal z).1 < X ∧
      (diagonal z).2 ∈ U)
    (hcell : ∀ x ∈ F, 0 ≤ (view x).1 ∧ (view x).1 ≤ L ∧ (view x).2 ∈ V)
    (hinside : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ O) :
    c * (Z.card : ℝ) ≤ (X + L) * μ.real O := by
  exact card_mul_mass_le_rectangle Z hF hc hmass hview hX hL hO hOfinite
    (finite_vadd_subset_rectangle Z hview_add hstrip hcell hinside)

end Strip

end Psc.FundamentalCellPacking
