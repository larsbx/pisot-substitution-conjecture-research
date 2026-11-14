import PscVerif.MadicFundamentalCell
import PscVerif.FundamentalCellPacking
import PscVerif.NamedFullChart
import PscVerif.NamedCellBounds
import PscVerif.NamedPrefixCompact
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Fundamental cells in the named physical, stable and matrix-adic space

The two literal substitutions retain their own original inverse-limit
carriers. Their common real incidence and the full physical/stable chart
discharge the generic cell hypotheses. Product Haar measure is taken in
the physical and stable coordinates themselves: the chart is not assumed
to preserve canonical real volume. The common positive finite cell mass
is obtained from exact fundamental domains for the same integer action.

Pre-code gate: `docs/c4-finite-cut-count.md`, following-increment decision,
committed in `d6d6ba2331bc`.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Psc.NamedFundamentalCell

open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedFullChart
open Psc.OccurrenceResidue Psc.OccurrenceTransport

abbrev Int3 := MadicFundamentalCell.Int3
abbrev M (f : Fin 2) := incidenceLinear (substitution f)
abbrev H (f : Fin 2) := MadicResidue.Carrier (M f)
abbrev Full (f : Fin 2) := (ℝ × Stable) × H f
abbrev Internal (f : Fin 2) := Stable × H f

def cell (f : Fin 2) (q : ℕ) : Set (Full f) :=
  MadicFundamentalCell.cell (M f) realIncidence fullChart q

theorem compatible (f : Fin 2) (z : Int3) :
    realIncidence (MadicFundamentalCell.intCast z) =
      MadicFundamentalCell.intCast (M f z) := by
  change realIncidence (castZ z) = castZ (incidenceLinear (substitution f) z)
  rw [incidenceLinear_apply, incidence_eq]
  exact realIncidence_castZ z

/-- This view only changes parentheses in the product. -/
def view (f : Fin 2) : Full f ≃ᵐ (ℝ × Internal f) :=
  MeasurableEquiv.prodAssoc

def diagonal (f : Fin 2) (z : Int3) : ℝ × Internal f :=
  (offset physicalRow z, ambientStar (substitution f) piZ z)

theorem view_diagonal (f : Fin 2) (z : Int3) :
    view f (MadicFundamentalCell.diagonal (M f) fullChart z) = diagonal f z := rfl

theorem view_add (f : Fin 2) (z : Int3) (x : Full f) :
    letI := MadicFundamentalCell.diagonalAction (M f) fullChart
    view f (z +ᵥ x) = diagonal f z + view f x := rfl

abbrev fullMeasure (f : Fin 2) (ν : Measure (H f)) : Measure (Full f) :=
  ((volume : Measure ℝ).prod (volume : Measure Stable)).prod ν

abbrev internalMeasure (f : Fin 2) (ν : Measure (H f)) : Measure (Internal f) :=
  (volume : Measure Stable).prod ν

variable (f : Fin 2) (ν : Measure (H f)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]

/-- Translation invariance belongs to the actual target product measure. -/
theorem fullMeasure_isAddLeftInvariant : (fullMeasure f ν).IsAddLeftInvariant := by
  change (((volume : Measure ℝ).prod (volume : Measure Stable)).prod ν).IsAddLeftInvariant
  exact Measure.prod.instIsAddLeftInvariant

omit [ν.IsAddHaarMeasure] in
theorem view_measurePreserving :
    MeasurePreserving (view f) (fullMeasure f ν)
      ((volume : Measure ℝ).prod (internalMeasure f ν)) :=
  measurePreserving_prodAssoc volume volume ν

theorem cell_measurableSet (q : ℕ) : MeasurableSet (cell f q) :=
  MadicFundamentalCell.cell_measurableSet (M f) realIncidence fullChart q

omit [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] in
theorem cell_isAddFundamentalDomain (q : ℕ) :
    letI := MadicFundamentalCell.diagonalAction (M f) fullChart
    IsAddFundamentalDomain Int3 (cell f q) (fullMeasure f ν) :=
  MadicFundamentalCell.isAddFundamentalDomain (M f) realIncidence fullChart
    (compatible f) q (fullMeasure f ν)

theorem cell_measure_finite (q : ℕ) : (fullMeasure f ν) (cell f q) ≠ ∞ := by
  have hcompact := MadicFundamentalCell.compactContainer_isCompact
    (M f) realIncidence fullChart (compatible f) q
  exact (lt_of_le_of_lt (measure_mono
    (MadicFundamentalCell.cell_subset_compactContainer (M f) realIncidence fullChart q))
      hcompact.measure_lt_top).ne

/-- The actual canonical physical/stable product measure has one strictly
positive finite real cell mass, independent of the residue depth. -/
theorem exists_positive_common_mass :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, (fullMeasure f ν) (cell f q) = ENNReal.ofReal c := by
  let := fullMeasure_isAddLeftInvariant f ν
  let := MadicFundamentalCell.diagonalAction (M f) fullChart
  let := MadicFundamentalCell.diagonal_measurableConstVAdd (M f) fullChart
  let := MadicFundamentalCell.diagonal_vaddInvariantMeasure (M f) fullChart (fullMeasure f ν)
  exact FundamentalCellPacking.exists_positive_common_mass (cell f) 0
    (cell_isAddFundamentalDomain f ν) (NeZero.ne (fullMeasure f ν))
    (cell_measure_finite f ν 0)

/-- A measurable rectangle bounds the mass of any finite collection of
original integer translates of an actual named cell. -/
theorem finite_packing (q : ℕ) (Z : Finset Int3) {c X L : ℝ}
    (hc : 0 ≤ c) (hmass : (fullMeasure f ν) (cell f q) = ENNReal.ofReal c)
    (hX : 0 ≤ X) (hL : 0 ≤ L) {U V O : Set (Internal f)}
    (hO : MeasurableSet O) (hOfinite : (internalMeasure f ν) O ≠ ∞)
    (hstrip : ∀ z ∈ Z, 0 ≤ (diagonal f z).1 ∧ (diagonal f z).1 < X ∧
      (diagonal f z).2 ∈ U)
    (hcell : ∀ x ∈ cell f q, 0 ≤ (view f x).1 ∧ (view f x).1 ≤ L ∧
      (view f x).2 ∈ V)
    (hinside : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ O) :
    c * (Z.card : ℝ) ≤ (X + L) * (internalMeasure f ν).real O := by
  let := fullMeasure_isAddLeftInvariant f ν
  let := MadicFundamentalCell.diagonalAction (M f) fullChart
  let := MadicFundamentalCell.diagonal_measurableConstVAdd (M f) fullChart
  let := MadicFundamentalCell.diagonal_vaddInvariantMeasure (M f) fullChart (fullMeasure f ν)
  exact FundamentalCellPacking.card_mul_mass_le_rectangle_of_strip Z
    (cell_isAddFundamentalDomain f ν q) hc hmass (view_measurePreserving f ν)
    (view_add f) hX hL hO hOfinite hstrip hcell hinside

/-- The named cell supplies its own physical width. Only its internal
containment and the target enclosure remain as geometric premises. -/
theorem finite_packing_of_internal_subset (q : ℕ) (Z : Finset Int3) {c X : ℝ}
    (hc : 0 ≤ c) (hmass : (fullMeasure f ν) (cell f q) = ENNReal.ofReal c)
    (hX : 0 ≤ X) {U V O : Set (Internal f)}
    (hO : MeasurableSet O) (hOfinite : (internalMeasure f ν) O ≠ ∞)
    (hstrip : ∀ z ∈ Z, 0 ≤ (diagonal f z).1 ∧ (diagonal f z).1 < X ∧
      (diagonal f z).2 ∈ U)
    (hinternal : ∀ x ∈ cell f q, (view f x).2 ∈ V)
    (hinside : ∀ u ∈ U, ∀ v ∈ V, u + v ∈ O) :
    c * (Z.card : ℝ) ≤
      (X + NamedCellBounds.physicalWidth q) * (internalMeasure f ν).real O := by
  apply finite_packing f ν q Z hc hmass hX
    (NamedCellBounds.physicalWidth_nonneg q) hO hOfinite hstrip _ hinside
  intro x hx
  obtain ⟨h0, hwidth⟩ := NamedCellBounds.cell_physical_bounds (M f) q hx
  exact ⟨h0, hwidth, hinternal x hx⟩

/-- One positive mass works at every depth. After fixing an internal
neighborhood, every sufficiently deep block cell yields the finite packing
bound for any finite set of original integer indices in the stated strip.
The neighborhood and the cell depth are chosen before the strip length. -/
theorem exists_positive_uniform_packing :
    ∃ c : ℝ, 0 < c ∧
      (∀ q : ℕ, (fullMeasure f ν) (cell f q) = ENNReal.ofReal c) ∧
      ∀ (V : Set (Internal f)), V ∈ 𝓝 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ (Z : Finset Int3) (X : ℝ), 0 ≤ X →
            ∀ (U O : Set (Internal f)), MeasurableSet O →
              (internalMeasure f ν) O ≠ ∞ →
              (∀ z ∈ Z, 0 ≤ (diagonal f z).1 ∧ (diagonal f z).1 < X ∧
                (diagonal f z).2 ∈ U) →
              (∀ u ∈ U, ∀ v ∈ V, u + v ∈ O) →
              c * (Z.card : ℝ) ≤
                (X + NamedCellBounds.physicalWidth (12 * n)) *
                  (internalMeasure f ν).real O := by
  obtain ⟨c, hc, hmass⟩ := exists_positive_common_mass f ν
  refine ⟨c, hc, hmass, ?_⟩
  intro V hV
  obtain ⟨N, hN⟩ := NamedCellBounds.eventually_cell_internal_mem (M f) hV
  refine ⟨N, ?_⟩
  intro n hn Z X hX U O hO hOfinite hstrip hinside
  exact finite_packing_of_internal_subset f ν (12 * n) Z hc.le (hmass (12 * n))
    hX hO hOfinite hstrip (hN n hn) hinside

end Psc.NamedFundamentalCell
