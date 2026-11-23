import PscVerif.C4FamilySymbolicMeasureUniqueness

/-!
# The literal family spectrum for any invariant probability

The canonical measure is not introduced as another name for `wordMeasure`.
Instead, an arbitrary Borel probability is identified by the independently
proved uniqueness theorem, and the existing complex L² spectral endpoint is
transported through that explicit equality. The carrier is the actual legal
two-sided word shift, and the parameter range remains `k ≥ 2`.

Source decision: `docs/c4-family-canonical-measure-2026-11-23.md`.
-/

namespace Psc.C4FamilyCanonicalSpectrum

open MeasureTheory
open scoped Psc.C4FamilySymbolicSpectrum
open Psc.C4FamilySymbolicLanguage (SymbolicHull shift)
open Psc.C4FamilySymbolicSpectrum (wordMeasure measurePreserving_wordShift
  pureDiscrete_shift)
open Psc.C4FamilySymbolicMeasureUniqueness (invariant_probability_eq_wordMeasure)

variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)

include hk₂

/-- Explicit measure transport of the previously proved spectral endpoint.
The equality is an input here, separate from its uniqueness proof. -/
theorem pureDiscrete_shift_of_measure_eq
    (μ : Measure (SymbolicHull k hk))
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ)
    (hEq : μ = wordMeasure k hk hk₂) :
    (Submodule.span ℂ {v : Lp ℂ 2 μ |
      v ≠ 0 ∧ ∃ z : ℂ,
        Lp.compMeasurePreserving (shift (k := k) (hk := hk)) hμ v = z • v}
    ).topologicalClosure = ⊤ := by
  subst μ
  exact pureDiscrete_shift k hk hk₂

/-- Every invariant Borel probability on the literal legal word shift has
the same pure discrete complex L² spectrum. This includes an independently
defined canonical probability once its probability and invariance proofs
are supplied. -/
theorem pureDiscrete_shift_of_invariant_probability
    (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ) :
    (Submodule.span ℂ {v : Lp ℂ 2 μ |
      v ≠ 0 ∧ ∃ z : ℂ,
        Lp.compMeasurePreserving (shift (k := k) (hk := hk)) hμ v = z • v}
    ).topologicalClosure = ⊤ := by
  exact pureDiscrete_shift_of_measure_eq k hk hk₂ μ hμ
    (invariant_probability_eq_wordMeasure k hk hk₂ μ hμ)

/-- Unique existence is quantified over all Borel measures on the actual
legal symbolic hull, with both normalization and invariance explicit. -/
theorem existsUnique_invariant_probability :
    ∃! μ : Measure (SymbolicHull k hk),
      IsProbabilityMeasure μ ∧
        MeasurePreserving (shift (k := k) (hk := hk)) μ μ := by
  refine ⟨wordMeasure k hk hk₂,
    ⟨inferInstance, measurePreserving_wordShift k hk hk₂⟩, ?_⟩
  intro μ hμ
  let : IsProbabilityMeasure μ := hμ.1
  exact invariant_probability_eq_wordMeasure k hk hk₂ μ hμ.2

end Psc.C4FamilyCanonicalSpectrum
