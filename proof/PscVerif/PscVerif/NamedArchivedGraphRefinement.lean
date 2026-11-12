import PscVerif.ArchivedGraphRefinement
import PscVerif.NamedOverlapHaar

/-!
# Named original geometry consumes the authenticated archived graph interface

The literal substitution power, original matrix-adic range detector, compact
prefix tiles and normalized product-Haar modulus are supplied by their proved
named constructions. The finite payload's literal binding, candidate closure,
rooted discovery and potential acceptance remain explicit inputs until their
serialized values are independently authenticated in Lean.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.ArchivedGraphRefinement

open Set MeasureTheory Matrix
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Psc.OccurrencePiece Psc.OccurrenceCover
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedFiniteCarrier
open Psc.NamedProductHaar Psc.OccurrenceResidue
open PscVerif.OverlapContraction
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

section Named

variable (f : Fin 2) (ν : Measure (H (substitution f)))
  [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]

local notation "T" => ambientAction (substitution f) B
local notation "star" => ambientStar (substitution f) piZ
local notation "E" => overlap star (tiles f)
local notation "μ" => (volume.prod ν)

/-- The period-two equation in exactly the action and source types used by
the finite graph consumer. No one-step equation or changed word is inferred. -/
theorem named_tileEquation_two :
    TileEquation (iterateImages (substitution f) 2) (T ^ 2) star (tiles f) := by
  exact tileEquation_even f 1

/-- The named source, literal two-step ancestry and the three original roots
are fixed.  Exact finite discovery plus complete candidate closure identifies
every genuine nonempty rooted geometric ancestor with the ordered table. -/
theorem named_rooted_nonempty_domain_iff {n : ℕ}
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (admitted : Packet → Prop) (sound : AdmissionSound star (tiles f) admitted)
    (closed : CandidateClosed (iterateImages (substitution f) 2) states admitted)
    (rootID : Fin 3 → Fin n) (rootBound : ∀ i, states (rootID i) = archivedRoot i)
    (discovery : TableDiscovery table.row ArchivedRoot) (p : Packet) :
    (p ∈ orderedLift states ∧ (E p).Nonempty) ↔
      (Ancestry (iterateImages (substitution f) 2) ArchivedRoot p ∧ (E p).Nonempty) :=
  table.rooted_nonempty_domain_iff (T ^ 2) star (tiles f)
    (block_action_injective f 2) (block_commute f 2)
    (named_tileEquation_two f) admitted sound closed
    ArchivedRoot archivedRoots_swap discovery (archivedRoots_complete states rootID rootBound) p

theorem named_rowPiece_scaling {n : ℕ} (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (i : Fin n) (e : Fin (cert.degree i)) :
    ENNReal.ofReal (beta ^ 2) * μ (table.rowPiece (T ^ 2) star (tiles f) i e) =
      μ (E (states (cert.target i e))) := by
  have cancel : ENNReal.ofReal (beta ^ 2) * (ENNReal.ofReal beta⁻¹) ^ 2 = 1 := by
    rw [ENNReal.ofReal_pow beta_pos.le, ← mul_pow,
      ← ENNReal.ofReal_mul beta_pos.le, mul_inv_cancel₀ beta_ne_zero]
    simp
  change ENNReal.ofReal (beta ^ 2) *
    μ ((fun x => (T ^ 2) x + star (slotTranslation (table.slot i e))) ''
      E (states (cert.target i e))) = _
  rw [measure_affine_power (substitution f) (incidence_eq f) ν 2, ← mul_assoc,
    cancel, one_mul]

/-- The named original geometry discharges action, residue, compactness,
tile and Haar hypotheses.  The remaining inputs are precisely admission
soundness, full candidate closure, literal row binding and integer acceptance. -/
theorem named_null_of_refinement {n : ℕ} [Nonempty (Fin n)]
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (admitted : Packet → Prop) (sound : AdmissionSound star (tiles f) admitted)
    (closed : CandidateClosed (iterateImages (substitution f) 2) states admitted)
    (accepted : cert.check = true)
    (gap : (cert.numerator : ℝ) < cert.denominator * beta ^ 2) :
    ∀ i, μ (E (states i)) = 0 := by
  apply cert.null_of_cover accepted μ (fun i => E (states i))
    (table.rowPiece (T ^ 2) star (tiles f)) (beta ^ 2) (sq_nonneg beta)
    (fun i => overlap_measure_finite f ν (states i))
  · intro i
    exact (table.overlap_eq_iUnion_rowPiece (T ^ 2) star (tiles f)
      (block_action_injective f 2) (block_commute f 2) (block_reflectsIntegralRange f 2)
      (named_tileEquation_two f) admitted sound closed i).le
  · exact fun i e => (named_rowPiece_scaling f ν states cert table i e).le
  · exact gap

/-- The named real root's already authenticated bracket gives the strict
historical spectral comparison; no floating-point input is used. -/
theorem named_beta_square_gap : (103 / 20 : ℝ) < beta ^ 2 := by
  have hlo : (22695 / 10000 : ℝ) ≤ beta := by
    apply le_trans _ beta_ge_lo
    norm_num [betaLo]
  nlinarith [beta_pos]

/-- Both original certificate rates retain their original common denominator;
the later 102/20 class certificate is not identified with either payload. -/
theorem named_archived_gap {n : ℕ} (cert : Certificate n)
    (num : cert.numerator = 99 ∨ cert.numerator = 101)
    (den : cert.denominator = 20) :
    (cert.numerator : ℝ) < cert.denominator * beta ^ 2 := by
  rcases num with h | h <;> rw [h, den] <;>
    norm_num <;> linarith [named_beta_square_gap]

theorem named_archived_null {n : ℕ} [Nonempty (Fin n)]
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (admitted : Packet → Prop) (sound : AdmissionSound star (tiles f) admitted)
    (closed : CandidateClosed (iterateImages (substitution f) 2) states admitted)
    (accepted : cert.check = true)
    (num : cert.numerator = 99 ∨ cert.numerator = 101)
    (den : cert.denominator = 20) : ∀ i, μ (E (states i)) = 0 :=
  named_null_of_refinement f ν states cert table admitted sound closed accepted
    (named_archived_gap cert num den)

/-- Track normalization preserves actual product-Haar measure by its proved
translation identity; the two overlap sets themselves need not be equal. -/
theorem named_overlap_swap_measure (p : Packet) : μ (E p.swap) = μ (E p) := by
  rw [overlap_swap_eq_translate]
  have ht := measure_affine_power (substitution f) (incidence_eq f) ν 0
    (-star p.delta) (E p)
  simpa only [pow_zero, AddMonoid.End.one_apply, one_mul, sub_eq_add_neg] using ht

theorem named_archived_orderedLift_null {n : ℕ} [Nonempty (Fin n)]
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (admitted : Packet → Prop) (sound : AdmissionSound star (tiles f) admitted)
    (closed : CandidateClosed (iterateImages (substitution f) 2) states admitted)
    (accepted : cert.check = true)
    (num : cert.numerator = 99 ∨ cert.numerator = 101) (den : cert.denominator = 20)
    (p : Packet) (hp : p ∈ orderedLift states) : μ (E p) = 0 := by
  have hz := named_archived_null f ν states cert table admitted sound closed accepted num den
  obtain ⟨i, rfl | rfl⟩ := (mem_orderedLift states p).mp hp
  · exact hz i
  · rw [named_overlap_swap_measure]
    exact hz i

/-- The authenticated rooted refinement extends the finite certificate's
nullity to every original literal inverse ancestor of the three roots.
Geometrically empty ancestors need not occur in the table. -/
theorem named_archived_ancestry_null {n : ℕ} [Nonempty (Fin n)]
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution f) 2) states cert)
    (admitted : Packet → Prop) (sound : AdmissionSound star (tiles f) admitted)
    (closed : CandidateClosed (iterateImages (substitution f) 2) states admitted)
    (rootID : Fin 3 → Fin n) (rootBound : ∀ i, states (rootID i) = archivedRoot i)
    (discovery : TableDiscovery table.row ArchivedRoot)
    (accepted : cert.check = true)
    (num : cert.numerator = 99 ∨ cert.numerator = 101) (den : cert.denominator = 20)
    (p : Packet) (hp : Ancestry (iterateImages (substitution f) 2) ArchivedRoot p) :
    μ (E p) = 0 := by
  by_cases hn : (E p).Nonempty
  · have hm := ((named_rooted_nonempty_domain_iff f states cert table admitted sound closed
      rootID rootBound discovery p).mpr ⟨hp, hn⟩).1
    exact named_archived_orderedLift_null f ν states cert table admitted sound closed
      accepted num den p hm
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]

end Named

end Psc.ArchivedGraphRefinement
