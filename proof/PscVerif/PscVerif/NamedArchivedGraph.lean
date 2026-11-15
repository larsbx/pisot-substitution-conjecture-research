import PscVerif.NamedSharpDigits
import PscVerif.NamedSharpBox
import PscVerif.NamedInverseDecoder
import PscVerif.NamedArchivedGraphRefinement

/-!
# Original named geometry at the archived finite-table boundary

The complete digit proof discharges the original sharp-box exclusion
hypothesis. The exact residue decoder authenticates the matrix-adic
exclusion. The original named tile equations, compactness and product-Haar
scaling then feed the existing contraction consumer through literal rows.

The remaining finite premises are the source-bound typed table, exhaustive
candidate closure, exact root/discovery records and accepted potential.
The native/oracle receipt is not silently cast to these Lean proof terms.
No equality with all noncomputable strict packets or positive root measure
is inferred.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.NamedArchivedGraph

open Set MeasureTheory
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Psc.OccurrencePiece Psc.OccurrenceResidue Psc.OccurrenceAdmissibility
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar
open Psc.ArchivedGraphRefinement
open PscVerif.OverlapContraction
open Matrix

/-- A selected pair keeps the original parent words and both full marks;
only its offset is decoded by the proved exact integer inverse. -/
def decodedCandidate (fixture : Fin 2) {p : Packet}
    (d : SelectedPair (iterateImages (substitution fixture) 2) p) : Packet :=
  pairTarget d (NamedInverseDecoder.inverse (pairRhs d))

/-- Every actual integral inverse occurrence is exactly its finite selected
pair's decoded candidate, with the authentic residue check accepted. -/
theorem decodedCandidate_of_occurrence (fixture : Fin 2) {p u : Packet}
    (e : InverseOccurrence (iterateImages (substitution fixture) 2) p u) :
    NamedInverseDecoder.check (pairRhs (pairOfInverse e)) = true ∧
      decodedCandidate fixture (pairOfInverse e) = u := by
  obtain ⟨hc, hd⟩ := NamedInverseDecoder.occurrence_offset fixture e
  refine ⟨hc, ?_⟩
  unfold decodedCandidate
  have hd' : u.delta = NamedInverseDecoder.inverse (pairRhs (pairOfInverse e)) := hd
  rw [← hd']
  exact pairTarget_ofInverse e

/-- This remaining closure obligation quantifies only finite literal pairs,
with a unique offset per pair. No unbounded packet search is required. -/
def DecodedCandidatesClosed (fixture : Fin 2) {n : ℕ} (states : Fin n → Packet) : Prop :=
  ∀ i (d : SelectedPair (iterateImages (substitution fixture) 2) (states i)),
    NamedInverseDecoder.check (pairRhs d) = true →
    NamedSharpBox.admitted (decodedCandidate fixture d) →
    decodedCandidate fixture d ∈ orderedLift states

/-- Exhausting the finite decoded candidate list is equivalent to the
unrestricted actual inverse-occurrence closure needed by the consumer. -/
theorem candidateClosed_iff_decoded (fixture : Fin 2) {n : ℕ}
    (states : Fin n → Packet) :
    CandidateClosed (iterateImages (substitution fixture) 2) states
      NamedSharpBox.admitted ↔ DecodedCandidatesClosed fixture states := by
  constructor
  · intro closed i d hc ha
    have hy : incidenceZ (iterateImages (substitution fixture) 2) *ᵥ
        NamedInverseDecoder.inverse (pairRhs d) = pairRhs d := by
      rw [incidenceZ_iterateImages, incidence_eq]
      exact NamedInverseDecoder.inverse_equation _ ((NamedInverseDecoder.check_iff _).mp hc)
    exact closed i (decodedCandidate fixture d)
      (pairLift d (NamedInverseDecoder.inverse (pairRhs d)) hy) ha
  · intro closed i u e ha
    obtain ⟨hc, hu⟩ := decodedCandidate_of_occurrence fixture e
    have hm := closed i (pairOfInverse e) hc (by simpa only [hu] using ha)
    simpa only [hu] using hm

/-- The sharp digit premise is discharged by complete source-bound kernel arithmetic. -/
theorem digits_authenticated (fixture : Fin 2) : NamedSharpBox.DigitsBound fixture :=
  NamedSharpDigits.mark_coordinate_bound fixture

/-- Every actual named tile point lies in the original `(16,8)` box. -/
theorem tile_box (fixture : Fin 2) (letter : Fin 3)
    (x : Ambient (substitution fixture) Stable) (hx : x ∈ tiles fixture letter) :
    |x.1 0| ≤ 16 ∧ |x.1 1| ≤ 8 :=
  NamedSharpBox.tile_box_of_digits fixture (digits_authenticated fixture) letter x hx

/-- All geometric admission hypotheses are discharged for the historical
strict interval predicate; touching or uncertain candidates remain admitted. -/
theorem admission_sound (fixture : Fin 2) :
    AdmissionSound (ambientStar (substitution fixture) piZ) (tiles fixture)
      NamedSharpBox.admitted :=
  NamedSharpBox.nonempty_admitted_of_digits fixture (digits_authenticated fixture)

/-- Every geometrically excluded original overlap is empty. -/
theorem excluded_overlap_empty (fixture : Fin 2) (p : Packet)
    (reject : NamedSharpBox.Reject p.delta) :
    overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p = ∅ :=
  NamedSharpBox.overlap_empty_of_reject fixture (digits_authenticated fixture) p reject

/-- Rates stay indexed by the original literal substitutions. -/
def archivedNumerator (fixture : Fin 2) : ℕ := ![99, 101] fixture

theorem archivedNumerator_cases (fixture : Fin 2) :
    archivedNumerator fixture = 99 ∨ archivedNumerator fixture = 101 := by
  fin_cases fixture <;> decide

/-- A source-bound typed table refines exactly the nonempty part of the
original rooted ancestry. Completeness includes all intermediate ancestors
at every finite depth. All geometric premises are proved above. -/
theorem rooted_nonempty_domain_iff (fixture : Fin 2) {n : ℕ}
    (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution fixture) 2) states cert)
    (closed : DecodedCandidatesClosed fixture states)
    (rootID : Fin 3 → Fin n) (rootBound : ∀ i, states (rootID i) = archivedRoot i)
    (discovery : TableDiscovery table.row ArchivedRoot) (p : Packet) :
    (p ∈ orderedLift states ∧
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p).Nonempty) ↔
    (Ancestry (iterateImages (substitution fixture) 2) ArchivedRoot p ∧
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p).Nonempty) :=
  named_rooted_nonempty_domain_iff fixture states cert table NamedSharpBox.admitted
    (admission_sound fixture) ((candidateClosed_iff_decoded fixture states).mpr closed)
    rootID rootBound discovery p

/-- The historical integer potential can feed `OverlapContraction` on this
same table. Its finite proof terms remain explicit; no numeric replay is
substituted for a Lean table proof. -/
theorem null_of_source_bound_table (fixture : Fin 2)
    (ν : Measure (H (substitution fixture))) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    {n : ℕ} (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution fixture) 2) states cert)
    (closed : DecodedCandidatesClosed fixture states)
    (accepted : cert.check = true)
    (num : cert.numerator = archivedNumerator fixture) (den : cert.denominator = 20)
    (rootID : Fin 3 → Fin n) :
    ∀ i, (volume.prod ν)
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) (states i)) = 0 := by
  letI : Nonempty (Fin n) := ⟨rootID 0⟩
  exact named_archived_null fixture ν states cert table NamedSharpBox.admitted
    (admission_sound fixture) ((candidateClosed_iff_decoded fixture states).mpr closed) accepted
    (by rw [num]; exact archivedNumerator_cases fixture) den

/-- In particular the exact three original zero-offset roots are null when
the same source-bound table and integer certificate are instantiated. -/
theorem original_roots_null_of_table (fixture : Fin 2)
    (ν : Measure (H (substitution fixture))) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    {n : ℕ} (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution fixture) 2) states cert)
    (closed : DecodedCandidatesClosed fixture states)
    (accepted : cert.check = true)
    (num : cert.numerator = archivedNumerator fixture) (den : cert.denominator = 20)
    (rootID : Fin 3 → Fin n) (rootBound : ∀ i, states (rootID i) = archivedRoot i) :
    ∀ i, (volume.prod ν)
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) (archivedRoot i)) = 0 := by
  intro i
  simpa only [rootBound i] using
    null_of_source_bound_table fixture ν states cert table closed accepted num den rootID (rootID i)

/-- Nullity extends to every original literal inverse ancestor, at arbitrary
finite depth. Empty ancestors may be absent from the finite table. -/
theorem all_original_ancestors_null_of_table (fixture : Fin 2)
    (ν : Measure (H (substitution fixture))) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    {n : ℕ} (states : Fin n → Packet) (cert : Certificate n)
    (table : TableBinding (iterateImages (substitution fixture) 2) states cert)
    (closed : DecodedCandidatesClosed fixture states)
    (accepted : cert.check = true)
    (num : cert.numerator = archivedNumerator fixture) (den : cert.denominator = 20)
    (rootID : Fin 3 → Fin n) (rootBound : ∀ i, states (rootID i) = archivedRoot i)
    (discovery : TableDiscovery table.row ArchivedRoot)
    (p : Packet) (hp : Ancestry (iterateImages (substitution fixture) 2) ArchivedRoot p) :
    (volume.prod ν)
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p) = 0 := by
  letI : Nonempty (Fin n) := ⟨rootID 0⟩
  exact named_archived_ancestry_null fixture ν states cert table NamedSharpBox.admitted
    (admission_sound fixture) ((candidateClosed_iff_decoded fixture states).mpr closed)
    rootID rootBound discovery accepted
    (by rw [num]; exact archivedNumerator_cases fixture) den p hp

end Psc.NamedArchivedGraph
