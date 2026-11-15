import PscVerif.ArchivedGraphRefinement
import PscVerif.NamedOverlapBalanceControls
import PscVerif.NamedPrefixCompact

/-!
# Direct controls for source-bound archived graph refinement

The controls exercise the actual literal interfaces: dropping or duplicating
one of two repeated occurrences fails positional exactness; reversing an
inverse equation changes its meaning; terminal membership omits intermediate
ancestry; equal incidence matrices do not authenticate literal source words;
an incorrect geometric enclosure cannot supply admission soundness.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.ArchivedGraphRefinementControls

open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceInverse
open Psc.OccurrenceGraphBinding Psc.OccurrencePiece Psc.OccurrenceCover
open Psc.OccurrenceMass Psc.NamedOverlapBalanceControls
open Psc.NamedPrefixCompact Psc.ArchivedGraphRefinement
open Matrix

def repeatedSlot (i : Fin 2) : Slot repeatedImages diagonal diagonal where
  targetSwapped := false
  topIndex := i
  bottomIndex := i
  packet_eq := (repeatedForward i).packet_eq

def oneState (_ : Fin 1) : Packet := diagonal

def omittedRow : OccurrenceGraphBinding.Row repeatedImages oneState 0 where
  degree := 1
  targetID := fun _ => 0
  slot := fun _ => repeatedSlot 0

/-- Two different actual positions share one endpoint; an endpoint-only
row necessarily omits one of the required positional records. -/
theorem omitted_positional_edge_rejected : ¬ omittedRow.Exact := by
  intro h
  obtain ⟨k, _, ht, _⟩ := h.2 diagonal (state_mem_orderedLift oneState 0)
    (1 : Fin 2) (1 : Fin 2) (repeatedForward 1).packet_eq
  change (0 : ℕ) = 1 at ht
  omega

def duplicatedRow : OccurrenceGraphBinding.Row repeatedImages oneState 0 where
  degree := 2
  targetID := fun _ => 0
  slot := fun _ => repeatedSlot 0

/-- Duplicating a genuine occurrence cannot repair the missing distinct one. -/
theorem duplicated_positional_edge_rejected : ¬ duplicatedRow.Exact := by
  intro h
  have bad : (0 : Fin 2) = 1 :=
    h.1 (show duplicatedRow.key (0 : Fin 2) = duplicatedRow.key (1 : Fin 2) from rfl)
  have := congrArg Fin.val bad
  norm_num at this

theorem parallel_target_keeps_distinct_addresses :
    (repeatedSlot 0).rawTarget = (repeatedSlot 1).rawTarget ∧
      (repeatedSlot 0).topIndex.val ≠ (repeatedSlot 1).topIndex.val := by
  exact ⟨rfl, by decide⟩

def along (z : ℤ) : Packet := ⟨0, 0, ![z, 0, 0]⟩

theorem along_digit (z : ℤ) :
    digitPacket repeatedImages (along z) (0 : Fin 2) (0 : Fin 2) = along (2 * z) := by
  apply packet_ext
  · rfl
  · rfl
  · funext a
    fin_cases a <;>
      simp [digitPacket, repeatedImages, along, markAt, incidenceZ,
        Psc.Incidence.inc, Psc.OccurrenceTransport.residual, parikhZ,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Actual forward/current and inverse/ancestor directions are not interchangeable. -/
theorem swapped_direction_rejected :
    digitPacket repeatedImages (along 1) (0 : Fin 2) (0 : Fin 2) = along 2 ∧
      digitPacket repeatedImages (along 2) (0 : Fin 2) (0 : Fin 2) ≠ along 1 := by
  constructor
  · simpa using along_digit 1
  · rw [along_digit]
    intro h
    have := congrArg (fun p : Packet => p.delta 0) h
    norm_num [along] at this

def alongInverse (z : ℤ) : InverseOccurrence repeatedImages (along (2 * z)) (along z) :=
  (⟨(0 : Fin 2), (0 : Fin 2), (along_digit z).symm⟩ :
    ForwardOccurrence repeatedImages (along z) (along (2 * z))).toInverse

def skippedMiddle : History repeatedImages 2 (along 4) :=
  ⟨⟨along 2, alongInverse 2⟩, ⟨⟨along 1, alongInverse 1⟩, ()⟩⟩

noncomputable def endpoints : Finset Packet := by
  classical
  exact {along 4, along 1}

/-- The terminal state can be present while an actual intermediate ancestor
is absent; endpoint checks cannot establish history completeness. -/
theorem terminal_membership_does_not_cover_history :
    historyTarget repeatedImages 2 (along 4) skippedMiddle ∈ endpoints ∧
      ¬ historyWithin repeatedImages endpoints 2 (along 4) skippedMiddle := by
  classical
  have h24 : along 2 ≠ along 4 := by
    intro h
    have := congrArg (fun p : Packet => p.delta 0) h
    norm_num [along] at this
  have h21 : along 2 ≠ along 1 := by
    intro h
    have := congrArg (fun p : Packet => p.delta 0) h
    norm_num [along] at this
  simp [historyTarget, historyWithin, skippedMiddle, endpoints, h24, h21]

/-- The two named sources have the same matrix, but the same parent and local
position select different letters.  An incidence digest is not source binding. -/
theorem same_matrix_different_literal_address :
    incidenceZ (substitution 0) = incidenceZ (substitution 1) ∧
      (digitPacket (iterateImages (substitution 0) 2) diagonal
        (1 : Fin 3) (1 : Fin 3)).top ≠
      (digitPacket (iterateImages (substitution 1) 2) diagonal
        (1 : Fin 3) (1 : Fin 3)).top := by
  exact ⟨(incidence_eq 0).trans (incidence_eq 1).symm, by decide⟩

def coordinateStar : (Fin 3 → ℤ) →+ ℝ where
  toFun z := z 0
  map_zero' := by simp
  map_add' x y := by simp

def separatedTiles (a : Fin 3) : Set ℝ := if a = 0 then {2} else {1}

def translatedPacket : Packet := ⟨0, 1, ![1, 0, 0]⟩

/-- A falsely small difference box excludes a genuinely nonempty overlap.
The sound-admission premise rejects it independently of finite graph checks. -/
theorem incorrect_box_rejected :
    ¬ AdmissionSound coordinateStar separatedTiles
      (fun p => |(p.delta 0 : ℝ)| ≤ 0) := by
  intro h
  have hx : (overlap coordinateStar separatedTiles translatedPacket).Nonempty := by
    refine ⟨2, ?_⟩
    norm_num [overlap, coordinateStar, separatedTiles, translatedPacket]
  have bad := h translatedPacket hx
  norm_num [translatedPacket] at bad

/-- A present root and a literal inverse witness do not certify an unrelated
state table containing only the root. The complete candidate check fails. -/
theorem graph_domain_mismatch_rejected :
    ¬ CandidateClosed repeatedImages (fun _ : Fin 1 => along 4) (fun _ => True) := by
  intro h
  have hm := h 0 (along 2) (alongInverse 2) trivial
  obtain ⟨i, hi | hi⟩ := (mem_orderedLift (fun _ : Fin 1 => along 4) (along 2)).mp hm
  · have := congrArg (fun p : Packet => p.delta 0) hi
    norm_num [along] at this
  · have := congrArg (fun p : Packet => p.delta 0) hi
    norm_num [along, Packet.swap] at this

end Psc.ArchivedGraphRefinementControls
