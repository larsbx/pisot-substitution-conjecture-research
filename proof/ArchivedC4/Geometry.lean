import Contraction
import PscVerif.NamedArchivedGraph

namespace ArchivedC4

open MeasureTheory
open Psc.OccurrenceInverse (iterateImages)
open Psc.OccurrenceResidue (ambientStar)
open Psc.OccurrencePiece (overlap)
open Psc.OccurrenceGraphBinding (TableDiscovery Row.targetID)
open Psc.ArchivedGraphRefinement
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar
open Psc.NamedArchivedGraph

def Packet.toGeometry (p : Packet) : Psc.OccurrenceTransport.Packet :=
  ⟨Fin.ofNat _ p.top, Fin.ofNat _ p.bottom, ![p.offset.x, p.offset.y, p.offset.z]⟩

def statesOf {n : Nat} (rows : Nat → Option Row) (i : Fin n) :
    Psc.OccurrenceTransport.Packet :=
  (rowAt rows i).state.toGeometry

theorem birthWitness {n : Nat} {rows : Nat → Option Row} (i : Fin n)
    (valid : birthOK rows i (rowAt rows i) = true) :
    i.val < 3 ∨ ∃ (j : Fin n) (k : Fin (rowAt rows j).slots.length),
      j.val < i.val ∧ (rowAt rows j).slots[k.val].target = i.val := by
  by_cases h : i.val < 3
  · exact Or.inl h
  right
  have noRoot : roots[i.val]? = none := by
    apply List.getElem?_eq_none
    simpa [roots] using h
  cases hb : (rowAt rows i).birth with
  | none => simp [birthOK, noRoot, hb] at valid
  | some birth =>
    obtain ⟨parent, position⟩ := birth
    simp only [birthOK, noRoot, hb, Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨earlier, valid⟩ := valid
    cases hr : rows parent with
    | none => simp [hr] at valid
    | some previous =>
      simp only [hr, Bool.and_eq_true, beq_iff_eq] at valid
      have present : position < previous.slots.length := by
        by_contra missing
        rw [List.getElem?_eq_none (by omega)] at valid
        simp at valid
      have equal := valid.2
      rw [List.getElem?_eq_getElem present] at equal
      have same : previous.slots[position].target = i.val := by simpa using equal
      let j : Fin n := ⟨parent, Nat.lt_trans earlier i.isLt⟩
      have rowEq : rowAt rows j = previous := by simp [rowAt, j, hr]
      exact ⟨j, ⟨position, by simpa [rowEq] using present⟩, earlier,
        by simpa [rowEq] using same⟩

theorem importedDiscovery {n marks rows byRank numerator} {fixture : Fin 2}
    (accepted : ∀ i, 0 ≤ i → i < n → rowOK marks rows byRank n numerator i = true)
    (table : TableBinding (iterateImages (substitution fixture) 2) (statesOf rows)
      (toCertificate rows numerator
        (fun (i : Fin n) => (row_checks (accepted i (Nat.zero_le _) i.isLt)).2.1)))
    (rootBound : ∀ (i : Fin n) (hi : i.val < 3), statesOf rows i = archivedRoot ⟨i.val, hi⟩) :
    TableDiscovery table.row ArchivedRoot := by
  intro i
  rcases birthWitness i (row_checks (accepted i (Nat.zero_le _) i.isLt)).2.2 with
    hi | ⟨j, k, hj, hk⟩
  · exact Or.inl ⟨⟨i.val, hi⟩, Or.inl (rootBound i hi)⟩
  · exact Or.inr ⟨j, k, hj, Fin.ext hk⟩

/-- The imported potential is accepted on these very degrees and targets.
The geometric row binding and exhaustive closure are separate premises. -/
theorem conditionalNullity {n marks rows byRank numerator} (fixture : Fin 2)
    (accepted : ∀ i, 0 ≤ i → i < n → rowOK marks rows byRank n numerator i = true)
    (rate : numerator = archivedNumerator fixture)
    (ν : Measure (H (substitution fixture))) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (rootID : Fin 3 → Fin n)
    (table : TableBinding (iterateImages (substitution fixture) 2) (statesOf rows)
      (toCertificate rows numerator
        (fun (i : Fin n) => (row_checks (accepted i (Nat.zero_le _) i.isLt)).2.1)))
    (closed : DecodedCandidatesClosed fixture (statesOf (n := n) rows)) :
    ∀ i : Fin n, (volume.prod ν)
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) (statesOf rows i)) = 0 :=
  null_of_source_bound_table fixture ν _ _ table closed (certificateAccepted accepted) rate rfl
    rootID

end ArchivedC4
