import Check
import PscVerif.OverlapContraction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace ArchivedC4

open PscVerif.OverlapContraction
open scoped BigOperators

def emptyRow : Row :=
  ⟨⟨0, 0, ⟨0, 0, 0⟩⟩, 0, 0, none, 0, []⟩

def rowAt (rows : Nat → Option Row) (i : Nat) : Row :=
  (rows i).getD emptyRow

theorem row_checks {marks rows byRank count numerator i}
    (h : rowOK marks rows byRank count numerator i = true) :
    potentialOK rows numerator (rowAt rows i) = true ∧
      (∀ s ∈ (rowAt rows i).slots, s.target < count) ∧
      birthOK rows i (rowAt rows i) = true := by
  cases hr : rows i with
  | none => simp [rowOK, hr] at h
  | some row =>
    simp only [rowOK, hr, Bool.and_eq_true] at h
    simp only [rowAt, hr, Option.getD_some]
    exact ⟨h.1.1.2, fun s hs => of_decide_eq_true (List.all_eq_true.mp h.1.2 s hs),
      h.1.1.1.2⟩

def toCertificate {n : Nat} (rows : Nat → Option Row) (numerator : Nat)
    (bounds : ∀ i : Fin n, ∀ s ∈ (rowAt rows i).slots, s.target < n) :
    Certificate n where
  degree i := (rowAt rows i).slots.length
  target i e :=
    ⟨(rowAt rows i).slots[e.val].target,
      bounds i _ (List.getElem_mem e.isLt)⟩
  weight i := (rowAt rows i).weight
  numerator := numerator
  denominator := 20

theorem certificateAccepted {n marks rows byRank numerator}
    (accepted : ∀ i, 0 ≤ i → i < n → rowOK marks rows byRank n numerator i = true) :
    (toCertificate rows numerator
      (fun (i : Fin n) => (row_checks (accepted i (Nat.zero_le _) i.isLt)).2.1)).check = true := by
  apply (Certificate.check_iff _).mpr
  refine ⟨by change 0 < 20; decide, ?_⟩
  intro i
  have hp := (row_checks (accepted i (Nat.zero_le _) i.isLt)).1
  let row := rowAt rows i
  let weight (s : Slot) := (rowAt rows s.target).weight
  have weights : (row.slots.map weight).sum =
      (∑ e : Fin row.slots.length, weight row.slots[e.val]) := by
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  have hlookup (s : Slot) : ((rows s.target).map Row.weight).getD 0 = weight s := by
    cases h : rows s.target <;> simp [weight, rowAt, h, emptyRow]
  simp only [potentialOK, decide_eq_true_eq, hlookup] at hp
  change 0 < row.weight ∧
    20 * (∑ e : Fin row.slots.length, weight row.slots[e.val]) ≤ numerator * row.weight
  rw [← weights]
  exact hp

end ArchivedC4
