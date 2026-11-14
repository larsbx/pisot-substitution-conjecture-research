import PscVerif.C4ParameterFamilyWords
import PscVerif.FastForwardCarrier

/-!
# Sharp parameter boundary for immediate coincidence

At `k = 2`, the ordered seed `01/10` reaches a noncoincident block whose
only actual child is again noncoincident.  Thus the family's immediate-exit
theorem needs `k ≥ 3`; termination with coincidence at `k = 2` instead uses
an available path of length two from some reached states.

The seven edges below use complete literal rows.  The existing sound
streaming block checker and `red_unique` identify each row with the actual
ordered reduction.  No carrier, rank, symbolic template, or external
executable is trusted by these proofs.
-/

namespace Psc.ParameterFamilyControls

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.FastForwardCarrier
open Psc.ParameterFamilyRows (substitution)

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- A reached block at the boundary parameter whose coincidence exit is delayed. -/
def delayedPair : Pair := (word "010112", word "200111")

/-- The complete reduction of the delayed block has this one noncoincident child. -/
def onlyChild : Pair := (word "10112101120112001", word "00111011201120112")

private def pairs (xs : List (String × String)) : List Pair :=
  xs.map fun p => (word p.1, word p.2)

private def rowCheck (p : Pair) (row : List Pair) : Bool :=
  row.all isBlockCheck &&
    (((row.map Prod.fst).flatten == subst (substitution 2) p.1) &&
      ((row.map Prod.snd).flatten == subst (substitution 2) p.2))

private theorem checked_row {p : Pair} {row : List Pair} (h : rowCheck p row = true) :
    row = red (subst (substitution 2) p.1) (subst (substitution 2) p.2) := by
  simp only [rowCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact red_unique row (fun T hT => isBlockCheck_sound (h.1 T hT)) h.2.1 h.2.2

private theorem checked_edge (p q : Pair) (row : List Pair)
    (hne : p.1 ≠ p.2) (hrow : rowCheck p row = true) (hq : q ∈ row) :
    ChildNC (substitution 2) p q := by
  refine ⟨hne, ?_⟩
  change q ∈ red (subst (substitution 2) p.1) (subst (substitution 2) p.2)
  rw [← checked_row hrow]
  exact hq

/-- Every edge in this path uses the repository's actual ordered reduction. -/
theorem delayedPair_reachable :
    Relation.ReflTransGen (ChildNC (substitution 2)) ([0, 1], [1, 0]) delayedPair := by
  have e1 : ChildNC (substitution 2) ([0, 1], [1, 0])
      (word "12", word "21") :=
    checked_edge _ _ (pairs [("10", "01"), ("1", "1"), ("12", "21")])
      (by decide) (by decide +kernel) (by decide)
  have e2 : ChildNC (substitution 2) (word "12", word "21")
      (word "112001", word "010112") :=
    checked_edge _ _ (pairs [("0", "0"), ("112001", "010112")])
      (by decide) (by decide +kernel) (by decide)
  have e3 : ChildNC (substitution 2) (word "112001", word "010112")
      (word "2001110112", word "1120112001") :=
    checked_edge _ _ (pairs [("01", "10"), ("1", "1"), ("2011", "1210"),
      ("2001110112", "1120112001")]) (by decide) (by decide +kernel) (by decide)
  have e4 : ChildNC (substitution 2) (word "2001110112", word "1120112001")
      (word "0111011201120", word "1120112001101") :=
    checked_edge _ _ (pairs [("0", "0"), ("0111011201120", "1120112001101"),
      ("1", "1"), ("1210", "2011"), ("1120112001", "2001110112")])
      (by decide) (by decide +kernel) (by decide)
  have e5 : ChildNC (substitution 2) (word "0111011201120", word "1120112001101")
      (word "1201121011201120011011201120011",
       word "2001101120112001110112011210112") :=
    checked_edge _ _ (pairs [("10", "01"), ("1", "1"), ("120", "201"), ("1", "1"),
      ("1201121011201120011011201120011", "2001101120112001110112011210112")])
      (by decide) (by decide +kernel) (by decide)
  have e6 : ChildNC (substitution 2)
      (word "1201121011201120011011201120011",
       word "2001101120112001110112011210112")
      (word "200101121", word "112011200") :=
    checked_edge _ _ (pairs [("0", "0"), ("112001101", "011101120"), ("1", "1"),
      ("2011", "1210"), ("200101121", "112011200"), ("011", "110"), ("2011", "1120"),
      ("20011", "11200"), ("01120112001110112011210112", "11101120112011210112011200"),
      ("011", "110"), ("200110112", "112011200"), ("01", "10"), ("1", "1"),
      ("20011101120112", "12101120112001")]) (by decide) (by decide +kernel) (by decide)
  have e7 : ChildNC (substitution 2) (word "200101121", word "112011200")
      delayedPair :=
    checked_edge _ _ (pairs [("0", "0"), ("01110112101120", "11201120011011"),
      ("1120", "2011"), ("010112", "200111")]) (by decide) (by decide +kernel) (by decide)
  exact ((((((Relation.ReflTransGen.single e1).tail e2).tail e3).tail e4).tail e5).tail e6).tail e7

/-- Complete factorization, including order and multiplicity. -/
theorem delayedPair_row :
    red (subst (substitution 2) delayedPair.1) (subst (substitution 2) delayedPair.2) =
      [onlyChild] :=
  (checked_row (p := delayedPair) (row := [onlyChild]) (by decide +kernel)).symm

/-- The stronger all-`k ≥ 2` immediate-coincidence claim is false at a reached state. -/
theorem delayedPair_no_coincidence_child :
    delayedPair.1 ≠ delayedPair.2 ∧
      ¬ ∃ U, ChildNC (substitution 2) delayedPair U ∧ U.1 = U.2 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨U, hU, hdiag⟩
  have hmem := hU.2
  change U ∈ red (subst (substitution 2) delayedPair.1)
    (subst (substitution 2) delayedPair.2) at hmem
  rw [delayedPair_row, List.mem_singleton] at hmem
  subst U
  exact (by decide : onlyChild.1 ≠ onlyChild.2) hdiag

end Psc.ParameterFamilyControls
