import PscVerif.FastForwardCarrier

/-!
# Discriminating controls for indexed forward-carrier refinement

The constant substitution below is a finite calibration, not a Pisot
counterexample. Its complete eight-state packet has all six ordered seeds
and both singleton coincidences. Mutations preserve those source states
while changing complete literal factor rows.

The seven-state control is deliberately subtler: every seed row passes
literal concatenation, but its shared child is reducible. Only checking
all state blocks excludes that invalid proposed factorization.

Pre-code refinement gate:
`docs/c4-forward-carrier-fast-addendum-2026-11-12.md`.
-/

namespace Psc.FastForwardCarrierControls

open Psc.FastForwardCarrier

def seedState : Fin 6 → Pair :=
  ![([0, 1], [1, 0]), ([1, 0], [0, 1]),
    ([0, 2], [2, 0]), ([2, 0], [0, 2]),
    ([1, 2], [2, 1]), ([2, 1], [1, 2])]

/-- The diagonal values are unused; all six unequal pairs are exact. -/
def seedIndex : Fin 3 → Fin 3 → Fin 6 :=
  ![![0, 0, 2], ![1, 0, 4], ![3, 5, 0]]

def constantSubst (_ : Fin 3) : Word := [0, 1]

def positive : Packet 8 where
  state := fun i =>
    if h : i.val < 6 then seedState ⟨i.val, h⟩
    else if i.val = 6 then ([0], [0]) else ([1], [1])
  rows := fun i => if i.val < 6 then
    [⟨6, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩] else []
  seed := fun a b =>
    ⟨(seedIndex a b).val, Nat.lt_trans (seedIndex a b).isLt (by decide : 6 < 8)⟩

theorem positive_seeds : positive.SeedsValid := by decide

theorem positive_complete_rows : positive.checkRange constantSubst 0 8 = true := by
  decide

theorem positive_valid : positive.Valid constantSubst :=
  positive.valid_of_range constantSubst positive_seeds positive_complete_rows

/-- This exercises the complete refinement-to-finiteness consumer. -/
theorem positive_finite : (Psc.Descendants.bpaStatesNC constantSubst).Finite :=
  positive.finite_bpaStatesNC constantSubst positive_valid

def reducibleChild : Packet 7 where
  state := fun i =>
    if h : i.val < 6 then seedState ⟨i.val, h⟩
    else ([0, 1, 0, 1], [0, 1, 0, 1])
  rows := fun i => if i.val < 6 then [⟨6, by decide⟩] else []
  seed := fun a b =>
    ⟨(seedIndex a b).val, Nat.lt_trans (seedIndex a b).isLt (by decide : 6 < 7)⟩

/-- Every seed row passes and the last row is correctly terminal. The
last state's reducibility alone prevents complete acceptance. -/
theorem every_child_block_check_required :
    reducibleChild.SeedsValid ∧
    reducibleChild.checkRange constantSubst 0 6 = true ∧
    reducibleChild.rows ⟨6, by decide⟩ = [] ∧
    isBlockCheck (reducibleChild.state ⟨6, by decide⟩) = false ∧
    reducibleChild.checkAt constantSubst 6 = false ∧
    reducibleChild.checkRange constantSubst 0 7 = false := by
  decide

def replaceFirstRow (row : List (Fin 8)) : Packet 8 :=
  { positive with rows := fun i => if i.val = 0 then row else positive.rows i }

def omittedExit : Packet 8 :=
  replaceFirstRow [⟨6, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩]

def collapsedOccurrences : Packet 8 :=
  replaceFirstRow [⟨6, by decide⟩, ⟨7, by decide⟩]

def extraOccurrence : Packet 8 :=
  replaceFirstRow [⟨6, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩,
    ⟨7, by decide⟩, ⟨7, by decide⟩]

def reorderedOccurrences : Packet 8 :=
  replaceFirstRow [⟨7, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]

theorem omitted_exit_rejected : omittedExit.checkAt constantSubst 0 = false := by
  decide

/-- A set of child IDs cannot replace the complete occurrence list, and
an extra copy is rejected as well. -/
theorem multiplicity_changes_rejected :
    collapsedOccurrences.checkAt constantSubst 0 = false ∧
    extraOccurrence.checkAt constantSubst 0 = false := by
  decide

/-- The child multiset is unchanged; the literal order is wrong. -/
theorem reordered_occurrences_rejected :
    reorderedOccurrences.checkAt constantSubst 0 = false := by
  decide

def identitySubst (a : Fin 3) : Word := [a]

def identityPacket : Packet 6 where
  state := seedState
  rows := fun i => [i]
  seed := seedIndex

theorem identity_packet_valid : identityPacket.Valid identitySubst :=
  identityPacket.valid_of_range identitySubst (by decide) (by decide)

def wrongOrientation : Packet 6 :=
  { identityPacket with
    rows := fun i => if i.val = 0 then [⟨1, by decide⟩] else [i] }

/-- Replacing a child by its track swap preserves balance but breaks the
required ordered source-word equality. -/
theorem wrong_orientation_rejected :
    wrongOrientation.checkAt identitySubst 0 = false := by
  decide

/-- The same carrier words cannot transfer the constant substitution's
rows to another literal substitution without rechecking its images. -/
theorem wrong_literal_source_rejected : positive.checkAt identitySubst 0 = false := by
  decide

end Psc.FastForwardCarrierControls
