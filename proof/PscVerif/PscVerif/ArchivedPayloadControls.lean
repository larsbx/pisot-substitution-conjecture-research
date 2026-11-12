import PscVerif.ArchivedPayload

/-!
# Kernel negative controls for the original archived-payload decoder

These small controls use the original named root and actual period-two
digits.  In particular an empty positional table can pass the integer
potential inequality while failing the source-completeness check.  The
large original payloads are separately imported and independently replayed;
these controls do not replace those evaluations.
-/

namespace Psc.ArchivedPayloadControls

open Psc.ArchivedPayload
open PscVerif.OverlapContraction

def encodeState (top bottom x y z : Nat) : Nat :=
  top + 4 * bottom + 16 * x + 2048 * y + 262144 * z

def encodeSlot (target top bottom swap : Nat) : Nat :=
  target + 16384 * top + 262144 * bottom + 4194304 * swap

def encodeRow (state weight parent slot depth : Nat) (edges : List Nat) : Nat :=
  let tail := edges.foldr (fun e rest => e + 8388608 * rest) 0
  weight + 1048576 * (edges.length + 256 * (state + 33554432 *
    (parent + 16384 * (slot + 256 * (depth + 32 * tail)))))

def root0 := encodeState 0 1 64 64 64
def root1 := encodeState 0 2 64 64 64
def root2 := encodeState 1 2 64 64 64

def control : Packet where
  fixture := 0
  count := 3
  table := .branch 1 (.leaf (encodeRow root0 1 0 0 0 []))
    (.branch 1 (.leaf (encodeRow root1 1 0 0 0 []))
      (.leaf (encodeRow root2 1 0 0 0 [])))
  index := .empty
  power := 2
  boxX := 16
  boxY := 8
  direction := 0
  numerator := 99
  residueRejections := 0
  boxRejections := 0
  edges := 0
  swapped := 0
  repeated := 0
  maxDepth := 0
  sweeps := 0
  minimumGap := 99

theorem exact_original_header_accepted : control.HeaderValid := by decide +kernel

def zero : Fin control.count := ⟨0, by decide⟩

/-- Numerical contraction alone admits the empty-row falsification. -/
def emptyPotential : Certificate 3 where
  degree := fun _ => 0
  target := fun _ e => Fin.elim0 e
  weight := fun _ => 1
  numerator := 99
  denominator := 20

theorem omitted_edges_preserve_numeric_contraction : emptyPotential.check = true := by
  decide +kernel

/-- The true original pair0/10 reaches root1 and cannot disappear. -/
theorem omitted_original_position_refused : ¬control.PairComplete zero 0 10 := by
  decide +kernel

theorem original_direction_slot_accepted :
    control.SlotValid zero ⟨encodeSlot 0 0 3 0⟩ := by decide +kernel

theorem swapped_direction_refused :
    ¬control.SlotValid zero ⟨encodeSlot 0 0 3 1⟩ := by decide +kernel

theorem graph_domain_target_mismatch_refused :
    ¬control.SlotValid zero ⟨encodeSlot 1 0 3 0⟩ := by decide +kernel

theorem out_of_range_target_refused :
    ¬control.SlotValid zero ⟨encodeSlot 3 0 3 0⟩ := by decide +kernel

theorem impossible_digit_field_refused :
    ¬control.SlotValid zero ⟨encodeSlot 0 15 3 0⟩ := by decide +kernel

theorem impossible_state_letter_refused :
    ¬stateFieldsValid (encodeState 3 1 64 64 64) := by decide +kernel

theorem hidden_slot_payload_refused :
    ¬control.SlotValid zero ⟨encodeSlot 0 0 3 0 + 8388608⟩ := by decide +kernel

theorem later_wide_box_refused :
    ¬({control with boxX := 24, boxY := 12} : Packet).HeaderValid := by decide +kernel

theorem reversed_graph_direction_refused :
    ¬({control with direction := 1} : Packet).HeaderValid := by decide +kernel

theorem wrong_substitution_power_refused :
    ¬({control with power := 12} : Packet).HeaderValid := by decide +kernel

def orphan : Packet :=
  { control with
    count := 4
    table := .branch 3 control.table (.leaf (encodeRow root0 1 0 0 0 [])) }

theorem incomplete_inverse_ancestry_refused : ¬orphan.BirthValid ⟨3, by decide⟩ := by
  decide +kernel

def circularBirth : Packet :=
  { orphan with
    table := .branch 3 control.table
      (.leaf (encodeRow root0 1 4 1 1 [encodeSlot 3 0 3 0])) }

theorem circular_inverse_ancestry_refused : ¬circularBirth.BirthValid ⟨3, by decide⟩ := by
  decide +kernel

def hiddenRow : Packet :=
  { control with
    table := .branch 1
      (.leaf (encodeRow root0 1 0 0 0 [] + 1208925819614629174706176))
      (.branch 1 (.leaf (encodeRow root1 1 0 0 0 []))
        (.leaf (encodeRow root2 1 0 0 0 []))) }

theorem hidden_row_payload_refused : hiddenRow.canonical 0 = false := by decide +kernel

/-- A route that maps every key to one ID cannot establish two state IDs. -/
theorem collapsed_index_refused :
    (Lookup.node (orbitCode (control.state 0)) 0 .empty .empty).find
      (orbitCode (control.state 1)) ≠ some 1 := by decide +kernel

theorem repeated_positional_addresses_refused :
    ¬StrictMono (fun _ : Fin 2 => (⟨encodeSlot 0 0 3 0⟩ : RawSlot).address) := by
  decide +kernel

def fourOriginalStates : Packet :=
  { control with
    count := 4
    table := .branch 3 control.table
      (.leaf (encodeRow (encodeState 0 1 62 64 65) 1 1 3 1 [])) }

theorem original_full_mark_slot_accepted :
    fourOriginalStates.SlotValid ⟨0, by decide⟩ ⟨encodeSlot 3 4 2 1⟩ := by
  decide +kernel

def wrongLiteralSource : Packet := { fourOriginalStates with fixture := 1 }

/-- The two original words share their matrix; their actual positions do
not become interchangeable under that matrix equality. -/
theorem same_matrix_wrong_literal_source_refused :
    ¬wrongLiteralSource.SlotValid ⟨0, by decide⟩ ⟨encodeSlot 3 4 2 1⟩ := by
  decide +kernel

end Psc.ArchivedPayloadControls
