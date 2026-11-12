import Lean

/-! Finite replay of the original paired graphs using kernel arithmetic.
The packet and slot types here are serialized data types. -/

namespace ArchivedC4

structure Offset where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq

structure Packet where
  top : Nat
  bottom : Nat
  offset : Offset
  deriving DecidableEq

def Packet.swap (p : Packet) : Packet :=
  ⟨p.bottom, p.top, ⟨-p.offset.x, -p.offset.y, -p.offset.z⟩⟩

def Packet.key (p : Packet) : Int :=
  (((Int.ofNat (p.top * 3 + p.bottom) * 65 + p.offset.x + 32) * 65
    + p.offset.y + 32) * 65 + p.offset.z + 32)

def Packet.bounded (p : Packet) : Bool :=
  decide (p.top < 3 ∧ p.bottom < 3 ∧
    p.offset.x.natAbs ≤ 32 ∧ p.offset.y.natAbs ≤ 32 ∧ p.offset.z.natAbs ≤ 32)

structure Digit where
  selected : Nat
  parent : Nat
  position : Nat
  outer : Nat
  localPosition : Nat
  counts : Offset
  deriving DecidableEq

structure Slot where
  target : Nat
  top : Nat
  bottom : Nat
  swapped : Bool
  deriving DecidableEq

structure Row where
  state : Packet
  rank : Nat
  weight : Nat
  birth : Option (Nat × Nat)
  depth : Nat
  slots : List Slot

def digits (images : List (List Nat)) : List Digit :=
  images.zipIdx.flatMap fun (word, parent) =>
    let addressed := word.zipIdx.flatMap fun (letter, outer) =>
      (images[letter]?.getD []).zipIdx.map fun (selected, localPosition) =>
        (selected, outer, localPosition)
    addressed.zipIdx.map fun ((selected, outer, localPosition), position) =>
      let counts := (addressed.take position).map Prod.fst
      ⟨selected, parent, position, outer, localPosition,
        ⟨counts.count 0, counts.count 1, counts.count 2⟩⟩

def admitted (d : Offset) : Bool :=
  let x0 := 1000000 * d.x - 828911 * d.y
  let x1 := 1000000 * d.x - 828912 * d.y
  let z0 := 1000000 * d.z - 440619 * d.y
  let z1 := 1000000 * d.z - 440620 * d.y
  !decide ((32000000 < x0 ∧ 32000000 < x1) ∨
    (x0 < -32000000 ∧ x1 < -32000000) ∨
    (16000000 < z0 ∧ 16000000 < z1) ∨ (z0 < -16000000 ∧ z1 < -16000000))

def candidate (p : Packet) (a b : Digit) : Option Packet :=
  let x := p.offset.x + b.counts.x - a.counts.x
  let y := p.offset.y + b.counts.y - a.counts.y
  let z := p.offset.z + b.counts.z - a.counts.z
  let u := 3 * z - y
  let v := x - z
  let w := y - x
  if u % 2 == 0 && v % 2 == 0 && w % 2 == 0 then
    let offset : Offset := ⟨u / 2, v / 2, w / 2⟩
    if admitted offset then some ⟨a.parent, b.parent, offset⟩ else none
  else none

def candidates (marks : List Digit) (p : Packet) : List (Nat × Nat × Packet) :=
  marks.zipIdx.flatMap fun (a, top) =>
    if a.selected == p.top then
      marks.zipIdx.filterMap fun (b, bottom) =>
        if b.selected == p.bottom then
          (candidate p a b).map fun raw => (top, bottom, raw)
        else none
    else []

def slotsMatch (rows : Nat → Option Row) :
    List (Nat × Nat × Packet) → List Slot → Bool
  | [], [] => true
  | (top, bottom, raw) :: rest, slot :: slots =>
      top == slot.top && bottom == slot.bottom &&
      (match rows slot.target with
       | some target =>
           let swapped := decide (raw.swap.key < raw.key)
           swapped == slot.swapped && decide ((if swapped then raw.swap else raw) = target.state)
       | none => false) &&
      slotsMatch rows rest slots
  | _, _ => false

def roots : List Packet :=
  [⟨0, 1, ⟨0, 0, 0⟩⟩, ⟨0, 2, ⟨0, 0, 0⟩⟩, ⟨1, 2, ⟨0, 0, 0⟩⟩]

def birthOK (rows : Nat → Option Row) (i : Nat) (row : Row) : Bool :=
  match roots[i]?, row.birth with
  | some root, none => decide (row.state = root ∧ row.depth = 0)
  | none, some (parent, position) =>
      decide (parent < i) && (match rows parent with
      | some previous =>
          row.depth == previous.depth + 1 &&
          (previous.slots[position]?.map Slot.target) == some i
      | none => false)
  | _, _ => false

def rankOK (rows : Nat → Option Row) (byRank : Nat → Option Nat) (row : Row) (i : Nat) :
    Bool :=
  byRank row.rank == some i &&
  (if row.rank == 0 then true else
    match (byRank (row.rank - 1)).bind rows with
    | some previous => decide (previous.state.key < row.state.key)
    | none => false)

def potentialOK (rows : Nat → Option Row) (numerator : Nat) (row : Row) : Bool :=
  let targetWeights := row.slots.map fun s => ((rows s.target).map Row.weight).getD 0
  decide (0 < row.weight ∧ 20 * targetWeights.sum ≤ numerator * row.weight)

def rowOK (marks : List Digit) (rows : Nat → Option Row) (byRank : Nat → Option Nat)
    (count numerator i : Nat) : Bool :=
  match rows i with
  | none => false
  | some row =>
      row.state.bounded && admitted row.state.offset && decide (row.state.key < row.state.swap.key) &&
      rankOK rows byRank row i && birthOK rows i row &&
      potentialOK rows numerator row && row.slots.all (fun slot => decide (slot.target < count)) &&
      slotsMatch rows (candidates marks row.state) row.slots

def checkChunk (first count : Nat) (check : Nat → Bool) : Bool :=
  (List.range' first count).all check

theorem row_of_chunk {first count i : Nat} {check : Nat → Bool}
    (accepted : checkChunk first count check = true)
    (lower : first ≤ i) (upper : i < first + count) : check i = true := by
  apply (List.all_eq_true.mp accepted) i
  exact List.mem_range'.mpr ⟨i - first, by omega, by omega⟩

theorem joinRows {first middle last : Nat} {check : Nat → Bool}
    (left : ∀ i, first ≤ i → i < middle → check i = true)
    (right : ∀ i, middle ≤ i → i < last → check i = true) :
    ∀ i, first ≤ i → i < last → check i = true := by
  intro i low high
  if h : i < middle then exact left i low h
  else exact right i (by omega) high

end ArchivedC4
