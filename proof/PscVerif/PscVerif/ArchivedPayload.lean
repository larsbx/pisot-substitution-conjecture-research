import PscVerif.OverlapPacket
import PscVerif.NamedArchivedDigits
import PscVerif.NamedArchivedGraph

/-!
# Kernel reflection of the original archived positional graph payload

The balanced row table and auxiliary search tree are untrusted data.  A
row-wise left inverse proves that stored IDs represent distinct swap orbits;
no correctness, ordering or injectivity of the search tree is assumed.
Every one of the 15 × 15 actual digit pairs is checked at every stored
source.  An admitted integral pair must occur at its full positional
address, and every supplied slot is checked in the original direction.

The checks construct `TableBinding`, decoded candidate closure, the exact
roots, earlier-slot discovery and the integer-potential certificate.  They
do not identify this rooted graph with all strict packets or assert
positive root measure.  Arithmetic acceptance uses kernel reduction only.

Pre-code gate: `docs/c4-archived-payload-import-literature-2026-11-12.md`.
-/

namespace Psc.ArchivedPayload

open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceInverse
open Psc.OccurrenceGraphBinding Psc.OccurrenceAdmissibility
open Psc.OccurrenceCover Psc.ArchivedGraphRefinement
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedArchivedGraph
open PscVerif.OverlapContraction
open scoped BigOperators

abbrev Table := PscVerif.OverlapPacket.Table

/-- This search tree is merely an untrusted function.  Acceptance checks a
left inverse at every original state, so malformed routing cannot merge IDs. -/
inductive Lookup where
  | empty
  | node (key id : Nat) (left right : Lookup)

def Lookup.find : Lookup → Nat → Option Nat
  | .empty, _ => none
  | .node key id left right, sought =>
      if sought = key then some id
      else if sought < key then left.find sought else right.find sought

/-- A computable equality test, with no classical decision procedure for
the functional displacement field. -/
def packetEq (p q : OccurrenceTransport.Packet) : Bool :=
  decide (p.top = q.top ∧ p.bottom = q.bottom ∧ ∀ k : Fin 3, p.delta k = q.delta k)

theorem packetEq_iff (p q : OccurrenceTransport.Packet) :
    packetEq p q = true ↔ p = q := by
  simp only [packetEq, decide_eq_true_eq]
  constructor
  · rintro ⟨ht, hb, hd⟩
    exact packet_ext ht hb (funext hd)
  · rintro rfl
    exact ⟨rfl, rfl, fun _ => rfl⟩

def stateCode (p : OccurrenceTransport.Packet) : Nat :=
  p.top.val + 4 * p.bottom.val + 16 * (p.delta 0 + 64).toNat +
    2048 * (p.delta 1 + 64).toNat + 262144 * (p.delta 2 + 64).toNat

def orbitCode (p : OccurrenceTransport.Packet) : Nat :=
  min (stateCode p) (stateCode p.swap)

theorem orbitCode_swap (p : OccurrenceTransport.Packet) : orbitCode p.swap = orbitCode p := by
  simp only [orbitCode, packet_swap_swap, min_comm]

/-- Bad letter fields are separately refused.  The total decoder does not
turn an invalid field into accepted mathematical evidence. -/
def decodeState (bits : Nat) : OccurrenceTransport.Packet :=
  ⟨⟨(bits % 4) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨((bits / 4) % 4) % 3, Nat.mod_lt _ (by decide)⟩,
   ![((bits / 16) % 128 : Int) - 64,
     ((bits / 2048) % 128 : Int) - 64,
     ((bits / 262144) % 128 : Int) - 64]⟩

def stateFieldsValid (bits : Nat) : Prop :=
  bits < 33554432 ∧ bits % 4 < 3 ∧ (bits / 4) % 4 < 3

instance (bits : Nat) : Decidable (stateFieldsValid bits) := by
  unfold stateFieldsValid
  infer_instance

structure RawSlot where
  bits : Nat
deriving Inhabited

def RawSlot.target (e : RawSlot) : Nat := e.bits % 16384
def RawSlot.topID (e : RawSlot) : Nat := (e.bits / 16384) % 16
def RawSlot.bottomID (e : RawSlot) : Nat := (e.bits / 262144) % 16
def RawSlot.swapped (e : RawSlot) : Bool := decide ((e.bits / 4194304) % 2 = 1)
def RawSlot.top (e : RawSlot) : Fin 15 := ⟨e.topID % 15, Nat.mod_lt _ (by decide)⟩
def RawSlot.bottom (e : RawSlot) : Fin 15 := ⟨e.bottomID % 15, Nat.mod_lt _ (by decide)⟩
def RawSlot.address (e : RawSlot) : Nat := 15 * e.top.val + e.bottom.val

def decodeSlots : Nat → Nat → List RawSlot
  | 0, _ => []
  | n + 1, bits => ⟨bits % 8388608⟩ :: decodeSlots n (bits / 8388608)

structure RawRow where
  stateBits : Nat
  weight : Nat
  birthParent : Nat
  birthSlot : Nat
  depth : Nat
  slots : List RawSlot
deriving Inhabited

/-- Low-to-high fields: weight20, degree8, state25, parent-plus-one14,
slot-plus-one8, depth5, then one23-bit record per positional slot. -/
def decodeRow (bits : Nat) : RawRow where
  stateBits := (bits / 268435456) % 33554432
  weight := bits % 1048576
  birthParent := (bits / 9007199254740992) % 16384
  birthSlot := (bits / 147573952589676412928) % 256
  depth := (bits / 37778931862957161709568) % 32
  slots := decodeSlots ((bits / 1048576) % 256) (bits / 1208925819614629174706176)

structure Packet where
  fixture : Fin 2
  count : Nat
  table : Table Nat
  index : Lookup
  power : Nat
  boxX : Nat
  boxY : Nat
  direction : Nat
  numerator : Nat
  residueRejections : Nat
  boxRejections : Nat
  edges : Nat
  swapped : Nat
  repeated : Nat
  maxDepth : Nat
  sweeps : Nat
  minimumGap : Nat

def Packet.raw (p : Packet) (i : Nat) : Nat := (p.table.get? i).getD 0
def Packet.record (p : Packet) (i : Nat) : RawRow := decodeRow (p.raw i)
def Packet.state (p : Packet) (i : Nat) : OccurrenceTransport.Packet :=
  decodeState (p.record i).stateBits
def Packet.states (p : Packet) : Fin p.count → OccurrenceTransport.Packet :=
  fun i => p.state i.val
def Packet.weight (p : Packet) (i : Nat) : Nat := (p.record i).weight
def Packet.row (p : Packet) (i : Fin p.count) : List RawSlot := (p.record i.val).slots
def Packet.slot (p : Packet) (i : Fin p.count) (e : Fin (p.row i).length) : RawSlot :=
  (p.row i)[e]
def Packet.canonical (p : Packet) (i : Nat) : Bool :=
  let bits := p.raw i
  decide ((bits / 1208925819614629174706176) /
    (8388608 ^ ((bits / 1048576) % 256)) = 0)

def rhs (fixture : Fin 2) (p : OccurrenceTransport.Packet) (a b : Fin 15) : Fin 3 → Int :=
  p.delta + residual (NamedArchivedDigits.digit fixture b).2.before
    (NamedArchivedDigits.digit fixture a).2.before

def candidate (fixture : Fin 2) (p : OccurrenceTransport.Packet) (a b : Fin 15) :
    OccurrenceTransport.Packet :=
  ⟨(NamedArchivedDigits.digit fixture a).1,
   (NamedArchivedDigits.digit fixture b).1,
   NamedInverseDecoder.inverse (rhs fixture p a b)⟩

def Selected (fixture : Fin 2) (p : OccurrenceTransport.Packet) (a b : Fin 15) : Prop :=
  (NamedArchivedDigits.digit fixture a).2.letter = p.top ∧
    (NamedArchivedDigits.digit fixture b).2.letter = p.bottom

instance (fixture : Fin 2) (p : OccurrenceTransport.Packet) (a b : Fin 15) :
    Decidable (Selected fixture p a b) := by
  unfold Selected
  infer_instance

def selectedPair (fixture : Fin 2) (p : OccurrenceTransport.Packet) (a b : Fin 15)
    (h : Selected fixture p a b) :
    SelectedPair (iterateImages (substitution fixture) 2) p :=
  ⟨(NamedArchivedDigits.digit fixture a, NamedArchivedDigits.digit fixture b), h⟩

theorem selectedPair_candidate (fixture : Fin 2) (p : OccurrenceTransport.Packet)
    (a b : Fin 15) (h : Selected fixture p a b) :
    decodedCandidate fixture (selectedPair fixture p a b h) = candidate fixture p a b := rfl

def Packet.SlotValid (p : Packet) (i : Fin p.count) (e : RawSlot) : Prop :=
  e.bits < 8388608 ∧ e.topID < 15 ∧ e.bottomID < 15 ∧ e.target < p.count ∧
  Selected p.fixture (p.states i) e.top e.bottom ∧
  NamedInverseDecoder.check (rhs p.fixture (p.states i) e.top e.bottom) = true ∧
  packetEq (candidate p.fixture (p.states i) e.top e.bottom)
    (orient (p.state e.target) e.swapped) = true

instance (p : Packet) (i : Fin p.count) (e : RawSlot) : Decidable (p.SlotValid i e) := by
  unfold Packet.SlotValid
  infer_instance

def Packet.PairComplete (p : Packet) (i : Fin p.count) (a b : Fin 15) : Prop :=
  Selected p.fixture (p.states i) a b →
  NamedInverseDecoder.check (rhs p.fixture (p.states i) a b) = true →
  NamedSharpBox.admitted (candidate p.fixture (p.states i) a b) →
  ∃ e : Fin (p.row i).length, (p.slot i e).top = a ∧ (p.slot i e).bottom = b

instance (p : Packet) (i : Fin p.count) (a b : Fin 15) :
    Decidable (p.PairComplete i a b) := by
  unfold Packet.PairComplete
  infer_instance

def Packet.BirthValid (p : Packet) (i : Fin p.count) : Prop :=
  let r := p.record i.val
  if i.val < 3 then r.birthParent = 0 ∧ r.birthSlot = 0 ∧ r.depth = 0
  else 0 < r.birthParent ∧ r.birthParent - 1 < i.val ∧ 0 < r.birthSlot ∧
    ∃ h : r.birthSlot - 1 < (p.record (r.birthParent - 1)).slots.length,
      ((p.record (r.birthParent - 1)).slots[r.birthSlot - 1]'h).target = i.val ∧
      r.depth = (p.record (r.birthParent - 1)).depth + 1

instance (p : Packet) (i : Fin p.count) : Decidable (p.BirthValid i) := by
  unfold Packet.BirthValid
  infer_instance

def Packet.HeaderValid (p : Packet) : Prop :=
  3 ≤ p.count ∧ p.table.size = p.count ∧ p.table.layout = true ∧
  p.power = 2 ∧ p.boxX = 16 ∧ p.boxY = 8 ∧ p.direction = 0 ∧
  p.numerator = archivedNumerator p.fixture ∧
  ∀ k : Fin 3, packetEq (p.state k.val) (archivedRoot k) = true

instance (p : Packet) : Decidable p.HeaderValid := by
  unfold Packet.HeaderValid
  infer_instance

def Packet.RowValid (p : Packet) (i : Fin p.count) : Prop :=
  stateFieldsValid (p.record i.val).stateBits ∧ p.canonical i.val = true ∧
  NamedSharpBox.admitted (p.states i) ∧ NamedSharpBox.admitted (p.states i).swap ∧
  p.index.find (orbitCode (p.states i)) = some i.val ∧
  (∀ e : Fin (p.row i).length, p.SlotValid i (p.slot i e)) ∧
  StrictMono (fun e : Fin (p.row i).length => (p.slot i e).address) ∧
  (∀ a b : Fin 15, p.PairComplete i a b) ∧ p.BirthValid i ∧
  0 < p.weight i.val ∧
  20 * (∑ e : Fin (p.row i).length, p.weight (p.slot i e).target) ≤
    p.numerator * p.weight i.val

instance (p : Packet) (i : Fin p.count) : Decidable (p.RowValid i) := by
  unfold Packet.RowValid StrictMono
  infer_instance

def Packet.Valid (p : Packet) : Prop := p.HeaderValid ∧ ∀ i, p.RowValid i

def Packet.check (p : Packet) : Bool :=
  decide p.HeaderValid && Nat.allLTTR p.count (fun i h => decide (p.RowValid ⟨i,h⟩))

theorem Packet.check_iff (p : Packet) : p.check = true ↔ p.Valid := by
  simp [Packet.check, Packet.Valid, Nat.allLTTR_eq_true, Fin.forall_iff]

def Packet.checkAt (p : Packet) (i : Nat) : Bool :=
  if h : i < p.count then decide (p.RowValid ⟨i,h⟩) else false

theorem Packet.checkAt_iff (p : Packet) (i : Nat) :
    p.checkAt i = true ↔ ∃ h : i < p.count, p.RowValid ⟨i,h⟩ := by
  unfold Packet.checkAt
  split_ifs with h <;> simp [h]

def Packet.checkRange (p : Packet) (start count : Nat) : Bool :=
  Nat.allLTTR count (fun i _ => p.checkAt (start+i))

theorem Packet.checkRange_append (p : Packet) (start a b : Nat)
    (ha : p.checkRange start a = true) (hb : p.checkRange (start+a) b = true) :
    p.checkRange start (a+b) = true := by
  simp only [Packet.checkRange, Nat.allLTTR_eq_true] at *
  intro i hi
  by_cases h : i < a
  · exact ha i h
  · have hsub : i-a < b := by omega
    have heq : start+a+(i-a) = start+i := by omega
    simpa only [heq] using hb (i-a) hsub

theorem Packet.valid_of_range (p : Packet) (header : p.HeaderValid)
    (rows : p.checkRange 0 p.count = true) : p.Valid := by
  refine ⟨header, fun i => ?_⟩
  have hi := (Nat.allLTTR_eq_true.mp rows) i.val i.isLt
  simp only [Nat.zero_add] at hi
  exact (p.checkAt_iff i.val).mp hi |>.choose_spec

/-- Named projections keep the semantic proof independent of the shape of
the executable conjunction. -/
structure RowFacts (p : Packet) (i : Fin p.count) : Prop where
  admitted : NamedSharpBox.admitted (p.states i)
  admitted_swap : NamedSharpBox.admitted (p.states i).swap
  index : p.index.find (orbitCode (p.states i)) = some i.val
  slots : ∀ e : Fin (p.row i).length, p.SlotValid i (p.slot i e)
  ordered : StrictMono (fun e : Fin (p.row i).length => (p.slot i e).address)
  complete : ∀ a b : Fin 15, p.PairComplete i a b
  birth : p.BirthValid i
  positive : 0 < p.weight i.val
  bound : 20 * (∑ e : Fin (p.row i).length, p.weight (p.slot i e).target) ≤
    p.numerator * p.weight i.val

theorem Packet.rowFacts (p : Packet) (h : p.Valid) (i : Fin p.count) : RowFacts p i := by
  obtain ⟨_, _, ha, hs, hl, he, ho, hc, hb, hw, hn⟩ := h.2 i
  exact ⟨ha, hs, hl, he, ho, hc, hb, hw, hn⟩

theorem Packet.target_lt (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin (p.row i).length) : (p.slot i e).target < p.count :=
  ((p.rowFacts h i).slots e).2.2.2.1

def Packet.toCertificate (p : Packet) (h : p.Valid) : Certificate p.count where
  degree := fun i => (p.row i).length
  target := fun i e => ⟨(p.slot i e).target, p.target_lt h i e⟩
  weight := fun i => p.weight i.val
  numerator := p.numerator
  denominator := 20

theorem Packet.toCertificate_valid (p : Packet) (h : p.Valid) :
    (p.toCertificate h).Valid := by
  exact ⟨by change 0 < 20; decide,
    fun i => ⟨(p.rowFacts h i).positive, (p.rowFacts h i).bound⟩⟩

theorem Packet.toCertificate_check (p : Packet) (h : p.Valid) :
    (p.toCertificate h).check = true :=
  (p.toCertificate h).check_iff.mpr (p.toCertificate_valid h)

theorem Packet.orbitDistinct (p : Packet) (h : p.Valid) : OrbitDistinct p.states := by
  intro i j hij
  apply Fin.ext
  have hi := (p.rowFacts h i).index
  have hj := (p.rowFacts h j).index
  have hk : orbitCode (p.states i) = orbitCode (p.states j) := by
    rcases hij with hij | hij
    · rw [hij]
    · rw [hij, orbitCode_swap]
  rw [hk, hj] at hi
  exact (Option.some.inj hi).symm

theorem Packet.literalRowOrdered (p : Packet) (h : p.Valid) (i : Fin p.count) :
    StrictMono (fun e : Fin (p.row i).length => (p.slot i e).address) :=
  (p.rowFacts h i).ordered

theorem Packet.admitted_orderedLift (p : Packet) (h : p.Valid)
    (u : OccurrenceTransport.Packet) (hu : u ∈ orderedLift p.states) :
    NamedSharpBox.admitted u := by
  obtain ⟨i, rfl | rfl⟩ := (mem_orderedLift p.states u).mp hu
  · exact (p.rowFacts h i).admitted
  · exact (p.rowFacts h i).admitted_swap

/-- The named residue decoder constructs an actual occurrence of the same
two full marks, rather than an abstract edge with a matching endpoint. -/
def inverseFromCheck (fixture : Fin 2) {p : OccurrenceTransport.Packet}
    (d : SelectedPair (iterateImages (substitution fixture) 2) p)
    (hc : NamedInverseDecoder.check (pairRhs d) = true) :
    InverseOccurrence (iterateImages (substitution fixture) 2) p
      (decodedCandidate fixture d) :=
  pairLift d (NamedInverseDecoder.inverse (pairRhs d)) (by
    rw [incidenceZ_iterateImages, incidence_eq]
    exact NamedInverseDecoder.inverse_equation _ ((NamedInverseDecoder.check_iff _).mp hc))

@[simp] theorem inverseFromCheck_pair (fixture : Fin 2) {p : OccurrenceTransport.Packet}
    (d : SelectedPair (iterateImages (substitution fixture) 2) p)
    (hc : NamedInverseDecoder.check (pairRhs d) = true) :
    pairOfInverse (inverseFromCheck fixture d hc) = d :=
  pairOfInverse_lift d _ _

def transportInverse {s : Fin 3 → Word} {p u v : OccurrenceTransport.Packet}
    (e : InverseOccurrence s p u) (h : u = v) : InverseOccurrence s p v := h ▸ e

@[simp] theorem transportInverse_pair {s : Fin 3 → Word}
    {p u v : OccurrenceTransport.Packet} (e : InverseOccurrence s p u) (h : u = v) :
    pairOfInverse (transportInverse e h) = pairOfInverse e := by
  cases h
  rfl

def inverseToSlot {s : Fin 3 → Word} {p u : OccurrenceTransport.Packet}
    (swapped : Bool) (e : InverseOccurrence s p (orient u swapped)) : Slot s p u where
  targetSwapped := swapped
  topIndex := e.toForward.topIndex
  bottomIndex := e.toForward.bottomIndex
  packet_eq := e.toForward.packet_eq

@[simp] theorem inverseToSlot_inverse {s : Fin 3 → Word}
    {p u : OccurrenceTransport.Packet} (swapped : Bool)
    (e : InverseOccurrence s p (orient u swapped)) :
    (inverseToSlot swapped e).toInverse = e :=
  e.toForward_toInverse

def Packet.slotPair (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin (p.row i).length) :
    SelectedPair (iterateImages (substitution p.fixture) 2) (p.states i) :=
  selectedPair p.fixture (p.states i) (p.slot i e).top (p.slot i e).bottom
    (((p.rowFacts h i).slots e).2.2.2.2.1)

theorem Packet.slotResidue (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin (p.row i).length) :
    NamedInverseDecoder.check (pairRhs (p.slotPair h i e)) = true :=
  ((p.rowFacts h i).slots e).2.2.2.2.2.1

theorem Packet.slotCandidate (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin (p.row i).length) :
    decodedCandidate p.fixture (p.slotPair h i e) =
      orient (p.states ((p.toCertificate h).target i e)) (p.slot i e).swapped :=
  (packetEq_iff _ _).mp (((p.rowFacts h i).slots e).2.2.2.2.2.2)

def Packet.boundSlot (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin ((p.toCertificate h).degree i)) :
    Slot (iterateImages (substitution p.fixture) 2) (p.states i)
      (p.states ((p.toCertificate h).target i e)) :=
  inverseToSlot (p.slot i e).swapped
    (transportInverse (inverseFromCheck p.fixture (p.slotPair h i e) (p.slotResidue h i e))
      (p.slotCandidate h i e))

theorem Packet.boundSlot_pair (p : Packet) (h : p.Valid) (i : Fin p.count)
    (e : Fin (p.row i).length) :
    pairOfInverse (p.boundSlot h i e).toInverse = p.slotPair h i e := by
  simp only [Packet.boundSlot, inverseToSlot_inverse]
  exact (transportInverse_pair
    (inverseFromCheck p.fixture (p.slotPair h i e) (p.slotResidue h i e))
    (p.slotCandidate h i e)).trans
      (inverseFromCheck_pair p.fixture (p.slotPair h i e) (p.slotResidue h i e))

/-- Exhaustive original digit indexing covers every full selected pair. -/
theorem selectedPair_index (fixture : Fin 2) (p : OccurrenceTransport.Packet)
    (d : SelectedPair (iterateImages (substitution fixture) 2) p) :
    ∃ (a b : Fin 15) (hs : Selected fixture p a b), selectedPair fixture p a b hs = d := by
  let a := NamedArchivedDigits.index fixture d.val.1
  let b := NamedArchivedDigits.index fixture d.val.2
  have ha : NamedArchivedDigits.digit fixture a = d.val.1 :=
    NamedArchivedDigits.digit_index fixture d.val.1
  have hb : NamedArchivedDigits.digit fixture b = d.val.2 :=
    NamedArchivedDigits.digit_index fixture d.val.2
  have hs : Selected fixture p a b := by
    unfold Selected
    rw [ha, hb]
    exact d.property
  refine ⟨a, b, hs, ?_⟩
  exact Subtype.ext (Prod.ext ha hb)

/-- An accepted complete row represents each admitted integral original
pair at an exact slot, retaining its two original parents and full marks. -/
theorem Packet.matchingSlot (p : Packet) (h : p.Valid) (i : Fin p.count)
    (d : SelectedPair (iterateImages (substitution p.fixture) 2) (p.states i))
    (hc : NamedInverseDecoder.check (pairRhs d) = true)
    (ha : NamedSharpBox.admitted (decodedCandidate p.fixture d)) :
    ∃ e : Fin (p.row i).length, pairOfInverse (p.boundSlot h i e).toInverse = d := by
  obtain ⟨a, b, hs, hd⟩ := selectedPair_index p.fixture (p.states i) d
  have hcheck : NamedInverseDecoder.check (rhs p.fixture (p.states i) a b) = true := by
    rw [← hd] at hc
    exact hc
  have hadmit : NamedSharpBox.admitted (candidate p.fixture (p.states i) a b) := by
    rw [← hd] at ha
    exact ha
  obtain ⟨e, ht, hb⟩ := (p.rowFacts h i).complete a b hs hcheck hadmit
  refine ⟨e, ?_⟩
  rw [p.boundSlot_pair]
  apply Subtype.ext
  change (NamedArchivedDigits.digit p.fixture (p.slot i e).top,
    NamedArchivedDigits.digit p.fixture (p.slot i e).bottom) = d.val
  rw [ht, hb]
  exact congrArg Subtype.val hd

theorem slot_pairAddress {s : Fin 3 → Word} {p u : OccurrenceTransport.Packet}
    (e : Slot s p u) :
    pairAddress (pairOfInverse e.toInverse) =
      ((e.rawTarget.top, e.topIndex.val), (e.rawTarget.bottom, e.bottomIndex.val)) := by
  change ((e.rawTarget.top, e.toInverse.toForward.topIndex.val),
    (e.rawTarget.bottom, e.toInverse.toForward.bottomIndex.val)) = _
  rw [e.top_index, e.bottom_index]

def Packet.boundRow (p : Packet) (h : p.Valid) (i : Fin p.count) :
    OccurrenceGraphBinding.Row (iterateImages (substitution p.fixture) 2) p.states i :=
  ⟨(p.toCertificate h).degree i, (p.toCertificate h).target i, p.boundSlot h i⟩

/-- Original order is checked, and in particular excludes duplicated
positional addresses even when their normalized targets coincide. -/
theorem Packet.row_key_injective (p : Packet) (h : p.Valid) (i : Fin p.count) :
    Function.Injective (p.boundRow h i).key := by
  intro e f hkey
  have haddr : pairAddress (pairOfInverse (p.boundSlot h i e).toInverse) =
      pairAddress (pairOfInverse (p.boundSlot h i f).toInverse) := by
    rw [slot_pairAddress, slot_pairAddress]
    exact congrArg (fun k : OccurrenceTransport.Packet × Nat × Nat =>
      ((k.1.top, k.2.1), (k.1.bottom, k.2.2))) hkey
  have hp := pairAddress_injective haddr
  have hp' := (p.boundSlot_pair h i e).symm.trans (hp.trans (p.boundSlot_pair h i f))
  have ht := congrArg (fun d : SelectedPair
    (iterateImages (substitution p.fixture) 2) (p.states i) => d.val.1) hp'
  have hb := congrArg (fun d : SelectedPair
    (iterateImages (substitution p.fixture) 2) (p.states i) => d.val.2) hp'
  change NamedArchivedDigits.digit p.fixture (p.slot i e).top =
    NamedArchivedDigits.digit p.fixture (p.slot i f).top at ht
  change NamedArchivedDigits.digit p.fixture (p.slot i e).bottom =
    NamedArchivedDigits.digit p.fixture (p.slot i f).bottom at hb
  have htop := (NamedArchivedDigits.digit_injective p.fixture) ht
  have hbottom := (NamedArchivedDigits.digit_injective p.fixture) hb
  apply (p.rowFacts h i).ordered.injective
  simp only [RawSlot.address, htop, hbottom]

/-- All actual incoming occurrences whose ancestors are represented occur
in the checked row.  Admission of every stored orientation is checked,
so a geometric exclusion cannot conceal an edge between stored states. -/
theorem Packet.row_exact (p : Packet) (h : p.Valid) (i : Fin p.count) :
    (p.boundRow h i).Exact := by
  refine ⟨p.row_key_injective h i, ?_⟩
  intro u hu ti bi hp
  let f : ForwardOccurrence (iterateImages (substitution p.fixture) 2) u (p.states i) :=
    ⟨ti, bi, hp⟩
  let inv := f.toInverse
  obtain ⟨hc, hd⟩ := decodedCandidate_of_occurrence p.fixture inv
  obtain ⟨e, he⟩ := p.matchingSlot h i (pairOfInverse inv) hc (by
    rw [hd]
    exact p.admitted_orderedLift h u hu)
  have hraw : (p.boundSlot h i e).rawTarget = u := by
    have hs := (decodedCandidate_of_occurrence p.fixture (p.boundSlot h i e).toInverse).2
    rw [he, hd] at hs
    exact hs.symm
  have ht : (p.boundSlot h i e).topIndex.val = ti.val := by
    have hh := congrArg (fun a : (Fin 3 × Nat) × (Fin 3 × Nat) => a.1.2)
      (congrArg pairAddress he)
    rw [slot_pairAddress] at hh
    change (p.boundSlot h i e).topIndex.val = inv.toForward.topIndex.val at hh
    simpa only [inv, ForwardOccurrence.toInverse_toForward] using hh
  have hb : (p.boundSlot h i e).bottomIndex.val = bi.val := by
    have hh := congrArg (fun a : (Fin 3 × Nat) × (Fin 3 × Nat) => a.2.2)
      (congrArg pairAddress he)
    rw [slot_pairAddress] at hh
    change (p.boundSlot h i e).bottomIndex.val = inv.toForward.bottomIndex.val at hh
    simpa only [inv, ForwardOccurrence.toInverse_toForward] using hh
  exact ⟨e, hraw, ht, hb⟩

/-- The same original target list indexes both literal geometric rows and
the potential inequality; parallel targets remain separate slots. -/
def Packet.tableBinding (p : Packet) (h : p.Valid) :
    TableBinding (iterateImages (substitution p.fixture) 2) p.states (p.toCertificate h) where
  slot := p.boundSlot h
  distinct := p.orbitDistinct h
  exactRows := p.row_exact h

theorem Packet.candidatesClosed (p : Packet) (h : p.Valid) :
    DecodedCandidatesClosed p.fixture p.states := by
  intro i d hc ha
  obtain ⟨e, he⟩ := p.matchingSlot h i d hc ha
  have hs := (decodedCandidate_of_occurrence p.fixture (p.boundSlot h i e).toInverse).2
  rw [he] at hs
  rw [hs]
  exact orient_mem_orderedLift p.states ((p.toCertificate h).target i e) (p.slot i e).swapped

def Packet.rootID (p : Packet) (h : p.Valid) (i : Fin 3) : Fin p.count :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt h.1.1⟩

theorem Packet.rootBound (p : Packet) (h : p.Valid) (i : Fin 3) :
    p.states (p.rootID h i) = archivedRoot i := by
  obtain ⟨_, _, _, _, _, _, _, _, hr⟩ := h.1
  exact (packetEq_iff _ _).mp (hr i)

theorem Packet.numerator_eq (p : Packet) (h : p.Valid) :
    (p.toCertificate h).numerator = archivedNumerator p.fixture := by
  obtain ⟨_, _, _, _, _, _, _, hn, _⟩ := h.1
  exact hn

/-- An actual earlier slot, not an endpoint-only reachability label,
authenticates every nonroot discovery in the original row inventory. -/
theorem Packet.tableDiscovery (p : Packet) (h : p.Valid) :
    TableDiscovery (p.tableBinding h).row ArchivedRoot := by
  intro i
  by_cases hi : i.val < 3
  · refine Or.inl ⟨⟨i.val, hi⟩, Or.inl ?_⟩
    exact p.rootBound h ⟨i.val, hi⟩
  · have hb := (p.rowFacts h i).birth
    simp only [Packet.BirthValid, hi, ↓reduceIte] at hb
    obtain ⟨_, hlt, _, hlen, htarget, _⟩ := hb
    let j : Fin p.count := ⟨(p.record i.val).birthParent - 1, Nat.lt_trans hlt i.isLt⟩
    let k : Fin (p.row j).length := ⟨(p.record i.val).birthSlot - 1, hlen⟩
    refine Or.inr ⟨j, k, hlt, ?_⟩
    exact Fin.ext htarget

end Psc.ArchivedPayload
