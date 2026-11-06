import PscVerif.OverlapContraction

/-! Balanced row data imported from the canonical Mojo graph engine. Kernel computation
checks dimensions, target bounds, positive weights and every occurrence sum.
No graph-completeness or geometric assertion is inferred from these checks. -/

namespace PscVerif.OverlapPacket

open scoped BigOperators
open PscVerif.OverlapContraction

inductive Table (α : Type) where
  | empty
  | leaf (value : α)
  | branch (leftSize : Nat) (left right : Table α)

def Table.size {α : Type} : Table α → Nat
  | .empty => 0
  | .leaf _ => 1
  | .branch _ l r => l.size + r.size

def Table.toList {α : Type} : Table α → List α
  | .empty => []
  | .leaf a => [a]
  | .branch _ l r => l.toList ++ r.toList

def Table.layout {α : Type} : Table α → Bool
  | .empty => true
  | .leaf _ => true
  | .branch cut l r => decide (cut = l.size) && l.layout && r.layout

def Table.get? {α : Type} : Table α → Nat → Option α
  | .empty, _ => none
  | .leaf a, i => if i = 0 then some a else none
  | .branch cut l r, i => if i < cut then l.get? i else r.get? (i - cut)

theorem Table.length_toList {α : Type} (t : Table α) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | branch cut l r ihl ihr => simp [Table.toList, Table.size, ihl, ihr]

theorem Table.get?_eq_toList {α : Type} (t : Table α) (valid : t.layout = true)
    (i : Nat) : t.get? i = t.toList[i]? := by
  induction t generalizing i with
  | empty => simp [Table.get?, Table.toList]
  | leaf a => cases i <;> simp [Table.get?, Table.toList]
  | branch cut l r ihl ihr =>
    simp only [Table.layout, Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨⟨hc, hl⟩, hr⟩ := valid
    subst cut
    simp only [Table.get?, Table.toList]
    split_ifs with h
    · rw [ihl hl]
      exact (List.getElem?_append_left (by simpa [Table.length_toList] using h)).symm
    · rw [ihr hr]
      rw [List.getElem?_append_right (by simpa [Table.length_toList] using Nat.le_of_not_gt h)]
      rw [Table.length_toList]

structure Row where
  state : String
  weight : Nat
  targets : List Nat
deriving Inhabited

structure Packet where
  source : Nat
  count : Nat
  table : Table Nat
  residueRejections : Nat
  boxRejections : Nat
  sweeps : Nat

def decodeTargets : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, bits => bits % 16384 :: decodeTargets k (bits / 16384)

def decodeRow (bits : Nat) : Row :=
  let state := (bits / 1073741824) % 33554432
  { state := s!"{state % 4} {(state / 4) % 4} {(state / 16 % 128 : Int)-64} {(state / 2048 % 128 : Int)-64} {(state / 262144 % 128 : Int)-64}"
    weight := bits % 1048576
    targets := decodeTargets ((bits / 1048576) % 1024) (bits / 36028797018963968) }

def Packet.raw (p : Packet) (i : Nat) : Nat := (p.table.get? i).getD 0
def Packet.record (p : Packet) (i : Nat) : Row := decodeRow (p.raw i)
def Packet.canonical (p : Packet) (i : Nat) : Bool :=
  let bits := p.raw i
  decide ((bits / 36028797018963968) / (16384 ^ ((bits / 1048576) % 1024)) = 0)
def Packet.weight (p : Packet) (i : Nat) : Nat := (p.record i).weight
def Packet.row (p : Packet) (i : Fin p.count) : List Nat := (p.record i.val).targets
def Packet.childWeight (p : Packet) (i : Nat) : Nat := p.weight i

def Packet.HeaderValid (p : Packet) : Prop :=
  p.source < 18 ∧ 3 ≤ p.count ∧
  p.table.size = p.count ∧ p.table.layout = true ∧
  (p.record 0).state = "0 1 0 0 0" ∧
  (p.record 1).state = "0 2 0 0 0" ∧
  (p.record 2).state = "1 2 0 0 0"

def Packet.RowValid (p : Packet) (i : Fin p.count) : Prop :=
    0 < p.weight i.val ∧
    (∀ e : Fin (p.row i).length, (p.row i)[e] < p.count) ∧
    20 * (∑ e : Fin (p.row i).length, p.childWeight ((p.row i)[e])) ≤
      102 * p.weight i.val ∧ p.canonical i.val = true

instance (p : Packet) : Decidable p.HeaderValid := by
  unfold Packet.HeaderValid
  infer_instance

instance (p : Packet) (i : Fin p.count) : Decidable (p.RowValid i) := by
  unfold Packet.RowValid
  infer_instance

def Packet.Valid (p : Packet) : Prop := p.HeaderValid ∧ ∀ i, p.RowValid i

/-- The proven-equivalent linear Boolean loop avoids quadratic kernel
reduction of the generic bounded-forall decision procedure. -/
def Packet.check (p : Packet) : Bool :=
  decide p.HeaderValid &&
    Nat.allLTTR p.count (fun i h => decide (p.RowValid ⟨i, h⟩))

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

theorem Packet.row_valid (p : Packet) (h : p.Valid) (i : Fin p.count) :
    0 < p.weight i.val ∧
    (∀ e : Fin (p.row i).length, (p.row i)[e] < p.count) ∧
    20 * (∑ e : Fin (p.row i).length, p.childWeight ((p.row i)[e])) ≤
      102 * p.weight i.val := ⟨(h.2 i).1, (h.2 i).2.1, (h.2 i).2.2.1⟩

/-- Invalid target indices are rejected, never reduced modulo the graph size. -/
def Packet.toCertificate (p : Packet) (h : p.Valid) : Certificate p.count where
  degree := fun i => (p.row i).length
  target := fun i e => ⟨(p.row i)[e], (p.row_valid h i).2.1 e⟩
  weight := fun i => p.weight i.val
  numerator := 102
  denominator := 20

theorem Packet.toCertificate_valid (p : Packet) (h : p.Valid) :
    (p.toCertificate h).Valid := by
  refine ⟨by change 0 < 20; decide, fun i => ⟨(p.row_valid h i).1, ?_⟩⟩
  exact (p.row_valid h i).2.2

theorem Packet.toCertificate_check (p : Packet) (h : p.Valid) :
    (p.toCertificate h).check = true :=
  (p.toCertificate h).check_iff.mpr (p.toCertificate_valid h)

/-- The concrete imported inequalities feed the previously verified inference.
The caller still supplies the recurrence for the actual measured overlaps. -/
theorem Packet.sound (p : Packet) (accepted : p.check = true)
    (v : Fin p.count → ℝ) (scale : ℝ) (hv : ∀ i, 0 ≤ v i)
    (recurrence : ∀ i, scale * v i ≤
      ∑ e : Fin (p.row i).length,
        v ⟨(p.row i)[e], (p.row_valid (p.check_iff.mp accepted) i).2.1 e⟩)
    (gap : (102 : ℝ) < 20 * scale) : ∀ i, v i = 0 := by
  let h := p.check_iff.mp accepted
  let : Nonempty (Fin p.count) := ⟨⟨0, by have := h.1.2.1; omega⟩⟩
  exact (p.toCertificate h).sound (p.toCertificate_check h) v scale hv recurrence gap

def Packet.emit (p : Packet) : IO Unit := do
  let records := (p.table.toList.map decodeRow).toArray
  let edges := records.foldl (fun total row => total + row.targets.length) 0
  IO.println s!"graph {p.source} {p.count} {edges} {p.residueRejections} {p.boxRejections} {p.sweeps} 102 20"
  for i in [:records.size] do
    let r := records[i]!
    IO.println s!"node {p.source} {i} {r.state} {r.weight}"
    let targets := r.targets.foldl (fun text j => text ++ s!" {j}") ""
    IO.println s!"row {p.source} {i} {r.targets.length}{targets}"

def encodeControl (c d weight : Nat) (targets : List Nat) : Nat :=
  let payload := targets.foldr (fun j rest => j + 16384 * rest) 0
  let state := c + 4*d + 16*64 + 2048*64 + 262144*64
  ((payload*33554432+state)*1024+targets.length)*1048576+weight

def control (firstBits : Nat) : Packet where
  source := 0
  count := 3
  table := .branch 1 (.leaf firstBits)
    (.branch 1 (.leaf (encodeControl 0 2 1 [])) (.leaf (encodeControl 1 2 1 [])))
  residueRejections := 0
  boxRejections := 0
  sweeps := 0

def terminalControl := control (encodeControl 0 1 1 [])

theorem terminal_packet_accepted : terminalControl.check = true := by decide +kernel

theorem invalid_target_refused :
    (control (encodeControl 0 1 1 [3])).check = false := by decide +kernel

theorem repeated_occurrences_counted :
    (control (encodeControl 0 1 1 [0,0,0,0,0,0])).check = false := by decide +kernel

theorem zero_weight_refused :
    (control (encodeControl 0 1 0 [])).check = false := by decide +kernel

theorem missing_row_refused :
    ({terminalControl with count := 4} : Packet).check = false := by decide +kernel

theorem invalid_source_refused :
    ({terminalControl with source := 18} : Packet).check = false := by decide +kernel

theorem false_layout_refused :
    ({terminalControl with table := (.branch 0
      (.leaf (encodeControl 0 1 1 []))
      (.branch 1 (.leaf (encodeControl 0 2 1 [])) (.leaf (encodeControl 1 2 1 []))))} : Packet).check = false := by decide +kernel

theorem hidden_payload_refused :
    (control (encodeControl 0 1 1 [] + 36028797018963968)).check = false := by decide +kernel

end PscVerif.OverlapPacket
