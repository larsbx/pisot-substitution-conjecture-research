import PscVerif.OccurrenceSwapCounts

/-!
# Literal binding of normalized inverse rows

A normalized target identifier does not identify an oriented inverse edge.
Each slot below keeps the target orientation and both actual image positions.
Earlier-index discovery witnesses derive ancestry on the ordered lift; they
do not assume ancestry, uniform degrees, or a compact-overlap cover.

The executable twelve-source inventory is a separate finite receipt. These
theorems give its mathematical interface, not a kernel evaluation of that
serialized inventory. Pre-code gate:
`docs/c4-literal-inverse-binding-literature-2026-11-10.md`.
-/

namespace Psc.OccurrenceGraphBinding

open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceMass
open Psc.OccurrenceInverse Psc.OccurrenceSwapCounts Psc.OccurrenceNewborn
open Matrix

attribute [local instance] Classical.propDecidable

/-- Recover the raw target from its stored representative and orientation. -/
def orient (p : Packet) : Bool → Packet
  | false => p
  | true => p.swap

@[simp] theorem orient_false (p : Packet) : orient p false = p := rfl
@[simp] theorem orient_true (p : Packet) : orient p true = p.swap := rfl

theorem orient_orient (p : Packet) (b : Bool) : orient (orient p b) b = p := by
  cases b
  · rfl
  · exact packet_swap_swap p

/-- A single serialized slot authenticates both positions and the raw
ancestor. Equal normalized targets remain distinct positional records. -/
structure Slot (s : Fin 3 → Word) (current stored : Packet) where
  targetSwapped : Bool
  topIndex : Fin (s (orient stored targetSwapped).top).length
  bottomIndex : Fin (s (orient stored targetSwapped).bottom).length
  packet_eq : current = digitPacket s (orient stored targetSwapped) topIndex bottomIndex

def Slot.rawTarget {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) : Packet :=
  orient u e.targetSwapped

def Slot.toForward {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    ForwardOccurrence s e.rawTarget p :=
  ⟨e.topIndex, e.bottomIndex, e.packet_eq⟩

/-- Binding a normalized slot constructs the actual incoming marks. -/
def Slot.toInverse {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    InverseOccurrence s p e.rawTarget := e.toForward.toInverse

theorem Slot.top_index {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    e.toInverse.toForward.topIndex = e.topIndex := by
  exact congrArg ForwardOccurrence.topIndex
    (ForwardOccurrence.toInverse_toForward e.toForward)

theorem Slot.bottom_index {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    e.toInverse.toForward.bottomIndex = e.bottomIndex := by
  exact congrArg ForwardOccurrence.bottomIndex
    (ForwardOccurrence.toInverse_toForward e.toForward)

theorem Slot.top_prefix {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    e.toInverse.topMark.before = (s e.rawTarget.top).take e.topIndex.val := rfl

theorem Slot.bottom_prefix {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    e.toInverse.bottomMark.before = (s e.rawTarget.bottom).take e.bottomIndex.val := rfl

theorem Slot.integral_equation {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) :
    incidenceZ s *ᵥ e.rawTarget.delta = p.delta +
      residual ((s e.rawTarget.bottom).take e.bottomIndex.val)
        ((s e.rawTarget.top).take e.topIndex.val) := e.toInverse.equation

/-- Both orientations are represented even though serialized rows use only
one representative per orbit. No assertion of unique representatives yet. -/
noncomputable def orderedLift {n : ℕ} (states : Fin n → Packet) : Finset Packet := by
  classical
  exact Finset.univ.image states ∪ Finset.univ.image (fun i => (states i).swap)

theorem mem_orderedLift {n : ℕ} (states : Fin n → Packet) (p : Packet) :
    p ∈ orderedLift states ↔ ∃ i, p = states i ∨ p = (states i).swap := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      exact ⟨i, Or.inl hi.symm⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      exact ⟨i, Or.inr hi.symm⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem state_mem_orderedLift {n : ℕ} (states : Fin n → Packet) (i : Fin n) :
    states i ∈ orderedLift states :=
  (mem_orderedLift states (states i)).mpr ⟨i, Or.inl rfl⟩

theorem orient_mem_orderedLift {n : ℕ} (states : Fin n → Packet)
    (i : Fin n) (b : Bool) : orient (states i) b ∈ orderedLift states := by
  apply (mem_orderedLift states _).mpr
  exact ⟨i, by cases b <;> simp [orient]⟩

theorem orderedLift_swap_closed {n : ℕ} (states : Fin n → Packet) :
    ∀ p ∈ orderedLift states, p.swap ∈ orderedLift states := by
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := (mem_orderedLift states p).mp hp
  · exact (mem_orderedLift states _).mpr ⟨i, Or.inr rfl⟩
  · rw [packet_swap_swap]
    exact state_mem_orderedLift states i

/-- A bound slot is one of the complete positional edges on the ordered lift. -/
def Slot.edge {n : ℕ} {s : Fin 3 → Word} (states : Fin n → Packet)
    {i j : Fin n} (e : Slot s (states i) (states j)) : Edge s (orderedLift states) :=
  ⟨⟨orient (states j) e.targetSwapped, orient_mem_orderedLift states j e.targetSwapped⟩,
    ⟨(e.topIndex, e.bottomIndex), by
      change digitPacket s (orient (states j) e.targetSwapped) e.topIndex e.bottomIndex ∈
        orderedLift states
      rw [← e.packet_eq]
      exact state_mem_orderedLift states i⟩⟩

theorem Slot.edge_target {n : ℕ} {s : Fin 3 → Word} (states : Fin n → Packet)
    {i j : Fin n} (e : Slot s (states i) (states j)) :
    target s (orderedLift states) (e.edge states) =
      ⟨states i, state_mem_orderedLift states i⟩ :=
  Subtype.ext e.packet_eq.symm

/-- Compare full edge identities using source and both numeric positions. -/
theorem edge_ext {s : Fin 3 → Word} {S : Finset Packet} (e f : Edge s S)
    (hs : e.1.val = f.1.val)
    (ht : e.2.val.1.val = f.2.val.1.val)
    (hb : e.2.val.2.val = f.2.val.2.val) : e = f := by
  rcases e with ⟨⟨p, hp⟩, ⟨⟨ti, bi⟩, he⟩⟩
  rcases f with ⟨⟨q, hq⟩, ⟨⟨tj, bj⟩, hf⟩⟩
  dsimp at hs ht hb
  cases hs
  have hi : ti = tj := Fin.ext ht
  have hj : bi = bj := Fin.ext hb
  cases hi
  cases hj
  rfl

/-- A serialized inverse row with one distinct type element per slot. -/
structure Row {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet) (i : Fin n) where
  degree : ℕ
  targetID : Fin degree → Fin n
  slot : (k : Fin degree) → Slot s (states i) (states (targetID k))

def Row.key {n : ℕ} {s : Fin 3 → Word} {states : Fin n → Packet} {i : Fin n}
    (row : Row s states i) (k : Fin row.degree) : Packet × ℕ × ℕ :=
  ((row.slot k).rawTarget, (row.slot k).topIndex.val, (row.slot k).bottomIndex.val)

/-- Exactness states the finite positional checks, without referring to the
desired transpose, degree uniformity or an asserted graph isomorphism. -/
def Row.Exact {n : ℕ} {s : Fin 3 → Word} {states : Fin n → Packet} {i : Fin n}
    (row : Row s states i) : Prop :=
  Function.Injective row.key ∧
    ∀ u ∈ orderedLift states,
      ∀ ti : Fin (s u.top).length, ∀ bi : Fin (s u.bottom).length,
      states i = digitPacket s u ti bi →
        ∃ k, (row.slot k).rawTarget = u ∧
          (row.slot k).topIndex.val = ti.val ∧ (row.slot k).bottomIndex.val = bi.val

/-- All incoming positional edges at the particular serialized representative. -/
abbrev Incoming {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet) (i : Fin n) :=
  {e : Edge s (orderedLift states) //
    target s (orderedLift states) e = ⟨states i, state_mem_orderedLift states i⟩}

def Row.toIncoming {n : ℕ} {s : Fin 3 → Word} {states : Fin n → Packet} {i : Fin n}
    (row : Row s states i) (k : Fin row.degree) : Incoming s states i :=
  ⟨(row.slot k).edge states, (row.slot k).edge_target states⟩

theorem Row.toIncoming_injective {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact) : Function.Injective row.toIncoming := by
  intro k l h
  apply exactness.1
  have hs := congrArg (fun e : Incoming s states i => e.val.1.val) h
  have ht := congrArg (fun e : Incoming s states i => e.val.2.val.1.val) h
  have hb := congrArg (fun e : Incoming s states i => e.val.2.val.2.val) h
  exact Prod.ext hs (Prod.ext ht hb)

theorem Row.toIncoming_surjective {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact) : Function.Surjective row.toIncoming := by
  intro e
  have hp : states i = digitPacket s e.val.1.val e.val.2.val.1 e.val.2.val.2 :=
    (congrArg Subtype.val e.property).symm
  obtain ⟨k, hu, ht, hb⟩ := exactness.2 e.val.1.val e.val.1.property
    e.val.2.val.1 e.val.2.val.2 hp
  refine ⟨k, Subtype.ext ?_⟩
  exact edge_ext _ _ hu ht hb

/-- The positional checks prove an equivalence; no slot or parallel edge is lost. -/
noncomputable def Row.incomingEquiv {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact) : Fin row.degree ≃ Incoming s states i :=
  Equiv.ofBijective row.toIncoming
    ⟨row.toIncoming_injective exactness, row.toIncoming_surjective exactness⟩

noncomputable def labelAt {n : ℕ} (states : Fin n → Packet) (i : Fin n) :
    PacketLabel (orderedLift states) (orderedLift_swap_closed states) :=
  label (stateSwap (orderedLift states) (orderedLift_swap_closed states))
    ⟨states i, state_mem_orderedLift states i⟩

/-- Different stored IDs must denote different exact track-swap orbits. -/
def OrbitDistinct {n : ℕ} (states : Fin n → Packet) : Prop :=
  ∀ i j, states i = states j ∨ states i = (states j).swap → i = j

theorem labelAt_injective {n : ℕ} (states : Fin n → Packet)
    (distinct : OrbitDistinct states) : Function.Injective (labelAt states) := by
  intro i j hij
  apply distinct i j
  rcases (label_eq_iff _ (stateSwap_involutive _ _) _ _).mp hij with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem labelAt_surjective {n : ℕ} (states : Fin n → Packet) :
    Function.Surjective (labelAt states) := by
  intro q
  let sw := stateSwap (orderedLift states) (orderedLift_swap_closed states)
  let p := representative sw q
  have hp : p.val ∈ orderedLift states := p.property
  obtain ⟨i, hi⟩ := (mem_orderedLift states p.val).mp hp
  refine ⟨i, ?_⟩
  have heq : labelAt states i = label sw p := by
    apply (label_eq_iff sw (stateSwap_involutive _ _) _ _).mpr
    rcases hi with hi | hi
    · exact Or.inl (Subtype.ext hi.symm)
    · apply Or.inr
      apply Subtype.ext
      change states i = p.val.swap
      rw [hi, packet_swap_swap]
  exact heq.trans (label_representative sw q)

/-- A duplicate-free representative table is exactly the actual orbit label set. -/
noncomputable def labelEquiv {n : ℕ} (states : Fin n → Packet)
    (distinct : OrbitDistinct states) :
    Fin n ≃ PacketLabel (orderedLift states) (orderedLift_swap_closed states) :=
  Equiv.ofBijective (labelAt states)
    ⟨labelAt_injective states distinct, labelAt_surjective states⟩

/-- Normalization changes the source representative but not its exact orbit. -/
theorem Slot.edge_source_label {n : ℕ} {s : Fin 3 → Word}
    (states : Fin n → Packet) {i j : Fin n} (e : Slot s (states i) (states j)) :
    label (stateSwap (orderedLift states) (orderedLift_swap_closed states))
      (source s (orderedLift states) (e.edge states)) = labelAt states j := by
  cases hb : e.targetSwapped with
  | false =>
    apply congrArg (label (stateSwap (orderedLift states) (orderedLift_swap_closed states)))
    apply Subtype.ext
    simp [source, Slot.edge, hb]
  | true =>
    have hs : source s (orderedLift states) (e.edge states) =
        stateSwap (orderedLift states) (orderedLift_swap_closed states)
          ⟨states j, state_mem_orderedLift states j⟩ := by
      apply Subtype.ext
      simp [source, Slot.edge, hb, stateSwap]
    rw [hs]
    exact label_swap _ (stateSwap_involutive _ _) _

/-- Serialized inverse multiplicity counts positions with a matching target orbit. -/
noncomputable def Row.count {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (j : PacketLabel (orderedLift states) (orderedLift_swap_closed states)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k => labelAt states (row.targetID k) = j)).card

/-- The ordinary serialized matrix entry counts repeated target IDs. -/
def Row.matrixEntry {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => row.targetID k = j)).card

theorem Row.count_labelAt {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (distinct : OrbitDistinct states) (j : Fin n) :
    row.count (labelAt states j) = row.matrixEntry j := by
  classical
  simp only [Row.count, Row.matrixEntry, (labelAt_injective states distinct).eq_iff]

theorem Row.count_eq_inverseDegree {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact)
    (j : PacketLabel (orderedLift states) (orderedLift_swap_closed states)) :
    row.count j = PscVerif.OccurrenceMassCounts.inverseDegree
      (source s (orderedLift states)) (target s (orderedLift states))
      (label (stateSwap (orderedLift states) (orderedLift_swap_closed states)))
      ⟨states i, state_mem_orderedLift states i⟩ j := by
  classical
  unfold Row.count PscVerif.OccurrenceMassCounts.inverseDegree
  apply Finset.card_bij (fun k _ => (row.slot k).edge states)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    refine ⟨(row.slot k).edge_target states, ?_⟩
    rw [(row.slot k).edge_source_label states]
    exact hk
  · intro k hk l hl h
    apply row.toIncoming_injective exactness
    exact Subtype.ext h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨ht, hs⟩ := he
    obtain ⟨k, hk⟩ := row.toIncoming_surjective exactness ⟨e, ht⟩
    have hedge : (row.slot k).edge states = e := congrArg Subtype.val hk
    refine ⟨k, ?_, hedge⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← (row.slot k).edge_source_label states, hedge]
    exact hs

/-- Exact serialized positional rows inherit the already proved uniform
quotient matrix, without assuming uniformity as another input. -/
theorem Row.count_eq_packetInverse {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact)
    (j : PacketLabel (orderedLift states) (orderedLift_swap_closed states)) :
    row.count j = packetInverse s (orderedLift states) (orderedLift_swap_closed states)
      (labelAt states i) j := by
  rw [row.count_eq_inverseDegree exactness]
  exact packet_inverse_uniform s _ _ _ _

theorem ancestry_root (s : Fin 3 → Word) (roots : Packet → Prop) {p : Packet}
    (hp : roots p) : Ancestry s roots p := ⟨p, hp, .refl⟩

theorem ancestry_step (s : Fin 3 → Word) (roots : Packet → Prop) {p u : Packet}
    (hp : Ancestry s roots p) (e : InverseOccurrence s p u) : Ancestry s roots u := by
  obtain ⟨r, hr, hpath⟩ := hp
  exact ⟨r, hr, hpath.tail ⟨e⟩⟩

/-- A normalized discovery transports ancestry by swapping the entire path
when necessary, not by replacing only its final packet label. -/
theorem Slot.ancestry {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u)
    (roots : Packet → Prop) (closed : ∀ r, roots r → roots r.swap)
    (hp : Ancestry s roots p) : Ancestry s roots u := by
  have hu := ancestry_step s roots hp e.toInverse
  cases hb : e.targetSwapped with
  | false => simpa [Slot.rawTarget, hb] using hu
  | true =>
    have hswap := ancestry_swap_closed s roots closed hu
    simpa [Slot.rawTarget, hb, packet_swap_swap] using hswap

/-- Every nonroot has a literal discovery edge from a strictly earlier ID.
The order condition excludes self-justifying and circular certificates. -/
def Discovery {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet)
    (roots : Packet → Prop) : Prop :=
  ∀ i, roots (states i) ∨
    ∃ j, j.val < i.val ∧ Nonempty (Slot s (states j) (states i))

/-- A discovery certificate can name an existing serialized row slot.
This binds the spanning witness to the same inventory used for counting. -/
def TableDiscovery {n : ℕ} {s : Fin 3 → Word} {states : Fin n → Packet}
    (rows : (i : Fin n) → Row s states i) (roots : Packet → Prop) : Prop :=
  ∀ i, roots (states i) ∨ ∃ j, ∃ k : Fin (rows j).degree,
    j.val < i.val ∧ (rows j).targetID k = i

theorem tableDiscovery_discovery {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} (rows : (i : Fin n) → Row s states i)
    (roots : Packet → Prop) (discovery : TableDiscovery rows roots) :
    Discovery s states roots := by
  intro i
  rcases discovery i with hr | ⟨j, k, hj, hk⟩
  · exact Or.inl hr
  · refine Or.inr ⟨j, hj, ?_⟩
    have e := (rows j).slot k
    rw [hk] at e
    exact ⟨e⟩

/-- The earliest serialized state cannot be justified by a circular edge. -/
theorem discovery_zero_root {n : ℕ} (s : Fin 3 → Word)
    (states : Fin (n + 1) → Packet) (roots : Packet → Prop)
    (discovery : Discovery s states roots) : roots (states 0) := by
  rcases discovery 0 with hr | ⟨j, hj, _⟩
  · exact hr
  · simp at hj

theorem discovery_ancestry {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet)
    (roots : Packet → Prop) (closed : ∀ r, roots r → roots r.swap)
    (discovery : Discovery s states roots) :
    ∀ i, Ancestry s roots (states i) := by
  have aux : ∀ k, ∀ i : Fin n, i.val = k → Ancestry s roots (states i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hval
      rcases discovery i with hroot | ⟨j, hji, ⟨e⟩⟩
      · exact ancestry_root s roots hroot
      · exact e.ancestry roots closed (ih j.val (by omega) j rfl)
  intro i
  exact aux i.val i rfl

theorem orderedLift_ancestry {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet)
    (roots : Packet → Prop) (closed : ∀ r, roots r → roots r.swap)
    (discovery : Discovery s states roots) :
    ∀ p ∈ orderedLift states, Ancestry s roots p := by
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := (mem_orderedLift states p).mp hp
  · exact discovery_ancestry s states roots closed discovery i
  · exact ancestry_swap_closed s roots closed
      (discovery_ancestry s states roots closed discovery i)

/-- Actual earlier-ID witnesses discharge the ancestry premise of the
existing transpose theorem. Neither uniformity nor freeness is assumed. -/
theorem discovery_packet_transpose {n : ℕ} (s : Fin 3 → Word)
    (states : Fin n → Packet) (roots : Packet → Prop)
    (rootClosed : ∀ r, roots r → roots r.swap)
    (discovery : Discovery s states roots)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal) :
    ∀ i j, packetInverse s (orderedLift states) (orderedLift_swap_closed states) i j =
      packetForward s (orderedLift states) (orderedLift_swap_closed states) j i :=
  ancestry_packet_transpose s roots ℓ β hpos hβ hscale hroots
    (orderedLift states) (orderedLift_swap_closed states)
    (orderedLift_ancestry s states roots rootClosed discovery)

/-- Compose the two independent bindings: exact positional rows give the
incoming matrix, while rooted discovery makes its orbit transpose unweighted. -/
theorem Row.count_eq_packetForward {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {i : Fin n} (row : Row s states i)
    (exactness : row.Exact) (roots : Packet → Prop)
    (rootClosed : ∀ r, roots r → roots r.swap)
    (discovery : Discovery s states roots)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal)
    (j : PacketLabel (orderedLift states) (orderedLift_swap_closed states)) :
    row.count j = packetForward s (orderedLift states) (orderedLift_swap_closed states)
      j (labelAt states i) := by
  rw [row.count_eq_packetInverse exactness]
  exact discovery_packet_transpose s states roots rootClosed discovery
    ℓ β hpos hβ hscale hroots _ _

/-- A complete serialized table needs only positional exactness, rooted
earlier-slot discovery and the physical scaling inputs for the transpose. -/
theorem table_count_transpose {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} (rows : (i : Fin n) → Row s states i)
    (exactness : ∀ i, (rows i).Exact) (roots : Packet → Prop)
    (rootClosed : ∀ r, roots r → roots r.swap)
    (discovery : TableDiscovery rows roots)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal)
    (i : Fin n) (j : PacketLabel (orderedLift states) (orderedLift_swap_closed states)) :
    (rows i).count j = packetForward s (orderedLift states) (orderedLift_swap_closed states)
      j (labelAt states i) :=
  (rows i).count_eq_packetForward (exactness i) roots rootClosed
    (tableDiscovery_discovery rows roots discovery) ℓ β hpos hβ hscale hroots j

/-- With unique orbit representatives, the raw repeated-target matrix entry
is the forward positional count with its indices transposed. -/
theorem table_matrixEntry_transpose {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} (rows : (i : Fin n) → Row s states i)
    (distinct : OrbitDistinct states) (exactness : ∀ i, (rows i).Exact)
    (roots : Packet → Prop) (rootClosed : ∀ r, roots r → roots r.swap)
    (discovery : TableDiscovery rows roots)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal)
    (i j : Fin n) :
    (rows i).matrixEntry j = packetForward s (orderedLift states)
      (orderedLift_swap_closed states) (labelAt states j) (labelAt states i) := by
  rw [← (rows i).count_labelAt distinct j]
  exact table_count_transpose rows exactness roots rootClosed discovery
    ℓ β hpos hβ hscale hroots i (labelAt states j)

end Psc.OccurrenceGraphBinding
