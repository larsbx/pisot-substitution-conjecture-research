/-
# Literal track-swap quotient counts

The finite graph below retains every ordered pair of image positions.
Its edge involution swaps the positions as well as the source packet.
Orbit representatives only define the quotient matrices: their degree
uniformity is proved from this involution, not supplied as a hypothesis.

The state domain is supplied finite and swap-closed.  This module neither
constructs a geometrically complete inverse domain nor supplies a loss.
Pre-code review: `docs/c4-inverse-occurrence-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceMass
import PscVerif.OccurrenceMassCounts
import PscVerif.OccurrenceInverse

namespace Psc.OccurrenceSwapCounts

open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceMass
open Psc.OccurrenceNewborn
open PscVerif.OccurrenceMassCounts

attribute [local instance] Classical.propDecidable

section InvolutionCounts

variable {Ω E : Type*} [Fintype Ω] [Fintype E]

/-- The actual orbit, including its singleton fixed-point case. -/
noncomputable def orbit (swap : Ω → Ω) (x : Ω) : Finset Ω := by
  classical
  exact {x, swap x}

/-- Only represented orbits are quotient labels. -/
def Label (swap : Ω → Ω) := {A : Finset Ω // ∃ x, orbit swap x = A}

noncomputable instance labelFintype (swap : Ω → Ω) : Fintype (Label swap) := by
  classical
  unfold Label
  infer_instance

noncomputable def label (swap : Ω → Ω) (x : Ω) : Label swap :=
  ⟨orbit swap x, ⟨x, rfl⟩⟩

noncomputable def representative (swap : Ω → Ω) (i : Label swap) : Ω :=
  Classical.choose i.property

omit [Fintype Ω] in
theorem label_representative (swap : Ω → Ω) (i : Label swap) :
    label swap (representative swap i) = i :=
  Subtype.ext (Classical.choose_spec i.property)

omit [Fintype Ω] in
theorem orbit_swap (swap : Ω → Ω) (hinv : Function.Involutive swap) (x : Ω) :
    orbit swap (swap x) = orbit swap x := by
  classical
  simp [orbit, hinv x, Finset.pair_comm]

omit [Fintype Ω] in
theorem label_swap (swap : Ω → Ω) (hinv : Function.Involutive swap) (x : Ω) :
    label swap (swap x) = label swap x :=
  Subtype.ext (orbit_swap swap hinv x)

omit [Fintype Ω] in
theorem label_eq_iff (swap : Ω → Ω) (hinv : Function.Involutive swap) (x y : Ω) :
    label swap x = label swap y ↔ x = y ∨ x = swap y := by
  classical
  constructor
  · intro h
    have hsets : orbit swap x = orbit swap y := congrArg Subtype.val h
    have hx : x ∈ orbit swap x := by simp [orbit]
    rw [hsets] at hx
    simpa [orbit] using hx
  · rintro (rfl | rfl)
    · rfl
    · exact label_swap swap hinv y

/-- The fiber is exactly the displayed orbit, rather than a coarser label. -/
theorem label_fiber (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (i : Label swap) :
    Finset.univ.filter (fun x => label swap x = i) =
      orbit swap (representative swap i) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi := label_representative swap i
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact (label_eq_iff swap hinv x _).mp (h.trans hi.symm)
  · intro h
    exact ((label_eq_iff swap hinv x _).mpr h).trans hi

/-- Fixed and free orbits retain their different cardinalities. -/
theorem fiber_size (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (i : Label swap) :
    fiberSize (label swap) i =
      if swap (representative swap i) = representative swap i then 1 else 2 := by
  classical
  unfold fiberSize rowCount
  rw [label_fiber swap hinv]
  split_ifs with h
  · simp [orbit, h]
  · simp [orbit, Ne.symm h]

theorem fiber_size_two (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (free : ∀ x, swap x ≠ x) (i : Label swap) :
    fiberSize (label swap) i = 2 := by
  rw [fiber_size swap hinv]
  simp only [free _, ite_false]

omit [Fintype Ω] in
/-- The edge involution gives an actual outgoing-fiber bijection. -/
theorem forward_degree_swap (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e))
    (x : Ω) (j : Label swap) :
    forwardDegree source target (label swap) x j =
      forwardDegree source target (label swap) (swap x) j := by
  classical
  unfold forwardDegree
  apply Finset.card_bij (fun e _ => edgeSwap e)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨by rw [hsource, he.1], by rw [htarget, label_swap swap hinv, he.2]⟩
  · intro a _ b _ h
    exact hedge.injective h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    refine ⟨edgeSwap e, ?_, hedge e⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [hsource, he.1, hinv], by rw [htarget, label_swap swap hinv, he.2]⟩

omit [Fintype Ω] in
/-- Reversing source and target gives the incoming-fiber bijection. -/
theorem inverse_degree_swap (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e))
    (x : Ω) (j : Label swap) :
    inverseDegree source target (label swap) x j =
      inverseDegree source target (label swap) (swap x) j :=
  forward_degree_swap swap hinv edgeSwap hedge target source htarget hsource x j

noncomputable def forward (swap : Ω → Ω) (source target : E → Ω)
    (i j : Label swap) : ℕ :=
  forwardDegree source target (label swap) (representative swap i) j

noncomputable def inverse (swap : Ω → Ω) (source target : E → Ω)
    (i j : Label swap) : ℕ :=
  inverseDegree source target (label swap) (representative swap i) j

omit [Fintype Ω] in
/-- Representatives determine the same row because the counts are uniform. -/
theorem forward_uniform (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e))
    (x : Ω) (j : Label swap) :
    forwardDegree source target (label swap) x j = forward swap source target (label swap x) j := by
  change forwardDegree source target (label swap) x j =
    forwardDegree source target (label swap) (representative swap (label swap x)) j
  have heq := (label_eq_iff swap hinv x (representative swap (label swap x))).mp
    (label_representative swap (label swap x)).symm
  rcases heq with h | h
  · exact congrArg (fun z => forwardDegree source target (label swap) z j) h
  · exact (congrArg (fun z => forwardDegree source target (label swap) z j) h).trans
      (forward_degree_swap swap hinv edgeSwap hedge source target hsource htarget _ j).symm

omit [Fintype Ω] in
theorem inverse_uniform (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e))
    (x : Ω) (j : Label swap) :
    inverseDegree source target (label swap) x j = inverse swap source target (label swap x) j :=
  forward_uniform swap hinv edgeSwap hedge target source htarget hsource x j

/-- The earlier double-counting theorem now consumes proved uniformity. -/
theorem involution_weighted_transport (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e))
    (i j : Label swap) :
    fiberSize (label swap) i * inverse swap source target i j =
      fiberSize (label swap) j * forward swap source target j i :=
  weighted_count_transport source target (label swap) (forward swap source target)
    (inverse swap source target)
    (forward_uniform swap hinv edgeSwap hedge source target hsource htarget)
    (inverse_uniform swap hinv edgeSwap hedge source target hsource htarget) i j

/-- Free symmetry orbits have one common weight, so the transpose is literal. -/
theorem involution_transpose (swap : Ω → Ω) (hinv : Function.Involutive swap)
    (free : ∀ x, swap x ≠ x)
    (edgeSwap : E → E) (hedge : Function.Involutive edgeSwap)
    (source target : E → Ω)
    (hsource : ∀ e, source (edgeSwap e) = swap (source e))
    (htarget : ∀ e, target (edgeSwap e) = swap (target e)) :
    ∀ i j, inverse swap source target i j = forward swap source target j i :=
  transpose_of_constant_fiber source target (label swap) (forward swap source target)
    (inverse swap source target)
    (forward_uniform swap hinv edgeSwap hedge source target hsource htarget)
    (inverse_uniform swap hinv edgeSwap hedge source target hsource htarget)
    2 (by decide) (fiber_size_two swap hinv free)

end InvolutionCounts

section LiteralOccurrences

/-- Supplied finite ordered packet domain; its labels are not yet quotiented. -/
abbrev State (S : Finset Packet) := {p // p ∈ S}

noncomputable def stateSwap (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (p : State S) : State S :=
  ⟨p.val.swap, closed p.val p.property⟩

theorem stateSwap_involutive (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) : Function.Involutive (stateSwap S closed) := by
  intro p
  exact Subtype.ext (OccurrenceInverse.packet_swap_swap p.val)

/-- The swap transports both independent image-position identities. -/
theorem digitPacket_swap (s : Fin 3 → Word) (p : Packet)
    (i : Fin (s p.top).length) (j : Fin (s p.bottom).length) :
    digitPacket s p.swap j i = (digitPacket s p i j).swap := by
  simp only [digitPacket, Packet.swap, Matrix.mulVec_neg]
  rw [residual_swap (markAt (s p.top) i).before (markAt (s p.bottom) j).before]
  congr 1
  abel

/-- All actual image-position pairs whose endpoints lie in the domain.
Equal child labels remain different elements when their positions differ. -/
abbrev Edge (s : Fin 3 → Word) (S : Finset Packet) :=
  Σ p : State S, {ij : Fin (s p.val.top).length × Fin (s p.val.bottom).length //
    digitPacket s p.val ij.1 ij.2 ∈ S}

noncomputable instance edgeFintype (s : Fin 3 → Word) (S : Finset Packet) :
    Fintype (Edge s S) := by
  classical
  unfold Edge
  infer_instance

def source (s : Fin 3 → Word) (S : Finset Packet) (e : Edge s S) : State S := e.1

def target (s : Fin 3 → Word) (S : Finset Packet) (e : Edge s S) : State S :=
  ⟨digitPacket s e.1.val e.2.val.1 e.2.val.2, e.2.property⟩

/-- Every edge supplies the actual incoming marks in the reverse direction. -/
def edgeInverseOccurrence (s : Fin 3 → Word) (S : Finset Packet) (e : Edge s S) :
    OccurrenceInverse.InverseOccurrence s (target s S e).val (source s S e).val :=
  OccurrenceInverse.ForwardOccurrence.toInverse ⟨e.2.val.1, e.2.val.2, rfl⟩

theorem edgeInverseOccurrence_top_index (s : Fin 3 → Word) (S : Finset Packet)
    (e : Edge s S) :
    (edgeInverseOccurrence s S e).toForward.topIndex = e.2.val.1 := by
  exact congrArg OccurrenceInverse.ForwardOccurrence.topIndex
    (OccurrenceInverse.ForwardOccurrence.toInverse_toForward
      (⟨e.2.val.1, e.2.val.2, rfl⟩ :
        OccurrenceInverse.ForwardOccurrence s (source s S e).val (target s S e).val))

theorem edgeInverseOccurrence_bottom_index (s : Fin 3 → Word) (S : Finset Packet)
    (e : Edge s S) :
    (edgeInverseOccurrence s S e).toForward.bottomIndex = e.2.val.2 := by
  exact congrArg OccurrenceInverse.ForwardOccurrence.bottomIndex
    (OccurrenceInverse.ForwardOccurrence.toInverse_toForward
      (⟨e.2.val.1, e.2.val.2, rfl⟩ :
        OccurrenceInverse.ForwardOccurrence s (source s S e).val (target s S e).val))

/-- Conversely every actual incoming occurrence between represented endpoints
is present in the full finite digit inventory. -/
def inverseOccurrenceEdge (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) (e : OccurrenceInverse.InverseOccurrence s p.val u.val) : Edge s S :=
  ⟨u, ⟨(e.toForward.topIndex, e.toForward.bottomIndex), by
    rw [← e.toForward.packet_eq]
    exact p.property⟩⟩

theorem inverseOccurrenceEdge_source (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) (e : OccurrenceInverse.InverseOccurrence s p.val u.val) :
    source s S (inverseOccurrenceEdge s S p u e) = u := rfl

theorem inverseOccurrenceEdge_target (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) (e : OccurrenceInverse.InverseOccurrence s p.val u.val) :
    target s S (inverseOccurrenceEdge s S p u e) = p :=
  Subtype.ext e.toForward.packet_eq.symm

theorem inverseOccurrenceEdge_top_index (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) (e : OccurrenceInverse.InverseOccurrence s p.val u.val) :
    (inverseOccurrenceEdge s S p u e).2.val.1 = e.toForward.topIndex := rfl

theorem inverseOccurrenceEdge_bottom_index (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) (e : OccurrenceInverse.InverseOccurrence s p.val u.val) :
    (inverseOccurrenceEdge s S p u e).2.val.2 = e.toForward.bottomIndex := rfl

/-- Reversing and reconstructing an edge keeps its full finite identity. -/
theorem inverseOccurrenceEdge_roundtrip (s : Fin 3 → Word) (S : Finset Packet)
    (e : Edge s S) :
    inverseOccurrenceEdge s S (target s S e) (source s S e)
      (edgeInverseOccurrence s S e) = e := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact Prod.ext (edgeInverseOccurrence_top_index s S e)
      (edgeInverseOccurrence_bottom_index s S e)

noncomputable def edgeSwap (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (e : Edge s S) : Edge s S :=
  ⟨stateSwap S closed e.1, ⟨(e.2.val.2, e.2.val.1), by
    change digitPacket s e.1.val.swap e.2.val.2 e.2.val.1 ∈ S
    rw [digitPacket_swap]
    exact closed _ e.2.property⟩⟩

theorem edgeSwap_source (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (e : Edge s S) :
    source s S (edgeSwap s S closed e) = stateSwap S closed (source s S e) := rfl

theorem edgeSwap_target (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (e : Edge s S) :
    target s S (edgeSwap s S closed e) = stateSwap S closed (target s S e) :=
  Subtype.ext (digitPacket_swap s e.1.val e.2.val.1 e.2.val.2)

theorem edgeSwap_top_index (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (e : Edge s S) :
    (edgeSwap s S closed e).2.val.1.val = e.2.val.2.val := rfl

theorem edgeSwap_bottom_index (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (e : Edge s S) :
    (edgeSwap s S closed e).2.val.2.val = e.2.val.1.val := rfl

theorem edgeSwap_involutive (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) : Function.Involutive (edgeSwap s S closed) := by
  intro e
  apply Sigma.ext
  · exact stateSwap_involutive S closed e.1
  · refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
    intro ij
    change digitPacket s e.1.val.swap.swap ij.1 ij.2 ∈ S ↔
      digitPacket s e.1.val ij.1 ij.2 ∈ S
    simp only [digitPacket, Packet.swap, neg_neg]

/-- Actual orbit labels for this finite packet domain. -/
abbrev PacketLabel (S : Finset Packet) (closed : ∀ p ∈ S, p.swap ∈ S) :=
  Label (stateSwap S closed)

noncomputable def packetForward (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) : PacketLabel S closed → PacketLabel S closed → ℕ :=
  forward (stateSwap S closed) (source s S) (target s S)

noncomputable def packetInverse (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) : PacketLabel S closed → PacketLabel S closed → ℕ :=
  inverse (stateSwap S closed) (source s S) (target s S)

/-- Literal occurrence counts are uniform on every represented swap orbit. -/
theorem packet_forward_uniform (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (p : State S) (j : PacketLabel S closed) :
    forwardDegree (source s S) (target s S) (label (stateSwap S closed)) p j =
      packetForward s S closed (label (stateSwap S closed) p) j :=
  forward_uniform (stateSwap S closed) (stateSwap_involutive S closed)
    (edgeSwap s S closed) (edgeSwap_involutive s S closed) (source s S) (target s S)
    (edgeSwap_source s S closed) (edgeSwap_target s S closed) p j

theorem packet_inverse_uniform (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (p : State S) (j : PacketLabel S closed) :
    inverseDegree (source s S) (target s S) (label (stateSwap S closed)) p j =
      packetInverse s S closed (label (stateSwap S closed) p) j :=
  inverse_uniform (stateSwap S closed) (stateSwap_involutive S closed)
    (edgeSwap s S closed) (edgeSwap_involutive s S closed) (source s S) (target s S)
    (edgeSwap_source s S closed) (edgeSwap_target s S closed) p j

/-- Actual forward and inverse inventories obey the weighted transpose. -/
theorem packet_weighted_transport (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (i j : PacketLabel S closed) :
    fiberSize (label (stateSwap S closed)) i * packetInverse s S closed i j =
      fiberSize (label (stateSwap S closed)) j * packetForward s S closed j i :=
  involution_weighted_transport (stateSwap S closed) (stateSwap_involutive S closed)
    (edgeSwap s S closed) (edgeSwap_involutive s S closed) (source s S) (target s S)
    (edgeSwap_source s S closed) (edgeSwap_target s S closed) i j

/-- The actual count correspondence feeds the existing mass consumer.
This identity itself asserts neither a positive deficit nor geometric mass. -/
theorem packet_quotient_deficit (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (h : PacketLabel S closed → ℝ)
    (β : ℝ) (j : PacketLabel S closed) :
    PscVerif.PhysicalMass.deficit (fun i j => (packetInverse s S closed i j : ℝ))
      (fun i => (fiberSize (label (stateSwap S closed)) i : ℝ) * h i) β j =
      (fiberSize (label (stateSwap S closed)) j : ℝ) *
        (β * h j - PscVerif.PhysicalMass.action
          (fun i j => (packetForward s S closed i j : ℝ)) h j) :=
  quotient_deficit (source s S) (target s S) (label (stateSwap S closed))
    (packetForward s S closed) (packetInverse s S closed)
    (packet_forward_uniform s S closed) (packet_inverse_uniform s S closed) h β j

/-- Integral nondiagonality removes exactly the fixed-packet obstruction. -/
theorem stateSwap_eq_iff_diagonal (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (p : State S) :
    stateSwap S closed p = p ↔ p.val.Diagonal := by
  constructor
  · intro h
    exact (OccurrenceInverse.packet_swap_eq_iff_diagonal p.val).mp
      (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((OccurrenceInverse.packet_swap_eq_iff_diagonal p.val).mpr h)

/-- The concrete orbit has one state exactly in the diagonal case. -/
theorem packet_fiber_size (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (i : PacketLabel S closed) :
    fiberSize (label (stateSwap S closed)) i =
      if (representative (stateSwap S closed) i).val.Diagonal then 1 else 2 := by
  rw [fiber_size (stateSwap S closed) (stateSwap_involutive S closed)]
  rw [stateSwap_eq_iff_diagonal]

theorem stateSwap_free (S : Finset Packet) (closed : ∀ p ∈ S, p.swap ∈ S)
    (nondiagonal : ∀ p ∈ S, ¬p.Diagonal) :
    ∀ p, stateSwap S closed p ≠ p := by
  intro p h
  apply nondiagonal p.val p.property
  apply (OccurrenceInverse.packet_swap_eq_iff_diagonal p.val).mp
  exact congrArg Subtype.val h

theorem packet_fiber_size_two (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (nondiagonal : ∀ p ∈ S, ¬p.Diagonal)
    (i : PacketLabel S closed) :
    fiberSize (label (stateSwap S closed)) i = 2 :=
  fiber_size_two (stateSwap S closed) (stateSwap_involutive S closed)
    (stateSwap_free S closed nondiagonal) i

/-- The concrete nondiagonal occurrence quotient has the unweighted transpose.
No assumption of uniform counts or of a chosen orbit size remains. -/
theorem packet_transpose (s : Fin 3 → Word) (S : Finset Packet)
    (closed : ∀ p ∈ S, p.swap ∈ S) (nondiagonal : ∀ p ∈ S, ¬p.Diagonal) :
    ∀ i j, packetInverse s S closed i j = packetForward s S closed j i :=
  involution_transpose (stateSwap S closed) (stateSwap_involutive S closed)
    (stateSwap_free S closed nondiagonal) (edgeSwap s S closed)
    (edgeSwap_involutive s S closed) (source s S) (target s S)
    (edgeSwap_source s S closed) (edgeSwap_target s S closed)

/-- The complete inverse-ancestry argument supplies freeness to the concrete
counting theorem.  Finiteness and swap closure of the domain remain explicit;
its membership only needs inclusion in the actual ancestry, not equality. -/
theorem ancestry_packet_transpose (s : Fin 3 → Word) (roots : Packet → Prop)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal)
    (S : Finset Packet) (closed : ∀ p ∈ S, p.swap ∈ S)
    (contained : ∀ p ∈ S, OccurrenceInverse.Ancestry s roots p) :
    ∀ i j, packetInverse s S closed i j = packetForward s S closed j i := by
  apply packet_transpose s S closed
  intro p hp hdiag
  exact OccurrenceInverse.ancestry_free s roots ℓ β hpos hβ hscale hroots
    (contained p hp) ((OccurrenceInverse.packet_swap_eq_iff_diagonal p).mpr hdiag)

end LiteralOccurrences

end Psc.OccurrenceSwapCounts
