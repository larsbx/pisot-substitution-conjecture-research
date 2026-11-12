import PscVerif.OccurrenceCover
import PscVerif.OverlapContraction

/-!
# Source-bound refinement of normalized archived overlap graphs

The certificate's very same degree and target functions index literal slots
in the actual block substitution.  Exact rows retain both complete parent
words and both local positions, including parallel targets.  A separate
admission predicate has two independent obligations: genuine nonempty
overlaps pass it, and every passing integral incoming candidate occurs in
the ordered lift of the finite state table.  Neither obligation follows
from accepting the positive integer potential.

The proved refinement derives the normalized affine set union, preserving
the orientation-dependent translation.  For the two named actual prefix
systems, their original matrix-adic range detector, compactness, tile
equation and product-Haar modulus discharge the analytic hypotheses of
`OverlapContraction`.  No physical-interior assumption is needed.  The
serialized historical payload is not silently identified with this typed
interface, and no all-strict-packet or positive-measure conclusion is made.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.ArchivedGraphRefinement

open Set MeasureTheory
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceFinite
open Psc.OccurrenceGraphBinding Psc.OccurrencePiece Psc.OccurrenceCover
open PscVerif.OverlapContraction
open Matrix
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

/-- The potential certificate and literal rows share their indexing data by
construction.  No target-ID equality is accepted as an occurrence address. -/
structure TableBinding {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet)
    (cert : Certificate n) where
  slot : (i : Fin n) → (e : Fin (cert.degree i)) →
    Slot s (states i) (states (cert.target i e))
  distinct : OrbitDistinct states
  exactRows : ∀ i,
    (⟨cert.degree i, cert.target i, slot i⟩ : OccurrenceGraphBinding.Row s states i).Exact

def TableBinding.row {n : ℕ} {s : Fin 3 → Word} {states : Fin n → Packet}
    {cert : Certificate n} (table : TableBinding s states cert) (i : Fin n) :
    OccurrenceGraphBinding.Row s states i :=
  ⟨cert.degree i, cert.target i, table.slot i⟩

/-- Every retained literal incoming occurrence has one and only one slot.
The equality keeps its raw ancestor and both full marks, not just a target. -/
theorem TableBinding.incoming_exists {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (i : Fin n) (u : Packet)
    (hu : u ∈ orderedLift states) (e : InverseOccurrence s (states i) u) :
    ∃ k : Fin (cert.degree i),
      (⟨(table.slot i k).rawTarget, (table.slot i k).toInverse⟩ :
        OccurrenceCover.Incoming s (states i)) = ⟨u, e⟩ := by
  obtain ⟨k, hraw, ht, hb⟩ := (table.exactRows i).2 u hu
    e.toForward.topIndex e.toForward.bottomIndex e.toForward.packet_eq
  subst u
  refine ⟨k, Sigma.ext rfl (heq_of_eq ?_)⟩
  apply InverseOccurrence.ext
  · apply (markEquiv _).injective
    apply Fin.ext
    change (table.slot i k).toInverse.toForward.topIndex.val = e.toForward.topIndex.val
    rw [(table.slot i k).top_index]
    exact ht
  · apply (markEquiv _).injective
    apply Fin.ext
    change (table.slot i k).toInverse.toForward.bottomIndex.val = e.toForward.bottomIndex.val
    rw [(table.slot i k).bottom_index]
    exact hb

/-- Exactness certifies injectivity on raw parents and both positions. -/
theorem TableBinding.address_injective {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (i : Fin n) :
    Function.Injective (table.row i).key := (table.exactRows i).1

/-- The finite closure check quantifies over every actual integral candidate,
including candidates outside the serialized state table. -/
def CandidateClosed {n : ℕ} (s : Fin 3 → Word) (states : Fin n → Packet)
    (admitted : Packet → Prop) : Prop :=
  ∀ i u, InverseOccurrence s (states i) u → admitted u → u ∈ orderedLift states

section Geometry

variable {G : Type*} [AddCommGroup G]

/-- Admission must be proved from the original geometric overlap domain.
This is the soundness obligation for box or other geometric exclusions. -/
def AdmissionSound (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (admitted : Packet → Prop) : Prop :=
  ∀ p, (overlap star K p).Nonempty → admitted p

theorem overlap_nonempty_swap_iff (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (p : Packet) :
    (overlap star K p.swap).Nonempty ↔ (overlap star K p).Nonempty := by
  rw [overlap_swap_eq_translate]
  exact Set.image_nonempty

/-- Geometric exclusion soundness and exhaustive finite candidate closure
derive complete representation at both orientations of every table entry. -/
theorem represented_orderedLift {n : ℕ} {s : Fin 3 → Word}
    (states : Fin n → Packet) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted) :
    ∀ p ∈ orderedLift states, ∀ u, InverseOccurrence s p u →
      (overlap star K u).Nonempty → u ∈ orderedLift states := by
  intro p hp u e hn
  obtain ⟨i, rfl | rfl⟩ := (mem_orderedLift states p).mp hp
  · exact closed i u e (sound u hn)
  · have es : InverseOccurrence s (states i) u.swap := by
      simpa only [packet_swap_swap] using e.swap
    have hs : (overlap star K u.swap).Nonempty :=
      (overlap_nonempty_swap_iff star K u).mpr hn
    have hm := orderedLift_swap_closed states u.swap (closed i u.swap es (sound u.swap hs))
    simpa only [packet_swap_swap] using hm

theorem excluded_ancestor_empty {n : ℕ} {s : Fin 3 → Word}
    (states : Fin n → Packet) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted)
    (p : Packet) (hp : p ∈ orderedLift states) (u : Packet)
    (e : InverseOccurrence s p u) (outside : u ∉ orderedLift states) :
    overlap star K u = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hn
  exact outside (represented_orderedLift states star K admitted sound closed p hp u e hn)

/-- A slot's affine translation uses the bottom prefix plus current residual
when normalization swaps its raw ancestor. -/
def TableBinding.rowPiece {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (i : Fin n) (e : Fin (cert.degree i)) : Set G :=
  affine A (star (slotTranslation (table.slot i e))) ''
    overlap star K (states (cert.target i e))

theorem TableBinding.raw_piece_eq_rowPiece {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (i : Fin n) (e : Fin (cert.degree i)) :
    piece A star K (table.slot i e).toInverse = table.rowPiece A star K i e :=
  slot_piece_eq_stored A star K commute (table.slot i e)

/-- Complete literal rows, geometric admission and exact candidate closure
give the original overlap union.  No set-cover conclusion is assumed. -/
theorem TableBinding.overlap_eq_iUnion_rowPiece {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (reflects : ReflectsIntegralRange s A star) (tiles : TileEquation s A star K)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted) (i : Fin n) :
    overlap star K (states i) = ⋃ e, table.rowPiece A star K i e := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, e, he⟩ := overlap_mem_inverse_piece A star K injective commute reflects tiles
      (states i) hx
    have hn : (overlap star K u).Nonempty := Set.Nonempty.of_image ⟨x, he⟩
    obtain ⟨k, hk⟩ := table.incoming_exists i u (closed i u e (sound u hn)) e
    have hpiece := congrArg (fun q : OccurrenceCover.Incoming s (states i) =>
      piece A star K q.2) hk
    have hm : x ∈ piece A star K (table.slot i k).toInverse := by
      rw [hpiece]
      exact he
    rw [table.raw_piece_eq_rowPiece A star K commute i k] at hm
    exact Set.mem_iUnion.mpr ⟨k, hm⟩
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rw [← table.raw_piece_eq_rowPiece A star K commute i k] at hk
    exact inverse_piece_subset_overlap A star K injective commute tiles
      (table.slot i k).toInverse hk

/-- The same local completeness controls every intermediate ancestor at
every depth, retaining the full injective literal history address. -/
theorem restricted_history_cover {n : ℕ} {s : Fin 3 → Word}
    (states : Fin n → Packet) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (reflects : ReflectsIntegralRange s A star) (tiles : TileEquation s A star K)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted) (depth : ℕ)
    (p : Packet) (hp : p ∈ orderedLift states) :
    overlap star K p =
      ⋃ h : {h : History s depth p // historyWithin s (orderedLift states) depth p h},
        historyPiece s A star K depth p h.val :=
  overlap_eq_iUnion_restrictedHistory A star K injective commute tiles reflects
    (orderedLift states) (represented_orderedLift states star K admitted sound closed) depth p hp

/-- A nonempty final inverse overlap forces each previous actual overlap
to be nonempty.  This direction follows from literal affine containment. -/
theorem nonempty_of_inverse_path {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (tiles : TileEquation s A star K) {p u : Packet}
    (path : Relation.ReflTransGen (InverseStep s) p u)
    (hn : (overlap star K u).Nonempty) : (overlap star K p).Nonempty := by
  revert hn
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => h
  | head hedge _ ih =>
      intro hn
      obtain ⟨e⟩ := hedge
      exact ((ih hn).image (affine A (star (parikhZ e.topMark.before)))).mono
        (inverse_piece_subset_overlap A star K injective commute tiles e)

/-- Closure at every represented source covers arbitrary finite inverse
paths when the final overlap is nonempty.  Endpoints alone are insufficient. -/
theorem nonempty_path_represented {n : ℕ} {s : Fin 3 → Word}
    (states : Fin n → Packet) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (tiles : TileEquation s A star K)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted) {p u : Packet}
    (path : Relation.ReflTransGen (InverseStep s) p u)
    (hp : p ∈ orderedLift states) (hn : (overlap star K u).Nonempty) :
    u ∈ orderedLift states := by
  revert hp
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => h
  | head hedge tail ih =>
      intro hp
      obtain ⟨e⟩ := hedge
      exact ih (represented_orderedLift states star K admitted sound closed _ hp _ e
        (nonempty_of_inverse_path A star K injective commute tiles tail hn))

/-- Exact rooted representation, restricted only by actual nonemptiness.
This is a statement about the declared roots' original inverse ancestry,
not about the unrelated noncomputable all-strict-packet carrier. -/
theorem TableBinding.rooted_nonempty_domain_iff {n : ℕ} {s : Fin 3 → Word}
    {states : Fin n → Packet} {cert : Certificate n}
    (table : TableBinding s states cert) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (tiles : TileEquation s A star K)
    (admitted : Packet → Prop) (sound : AdmissionSound star K admitted)
    (closed : CandidateClosed s states admitted)
    (roots : Packet → Prop) (rootSwap : ∀ p, roots p → roots p.swap)
    (discovery : TableDiscovery table.row roots)
    (rootComplete : ∀ p, roots p → p ∈ orderedLift states) (p : Packet) :
    (p ∈ orderedLift states ∧ (overlap star K p).Nonempty) ↔
      (Ancestry s roots p ∧ (overlap star K p).Nonempty) := by
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨orderedLift_ancestry s states roots rootSwap
      (tableDiscovery_discovery table.row roots discovery) p hp, hn⟩
  · rintro ⟨⟨r, hr, path⟩, hn⟩
    exact ⟨nonempty_path_represented states A star K injective commute tiles
      admitted sound closed path (rootComplete r hr) hn, hn⟩

end Geometry

/-- The three original unshifted unordered letter-pair roots, in their
archived order.  Their ordered lift also contains the reverse tracks. -/
def archivedRoot (i : Fin 3) : Packet :=
  ![⟨0, 1, 0⟩, ⟨0, 2, 0⟩, ⟨1, 2, 0⟩] i

def ArchivedRoot (p : Packet) : Prop :=
  ∃ i, p = archivedRoot i ∨ p = (archivedRoot i).swap

theorem archivedRoots_swap (p : Packet) (hp : ArchivedRoot p) : ArchivedRoot p.swap := by
  obtain ⟨i, rfl | rfl⟩ := hp
  · exact ⟨i, Or.inr rfl⟩
  · exact ⟨i, Or.inl (packet_swap_swap _)⟩

/-- Three exact root records establish root coverage independently of the
discovery tree and independently of any positivity assertion. -/
theorem archivedRoots_complete {n : ℕ} (states : Fin n → Packet)
    (rootID : Fin 3 → Fin n) (bound : ∀ i, states (rootID i) = archivedRoot i)
    (p : Packet) (hp : ArchivedRoot p) : p ∈ orderedLift states := by
  obtain ⟨i, rfl | rfl⟩ := hp
  · rw [← bound i]
    exact state_mem_orderedLift states (rootID i)
  · rw [← bound i]
    exact orderedLift_swap_closed states _ (state_mem_orderedLift states (rootID i))

end Psc.ArchivedGraphRefinement
