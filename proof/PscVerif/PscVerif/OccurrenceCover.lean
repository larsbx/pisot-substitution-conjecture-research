import PscVerif.OccurrencePiece
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Bounded actual inverse histories and compact-piece covers

Every incoming edge keeps its integral ancestor and both full literal marks.
An injective integral incidence action makes each incoming fibre finite; it
is not necessary to posit a globally finite ancestor graph. Iterating the
original tile equation yields a complete occurrence-indexed cover at every
finite depth. Compactness is conditional on compact tiles and continuous
internal action in a Hausdorff topological additive group.

Restricting that complete cover to a supplied finite graph is a separate
step. The exact set-cover criterion is containment of each omitted piece
in the retained union. Empty excluded pieces give a stronger sufficient
certificate; no measure-additive or multiplicity conclusion follows from
set containment. Enclosure and residue interfaces make their hypotheses
explicit. Pre-code gate: `docs/c4-compact-cover-literature-2026-11-11.md`.
-/

namespace Psc.OccurrenceCover

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrencePiece
open Psc.OccurrenceFinite Psc.OccurrenceNewborn Matrix

/-- All actual incoming occurrences, without any stable-box or carrier filter. -/
abbrev Incoming (s : Fin 3 → Word) (p : Packet) :=
  Σ u : Packet, InverseOccurrence s p u

/-- A literal digit includes its source letter and full mark. -/
abbrev Digit (s : Fin 3 → Word) := Σ a : Fin 3, Mark (s a)

noncomputable def digitFintype (s : Fin 3 → Word) : Fintype (Digit s) := by
  letI (a : Fin 3) : Fintype (Mark (s a)) :=
    Fintype.ofEquiv (Fin (s a).length) (markEquiv (s a)).symm
  exact inferInstanceAs (Fintype (Σ a : Fin 3, Mark (s a)))

theorem digit_card (s : Fin 3 → Word) :
    Nat.card (Digit s) = ∑ a, (s a).length := by
  letI (a : Fin 3) : Fintype (Mark (s a)) :=
    Fintype.ofEquiv (Fin (s a).length) (markEquiv (s a)).symm
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  simpa using Nat.card_congr (markEquiv (s a))

/-- A pair of literal digits determines an incoming integral ancestor only
when the integral incidence action is injective. -/
def incomingKey {s : Fin 3 → Word} {p : Packet} (e : Incoming s p) :
    Digit s × Digit s :=
  (⟨e.1.top, e.2.topMark⟩, ⟨e.1.bottom, e.2.bottomMark⟩)

theorem incomingKey_injective {s : Fin 3 → Word} {p : Packet}
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y)) :
    Function.Injective (@incomingKey s p) := by
  intro e f h
  rcases e with ⟨⟨a, b, y⟩, ⟨dt, db, ht, hb, hy⟩⟩
  rcases f with ⟨⟨a', b', y'⟩, ⟨dt', db', ht', hb', hy'⟩⟩
  have htop := congrArg (fun k : Digit s × Digit s => k.1) h
  have hbot := congrArg (fun k : Digit s × Digit s => k.2) h
  have ha : a = a' := congrArg Sigma.fst htop
  have hb'': b = b' := congrArg Sigma.fst hbot
  subst a'
  subst b'
  have hdt : dt = dt' := eq_of_heq (Sigma.mk.inj_iff.mp htop).2
  have hdb : db = db' := eq_of_heq (Sigma.mk.inj_iff.mp hbot).2
  subst dt'
  subst db'
  have he : y = y' := integralInjective (hy.trans hy'.symm)
  subst y'
  rfl

/-- Construct a finite incoming inventory from finite literal positions;
there is no assumed global bound on ancestor residuals. -/
noncomputable def incomingFintype (s : Fin 3 → Word) (p : Packet)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y)) :
    Fintype (Incoming s p) := by
  classical
  letI := digitFintype s
  exact Fintype.ofInjective incomingKey (incomingKey_injective integralInjective)

theorem finite_incoming (s : Fin 3 → Word) (p : Packet)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y)) :
    Finite (Incoming s p) := by
  letI := incomingFintype s p integralInjective
  infer_instance

theorem incoming_card_le (s : Fin 3 → Word) (p : Packet)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y)) :
    Nat.card (Incoming s p) ≤ (∑ a, (s a).length) ^ 2 := by
  letI := digitFintype s
  calc
    Nat.card (Incoming s p) ≤ Nat.card (Digit s × Digit s) :=
      Nat.card_le_card_of_injective incomingKey (incomingKey_injective integralInjective)
    _ = (∑ a, (s a).length) ^ 2 := by rw [Nat.card_prod, digit_card, pow_two]

/-- A history retains every incoming occurrence, including distinct choices
with identical packet endpoints. No quotient or endpoint deduplication occurs. -/
def History (s : Fin 3 → Word) : ℕ → Packet → Type
  | 0, _ => Unit
  | n + 1, p => Σ e : Incoming s p, History s n e.1

/-- Every visited ancestor, rather than only the terminal packet, must be
represented when a bounded history is restricted to a supplied domain. -/
def historyWithin (s : Fin 3 → Word) (S : Finset Packet) :
    (n : ℕ) → (p : Packet) → History s n p → Prop
  | 0, _, _ => True
  | n + 1, _, ⟨e, h⟩ => e.1 ∈ S ∧ historyWithin s S n e.1 h

noncomputable def historyFintype (s : Fin 3 → Word)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y)) :
    (n : ℕ) → (p : Packet) → Fintype (History s n p)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | n + 1, p => by
      letI := incomingFintype s p integralInjective
      letI (e : Incoming s p) : Fintype (History s n e.1) :=
        historyFintype s integralInjective n e.1
      exact inferInstanceAs (Fintype (Σ e : Incoming s p, History s n e.1))

theorem finite_history (s : Fin 3 → Word)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y))
    (n : ℕ) (p : Packet) : Finite (History s n p) := by
  letI := historyFintype s integralInjective n p
  infer_instance

/-- A stated depth has an a priori finite budget from literal image sizes.
This bounds full histories, not a globally finite ancestor state set. -/
theorem history_card_le (s : Fin 3 → Word)
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y))
    (n : ℕ) (p : Packet) :
    Nat.card (History s n p) ≤ ((∑ a, (s a).length) ^ 2) ^ n := by
  classical
  induction n generalizing p with
  | zero => simp [History]
  | succ n ih =>
      letI := incomingFintype s p integralInjective
      letI (e : Incoming s p) : Finite (History s n e.1) :=
        finite_history s integralInjective n e.1
      change Nat.card (Σ e : Incoming s p, History s n e.1) ≤ _
      rw [Nat.card_sigma]
      calc
        ∑ e : Incoming s p, Nat.card (History s n e.1) ≤
            ∑ _e : Incoming s p, ((∑ a, (s a).length) ^ 2) ^ n :=
          Finset.sum_le_sum (fun e _ => ih e.1)
        _ = Nat.card (Incoming s p) * ((∑ a, (s a).length) ^ 2) ^ n := by
          simp [Nat.card_eq_fintype_card]
        _ ≤ (∑ a, (s a).length) ^ 2 * ((∑ a, (s a).length) ^ 2) ^ n :=
          Nat.mul_le_mul_right _ (incoming_card_le s p integralInjective)
        _ = ((∑ a, (s a).length) ^ 2) ^ (n + 1) := (pow_succ' _ _).symm

/-- The auditable address contains the ancestor and both numeric positions
at each level. Keeping the whole list prevents merging repeated paths. -/
def historyAddress (s : Fin 3 → Word) :
    (n : ℕ) → (p : Packet) → History s n p → List (Packet × ℕ × ℕ)
  | 0, _, _ => []
  | n + 1, _, ⟨e, h⟩ =>
      (e.1, (markIndex e.2.topMark).val, (markIndex e.2.bottomMark).val) ::
        historyAddress s n e.1 h

theorem historyAddress_length (s : Fin 3 → Word) (n : ℕ) (p : Packet)
    (h : History s n p) : (historyAddress s n p h).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      rcases h with ⟨e, h⟩
      simp only [historyAddress, List.length_cons, ih]

theorem historyAddress_injective (s : Fin 3 → Word) (n : ℕ) (p : Packet) :
    Function.Injective (historyAddress s n p) := by
  induction n generalizing p with
  | zero => intro h k _; exact Subsingleton.elim h k
  | succ n ih =>
      rintro ⟨⟨u, e⟩, h⟩ ⟨⟨v, f⟩, k⟩ heq
      have he := List.cons.inj heq
      have huv : u = v := congrArg Prod.fst he.1
      subst v
      have hi := congrArg (fun t : Packet × ℕ × ℕ => t.2.1) he.1
      have hj := congrArg (fun t : Packet × ℕ × ℕ => t.2.2) he.1
      have hef : e = f := InverseOccurrence.ext
        ((markEquiv (s u.top)).injective (Fin.ext hi))
        ((markEquiv (s u.bottom)).injective (Fin.ext hj))
      subst f
      have hhk : h = k := ih u he.2
      subst k
      rfl

/-- Terminal ancestor, kept separately from the address that reached it. -/
def historyTarget (s : Fin 3 → Word) :
    (n : ℕ) → (p : Packet) → History s n p → Packet
  | 0, p, _ => p
  | n + 1, _, ⟨e, h⟩ => historyTarget s n e.1 h

/-- The exact top prefix of the composed affine address. -/
def historyTopPrefix (s : Fin 3 → Word) :
    (n : ℕ) → (p : Packet) → History s n p → (Fin 3 → ℤ)
  | 0, _, _ => 0
  | n + 1, _, ⟨e, h⟩ =>
      parikhZ e.2.topMark.before + incidenceZ s *ᵥ historyTopPrefix s n e.1 h

/-- The bottom track retains its own prefix throughout composition. -/
def historyBottomPrefix (s : Fin 3 → Word) :
    (n : ℕ) → (p : Packet) → History s n p → (Fin 3 → ℤ)
  | 0, _, _ => 0
  | n + 1, _, ⟨e, h⟩ =>
      parikhZ e.2.bottomMark.before + incidenceZ s *ᵥ historyBottomPrefix s n e.1 h

/-- The powered inverse equation follows from the complete address, with
both prefixes and their incidence actions retained. -/
theorem history_integral_equation (s : Fin 3 → Word) (n : ℕ) (p : Packet)
    (h : History s n p) :
    (incidenceZ s) ^ n *ᵥ (historyTarget s n p h).delta =
      p.delta + historyBottomPrefix s n p h - historyTopPrefix s n p h := by
  induction n generalizing p with
  | zero => simp [historyTarget, historyTopPrefix, historyBottomPrefix]
  | succ n ih =>
      rcases h with ⟨e, h⟩
      simp only [historyTarget, historyTopPrefix, historyBottomPrefix,
        pow_succ', ← Matrix.mulVec_mulVec]
      rw [ih, Matrix.mulVec_sub, Matrix.mulVec_add, e.2.equation]
      simp only [residual]
      abel

variable {G : Type*} [AddCommGroup G]

/-- Affine image associated with one actual occurrence. -/
def piece {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    {p u : Packet} (e : InverseOccurrence s p u) : Set G :=
  affine A (star (parikhZ e.topMark.before)) '' overlap star K u

@[simp] theorem piece_empty_iff {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    {p u : Packet} (e : InverseOccurrence s p u) :
    piece A star K e = ∅ ↔ overlap star K u = ∅ := by
  simp [piece]

/-- The exact nested affine maps, retaining the first occurrence outermost. -/
def historyMap (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) :
    (n : ℕ) → (p : Packet) → History s n p → G → G
  | 0, _, _ => id
  | n + 1, _, ⟨e, h⟩ =>
      affine A (star (parikhZ e.2.topMark.before)) ∘ historyMap s A star n e.1 h

/-- The nested map has exactly the powered internal action and the
composed integral top prefix, in the same order as the finite constructor. -/
theorem historyMap_eq (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (n : ℕ) (p : Packet) (h : History s n p) (x : G) :
    historyMap s A star n p h x =
      ((A : G → G)^[n]) x + star (historyTopPrefix s n p h) := by
  induction n generalizing p with
  | zero => simp [historyMap, historyTopPrefix]
  | succ n ih =>
      rcases h with ⟨e, h⟩
      simp only [historyMap, Function.comp_apply, affine, historyTopPrefix,
        Function.iterate_succ_apply', ih, map_add, commute]
      abel

/-- A bounded piece is the exact nested affine image of its terminal overlap. -/
def historyPiece (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) :
    (n : ℕ) → (p : Packet) → History s n p → Set G
  | 0, p, _ => overlap star K p
  | n + 1, _, ⟨e, h⟩ =>
      affine A (star (parikhZ e.2.topMark.before)) '' historyPiece s A star K n e.1 h

theorem historyPiece_eq_image (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (n : ℕ) (p : Packet) (h : History s n p) :
    historyPiece s A star K n p h =
      historyMap s A star n p h '' overlap star K (historyTarget s n p h) := by
  induction n generalizing p with
  | zero => simp [historyPiece, historyMap, historyTarget]
  | succ n ih =>
      rcases h with ⟨e, h⟩
      simp only [historyPiece, historyMap, historyTarget, ih, Set.image_image]

section TileCover

variable {s : Fin 3 → Word} (A : G →+ G)
  (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
  (injective : Function.Injective A)
  (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
  (tiles : TileEquation s A star K)

theorem piece_subset_overlap {p u : Packet} (e : InverseOccurrence s p u) :
    piece A star K e ⊆ overlap star K p :=
  inverse_piece_subset_overlap A star K injective commute tiles e

theorem historyPiece_subset (n : ℕ) (p : Packet) (h : History s n p) :
    historyPiece s A star K n p h ⊆ overlap star K p := by
  induction n generalizing p with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
      rcases h with ⟨e, h⟩
      exact (Set.image_mono (ih e.1 h)).trans
        (piece_subset_overlap A star K injective commute tiles e.2)

/-- Original tile equations and integral range reflection cover every point
at every finite depth. The full-history index needs no finite graph premise. -/
theorem overlap_mem_historyPiece (reflects : ReflectsIntegralRange s A star)
    (n : ℕ) (p : Packet) {x : G} (hx : x ∈ overlap star K p) :
    ∃ h : History s n p, x ∈ historyPiece s A star K n p h := by
  induction n generalizing p x with
  | zero => exact ⟨(), hx⟩
  | succ n ih =>
      obtain ⟨u, e, y, hy, hyx⟩ :=
        overlap_mem_inverse_piece A star K injective commute reflects tiles p hx
      obtain ⟨h, hh⟩ := ih u hy
      exact ⟨⟨⟨u, e⟩, h⟩, y, hh, hyx⟩

theorem overlap_eq_iUnion_history (reflects : ReflectsIntegralRange s A star)
    (n : ℕ) (p : Packet) :
    overlap star K p = ⋃ h : History s n p, historyPiece s A star K n p h := by
  ext x
  constructor
  · intro hx
    obtain ⟨h, hh⟩ := overlap_mem_historyPiece A star K injective commute tiles reflects n p hx
    exact Set.mem_iUnion.mpr ⟨h, hh⟩
  · intro hx
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hx
    exact historyPiece_subset A star K injective commute tiles n p h hh

/-- Restricting every level is justified by nonempty-ancestor
representability at EVERY represented source. Terminal membership alone
does not supply an address-preserving restricted history. -/
theorem overlap_mem_historyWithin (reflects : ReflectsIntegralRange s A star)
    (S : Finset Packet)
    (represented : ∀ p ∈ S, ∀ u, InverseOccurrence s p u →
      (overlap star K u).Nonempty → u ∈ S)
    (n : ℕ) (p : Packet) (hp : p ∈ S) {x : G} (hx : x ∈ overlap star K p) :
    ∃ h : History s n p,
      historyWithin s S n p h ∧ x ∈ historyPiece s A star K n p h := by
  induction n generalizing p x with
  | zero => exact ⟨(), trivial, hx⟩
  | succ n ih =>
      obtain ⟨u, e, y, hy, hyx⟩ :=
        overlap_mem_inverse_piece A star K injective commute reflects tiles p hx
      have hu := represented p hp u e ⟨y, hy⟩
      obtain ⟨h, hw, hh⟩ := ih u hu hy
      exact ⟨⟨⟨u, e⟩, h⟩, ⟨hu, hw⟩, y, hh, hyx⟩

theorem overlap_eq_iUnion_restrictedHistory (reflects : ReflectsIntegralRange s A star)
    (S : Finset Packet)
    (represented : ∀ p ∈ S, ∀ u, InverseOccurrence s p u →
      (overlap star K u).Nonempty → u ∈ S)
    (n : ℕ) (p : Packet) (hp : p ∈ S) :
    overlap star K p =
      ⋃ h : {h : History s n p // historyWithin s S n p h},
        historyPiece s A star K n p h.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨h, hw, hh⟩ :=
      overlap_mem_historyWithin A star K injective commute tiles reflects S represented n p hp hx
    exact Set.mem_iUnion.mpr ⟨⟨h, hw⟩, hh⟩
  · intro hx
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hx
    exact historyPiece_subset A star K injective commute tiles n p h.val hh

end TileCover

/-- Restrict incoming occurrences by represented ancestor, retaining every
literal pair for every represented target. -/
def restrictedUnion (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (S : Finset Packet) (p : Packet) : Set G :=
  ⋃ u : {u // u ∈ S}, ⋃ e : InverseOccurrence s p u.val, piece A star K e

theorem mem_restrictedUnion {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (S : Finset Packet) (p : Packet) (x : G) :
    x ∈ restrictedUnion s A star K S p ↔
      ∃ u, ∃ hu : u ∈ S, ∃ e : InverseOccurrence s p u, x ∈ piece A star K e := by
  simp [restrictedUnion]

section RestrictedCover

variable {s : Fin 3 → Word} (A : G →+ G)
  (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
  (injective : Function.Injective A)
  (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
  (tiles : TileEquation s A star K)

theorem restrictedUnion_subset (S : Finset Packet) (p : Packet) :
    restrictedUnion s A star K S p ⊆ overlap star K p := by
  intro x hx
  obtain ⟨u, _, e, he⟩ := (mem_restrictedUnion A star K S p x).mp hx
  exact piece_subset_overlap A star K injective commute tiles e he

/-- This is the weakest exact criterion for preserving the SET union.
It does not justify removing positive multiplicity from an additive recurrence. -/
theorem overlap_eq_restricted_iff (reflects : ReflectsIntegralRange s A star)
    (S : Finset Packet) (p : Packet) :
    overlap star K p = restrictedUnion s A star K S p ↔
      ∀ u, ∀ e : InverseOccurrence s p u, u ∉ S →
        piece A star K e ⊆ restrictedUnion s A star K S p := by
  classical
  constructor
  · intro heq u e _
    rw [← heq]
    exact piece_subset_overlap A star K injective commute tiles e
  · intro omitted
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨u, e, he⟩ :=
        overlap_mem_inverse_piece A star K injective commute reflects tiles p hx
      by_cases hu : u ∈ S
      · exact (mem_restrictedUnion A star K S p x).mpr ⟨u, hu, e, he⟩
      · exact omitted u e hu he
    · exact restrictedUnion_subset A star K injective commute tiles S p

/-- A stronger, local certificate: every actual omitted ancestor overlap
is empty. A merely finite inventory does not provide this premise. Genuine
inverse closure at the source does, by leaving no excluded occurrence. -/
theorem overlap_eq_restricted_of_excluded_empty
    (reflects : ReflectsIntegralRange s A star) (S : Finset Packet) (p : Packet)
    (excluded : ∀ u, InverseOccurrence s p u → u ∉ S → overlap star K u = ∅) :
    overlap star K p = restrictedUnion s A star K S p := by
  apply (overlap_eq_restricted_iff A star K injective commute tiles reflects S p).mpr
  intro u e hu
  rw [(piece_empty_iff A star K e).mpr (excluded u e hu)]
  exact Set.empty_subset _

/-- Nonempty incoming-ancestor representability is a precise sufficient
geometric lemma for the finite restriction. -/
theorem overlap_eq_restricted_of_nonempty_represented
    (reflects : ReflectsIntegralRange s A star) (S : Finset Packet) (p : Packet)
    (represented : ∀ u, InverseOccurrence s p u →
      (overlap star K u).Nonempty → u ∈ S) :
    overlap star K p = restrictedUnion s A star K S p := by
  classical
  apply overlap_eq_restricted_of_excluded_empty A star K injective commute tiles reflects S p
  intro u e hu
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hu (represented u e ⟨x, hx⟩)

/-- Actual inverse closure gives an incoming cover under the geometric
tile/range hypotheses. It says nothing about positive FORWARD exits. -/
theorem overlap_eq_restricted_of_inverse_closed
    (reflects : ReflectsIntegralRange s A star) (S : Finset Packet) (p : Packet)
    (closed : ∀ u, InverseOccurrence s p u → u ∈ S) :
    overlap star K p = restrictedUnion s A star K S p := by
  apply overlap_eq_restricted_of_nonempty_represented
    A star K injective commute tiles reflects S p
  intro u e _
  exact closed u e

end RestrictedCover

/-- An authenticated outer enclosure contains every genuine overlap. -/
theorem overlap_mono_enclosure (star : (Fin 3 → ℤ) →+ G)
    (K B : Fin 3 → Set G) (enclosed : ∀ a, K a ⊆ B a) (p : Packet) :
    overlap star K p ⊆ overlap star B p := by
  intro x hx
  exact ⟨enclosed p.top hx.1, enclosed p.bottom hx.2⟩

theorem overlap_empty_of_enclosure (star : (Fin 3 → ℤ) →+ G)
    (K B : Fin 3 → Set G) (enclosed : ∀ a, K a ⊆ B a) (p : Packet)
    (separated : overlap star B p = ∅) : overlap star K p = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he := overlap_mono_enclosure star K B enclosed p hx
  simpa [separated] using he

/-- A strict separating coordinate proves emptiness. Bounds on actual tiles
(or authenticated enclosing boxes) are essential; a constructor cap is not one. -/
theorem overlap_empty_of_separating_coordinate (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (p : Packet) (coordinate : G →+ ℝ)
    (topUpper bottomLower : ℝ)
    (topBound : ∀ x ∈ K p.top, coordinate x ≤ topUpper)
    (bottomBound : ∀ x ∈ K p.bottom, bottomLower ≤ coordinate x)
    (separated : topUpper < bottomLower + coordinate (star p.delta)) :
    overlap star K p = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := topBound x hx.1
  have hb := bottomBound (x - star p.delta) hx.2
  rw [map_sub] at hb
  linarith

/-- A concrete residue detector can discharge range reflection. Its
annihilation and exact integral-kernel criterion must be proved in the
chosen ambient space; they are not supplied by integer arithmetic alone. -/
theorem reflectsIntegralRange_of_residue {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    {R : Type*} [AddCommGroup R] (residue : G →+ R)
    (annihilates : ∀ x, residue (A x) = 0)
    (integralKernel : ∀ z, residue (star z) = 0 → ∃ y, incidenceZ s *ᵥ y = z) :
    ReflectsIntegralRange s A star := by
  intro z hz
  obtain ⟨x, hx⟩ := hz
  apply integralKernel
  rw [← hx]
  exact annihilates x

section Compactness

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- Compactness refers to the supplied internal overlap, not physical length. -/
theorem isCompact_overlap (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (compactTiles : ∀ a, IsCompact (K a)) (p : Packet) :
    IsCompact (overlap star K p) := by
  rw [overlap_eq_inter_translate]
  exact (compactTiles p.top).inter
    ((compactTiles p.bottom).image (continuous_id.add continuous_const))

theorem continuous_historyMap (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (continuousA : Continuous A)
    (n : ℕ) (p : Packet) (h : History s n p) :
    Continuous (historyMap s A star n p h) := by
  induction n generalizing p with
  | zero => exact continuous_id
  | succ n ih =>
      rcases h with ⟨e, h⟩
      exact (continuousA.add continuous_const).comp (ih e.1 h)

theorem isCompact_historyPiece (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (continuousA : Continuous A) (compactTiles : ∀ a, IsCompact (K a))
    (n : ℕ) (p : Packet) (h : History s n p) :
    IsCompact (historyPiece s A star K n p h) := by
  rw [historyPiece_eq_image]
  exact (isCompact_overlap star K compactTiles _).image
    (continuous_historyMap s A star continuousA n p h)

end Compactness

end Psc.OccurrenceCover
