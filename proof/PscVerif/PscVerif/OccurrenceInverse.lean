/-
# Literal inverse occurrences and diagonal-free ancestry

An inverse edge retains both actual incoming word marks.  Its integral
equation is exactly the reverse of the existing forward digit packet, and
the data equivalence below preserves both numeric occurrence indices.

Positive exact image scaling transports the strict physical strip backwards.
Within one literal word, distinct letter intervals have disjoint interiors;
therefore an interior child of an integral diagonal is diagonal.  Backward
ancestry from a nondiagonal interior root has no fixed track-swap packet.

No finite carrier, compact overlap set, Haar equation or loss witness is
constructed here.  The pre-code review is
`docs/c4-inverse-occurrence-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceMass

namespace Psc.OccurrenceInverse

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.OccurrenceFinite Psc.OccurrenceSuccessor
open Psc.OccurrenceMass Matrix

/-- The actual image word of a letter after the specified number of
substitutions, including the identity image at depth zero. -/
def iterateImages (s : Fin 3 → Word) (k : ℕ) (a : Fin 3) : Word :=
  (subst s)^[k] [a]

/-- A powered incidence is bound to the actual iterated image words. -/
theorem incidenceZ_iterateImages (s : Fin 3 → Word) (k : ℕ) :
    incidenceZ (iterateImages s k) = (incidenceZ s) ^ k := by
  calc
    incidenceZ (iterateImages s k) = ((inc s) ^ k).map (Nat.castRingHom ℤ) := by
      ext a b
      simp [incidenceZ, iterateImages, count_iterate_subst]
    _ = (incidenceZ s) ^ k :=
      map_pow ((Nat.castRingHom ℤ).mapMatrix) (inc s) k

theorem packet_ext {p q : Packet} (ht : p.top = q.top)
    (hb : p.bottom = q.bottom) (hz : p.delta = q.delta) : p = q := by
  cases p
  cases q
  cases ht
  cases hb
  cases hz
  rfl

@[simp] theorem packet_swap_swap (p : Packet) : p.swap.swap = p := by
  cases p
  simp [Packet.swap]

theorem packet_swap_involutive : Function.Involutive Packet.swap := packet_swap_swap

/-- Fixed track-swap packets are exactly integral diagonals.  No physical
length independence is needed: integral vectors have no two-torsion. -/
theorem packet_swap_eq_iff_diagonal (p : Packet) : p.swap = p ↔ p.Diagonal := by
  constructor
  · intro h
    refine ⟨(congrArg Packet.top h).symm, ?_⟩
    funext a
    have ha := congrArg (fun q : Packet => q.delta a) h
    change -(p.delta a) = p.delta a at ha
    change p.delta a = 0
    omega
  · rintro ⟨ht, hz⟩
    apply packet_ext
    · exact ht.symm
    · exact ht
    · simp [Packet.swap, hz]

/-- Current child `p` and inverse ancestor `u`, retaining both incoming
occurrences and exact lattice membership as an integral equation. -/
structure InverseOccurrence (s : Fin 3 → Word) (p u : Packet) where
  topMark : Mark (s u.top)
  bottomMark : Mark (s u.bottom)
  top_letter : topMark.letter = p.top
  bottom_letter : bottomMark.letter = p.bottom
  equation : incidenceZ s *ᵥ u.delta =
    p.delta + residual bottomMark.before topMark.before

/-- The historical powered-matrix equation, for the very same incoming
marks in the actual iterated words. -/
theorem InverseOccurrence.iterate_equation (s : Fin 3 → Word) (k : ℕ)
    {p u : Packet} (e : InverseOccurrence (iterateImages s k) p u) :
    (incidenceZ s) ^ k *ᵥ u.delta =
      p.delta + residual e.bottomMark.before e.topMark.before := by
  simpa only [incidenceZ_iterateImages] using e.equation

@[ext] theorem InverseOccurrence.ext {s : Fin 3 → Word} {p u : Packet}
    {e f : InverseOccurrence s p u}
    (ht : e.topMark = f.topMark) (hb : e.bottomMark = f.bottomMark) : e = f := by
  cases e
  cases f
  cases ht
  cases hb
  rfl

/-- Rearranging the equation preserves the two supplied actual marks. -/
theorem InverseOccurrence.forward_packet_eq {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) :
    p = ⟨e.topMark.letter, e.bottomMark.letter,
      incidenceZ s *ᵥ u.delta + residual e.topMark.before e.bottomMark.before⟩ := by
  apply packet_ext e.top_letter.symm e.bottom_letter.symm
  change p.delta = incidenceZ s *ᵥ u.delta +
    residual e.topMark.before e.bottomMark.before
  rw [e.equation, residual_swap e.topMark.before e.bottomMark.before]
  abel

def InverseOccurrence.ofMarks (s : Fin 3 → Word) (p u : Packet)
    (dt : Mark (s u.top)) (db : Mark (s u.bottom))
    (hp : p = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ u.delta + residual dt.before db.before⟩) :
    InverseOccurrence s p u where
  topMark := dt
  bottomMark := db
  top_letter := (congrArg Packet.top hp).symm
  bottom_letter := (congrArg Packet.bottom hp).symm
  equation := by
    have hz := congrArg Packet.delta hp
    change p.delta = incidenceZ s *ᵥ u.delta + residual dt.before db.before at hz
    rw [hz, residual_swap dt.before db.before]
    abel

theorem InverseOccurrence.digitStep {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) : DigitStep s u p :=
  ⟨e.topMark, e.bottomMark, e.forward_packet_eq⟩

theorem nonempty_inverse_iff_digitStep (s : Fin 3 → Word) (p u : Packet) :
    Nonempty (InverseOccurrence s p u) ↔ DigitStep s u p := by
  constructor
  · rintro ⟨e⟩
    exact e.digitStep
  · rintro ⟨dt, db, hp⟩
    exact ⟨InverseOccurrence.ofMarks s p u dt db hp⟩

/-- A forward occurrence uses the exact two indices of the production
`digitPacket` constructor, rather than an existential edge label. -/
structure ForwardOccurrence (s : Fin 3 → Word) (u p : Packet) where
  topIndex : Fin (s u.top).length
  bottomIndex : Fin (s u.bottom).length
  packet_eq : p = digitPacket s u topIndex bottomIndex

@[ext] theorem ForwardOccurrence.ext {s : Fin 3 → Word} {p u : Packet}
    {e f : ForwardOccurrence s u p}
    (ht : e.topIndex = f.topIndex) (hb : e.bottomIndex = f.bottomIndex) : e = f := by
  cases e
  cases f
  cases ht
  cases hb
  rfl

def InverseOccurrence.toForward {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) : ForwardOccurrence s u p where
  topIndex := markIndex e.topMark
  bottomIndex := markIndex e.bottomMark
  packet_eq := by
    simpa only [digitPacket, markAt_markIndex] using e.forward_packet_eq

def ForwardOccurrence.toInverse {s : Fin 3 → Word} {p u : Packet}
    (e : ForwardOccurrence s u p) : InverseOccurrence s p u :=
  InverseOccurrence.ofMarks s p u (markAt _ e.topIndex) (markAt _ e.bottomIndex)
    e.packet_eq

@[simp] theorem InverseOccurrence.toForward_topIndex {s : Fin 3 → Word}
    {p u : Packet} (e : InverseOccurrence s p u) :
    e.toForward.topIndex = markIndex e.topMark := rfl

@[simp] theorem InverseOccurrence.toForward_bottomIndex {s : Fin 3 → Word}
    {p u : Packet} (e : InverseOccurrence s p u) :
    e.toForward.bottomIndex = markIndex e.bottomMark := rfl

@[simp] theorem InverseOccurrence.toForward_toInverse {s : Fin 3 → Word}
    {p u : Packet} (e : InverseOccurrence s p u) : e.toForward.toInverse = e := by
  apply InverseOccurrence.ext <;>
    simp [InverseOccurrence.toForward, ForwardOccurrence.toInverse,
      InverseOccurrence.ofMarks, markAt_markIndex]

@[simp] theorem ForwardOccurrence.toInverse_toForward {s : Fin 3 → Word}
    {p u : Packet} (e : ForwardOccurrence s u p) : e.toInverse.toForward = e := by
  apply ForwardOccurrence.ext <;>
    apply Fin.ext <;>
    simp [InverseOccurrence.toForward, ForwardOccurrence.toInverse,
      InverseOccurrence.ofMarks, markIndex, markAt_index]

/-- Data-level reversal, with round trips on both occurrence identities. -/
def inverseEquivForward (s : Fin 3 → Word) (p u : Packet) :
    InverseOccurrence s p u ≃ ForwardOccurrence s u p where
  toFun := InverseOccurrence.toForward
  invFun := ForwardOccurrence.toInverse
  left_inv := InverseOccurrence.toForward_toInverse
  right_inv := ForwardOccurrence.toInverse_toForward

/-- Swap actual incoming marks together with packet letters and signs. -/
def InverseOccurrence.swap {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) : InverseOccurrence s p.swap u.swap where
  topMark := e.bottomMark
  bottomMark := e.topMark
  top_letter := e.bottom_letter
  bottom_letter := e.top_letter
  equation := by
    change incidenceZ s *ᵥ (-u.delta) =
      -p.delta + residual e.topMark.before e.bottomMark.before
    rw [Matrix.mulVec_neg, e.equation,
      residual_swap e.topMark.before e.bottomMark.before]
    abel

/-- Explicit inverse to the mark-swapping map avoids any quotient of the
two occurrence addresses. -/
def InverseOccurrence.unswap {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p.swap u.swap) : InverseOccurrence s p u where
  topMark := e.bottomMark
  bottomMark := e.topMark
  top_letter := e.bottom_letter
  bottom_letter := e.top_letter
  equation := by
    have h := e.equation
    change incidenceZ s *ᵥ (-u.delta) =
      -p.delta + residual e.bottomMark.before e.topMark.before at h
    calc
      incidenceZ s *ᵥ u.delta = -(incidenceZ s *ᵥ (-u.delta)) := by
        rw [Matrix.mulVec_neg, neg_neg]
      _ = -(-p.delta + residual e.bottomMark.before e.topMark.before) :=
        congrArg Neg.neg h
      _ = p.delta + residual e.topMark.before e.bottomMark.before := by
        rw [residual_swap e.bottomMark.before e.topMark.before]
        abel

def inverseSwapEquiv (s : Fin 3 → Word) (p u : Packet) :
    InverseOccurrence s p u ≃ InverseOccurrence s p.swap u.swap where
  toFun := InverseOccurrence.swap
  invFun := InverseOccurrence.unswap
  left_inv e := by apply InverseOccurrence.ext <;> rfl
  right_inv e := by apply InverseOccurrence.ext <;> rfl

@[simp] theorem InverseOccurrence.swap_topIndex {s : Fin 3 → Word}
    {p u : Packet} (e : InverseOccurrence s p u) :
    e.swap.toForward.topIndex = e.toForward.bottomIndex := rfl

@[simp] theorem InverseOccurrence.swap_bottomIndex {s : Fin 3 → Word}
    {p u : Packet} (e : InverseOccurrence s p u) :
    e.swap.toForward.bottomIndex = e.toForward.topIndex := rfl

/-! ## Literal partition geometry -/

theorem mark_prefix_bounds (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    {w : Word} (m : Mark w) :
    0 ≤ physicalLength ℓ m.before ∧
      physicalLength ℓ m.before + ℓ m.letter ≤ physicalLength ℓ w := by
  refine ⟨physicalLength_nonneg ℓ hnonneg _, ?_⟩
  have hlength := congrArg (physicalLength ℓ) m.split
  rw [physicalLength_append, physicalLength_cons] at hlength
  linarith [physicalLength_nonneg ℓ hnonneg m.after]

theorem physical_take_mono (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    (w : Word) {i j : ℕ} (hij : i ≤ j) :
    physicalLength ℓ (w.take i) ≤ physicalLength ℓ (w.take j) := by
  obtain ⟨rest, hrest⟩ := List.take_prefix_take_left (l := w) hij
  rw [← hrest, physicalLength_append]
  exact le_add_of_nonneg_right (physicalLength_nonneg ℓ hnonneg rest)

theorem mark_end_le_start (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    {w : Word} (m n : Mark w) (h : m.index < n.index) :
    physicalLength ℓ m.before + ℓ m.letter ≤ physicalLength ℓ n.before := by
  have hp := physical_take_mono ℓ hnonneg w (Nat.succ_le_of_lt h)
  rw [List.take_succ_eq_append_getElem m.index_lt, physicalLength_append,
    physicalLength_singleton, m.take_index, m.selected, n.take_index] at hp
  exact hp

/-- Distinct positions in one actual word cannot have a common strict
interior.  Zero-length intervening letters do not invalidate disjointness. -/
theorem marks_eq_of_overlap (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    {w : Word} (m n : Mark w) (x : ℝ)
    (hmlo : physicalLength ℓ m.before < x)
    (hmhi : x < physicalLength ℓ m.before + ℓ m.letter)
    (hnlo : physicalLength ℓ n.before < x)
    (hnhi : x < physicalLength ℓ n.before + ℓ n.letter) : m = n := by
  apply mark_index_injective w
  rcases lt_trichotomy m.index n.index with hlt | heq | hgt
  · have hsep := mark_end_le_start ℓ hnonneg m n hlt
    linarith
  · exact heq
  · have hsep := mark_end_le_start ℓ hnonneg n m hgt
    linarith

theorem marks_eq_of_packet_interior (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    {w : Word} (m n : Mark w)
    (h : (⟨m.letter, n.letter, residual m.before n.before⟩ : Packet).Interior ℓ) :
    m = n := by
  obtain ⟨x, hxlo, hxhi, hylo, hyhi⟩ := h
  change 0 < x at hxlo
  change x < ℓ m.letter at hxhi
  change 0 < x + offset ℓ (residual m.before n.before) at hylo
  change x + offset ℓ (residual m.before n.before) < ℓ n.letter at hyhi
  rw [offset_residual] at hylo hyhi
  apply marks_eq_of_overlap ℓ hnonneg m n (x + physicalLength ℓ m.before) <;>
    linarith

/-- An interior forward child of an integral diagonal is itself diagonal.
This is a literal one-word partition fact, not a Pisot independence result. -/
theorem diagonal_of_digitStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hnonneg : ∀ a, 0 ≤ ℓ a) {p q : Packet}
    (hstep : DigitStep s p q) (hp : p.Diagonal) (hq : q.Interior ℓ) :
    q.Diagonal := by
  rcases p with ⟨a, b, z⟩
  rcases hp with ⟨hab, hz⟩
  change a = b at hab
  change z = 0 at hz
  subst b
  subst z
  obtain ⟨dt, db, rfl⟩ := hstep
  have hoverlap : (⟨dt.letter, db.letter, residual dt.before db.before⟩ : Packet).Interior ℓ := by
    simpa only [Matrix.mulVec_zero, zero_add] using hq
  have hmarks := marks_eq_of_packet_interior ℓ hnonneg dt db hoverlap
  cases hmarks
  simp [Packet.Diagonal, OccurrenceTransport.residual]

/-! ## Interior inverse ancestry -/

theorem InverseOccurrence.offset_equation (s : Fin 3 → Word)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p u : Packet} (e : InverseOccurrence s p u) :
    β * offset ℓ u.delta = offset ℓ p.delta +
      physicalLength ℓ e.bottomMark.before - physicalLength ℓ e.topMark.before := by
  have h := congrArg (offset ℓ) e.equation
  rw [offset_incidence s ℓ β hscale, offset_add, offset_residual] at h
  linarith

/-- Every literal inverse ancestor of an interior packet retains the strict
typed strip.  Exact scaling and a positive scale are explicit premises. -/
theorem InverseOccurrence.interior (s : Fin 3 → Word)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p u : Packet} (e : InverseOccurrence s p u) (hp : p.Interior ℓ) :
    u.Interior ℓ := by
  have hnonneg : ∀ a, 0 ≤ ℓ a := fun a => (hpos a).le
  have htop := mark_prefix_bounds ℓ hnonneg e.topMark
  have hbottom := mark_prefix_bounds ℓ hnonneg e.bottomMark
  rw [hscale, e.top_letter] at htop
  rw [hscale, e.bottom_letter] at hbottom
  have hd := e.offset_equation s ℓ β hscale
  have hb := (Packet.interior_iff_bounds ℓ hpos p).mp hp
  apply (Packet.interior_iff_bounds ℓ hpos u).mpr
  constructor
  · apply (mul_lt_mul_iff_right₀ hβ).mp
    nlinarith
  · apply (mul_lt_mul_iff_right₀ hβ).mp
    nlinarith

theorem InverseOccurrence.nondiagonal {s : Fin 3 → Word}
    (ℓ : Fin 3 → ℝ) (hnonneg : ∀ a, 0 ≤ ℓ a)
    {p u : Packet} (e : InverseOccurrence s p u)
    (hp : p.Interior ℓ) (hnd : ¬p.Diagonal) : ¬u.Diagonal := by
  intro hu
  exact hnd (diagonal_of_digitStep s ℓ hnonneg e.digitStep hu hp)

def InverseStep (s : Fin 3 → Word) (p u : Packet) : Prop :=
  Nonempty (InverseOccurrence s p u)

theorem inverseStep_swap {s : Fin 3 → Word} {p u : Packet}
    (h : InverseStep s p u) : InverseStep s p.swap u.swap := by
  obtain ⟨e⟩ := h
  exact ⟨e.swap⟩

theorem inverse_path_swap {s : Fin 3 → Word} {p u : Packet}
    (h : Relation.ReflTransGen (InverseStep s) p u) :
    Relation.ReflTransGen (InverseStep s) p.swap u.swap := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hedge _ ih => exact .head (inverseStep_swap hedge) ih

/-- Interior and absence of integral diagonals persist together along
every finite backward ancestry path, including the length-zero path. -/
theorem inverse_path_interior_nondiagonal (s : Fin 3 → Word)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p u : Packet} (hpath : Relation.ReflTransGen (InverseStep s) p u)
    (hp : p.Interior ℓ) (hnd : ¬p.Diagonal) : u.Interior ℓ ∧ ¬u.Diagonal := by
  revert hp hnd
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hp hnd => ⟨hp, hnd⟩
  | head hedge _ ih =>
    intro hp hnd
    obtain ⟨e⟩ := hedge
    exact ih (e.interior s ℓ β hpos hβ hscale hp)
      (e.nondiagonal ℓ (fun a => (hpos a).le) hp hnd)

theorem inverse_ancestor_swap_ne (s : Fin 3 → Word)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p u : Packet} (hpath : Relation.ReflTransGen (InverseStep s) p u)
    (hp : p.Interior ℓ) (hnd : ¬p.Diagonal) : u.swap ≠ u := by
  intro hfixed
  exact (inverse_path_interior_nondiagonal s ℓ β hpos hβ hscale hpath hp hnd).2
    ((packet_swap_eq_iff_diagonal u).mp hfixed)

/-- All finite inverse ancestors of a supplied root predicate.  Finiteness
of this set is deliberately not asserted by the definition. -/
def Ancestry (s : Fin 3 → Word) (roots : Packet → Prop) (u : Packet) : Prop :=
  ∃ p, roots p ∧ Relation.ReflTransGen (InverseStep s) p u

theorem ancestry_swap_closed (s : Fin 3 → Word) (roots : Packet → Prop)
    (hroots : ∀ p, roots p → roots p.swap) {u : Packet}
    (hu : Ancestry s roots u) : Ancestry s roots u.swap := by
  obtain ⟨p, hp, hpath⟩ := hu
  exact ⟨p.swap, hroots p hp, inverse_path_swap hpath⟩

theorem ancestry_free (s : Fin 3 → Word) (roots : Packet → Prop)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hroots : ∀ p, roots p → p.Interior ℓ ∧ ¬p.Diagonal)
    {u : Packet} (hu : Ancestry s roots u) : u.swap ≠ u := by
  obtain ⟨p, hp, hpath⟩ := hu
  exact inverse_ancestor_swap_ne s ℓ β hpos hβ hscale hpath
    (hroots p hp).1 (hroots p hp).2

end Psc.OccurrenceInverse
