import PscVerif.OccurrenceGraphBinding

/-!
# Actual inverse-piece decomposition

The complete overlap union is derived from the original tile equation.
The ambient additive action must be injective, commute with the integral
incidence action, and reflect its range on integral translations. These
are explicit geometric inputs, not consequences of finite graph counts.

No topology or measure is needed for the set identities. In particular,
this module constructs neither compact prefix tiles nor Haar measure, and
it does not infer positive compact overlap from physical interval length.
Pre-code gate: `docs/c4-literal-inverse-binding-literature-2026-11-10.md`.
-/

namespace Psc.OccurrencePiece

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Matrix

variable {G : Type*} [AddCommGroup G]

/-- Affine image map in the chosen internal additive space. -/
def affine (A : G →+ G) (t : G) (x : G) : G := A x + t

/-- The positive-prefix overlap: the second tile is translated by `star z`. -/
def overlap (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) (p : Packet) : Set G :=
  {x | x ∈ K p.top ∧ x - star p.delta ∈ K p.bottom}

theorem overlap_eq_inter_translate (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (p : Packet) :
    overlap star K p = K p.top ∩ (fun x => x + star p.delta) '' K p.bottom := by
  ext x
  constructor
  · rintro ⟨ht, hb⟩
    exact ⟨ht, x - star p.delta, hb, sub_add_cancel _ _⟩
  · rintro ⟨ht, y, hy, rfl⟩
    exact ⟨ht, by simpa using hy⟩

/-- Swapping tracks changes the overlap by translation, not by equality. -/
theorem mem_overlap_swap (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (p : Packet) (x : G) :
    x ∈ overlap star K p.swap ↔ x + star p.delta ∈ overlap star K p := by
  simp only [overlap, Set.mem_ofPred_eq, Packet.swap, map_neg, sub_neg_eq_add,
    add_sub_cancel_right]
  exact and_comm

theorem overlap_swap_eq_translate (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (p : Packet) :
    overlap star K p.swap = (fun x => x - star p.delta) '' overlap star K p := by
  ext x
  constructor
  · intro hx
    exact ⟨x + star p.delta, (mem_overlap_swap star K p x).mp hx, add_sub_cancel_right _ _⟩
  · rintro ⟨y, hy, rfl⟩
    apply (mem_overlap_swap star K p _).mpr
    simpa using hy

/-- The two original occurrence pieces before integral inverse solving. -/
def pairedPiece (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) {s : Fin 3 → Word} (p : Packet)
    {a b : Fin 3} (dt : Mark (s a)) (db : Mark (s b)) : Set G :=
  affine A (star (parikhZ dt.before)) '' K a ∩
    affine A (star (p.delta + parikhZ db.before)) '' K b

/-- Integral reversal determines the affine translation of the inverse piece. -/
theorem inverse_shift {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    {p u : Packet} (e : InverseOccurrence s p u) :
    A (star u.delta) + star (parikhZ e.topMark.before) =
      star (p.delta + parikhZ e.bottomMark.before) := by
  rw [commute, e.equation]
  simp only [OccurrenceTransport.residual, map_add, map_sub]
  abel

/-- A single paired-cylinder intersection is exactly its literal inverse
overlap image. Injectivity is used to recover the parent-space equality. -/
theorem pairedPiece_eq_inverse {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    {p u : Packet} (e : InverseOccurrence s p u) :
    pairedPiece A star K p e.topMark e.bottomMark =
      affine A (star (parikhZ e.topMark.before)) '' overlap star K u := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hab : a = b + star u.delta := by
      apply injective
      have ht := inverse_shift A star commute e
      dsimp [affine] at hax hbx
      rw [map_add]
      exact add_right_cancel (show A a + star (parikhZ e.topMark.before) =
          (A b + A (star u.delta)) + star (parikhZ e.topMark.before) by
        rw [add_assoc, ht]
        exact hax.trans hbx.symm)
    refine ⟨a, ⟨ha, ?_⟩, hax⟩
    simpa [hab] using hb
  · rintro ⟨a, ⟨ha, hb⟩, hax⟩
    refine ⟨⟨a, ha, hax⟩, ⟨a - star u.delta, hb, ?_⟩⟩
    have ht := inverse_shift A star commute e
    dsimp [affine] at hax ⊢
    rw [map_sub, ← ht]
    calc
      A a - A (star u.delta) +
          (A (star u.delta) + star (parikhZ e.topMark.before)) =
          A a + star (parikhZ e.topMark.before) := by abel
      _ = x := hax

/-- A normalized target needs the adjusted translation `z + bottomPrefix`. -/
theorem inverse_piece_swapped {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    {p u : Packet} (e : InverseOccurrence s p u) :
    affine A (star (parikhZ e.topMark.before)) '' overlap star K u =
      affine A (star (p.delta + parikhZ e.bottomMark.before)) '' overlap star K u.swap := by
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨a - star u.delta, ?_, ?_⟩
    · apply (mem_overlap_swap star K u _).mpr
      simpa using ha
    · have ht := inverse_shift A star commute e
      dsimp [affine] at hax ⊢
      rw [map_sub, ← ht]
      calc
        A a - A (star u.delta) +
            (A (star u.delta) + star (parikhZ e.topMark.before)) =
            A a + star (parikhZ e.topMark.before) := by abel
        _ = x := hax
  · rintro ⟨b, hb, hbx⟩
    refine ⟨b + star u.delta, (mem_overlap_swap star K u b).mp hb, ?_⟩
    dsimp [affine] at hbx ⊢
    rw [map_add, add_assoc, inverse_shift A star commute e]
    exact hbx

/-- The orientation bit selects the translation for the stored target. -/
def slotTranslation {s : Fin 3 → Word} {p u : Packet} (e : Slot s p u) : Fin 3 → ℤ :=
  if e.targetSwapped then p.delta + parikhZ e.toInverse.bottomMark.before
    else parikhZ e.toInverse.topMark.before

theorem slot_piece_eq_stored {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    {p u : Packet} (e : Slot s p u) :
    affine A (star (parikhZ e.toInverse.topMark.before)) '' overlap star K e.rawTarget =
      affine A (star (slotTranslation e)) '' overlap star K u := by
  cases hb : e.targetSwapped with
  | false => simp [slotTranslation, Slot.rawTarget, hb]
  | true =>
    have h := inverse_piece_swapped A star K commute e.toInverse
    simpa [slotTranslation, Slot.rawTarget, hb, packet_swap_swap] using h

/-- Literal paired pieces are bound to the stored target with the exact
orientation-dependent translation, not merely with equal scalar measure. -/
theorem pairedPiece_eq_stored_slot {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    {p u : Packet} (e : Slot s p u) :
    pairedPiece A star K p e.toInverse.topMark e.toInverse.bottomMark =
      affine A (star (slotTranslation e)) '' overlap star K u :=
  (pairedPiece_eq_inverse A star K injective commute e.toInverse).trans
    (slot_piece_eq_stored A star K commute e)

/-- The original complete tile equation, indexed by actual incoming marks. -/
def TileEquation (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) : Prop :=
  ∀ c x, x ∈ K c ↔ ∃ a, ∃ d : Mark (s a), d.letter = c ∧
    ∃ y ∈ K a, A y + star (parikhZ d.before) = x

/-- The required nonunit residue interface: an ambient preimage of an
integral translation must have an integral incidence preimage. The intended
application uses the compact matrix-adic factor; this condition is not
asserted for the full noncompact adelic field product. -/
def ReflectsIntegralRange (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) : Prop :=
  ∀ z, (∃ x, A x = star z) → ∃ y, incidenceZ s *ᵥ y = z

theorem paired_difference_in_range {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (p : Packet) {a b : Fin 3} (dt : Mark (s a)) (db : Mark (s b))
    {x : G} (hx : x ∈ pairedPiece A star K p dt db) :
    ∃ y, A y = star (p.delta + residual db.before dt.before) := by
  obtain ⟨⟨u, _, hu⟩, ⟨v, _, hv⟩⟩ := hx
  refine ⟨u - v, ?_⟩
  dsimp [affine] at hu hv
  rw [map_sub]
  simp only [OccurrenceTransport.residual, map_add, map_sub]
  have heq := hu.trans hv.symm
  simp only [map_add] at heq
  exact sub_eq_of_eq_add (show A u =
      (star p.delta + (star (parikhZ db.before) - star (parikhZ dt.before))) + A v by
    apply add_right_cancel (b := star (parikhZ dt.before))
    calc
      A u + star (parikhZ dt.before) =
          A v + (star p.delta + star (parikhZ db.before)) := heq
      _ = _ := by abel)

/-- Nonintegrality removes an empty paired set only through the proved
ambient residue-range reflection, not through Euclidean division alone. -/
theorem pairedPiece_empty_of_nonintegral {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (reflects : ReflectsIntegralRange s A star)
    (p : Packet) {a b : Fin 3} (dt : Mark (s a)) (db : Mark (s b))
    (nonintegral : ¬ ∃ y, incidenceZ s *ᵥ y = p.delta + residual db.before dt.before) :
    pairedPiece A star K p dt db = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact nonintegral (reflects _ (paired_difference_in_range A star K p dt db hx))

theorem inverse_piece_subset_overlap {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (tiles : TileEquation s A star K) {p u : Packet} (e : InverseOccurrence s p u) :
    affine A (star (parikhZ e.topMark.before)) '' overlap star K u ⊆ overlap star K p := by
  rw [← pairedPiece_eq_inverse A star K injective commute e]
  intro x hx
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hx
  refine ⟨(tiles p.top x).mpr ⟨u.top, e.topMark, e.top_letter, a, ha, hax⟩, ?_⟩
  apply (tiles p.bottom (x - star p.delta)).mpr
  refine ⟨u.bottom, e.bottomMark, e.bottom_letter, b, hb, ?_⟩
  dsimp [affine] at hbx
  rw [map_add] at hbx
  rw [← hbx]
  abel

/-- The original two tile unions supply an actual integral incoming
occurrence for every point of the overlap. No overlap cover is assumed. -/
theorem overlap_mem_inverse_piece {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (reflects : ReflectsIntegralRange s A star)
    (tiles : TileEquation s A star K) (p : Packet) {x : G}
    (hx : x ∈ overlap star K p) :
    ∃ u, ∃ e : InverseOccurrence s p u,
      x ∈ affine A (star (parikhZ e.topMark.before)) '' overlap star K u := by
  obtain ⟨a, dt, hdt, y, hy, hyx⟩ := (tiles p.top x).mp hx.1
  obtain ⟨b, db, hdb, z, hz, hzx⟩ := (tiles p.bottom (x - star p.delta)).mp hx.2
  have hp : x ∈ pairedPiece A star K p dt db := by
    refine ⟨⟨y, hy, hyx⟩, ⟨z, hz, ?_⟩⟩
    dsimp [affine]
    rw [map_add]
    calc
      A z + (star p.delta + star (parikhZ db.before)) =
          (A z + star (parikhZ db.before)) + star p.delta := by abel
      _ = x := by rw [hzx, sub_add_cancel]
  obtain ⟨delta, hdelta⟩ := reflects _ (paired_difference_in_range A star K p dt db hp)
  let u : Packet := ⟨a, b, delta⟩
  let e : InverseOccurrence s p u := ⟨dt, db, hdt, hdb, hdelta⟩
  refine ⟨u, e, ?_⟩
  rw [← pairedPiece_eq_inverse A star K injective commute e]
  exact hp

/-- Complete incoming decomposition, derived from the original tile equation.
The index retains every actual pair of marks, including repeated targets. -/
theorem overlap_eq_iUnion_inverse {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (reflects : ReflectsIntegralRange s A star)
    (tiles : TileEquation s A star K) (p : Packet) :
    overlap star K p = ⋃ u, ⋃ e : InverseOccurrence s p u,
      affine A (star (parikhZ e.topMark.before)) '' overlap star K u := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, e, he⟩ := overlap_mem_inverse_piece A star K injective commute reflects tiles p hx
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨e, he⟩⟩
  · intro hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hu
    exact inverse_piece_subset_overlap A star K injective commute tiles e he

end Psc.OccurrencePiece
