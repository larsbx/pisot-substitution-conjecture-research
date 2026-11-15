import PscVerif.OccurrenceCover

/-!
# Local admissibility of actual incoming paired pieces

The literal tile equations give a finite union over all selected pairs of
full marks, including pairs with no integral inverse displacement. Turning
that union into an integral occurrence cover requires a separate local
lifting premise on its nonempty pieces. Restriction to a supplied finite
domain requires represented lifts at every intermediate source.

These interfaces do not authenticate compact Pisot tiles, their admissible
translation module, or any measure recurrence. Equal sets do not identify
occurrence addresses or remove multiplicities. The projected-profile
exclusion is conditional on a proved enclosure and commuting action. In
particular, a useful finite residue map on an authentic nonunit model may
require restriction to a proved support module; no such instance is supplied.
Pre-code gate: `docs/c4-local-admissibility-literature-2026-11-11.md`.
-/

namespace Psc.OccurrenceAdmissibility

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrencePiece
open Psc.OccurrenceCover Psc.OccurrenceFinite Psc.OccurrenceNewborn Matrix

/-- An actual selected pair retains both parent letters and both full marks.
No integral inverse test, box filter, or endpoint quotient is applied. -/
abbrev SelectedPair (s : Fin 3 → Word) (p : Packet) :=
  {d : Digit s × Digit s // d.1.2.letter = p.top ∧ d.2.2.letter = p.bottom}

@[instance_reducible] noncomputable def selectedPairFintype
    (s : Fin 3 → Word) (p : Packet) : Fintype (SelectedPair s p) := by
  classical
  letI := digitFintype s
  infer_instance

/-- The raw finite inventory exists even for singular integral incidence. -/
theorem finite_selectedPair (s : Fin 3 → Word) (p : Packet) :
    Finite (SelectedPair s p) := by
  let := selectedPairFintype s p
  infer_instance

/-- The exact count is the product of the two incoming literal-digit
counts; equal letters or equal geometric pieces do not collapse marks. -/
theorem selectedPair_card_eq (s : Fin 3 → Word) (p : Packet) :
    Nat.card (SelectedPair s p) =
      Nat.card {d : Digit s // d.2.letter = p.top} *
        Nat.card {d : Digit s // d.2.letter = p.bottom} := by
  let e : SelectedPair s p ≃
      {d : Digit s // d.2.letter = p.top} ×
        {d : Digit s // d.2.letter = p.bottom} :=
    { toFun := fun d => (⟨d.val.1, d.property.1⟩, ⟨d.val.2, d.property.2⟩)
      invFun := fun d => ⟨(d.1.val, d.2.val), d.1.property, d.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

theorem selectedPair_card_le (s : Fin 3 → Word) (p : Packet) :
    Nat.card (SelectedPair s p) ≤ (∑ a, (s a).length) ^ 2 := by
  let := digitFintype s
  calc
    Nat.card (SelectedPair s p) ≤ Nat.card (Digit s × Digit s) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = (∑ a, (s a).length) ^ 2 := by rw [Nat.card_prod, digit_card, pow_two]

/-- Numeric literal addresses still include both parent letters. -/
def pairAddress {s : Fin 3 → Word} {p : Packet} (d : SelectedPair s p) :
    (Fin 3 × ℕ) × (Fin 3 × ℕ) :=
  ((d.val.1.1, (markIndex d.val.1.2).val),
    (d.val.2.1, (markIndex d.val.2.2).val))

theorem pairAddress_injective {s : Fin 3 → Word} {p : Packet} :
    Function.Injective (@pairAddress s p) := by
  rintro ⟨⟨⟨a, dt⟩, ⟨b, db⟩⟩, ht, hb⟩
    ⟨⟨⟨a', dt'⟩, ⟨b', db'⟩⟩, ht', hb'⟩ h
  have ha : a = a' := congrArg (fun k : (Fin 3 × ℕ) × (Fin 3 × ℕ) => k.1.1) h
  have hb'' : b = b' := congrArg (fun k : (Fin 3 × ℕ) × (Fin 3 × ℕ) => k.2.1) h
  subst a'
  subst b'
  have hi := congrArg (fun k : (Fin 3 × ℕ) × (Fin 3 × ℕ) => k.1.2) h
  have hj := congrArg (fun k : (Fin 3 × ℕ) × (Fin 3 × ℕ) => k.2.2) h
  have hdt : dt = dt' := (markEquiv (s a)).injective (Fin.ext hi)
  have hdb : db = db' := (markEquiv (s b)).injective (Fin.ext hj)
  subst dt'
  subst db'
  rfl

/-- The exact right-hand side of the integer inverse equation. -/
def pairRhs {s : Fin 3 → Word} {p : Packet} (d : SelectedPair s p) : Fin 3 → ℤ :=
  p.delta + OccurrenceTransport.residual d.val.2.2.before d.val.1.2.before

def pairTarget {s : Fin 3 → Word} {p : Packet}
    (d : SelectedPair s p) (y : Fin 3 → ℤ) : Packet :=
  ⟨d.val.1.1, d.val.2.1, y⟩

/-- An integral lift reuses exactly the selected marks. -/
def pairLift {s : Fin 3 → Word} {p : Packet} (d : SelectedPair s p)
    (y : Fin 3 → ℤ) (hy : incidenceZ s *ᵥ y = pairRhs d) :
    InverseOccurrence s p (pairTarget d y) :=
  ⟨d.val.1.2, d.val.2.2, d.property.1, d.property.2, hy⟩

def pairOfInverse {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) : SelectedPair s p :=
  ⟨(⟨u.top, e.topMark⟩, ⟨u.bottom, e.bottomMark⟩), e.top_letter, e.bottom_letter⟩

@[simp] theorem pairTarget_ofInverse {s : Fin 3 → Word} {p u : Packet}
    (e : InverseOccurrence s p u) : pairTarget (pairOfInverse e) u.delta = u := by
  cases u
  rfl

@[simp] theorem pairOfInverse_lift {s : Fin 3 → Word} {p : Packet}
    (d : SelectedPair s p) (y : Fin 3 → ℤ)
    (hy : incidenceZ s *ᵥ y = pairRhs d) :
    pairOfInverse (pairLift d y hy) = d := by
  rcases d with ⟨⟨⟨a, dt⟩, ⟨b, db⟩⟩, ht, hb⟩
  rfl

/-- Fixing both endpoints leaves finitely many literal records even when
the unrestricted integral incoming fibre is infinite. -/
@[instance_reducible] noncomputable def inverseFintype
    (s : Fin 3 → Word) (p u : Packet) : Fintype (InverseOccurrence s p u) := by
  classical
  letI : Fintype (Mark (s u.top)) :=
    Fintype.ofEquiv (Fin (s u.top).length) (markEquiv (s u.top)).symm
  letI : Fintype (Mark (s u.bottom)) :=
    Fintype.ofEquiv (Fin (s u.bottom).length) (markEquiv (s u.bottom)).symm
  exact Fintype.ofInjective (fun e : InverseOccurrence s p u => (e.topMark, e.bottomMark))
    (fun _ _ h => InverseOccurrence.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- A finite retained domain and finite marks suffice for finite histories.
Integral incidence injectivity is not required for this restricted index. -/
theorem finite_restrictedHistory (s : Fin 3 → Word) (S : Finset Packet)
    (n : ℕ) (p : Packet) :
    Finite {h : History s n p // historyWithin s S n p h} := by
  classical
  induction n generalizing p with
  | zero =>
      change Finite {h : Unit // True}
      infer_instance
  | succ n ih =>
      let (u : {u // u ∈ S}) : Fintype (InverseOccurrence s p u.val) :=
        inverseFintype s p u.val
      let (u : {u // u ∈ S}) : Finite
          {h : History s n u.val // historyWithin s S n u.val h} := ih u.val
      let I := Σ u : {u // u ∈ S}, InverseOccurrence s p u.val ×
        {h : History s n u.val // historyWithin s S n u.val h}
      let f : {h : History s (n + 1) p // historyWithin s S (n + 1) p h} → I :=
        fun h => ⟨⟨h.val.1.1, h.property.1⟩, h.val.1.2, ⟨h.val.2, h.property.2⟩⟩
      let g : I → {h : History s (n + 1) p // historyWithin s S (n + 1) p h} :=
        fun v => ⟨⟨⟨v.1.val, v.2.1⟩, v.2.2.val⟩, v.1.property, v.2.2.property⟩
      have left : Function.LeftInverse g f := by
        intro h
        rfl
      exact Finite.of_injective f left.injective

variable {G : Type*} [AddCommGroup G]

/-- The original paired set indexed by its complete selected occurrence. -/
def pairPiece {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    {p : Packet} (d : SelectedPair s p) : Set G :=
  pairedPiece A star K p d.val.1.2 d.val.2.2

/-- Local lifting is required only for nonempty selected paired pieces. -/
def LocalAdmissible (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) (p : Packet) : Prop :=
  ∀ d : SelectedPair s p, (pairPiece A star K d).Nonempty →
    ∃ y, incidenceZ s *ᵥ y = pairRhs d

/-- Each nonempty pair has a lift in the supplied domain. If incidence is
singular this existential contract need not represent every possible lift. -/
def RepresentedAt (s : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (S : Finset Packet) (p : Packet) : Prop :=
  ∀ d : SelectedPair s p, (pairPiece A star K d).Nonempty →
    ∃ y, incidenceZ s *ᵥ y = pairRhs d ∧ pairTarget d y ∈ S

theorem localAdmissible_iff_nonintegral_empty {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) (p : Packet) :
    LocalAdmissible s A star K p ↔
      ∀ d : SelectedPair s p, (¬ ∃ y, incidenceZ s *ᵥ y = pairRhs d) →
        pairPiece A star K d = ∅ := by
  classical
  constructor
  · intro admissible d nonintegral
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact nonintegral (admissible d ⟨x, hx⟩)
  · intro excluded d hn
    by_contra nonintegral
    obtain ⟨x, hx⟩ := hn
    rw [excluded d nonintegral] at hx
    exact hx

theorem localAdmissible_of_reflects {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (reflects : ReflectsIntegralRange s A star) (p : Packet) :
    LocalAdmissible s A star K p := by
  rintro d ⟨x, hx⟩
  exact reflects _ (paired_difference_in_range A star K p d.val.1.2 d.val.2.2 hx)

theorem representedAt_implies_local {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (S : Finset Packet) (p : Packet) (represented : RepresentedAt s A star K S p) :
    LocalAdmissible s A star K p := by
  intro d hn
  obtain ⟨y, hy, _⟩ := represented d hn
  exact ⟨y, hy⟩

/-- Every pair with no retained integral lift must be empty for the
represented-pair contract. This is stronger than equality of set unions. -/
theorem representedAt_iff_unrepresented_empty {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (S : Finset Packet) (p : Packet) :
    RepresentedAt s A star K S p ↔
      ∀ d : SelectedPair s p,
        (¬ ∃ y, incidenceZ s *ᵥ y = pairRhs d ∧ pairTarget d y ∈ S) →
          pairPiece A star K d = ∅ := by
  classical
  constructor
  · intro represented d missing
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact missing (represented d ⟨x, hx⟩)
  · intro excluded d hn
    by_contra missing
    obtain ⟨x, hx⟩ := hn
    rw [excluded d missing] at hx
    exact hx

section RawCover

variable {s : Fin 3 → Word} (A : G →+ G)
  (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
  (tiles : TileEquation s A star K)

include tiles

/-- Every selected raw piece belongs to the original overlap. No action
injectivity, incidence commutation, or integral lift is needed. -/
theorem pairPiece_subset_overlap {p : Packet} (d : SelectedPair s p) :
    pairPiece A star K d ⊆ overlap star K p := by
  rintro x ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
  refine ⟨(tiles p.top x).mpr
    ⟨d.val.1.1, d.val.1.2, d.property.1, a, ha, hax⟩, ?_⟩
  apply (tiles p.bottom (x - star p.delta)).mpr
  refine ⟨d.val.2.1, d.val.2.2, d.property.2, b, hb, ?_⟩
  dsimp [affine] at hbx
  rw [map_add] at hbx
  rw [← hbx]
  abel

/-- Intersecting the two literal tile equations gives an actual selected
pair at every point, before testing any inverse equation. -/
theorem overlap_mem_pairPiece (p : Packet) {x : G} (hx : x ∈ overlap star K p) :
    ∃ d : SelectedPair s p, x ∈ pairPiece A star K d := by
  obtain ⟨a, dt, hdt, y, hy, hyx⟩ := (tiles p.top x).mp hx.1
  obtain ⟨b, db, hdb, z, hz, hzx⟩ := (tiles p.bottom (x - star p.delta)).mp hx.2
  refine ⟨⟨(⟨a, dt⟩, ⟨b, db⟩), hdt, hdb⟩, ⟨y, hy, hyx⟩, ⟨z, hz, ?_⟩⟩
  change A z + star (p.delta + parikhZ db.before) = x
  rw [map_add]
  calc
    A z + (star p.delta + star (parikhZ db.before)) =
        (A z + star (parikhZ db.before)) + star p.delta := by abel
    _ = x := by rw [hzx, sub_add_cancel]

/-- Complete finite raw-pair union from the tile equations alone. -/
theorem overlap_eq_iUnion_pairPiece (p : Packet) :
    overlap star K p = ⋃ d : SelectedPair s p, pairPiece A star K d := by
  ext x
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := overlap_mem_pairPiece A star K tiles p hx
    exact Set.mem_iUnion.mpr ⟨d, hd⟩
  · intro hx
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
    exact pairPiece_subset_overlap A star K tiles d hd

/-- The exact set-cover criterion checks all raw pairs, including those
with nonintegral inverse equations. It says nothing about counting measures. -/
theorem overlap_eq_set_iff_pairPiece_subset (p : Packet) (R : Set G)
    (retained : R ⊆ overlap star K p) :
    overlap star K p = R ↔ ∀ d : SelectedPair s p, pairPiece A star K d ⊆ R := by
  constructor
  · intro heq d
    rw [← heq]
    exact pairPiece_subset_overlap A star K tiles d
  · intro cover
    apply Set.Subset.antisymm ?_ retained
    intro x hx
    obtain ⟨d, hd⟩ := overlap_mem_pairPiece A star K tiles p hx
    exact cover d hd

end RawCover

section IntegralLift

variable {s : Fin 3 → Word} (A : G →+ G)
  (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
  (injective : Function.Injective A)
  (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))

include injective commute

theorem pairPiece_eq_piece {p : Packet} (d : SelectedPair s p)
    (y : Fin 3 → ℤ) (hy : incidenceZ s *ᵥ y = pairRhs d) :
    pairPiece A star K d = piece A star K (pairLift d y hy) :=
  pairedPiece_eq_inverse A star K injective commute (pairLift d y hy)

theorem pairPiece_ofInverse_eq {p u : Packet} (e : InverseOccurrence s p u) :
    pairPiece A star K (pairOfInverse e) = piece A star K e :=
  pairedPiece_eq_inverse A star K injective commute e

/-- Local lifting and representation of every nonempty inverse ancestor
imply the existential represented-pair contract without incidence injectivity. -/
theorem representedAt_of_local (S : Finset Packet) (p : Packet)
    (admissible : LocalAdmissible s A star K p)
    (represented : ∀ u, InverseOccurrence s p u →
      (overlap star K u).Nonempty → u ∈ S) :
    RepresentedAt s A star K S p := by
  intro d hn
  obtain ⟨y, hy⟩ := admissible d hn
  refine ⟨y, hy, represented (pairTarget d y) (pairLift d y hy) ?_⟩
  rw [pairPiece_eq_piece A star K injective commute d y hy] at hn
  obtain ⟨_, z, hz, _⟩ := hn
  exact ⟨z, hz⟩

/-- Incidence injectivity is needed to pass from some represented lift to
every nonempty actual inverse ancestor. Singular incidence can have many lifts. -/
theorem representedAt_all_ancestors
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y))
    (S : Finset Packet) (p : Packet) (represented : RepresentedAt s A star K S p)
    (u : Packet) (e : InverseOccurrence s p u) (hn : (overlap star K u).Nonempty) :
    u ∈ S := by
  obtain ⟨x, hx⟩ := hn
  have hp : (pairPiece A star K (pairOfInverse e)).Nonempty := by
    rw [pairPiece_ofInverse_eq A star K injective commute e]
    exact ⟨affine A (star (parikhZ e.topMark.before)) x, x, hx, rfl⟩
  obtain ⟨y, hy, hS⟩ := represented (pairOfInverse e) hp
  have he : y = u.delta := integralInjective (hy.trans e.equation.symm)
  rw [he, pairTarget_ofInverse] at hS
  exact hS

theorem representedAt_iff_local_and_all_ancestors
    (integralInjective : Function.Injective (fun y => incidenceZ s *ᵥ y))
    (S : Finset Packet) (p : Packet) :
    RepresentedAt s A star K S p ↔ LocalAdmissible s A star K p ∧
      ∀ u, InverseOccurrence s p u → (overlap star K u).Nonempty → u ∈ S := by
  constructor
  · intro represented
    exact ⟨representedAt_implies_local A star K S p represented,
      representedAt_all_ancestors A star K injective commute integralInjective S p represented⟩
  · rintro ⟨admissible, represented⟩
    exact representedAt_of_local A star K injective commute S p admissible represented

end IntegralLift

section LocalCover

variable {s : Fin 3 → Word} (A : G →+ G)
  (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
  (injective : Function.Injective A)
  (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
  (tiles : TileEquation s A star K)

include injective commute tiles

theorem overlap_mem_piece_of_local (p : Packet)
    (admissible : LocalAdmissible s A star K p) {x : G} (hx : x ∈ overlap star K p) :
    ∃ u, ∃ e : InverseOccurrence s p u, x ∈ piece A star K e := by
  obtain ⟨d, hd⟩ := overlap_mem_pairPiece A star K tiles p hx
  obtain ⟨y, hy⟩ := admissible d ⟨x, hd⟩
  refine ⟨pairTarget d y, pairLift d y hy, ?_⟩
  rw [← pairPiece_eq_piece A star K injective commute d y hy]
  exact hd

/-- Integral cover needs only admissibility at this source, with no global
range-reflection assumption and no injectivity of integral incidence. -/
theorem overlap_eq_iUnion_inverse_of_local (p : Packet)
    (admissible : LocalAdmissible s A star K p) :
    overlap star K p = ⋃ u, ⋃ e : InverseOccurrence s p u, piece A star K e := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, e, he⟩ := overlap_mem_piece_of_local A star K injective commute tiles p admissible hx
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨e, he⟩⟩
  · intro hx
    obtain ⟨u, he⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp he
    exact piece_subset_overlap A star K injective commute tiles e he

theorem overlap_mem_piece_of_represented (S : Finset Packet) (p : Packet)
    (represented : RepresentedAt s A star K S p) {x : G} (hx : x ∈ overlap star K p) :
    ∃ u, ∃ _hu : u ∈ S, ∃ e : InverseOccurrence s p u, x ∈ piece A star K e := by
  obtain ⟨d, hd⟩ := overlap_mem_pairPiece A star K tiles p hx
  obtain ⟨y, hy, hS⟩ := represented d ⟨x, hd⟩
  refine ⟨pairTarget d y, hS, pairLift d y hy, ?_⟩
  rw [← pairPiece_eq_piece A star K injective commute d y hy]
  exact hd

theorem overlap_eq_restricted_of_representedAt (S : Finset Packet) (p : Packet)
    (represented : RepresentedAt s A star K S p) :
    overlap star K p = restrictedUnion s A star K S p := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (mem_restrictedUnion A star K S p x).mpr
      (overlap_mem_piece_of_represented A star K injective commute tiles S p represented hx)
  · exact restrictedUnion_subset A star K injective commute tiles S p

/-- An exact weaker criterion for retained SET coverage, including all raw
pairs. It requires neither global reflection nor local admissibility. -/
theorem overlap_eq_restricted_iff_all_pairs (S : Finset Packet) (p : Packet) :
    overlap star K p = restrictedUnion s A star K S p ↔
      ∀ d : SelectedPair s p, pairPiece A star K d ⊆ restrictedUnion s A star K S p :=
  overlap_eq_set_iff_pairPiece_subset A star K tiles p _
    (restrictedUnion_subset A star K injective commute tiles S p)

/-- Representability is used at every intermediate source, so iteration
does not silently assume a global lifting condition. -/
theorem overlap_mem_historyWithin_of_representedAt (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt s A star K S p)
    (n : ℕ) (p : Packet) (hp : p ∈ S) {x : G} (hx : x ∈ overlap star K p) :
    ∃ h : History s n p,
      historyWithin s S n p h ∧ x ∈ historyPiece s A star K n p h := by
  induction n generalizing p x with
  | zero => exact ⟨(), trivial, hx⟩
  | succ n ih =>
      obtain ⟨u, hu, e, y, hy, hyx⟩ :=
        overlap_mem_piece_of_represented A star K injective commute tiles S p (represented p hp) hx
      obtain ⟨h, hw, hh⟩ := ih u hu hy
      exact ⟨⟨⟨u, e⟩, h⟩, ⟨hu, hw⟩, y, hh, hyx⟩

/-- Finite-depth retained cover. Its index is finite by
`finite_restrictedHistory`, including for singular integral incidence. -/
theorem overlap_eq_iUnion_restrictedHistory_of_representedAt (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt s A star K S p)
    (n : ℕ) (p : Packet) (hp : p ∈ S) :
    overlap star K p =
      ⋃ h : {h : History s n p // historyWithin s S n p h},
        historyPiece s A star K n p h.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨h, hw, hh⟩ := overlap_mem_historyWithin_of_representedAt
      A star K injective commute tiles S represented n p hp hx
    exact Set.mem_iUnion.mpr ⟨⟨h, hw⟩, hh⟩
  · intro hx
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hx
    exact historyPiece_subset A star K injective commute tiles n p h.val hh

end LocalCover

/-- Surjective integral incidence is sufficient for global reflection,
independently of the ambient action and star map. -/
theorem reflectsIntegralRange_of_integral_surjective {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (surjective : Function.Surjective (fun y => incidenceZ s *ᵥ y)) :
    ReflectsIntegralRange s A star := by
  intro z _
  exact surjective z

/-- With a surjective ambient action, global range reflection forces
surjectivity of the integral incidence action. No faithfulness of star is used. -/
theorem integral_surjective_of_reflects {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (surjective : Function.Surjective A) (reflects : ReflectsIntegralRange s A star) :
    Function.Surjective (fun y => incidenceZ s *ᵥ y) := by
  intro z
  exact reflects z (surjective (star z))

theorem reflectsIntegralRange_iff_integral_surjective {s : Fin 3 → Word}
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (surjective : Function.Surjective A) :
    ReflectsIntegralRange s A star ↔ Function.Surjective (fun y => incidenceZ s *ᵥ y) :=
  ⟨integral_surjective_of_reflects A star surjective,
    reflectsIntegralRange_of_integral_surjective A star⟩

section ProjectedProfiles

variable {R : Type*} [AddCommGroup R]
  {s : Fin 3 → Word} (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
  (K : Fin 3 → Set G) (rho : G →+ R) (B : R →+ R) (C : Fin 3 → Set R)
  (compatible : ∀ x, rho (A x) = B (rho x))
  (enclosed : ∀ a, rho '' K a ⊆ C a)

include compatible enclosed

/-- A proved profile enclosure and commuting action transport every actual
paired point into the projected paired profile. The target need not be finite. -/
theorem image_pairPiece_subset {p : Packet} (d : SelectedPair s p) :
    rho '' pairPiece A star K d ⊆ pairPiece B (rho.comp star) C d := by
  rintro _ ⟨x, ⟨⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩, rfl⟩
  refine ⟨⟨rho u, enclosed d.val.1.1 ⟨u, hu, rfl⟩, ?_⟩,
    ⟨rho v, enclosed d.val.2.1 ⟨v, hv, rfl⟩, ?_⟩⟩
  · have h := congrArg rho hux
    simpa only [affine, map_add, compatible, AddMonoidHom.comp_apply] using h
  · have h := congrArg rho hvx
    simpa only [affine, map_add, compatible, AddMonoidHom.comp_apply] using h

/-- Empty outer profiles soundly exclude an actual paired piece; nonempty
profiles do not certify an actual intersection. -/
theorem pairPiece_empty_of_projected_empty {p : Packet} (d : SelectedPair s p)
    (excluded : pairPiece B (rho.comp star) C d = ∅) : pairPiece A star K d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hp := image_pairPiece_subset A star K rho B C compatible enclosed d ⟨x, hx, rfl⟩
  rw [excluded] at hp
  exact hp

/-- Certified projected exclusions for all nonintegral pairs imply local
admissibility. A finite profile check cannot supply the enclosure premise.
For a full characteristic-zero field product, a nontrivial finite residue
map requires a separately authenticated support module or other carrier. -/
theorem localAdmissible_of_projected_exclusions (p : Packet)
    (excluded : ∀ d : SelectedPair s p, (¬ ∃ y, incidenceZ s *ᵥ y = pairRhs d) →
      pairPiece B (rho.comp star) C d = ∅) : LocalAdmissible s A star K p := by
  apply (localAdmissible_iff_nonintegral_empty A star K p).mpr
  intro d nonintegral
  exact pairPiece_empty_of_projected_empty A star K rho B C compatible enclosed d
    (excluded d nonintegral)

/-- The same authenticated profile test can justify finite-domain
exclusions. It must cover every pair with no retained integral lift. -/
theorem representedAt_of_projected_exclusions (S : Finset Packet) (p : Packet)
    (excluded : ∀ d : SelectedPair s p,
      (¬ ∃ y, incidenceZ s *ᵥ y = pairRhs d ∧ pairTarget d y ∈ S) →
        pairPiece B (rho.comp star) C d = ∅) : RepresentedAt s A star K S p := by
  apply (representedAt_iff_unrepresented_empty A star K S p).mpr
  intro d missing
  exact pairPiece_empty_of_projected_empty A star K rho B C compatible enclosed d
    (excluded d missing)

end ProjectedProfiles

section Compactness

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- Compactness of every raw paired set follows from compact tiles and
continuous action. It does not imply any integral lifting or positivity. -/
theorem isCompact_pairPiece {s : Fin 3 → Word} (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (continuousA : Continuous A) (compactTiles : ∀ a, IsCompact (K a))
    {p : Packet} (d : SelectedPair s p) : IsCompact (pairPiece A star K d) := by
  exact ((compactTiles d.val.1.1).image (continuousA.add continuous_const)).inter
    ((compactTiles d.val.2.1).image (continuousA.add continuous_const))

end Compactness

end Psc.OccurrenceAdmissibility
