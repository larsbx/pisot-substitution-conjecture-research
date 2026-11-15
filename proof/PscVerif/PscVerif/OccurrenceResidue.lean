import PscVerif.OccurrenceCover
import PscVerif.MadicResidue

/-!
# Literal residue profiles and the concrete matrix-adic cover bridge

The finite profile retains every literal digit before taking its set image.
The profile becomes an enclosure only from a supplied complete tile equation
and a proved annihilation of the action in the residue coordinate. Equality
requires nonempty contributing ancestor tiles. No set-support equality
identifies occurrence addresses or removes a counting multiplicity.

The ambient space is a product with the actual matrix-adic carrier. Its
first residue proves integral range reflection. Complete inverse covers
then follow from the supplied original literal tile equation. A block
profile uses an explicit complete block tile equation; authenticating
those tile sets and any finite packet restriction remains separate.

Pre-code gate: `docs/c4-madic-residue-literature-2026-11-11.md`.
-/

namespace Psc.OccurrenceResidue

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceInverse
open Psc.OccurrencePiece Psc.OccurrenceCover Matrix

variable {G R : Type*} [AddCommGroup G] [AddCommGroup R]

/-- The full incoming literal index, before projecting any prefix. -/
abbrev IncomingDigit (s : Fin 3 → Word) (c : Fin 3) :=
  {d : Digit s // d.2.letter = c}

/-- A set support is the image of the complete literal inventory. It does
not replace that inventory when counting repeated occurrences. -/
def digitProfile (s : Fin 3 → Word) (rstar : (Fin 3 → ℤ) →+ R)
    (c : Fin 3) : Set R :=
  Set.range (fun d : IncomingDigit s c => rstar (parikhZ d.val.2.before))

theorem finite_incomingDigit (s : Fin 3 → Word) (c : Fin 3) :
    Finite (IncomingDigit s c) := by
  let := digitFintype s
  infer_instance

theorem finite_digitProfile (s : Fin 3 → Word)
    (rstar : (Fin 3 → ℤ) →+ R) (c : Fin 3) :
    (digitProfile s rstar c).Finite := by
  let := finite_incomingDigit s c
  exact Set.finite_range _

/-- Complete tile equations and residue-annihilation give a profile bound.
No compactness, nonemptiness, or injectivity assumption is needed. -/
theorem image_tile_subset_digitProfile (s : Fin 3 → Word)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (rho : G →+ R) (tiles : TileEquation s A star K)
    (annihilates : ∀ x, rho (A x) = 0) (c : Fin 3) :
    rho '' K c ⊆ digitProfile s (rho.comp star) c := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, d, hd, y, hy, he⟩ := (tiles c x).mp hx
  refine Set.mem_range.mpr ⟨⟨⟨a, d⟩, hd⟩, ?_⟩
  have h := congrArg rho he
  simpa only [map_add, annihilates, zero_add, AddMonoidHom.comp_apply] using h

/-- Every listed digit is attained if each contributing ancestor is
nonempty. This extra premise is not inferred from a finite word table. -/
theorem digitProfile_subset_image_tile (s : Fin 3 → Word)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (rho : G →+ R) (tiles : TileEquation s A star K)
    (annihilates : ∀ x, rho (A x) = 0) (c : Fin 3)
    (nonempty : ∀ d : IncomingDigit s c, (K d.val.1).Nonempty) :
    digitProfile s (rho.comp star) c ⊆ rho '' K c := by
  rintro _ ⟨d, rfl⟩
  obtain ⟨y, hy⟩ := nonempty d
  refine ⟨A y + star (parikhZ d.val.2.before), ?_, ?_⟩
  · exact (tiles c _).mpr ⟨d.val.1, d.val.2, d.property, y, hy, rfl⟩
  · simp only [map_add, annihilates, zero_add, AddMonoidHom.comp_apply]

theorem image_tile_eq_digitProfile (s : Fin 3 → Word)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (rho : G →+ R) (tiles : TileEquation s A star K)
    (annihilates : ∀ x, rho (A x) = 0) (c : Fin 3)
    (nonempty : ∀ d : IncomingDigit s c, (K d.val.1).Nonempty) :
    rho '' K c = digitProfile s (rho.comp star) c :=
  Set.Subset.antisymm (image_tile_subset_digitProfile s A star K rho tiles annihilates c)
    (digitProfile_subset_image_tile s A star K rho tiles annihilates c nonempty)

/-- Separation of authenticated residue supports excludes an actual
overlap. Intersecting outer profiles are only inconclusive. -/
theorem overlap_empty_of_profile_separation
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (rho : G →+ R) (F : Fin 3 → Set R)
    (enclosed : ∀ c, rho '' K c ⊆ F c) (p : Packet)
    (separated : ∀ r ∈ F p.top, r - rho (star p.delta) ∉ F p.bottom) :
    overlap star K p = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply separated (rho x) (enclosed p.top ⟨x, hx.1, rfl⟩)
  have h := enclosed p.bottom ⟨x - star p.delta, hx.2, rfl⟩
  simpa only [map_sub] using h

/-- A full literal tile equation alone cannot turn the profile enclosure
into equality: empty tiles satisfy that equation, while any supplied
actual incoming digit gives a nonempty profile. -/
theorem empty_tiles_profile_control (s : Fin 3 → Word)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (rho : G →+ R)
    (c : Fin 3) (d : IncomingDigit s c) :
    TileEquation s A star (fun _ => ∅) ∧
      rho '' (∅ : Set G) ≠ digitProfile s (rho.comp star) c := by
  constructor
  · simp [TileEquation]
  · intro h
    have hd : (rho.comp star) (parikhZ d.val.2.before) ∈
        digitProfile s (rho.comp star) c := Set.mem_range.mpr ⟨d, rfl⟩
    rw [← h] at hd
    obtain ⟨x, hx, _⟩ := hd
    exact hx

section ConcreteCarrier

variable {E : Type*} [AddCommGroup E]

/-- The column action of the actual substitution incidence matrix. -/
def incidenceLinear (s : Fin 3 → Word) : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) :=
  (incidenceZ s).mulVecLin

@[simp]
theorem incidenceLinear_apply (s : Fin 3 → Word) (z : Fin 3 → ℤ) :
    incidenceLinear s z = incidenceZ s *ᵥ z := rfl

/-- The powered quotient lattice agrees with the incidence of the actual
iterated words, rather than merely a supplied matrix label. -/
theorem incidenceLinear_iterateImages (s : Fin 3 → Word) (q : ℕ) :
    incidenceLinear (iterateImages s q) = incidenceLinear s ^ q := by
  unfold incidenceLinear
  rw [incidenceZ_iterateImages]
  exact Matrix.toLin'_pow (incidenceZ s) q

/-- An arbitrary additional additive factor paired with the actual integral
matrix-adic carrier. No completion-field or tile identification is assumed. -/
abbrev Ambient (s : Fin 3 → Word) (E : Type*) :=
  E × MadicResidue.Carrier (incidenceLinear s)

def ambientAction (s : Fin 3 → Word) (B : E →+ E) :
    AddMonoid.End (Ambient s E) :=
  B.prodMap (MadicResidue.action (incidenceLinear s)).toAddMonoidHom

def ambientStar (s : Fin 3 → Word) (pi : (Fin 3 → ℤ) →+ E) :
    (Fin 3 → ℤ) →+ Ambient s E :=
  pi.prod (MadicResidue.star (incidenceLinear s)).toAddMonoidHom

/-- The quotient coordinate ignores the additional factor. -/
def residue (s : Fin 3 → Word) (q : ℕ) :
    Ambient s E →+ MadicResidue.Residue (incidenceLinear s) q :=
  (MadicResidue.eval (incidenceLinear s) q).toAddMonoidHom.comp
    (AddMonoidHom.snd E (MadicResidue.Carrier (incidenceLinear s)))

@[simp]
theorem ambientAction_apply (s : Fin 3 → Word) (B : E →+ E) (x : Ambient s E) :
    ambientAction s B x = (B x.1, MadicResidue.action (incidenceLinear s) x.2) := rfl

@[simp]
theorem ambientStar_apply (s : Fin 3 → Word) (pi : (Fin 3 → ℤ) →+ E)
    (z : Fin 3 → ℤ) :
    ambientStar s pi z = (pi z, MadicResidue.star (incidenceLinear s) z) := rfl

@[simp]
theorem residue_apply (s : Fin 3 → Word) (q : ℕ) (x : Ambient s E) :
    residue s q x = MadicResidue.eval (incidenceLinear s) q x.2 := rfl

@[simp]
theorem residue_ambientStar (s : Fin 3 → Word) (q : ℕ)
    (pi : (Fin 3 → ℤ) →+ E) (z : Fin 3 → ℤ) :
    residue s q (ambientStar s pi z) = MadicResidue.quotient (incidenceLinear s) q z := rfl

theorem residue_comp_ambientStar (s : Fin 3 → Word) (q : ℕ)
    (pi : (Fin 3 → ℤ) →+ E) :
    (residue s q).comp (ambientStar s pi) =
      (MadicResidue.quotient (incidenceLinear s) q).toAddMonoidHom := by
  ext z
  rfl

theorem residue_ambientAction (s : Fin 3 → Word) (q : ℕ)
    (B : E →+ E) (x : Ambient s E) :
    residue s q (ambientAction s B x) =
      MadicResidue.residueAction (incidenceLinear s) q (residue s q x) := rfl

theorem ambientAction_pow_snd (s : Fin 3 → Word) (B : E →+ E)
    (n : ℕ) (x : Ambient s E) :
    ((ambientAction s B ^ n) x).2 =
      (MadicResidue.action (incidenceLinear s) ^ n) x.2 := by
  simp only [AddMonoid.End.coe_pow, Module.End.pow_apply]
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Function.iterate_succ_apply', ambientAction_apply] using
        congrArg (MadicResidue.action (incidenceLinear s)) ih

/-- The finite block coordinate kills the corresponding powered action,
regardless of the dynamics on the additional factor. -/
theorem residue_ambientAction_pow_self_zero (s : Fin 3 → Word)
    (B : E →+ E) (q : ℕ) (x : Ambient s E) :
    residue s q ((ambientAction s B ^ q) x) = 0 := by
  rw [residue_apply, ambientAction_pow_snd]
  exact MadicResidue.eval_action_pow_self_zero (incidenceLinear s) q x.2

theorem residue_one_ambientAction (s : Fin 3 → Word)
    (B : E →+ E) (x : Ambient s E) :
    residue s 1 (ambientAction s B x) = 0 :=
  MadicResidue.eval_one_action (incidenceLinear s) x.2

theorem residue_one_ambientStar_eq_zero_iff (s : Fin 3 → Word)
    (pi : (Fin 3 → ℤ) →+ E) (z : Fin 3 → ℤ) :
    residue s 1 (ambientStar s pi z) = 0 ↔ ∃ y, incidenceZ s *ᵥ y = z :=
  MadicResidue.eval_one_star_eq_zero_iff (incidenceLinear s) z

theorem ambient_commute (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z)) (z : Fin 3 → ℤ) :
    ambientAction s B (ambientStar s pi z) = ambientStar s pi (incidenceZ s *ᵥ z) := by
  apply Prod.ext
  · exact commute z
  · exact MadicResidue.action_star (incidenceLinear s) z

theorem ambientAction_injective (s : Fin 3 → Word) (B : E →+ E)
    (injectiveB : Function.Injective B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z)) :
    Function.Injective (ambientAction s B) := by
  intro x y h
  apply Prod.ext
  · exact injectiveB (congrArg Prod.fst h)
  · exact MadicResidue.action_injective (incidenceLinear s) integralInjective
      (congrArg Prod.snd h)

/-- Range reflection is discharged by the constructed first coordinate.
It needs no tile, finite packet, compactness, or injectivity premise. -/
theorem ambient_reflectsIntegralRange (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) :
    ReflectsIntegralRange s (ambientAction s B) (ambientStar s pi) :=
  reflectsIntegralRange_of_residue (ambientAction s B) (ambientStar s pi)
    (residue s 1) (residue_one_ambientAction s B)
    (fun z => (residue_one_ambientStar_eq_zero_iff s pi z).mp)

/-- Commutation also supplies the converse integral lifting implication. -/
theorem ambient_preimage_star_iff (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z)) (z : Fin 3 → ℤ) :
    (∃ x, ambientAction s B x = ambientStar s pi z) ↔
      ∃ y, incidenceZ s *ᵥ y = z := by
  constructor
  · exact ambient_reflectsIntegralRange s B pi z
  · rintro ⟨y, rfl⟩
    exact ⟨ambientStar s pi y, ambient_commute s B pi commute y⟩

/-- All actual incoming occurrences cover the overlap in the constructed
ambient carrier once the original literal tile equation is supplied. -/
theorem ambient_overlap_eq_iUnion_inverse (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E))
    (injectiveB : Function.Injective B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (tiles : TileEquation s (ambientAction s B) (ambientStar s pi) K) (p : Packet) :
    overlap (ambientStar s pi) K p = ⋃ u, ⋃ e : InverseOccurrence s p u,
      affine (ambientAction s B) (ambientStar s pi (parikhZ e.topMark.before)) ''
        overlap (ambientStar s pi) K u :=
  overlap_eq_iUnion_inverse (ambientAction s B) (ambientStar s pi) K
    (ambientAction_injective s B injectiveB integralInjective)
    (ambient_commute s B pi commute) (ambient_reflectsIntegralRange s B pi) tiles p

/-- The original one-step equation covers all finite-depth histories with
their literal marks retained. No selected finite graph is presumed complete. -/
theorem ambient_overlap_eq_iUnion_history (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E))
    (injectiveB : Function.Injective B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (tiles : TileEquation s (ambientAction s B) (ambientStar s pi) K)
    (n : ℕ) (p : Packet) :
    overlap (ambientStar s pi) K p = ⋃ h : History s n p,
      historyPiece s (ambientAction s B) (ambientStar s pi) K n p h :=
  overlap_eq_iUnion_history (ambientAction s B) (ambientStar s pi) K
    (ambientAction_injective s B injectiveB integralInjective)
    (ambient_commute s B pi commute) tiles (ambient_reflectsIntegralRange s B pi) n p

/-- The same exact cover has the existing a priori finite literal-history
budget. This makes no bound on the union of ancestor states over all depths. -/
theorem ambient_finite_history_cover (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E))
    (injectiveB : Function.Injective B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (tiles : TileEquation s (ambientAction s B) (ambientStar s pi) K)
    (n : ℕ) (p : Packet) :
    Finite (History s n p) ∧
      Nat.card (History s n p) ≤ ((∑ a, (s a).length) ^ 2) ^ n ∧
      overlap (ambientStar s pi) K p = ⋃ h : History s n p,
        historyPiece s (ambientAction s B) (ambientStar s pi) K n p h :=
  ⟨finite_history s integralInjective n p, history_card_le s integralInjective n p,
    ambient_overlap_eq_iUnion_history s B pi K injectiveB integralInjective commute tiles n p⟩

/-- Restricting the constructed cover still requires representation of
every nonempty incoming ancestor at every represented intermediate source. -/
theorem ambient_overlap_eq_iUnion_restrictedHistory (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E))
    (injectiveB : Function.Injective B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (tiles : TileEquation s (ambientAction s B) (ambientStar s pi) K)
    (S : Finset Packet)
    (represented : ∀ p ∈ S, ∀ u, InverseOccurrence s p u →
      (overlap (ambientStar s pi) K u).Nonempty → u ∈ S)
    (n : ℕ) (p : Packet) (hp : p ∈ S) :
    overlap (ambientStar s pi) K p =
      ⋃ h : {h : History s n p // historyWithin s S n p h},
        historyPiece s (ambientAction s B) (ambientStar s pi) K n p h.val :=
  overlap_eq_iUnion_restrictedHistory (ambientAction s B) (ambientStar s pi) K
    (ambientAction_injective s B injectiveB integralInjective)
    (ambient_commute s B pi commute) tiles (ambient_reflectsIntegralRange s B pi)
    S represented n p hp

/-- The support of all actual depth-`q` prefix occurrences, in the exact
quotient by the depth-`q` image lattice. The digit inventory remains separate. -/
def blockProfile (s : Fin 3 → Word) (q : ℕ) (c : Fin 3) :
    Set (MadicResidue.Residue (incidenceLinear s) q) :=
  digitProfile (iterateImages s q)
    (MadicResidue.quotient (incidenceLinear s) q).toAddMonoidHom c

theorem finite_blockProfile (s : Fin 3 → Word) (q : ℕ) (c : Fin 3) :
    (blockProfile s q c).Finite :=
  finite_digitProfile (iterateImages s q)
    (MadicResidue.quotient (incidenceLinear s) q).toAddMonoidHom c

/-- A complete literal block equation authenticates the finite profile as
an outer support. The block equation is an explicit geometric premise. -/
theorem image_tile_subset_blockProfile (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E)) (q : ℕ)
    (tiles : TileEquation (iterateImages s q) (ambientAction s B ^ q)
      (ambientStar s pi) K) (c : Fin 3) :
    residue s q '' K c ⊆ blockProfile s q c := by
  simpa only [residue_comp_ambientStar, blockProfile] using
    image_tile_subset_digitProfile (iterateImages s q) (ambientAction s B ^ q)
      (ambientStar s pi) K (residue s q) tiles
      (residue_ambientAction_pow_self_zero s B q) c

/-- Equality of the profile needs nonempty contributing ancestor tiles. -/
theorem image_tile_eq_blockProfile (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E)) (q : ℕ)
    (tiles : TileEquation (iterateImages s q) (ambientAction s B ^ q)
      (ambientStar s pi) K) (c : Fin 3)
    (nonempty : ∀ d : IncomingDigit (iterateImages s q) c, (K d.val.1).Nonempty) :
    residue s q '' K c = blockProfile s q c := by
  simpa only [residue_comp_ambientStar, blockProfile] using
    image_tile_eq_digitProfile (iterateImages s q) (ambientAction s B ^ q)
      (ambientStar s pi) K (residue s q) tiles
      (residue_ambientAction_pow_self_zero s B q) c nonempty

/-- Separation of complete block profiles soundly excludes an actual
overlap under the displayed block tile equation. A failed separation test
does not establish a nonempty overlap or positive measure. -/
theorem overlap_empty_of_blockProfile_separation (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E)) (q : ℕ)
    (tiles : TileEquation (iterateImages s q) (ambientAction s B ^ q)
      (ambientStar s pi) K) (p : Packet)
    (separated : ∀ r ∈ blockProfile s q p.top,
      r - MadicResidue.quotient (incidenceLinear s) q p.delta ∉ blockProfile s q p.bottom) :
    overlap (ambientStar s pi) K p = ∅ :=
  overlap_empty_of_profile_separation (ambientStar s pi) K (residue s q)
    (blockProfile s q) (image_tile_subset_blockProfile s B pi K q tiles) p separated

/-- The profile-equality obstruction persists in the actual carrier even
with its proved block annihilation. A digit witness is required, so this
does not incorrectly assert a nonempty profile for an erased image. -/
theorem empty_tiles_blockProfile_control (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (q : ℕ) (c : Fin 3)
    (d : IncomingDigit (iterateImages s q) c) :
    TileEquation (iterateImages s q) (ambientAction s B ^ q)
        (ambientStar s pi) (fun _ => ∅) ∧
      (∀ x, residue s q ((ambientAction s B ^ q) x) = 0) ∧
      residue s q '' (∅ : Set (Ambient s E)) ≠ blockProfile s q c := by
  obtain ⟨ht, hn⟩ := empty_tiles_profile_control (iterateImages s q)
    (ambientAction s B ^ q) (ambientStar s pi) (residue s q) c d
  refine ⟨ht, residue_ambientAction_pow_self_zero s B q, ?_⟩
  simpa only [residue_comp_ambientStar, blockProfile] using hn

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]

omit [IsTopologicalAddGroup E] [T2Space E] in
theorem continuous_ambientAction (s : Fin 3 → Word) (B : E →+ E)
    (continuousB : Continuous B) : Continuous (ambientAction s B) :=
  (continuousB.comp continuous_fst).prodMk
    ((MadicResidue.continuous_action (incidenceLinear s)).comp continuous_snd)

/-- Compact history pieces require actual compact tiles. Compactness of
the matrix-adic factor alone does not supply that premise. -/
theorem isCompact_ambient_historyPiece (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (K : Fin 3 → Set (Ambient s E))
    (continuousB : Continuous B) (compactTiles : ∀ a, IsCompact (K a))
    (n : ℕ) (p : Packet) (h : History s n p) :
    IsCompact (historyPiece s (ambientAction s B) (ambientStar s pi) K n p h) :=
  isCompact_historyPiece s (ambientAction s B) (ambientStar s pi) K
    (continuous_ambientAction s B continuousB) compactTiles n p h

end Topology
end ConcreteCarrier

end Psc.OccurrenceResidue
