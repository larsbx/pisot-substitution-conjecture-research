import PscVerif.PrefixAddress
import PscVerif.OccurrenceResidue

/-!
# Literal prefix closures and their occurrence equation

The sets here are defined from all actual positions of a supplied infinite
word. Exact addressing proves their raw occurrence equation. Continuity and
closedness of the action then prove the equation for their closures, using
the finite full-digit index. No abstract attractor is substituted for these
sets.

The actual matrix-adic product supplies a closed action under the stated
additional-factor hypothesis. A word fixed at a block scale stays at that
scale, using the original carrier's corresponding residue coordinate.
Compactness still requires an explicit compact stable-coordinate window;
no authentic Pisot projection, bound, Haar scaling, or positivity is claimed.
Pre-code gate: `docs/c4-prefix-closure-literature-2026-11-11.md`.
-/

namespace Psc.PrefixClosure

open Psc.Binomial Psc.PrefixAddress Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceInverse Psc.OccurrencePiece Psc.OccurrenceCover
open Psc.OccurrenceResidue Matrix

variable {G : Type*} [AddCommGroup G]

/-- All actual prefix points whose next letter is `c`. Projection may
identify points; the literal address equivalence remains separate. -/
def raw (w : ℕ → Fin 3) (star : (Fin 3 → ℤ) →+ G) (c : Fin 3) : Set G :=
  {x | ∃ n, w n = c ∧ star (parikhZ (wordPrefix w n)) = x}

theorem raw_point_mem (w : ℕ → Fin 3) (star : (Fin 3 → ℤ) →+ G) (n : ℕ) :
    star (parikhZ (wordPrefix w n)) ∈ raw w star (w n) := ⟨n, rfl, rfl⟩

theorem raw_origin_mem (w : ℕ → Fin 3) (star : (Fin 3 → ℤ) →+ G) :
    (0 : G) ∈ raw w star (w 0) := by
  refine ⟨0, rfl, ?_⟩
  rw [prefix_zero]
  have hz : parikhZ [] = 0 := by ext a; simp [parikhZ]
  rw [hz, map_zero]

theorem raw_affine_point (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) (fixed : FixedPrefix τ w)
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z)) (e : Address τ w) :
    affine A (star (parikhZ e.2.before)) (star (parikhZ (wordPrefix w e.1))) =
      star (parikhZ (wordPrefix w (childIndex τ w e))) := by
  rw [affine, commute, parikhZ_prefix_childIndex τ w fixed, map_add]

/-- The raw equation is proved from every actual occurrence. It needs no
topology, injectivity, compactness, primitivity, or Pisot hypothesis. -/
theorem raw_tileEquation (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (fixed : FixedPrefix τ w) (cofinal : CofinalImages τ w)
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z)) :
    TileEquation τ A star (raw w star) := by
  intro c x
  constructor
  · rintro ⟨n, hc, rfl⟩
    obtain ⟨e, he⟩ := childIndex_surjective τ w cofinal n
    refine ⟨w e.1, e.2, ?_, star (parikhZ (wordPrefix w e.1)), raw_point_mem w star e.1, ?_⟩
    · have hl := letter_childIndex τ w fixed e
      rw [he] at hl
      exact hl.symm.trans hc
    · simpa only [he, affine] using raw_affine_point τ w A star fixed commute e
  · rintro ⟨a, d, hd, y, ⟨i, hi, rfl⟩, rfl⟩
    subst a
    refine ⟨childIndex τ w ⟨i, d⟩, (letter_childIndex τ w fixed ⟨i, d⟩).trans hd, ?_⟩
    exact (raw_affine_point τ w A star fixed commute ⟨i, d⟩).symm

/-- The finite full-mark form of the original literal equation. -/
theorem tileEquation_iff_iUnion (τ : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G) :
    TileEquation τ A star K ↔ ∀ c,
      K c = ⋃ d : IncomingDigit τ c,
        affine A (star (parikhZ d.val.2.before)) '' K d.val.1 := by
  constructor
  · intro tiles c
    ext x
    constructor
    · intro hx
      obtain ⟨a, d, hd, y, hy, he⟩ := (tiles c x).mp hx
      exact Set.mem_iUnion.mpr ⟨⟨⟨a, d⟩, hd⟩, y, hy, he⟩
    · intro hx
      obtain ⟨d, y, hy, he⟩ := Set.mem_iUnion.mp hx
      exact (tiles c x).mpr ⟨d.val.1, d.val.2, d.property, y, hy, he⟩
  · intro unions c x
    rw [unions c]
    constructor
    · intro hx
      obtain ⟨d, y, hy, he⟩ := Set.mem_iUnion.mp hx
      exact ⟨d.val.1, d.val.2, d.property, y, hy, he⟩
    · rintro ⟨a, d, hd, y, hy, he⟩
      exact Set.mem_iUnion.mpr ⟨⟨⟨a, d⟩, hd⟩, y, hy, he⟩

/-- Dropping cofinality fails even though the erasing fixed-prefix
identity holds: the actual raw origin has no incoming mark at all. -/
theorem erasing_not_raw_tileEquation (A : G →+ G) (star : (Fin 3 → ℤ) →+ G) :
    ¬ TileEquation (fun _ : Fin 3 => []) A star
      (raw (fun _ : ℕ => (0 : Fin 3)) star) := by
  intro tiles
  obtain ⟨a, d, _⟩ := (tiles 0 0).mp (raw_origin_mem (fun _ => 0) star)
  exact Nat.not_lt_zero _ d.index_lt

section Closures

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- The defined closure of the actual prefix points. -/
def prefixTiles (w : ℕ → Fin 3) (star : (Fin 3 → ℤ) →+ G) (c : Fin 3) : Set G :=
  closure (raw w star c)

/-- Taking closures preserves the literal equation because the incoming
index is finite and every affine branch is continuous and closed. -/
theorem closure_tileEquation (τ : Fin 3 → Word) (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (tiles : TileEquation τ A star K)
    (continuousA : Continuous A) (closedA : IsClosedMap A) :
    TileEquation τ A star (fun c => closure (K c)) := by
  apply (tileEquation_iff_iUnion τ A star _).mpr
  intro c
  let : Finite (IncomingDigit τ c) := finite_incomingDigit τ c
  rw [(tileEquation_iff_iUnion τ A star K).mp tiles c, closure_iUnion_of_finite]
  congr 1
  funext d
  have hc : IsClosedMap (affine A (star (parikhZ d.val.2.before))) :=
    (isClosedMap_add_right _).comp closedA
  exact hc.closure_image_eq_of_continuous (continuousA.add continuous_const) _

/-- The tile equation is now a theorem about the defined prefix closures,
rather than a premise supplied for an arbitrary family. -/
theorem prefixTiles_tileEquation (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (fixed : FixedPrefix τ w) (cofinal : CofinalImages τ w)
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z))
    (continuousA : Continuous A) (closedA : IsClosedMap A) :
    TileEquation τ A star (prefixTiles w star) :=
  closure_tileEquation τ A star (raw w star)
    (raw_tileEquation τ w A star fixed cofinal commute) continuousA closedA

theorem prefixTiles_tileEquation_of_nonerasing (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (fixed : FixedPrefix τ w) (nonerasing : ∀ a, τ a ≠ [])
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z))
    (continuousA : Continuous A) (closedA : IsClosedMap A) :
    TileEquation τ A star (prefixTiles w star) :=
  prefixTiles_tileEquation τ w A star fixed
    (cofinalImages_of_nonerasing τ w nonerasing) commute continuousA closedA

omit [IsTopologicalAddGroup G] in
/-- A concrete letter occurrence, rather than the prefix equation alone,
supplies nonemptiness of its prefix closure. -/
theorem prefixTiles_nonempty (w : ℕ → Fin 3) (star : (Fin 3 → ℤ) →+ G)
    (c : Fin 3) (n : ℕ) (occurs : w n = c) : (prefixTiles w star c).Nonempty :=
  ⟨star (parikhZ (wordPrefix w n)), subset_closure ⟨n, occurs, rfl⟩⟩

theorem seed_prefixTiles_tileEquation (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length)
    (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z))
    (continuousA : Continuous A) (closedA : IsClosedMap A) :
    TileEquation τ A star (prefixTiles (seedWord τ u nonerasing prolongable grows) star) :=
  prefixTiles_tileEquation τ _ A star
    (seedWord_fixedPrefix τ u nonerasing prolongable grows)
    (seedWord_cofinalImages τ u nonerasing prolongable grows) commute continuousA closedA

omit [IsTopologicalAddGroup G] in
theorem erasing_not_prefixTiles_tileEquation (A : G →+ G)
    (star : (Fin 3 → ℤ) →+ G) :
    ¬ TileEquation (fun _ : Fin 3 => []) A star
      (prefixTiles (fun _ : ℕ => (0 : Fin 3)) star) := by
  intro tiles
  obtain ⟨a, d, _⟩ := (tiles 0 0).mp (subset_closure (raw_origin_mem (fun _ => 0) star))
  exact Nat.not_lt_zero _ d.index_lt

end Closures

section MatrixAdicProduct

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E]

/-- The actual matrix-adic action is closed, using its proved compact
carrier and injectivity; no quotient-completion identification is assumed. -/
theorem madic_action_isClosedEmbedding (s : Fin 3 → Word)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z)) :
    Topology.IsClosedEmbedding (MadicResidue.action (incidenceLinear s)) := by
  let : CompactSpace (MadicResidue.Carrier (incidenceLinear s)) :=
    MadicResidue.carrier_compactSpace (incidenceLinear s) integralInjective
  exact (MadicResidue.continuous_action (incidenceLinear s)).isClosedEmbedding
    (MadicResidue.action_injective (incidenceLinear s) integralInjective)

omit [IsTopologicalAddGroup E] [T2Space E] in
theorem ambientAction_isClosedEmbedding (s : Fin 3 → Word) (B : E →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z)) :
    Topology.IsClosedEmbedding (ambientAction s B) :=
  closedB.prodMap (madic_action_isClosedEmbedding s integralInjective)

/-- Closed embeddings remain closed embeddings at the explicitly chosen
block scale. -/
theorem closedEmbedding_pow {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    (A : AddMonoid.End X) (closedA : Topology.IsClosedEmbedding A) (k : ℕ) :
    Topology.IsClosedEmbedding (A ^ k) := by
  change Topology.IsClosedEmbedding ((A : X → X)^[k])
  induction k with
  | zero => exact Topology.IsClosedEmbedding.id
  | succ k ih =>
      simpa only [Function.iterate_succ'] using closedA.comp ih

omit [IsTopologicalAddGroup E] [T2Space E] in
theorem ambientAction_pow_isClosedEmbedding (s : Fin 3 → Word) (B : E →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z)) (k : ℕ) :
    Topology.IsClosedEmbedding (ambientAction s B ^ k) :=
  closedEmbedding_pow (ambientAction s B)
    (ambientAction_isClosedEmbedding s B closedB integralInjective) k

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] in
theorem ambientAction_pow_star (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z)) (k : ℕ) (z : Fin 3 → ℤ) :
    (ambientAction s B ^ k) (ambientStar s pi z) =
      ambientStar s pi ((incidenceLinear s ^ k) z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ']
      change ambientAction s B ((ambientAction s B ^ k) (ambientStar s pi z)) = _
      rw [ih, ambient_commute s B pi commute, pow_succ', Module.End.mul_apply]
      rfl

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] in
theorem ambient_block_commute (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z)) (k : ℕ) (z : Fin 3 → ℤ) :
    (ambientAction s B ^ k) (ambientStar s pi z) =
      ambientStar s pi (incidenceZ (iterateImages s k) *ᵥ z) := by
  change (ambientAction s B ^ k) (ambientStar s pi z) =
    ambientStar s pi (incidenceLinear (iterateImages s k) z)
  rw [incidenceLinear_iterateImages]
  exact ambientAction_pow_star s B pi commute k z

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] in
/-- Level `k` of the original carrier reflects the integral range of the
literal block incidence. No `H_(M^k)` isomorphism is required. -/
theorem ambient_block_reflectsIntegralRange (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E) (k : ℕ) :
    ReflectsIntegralRange (iterateImages s k) (ambientAction s B ^ k) (ambientStar s pi) := by
  apply reflectsIntegralRange_of_residue (ambientAction s B ^ k) (ambientStar s pi)
    (residue s k) (residue_ambientAction_pow_self_zero s B k)
  intro z hz
  obtain ⟨y, hy⟩ := (MadicResidue.quotient_eq_zero_iff (incidenceLinear s) k z).mp hz
  refine ⟨y, ?_⟩
  change incidenceLinear (iterateImages s k) y = z
  rw [incidenceLinear_iterateImages]
  exact hy

theorem block_integralInjective (s : Fin 3 → Word)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z)) (k : ℕ) :
    Function.Injective (fun z => incidenceZ (iterateImages s k) *ᵥ z) := by
  change Function.Injective (incidenceLinear (iterateImages s k))
  rw [incidenceLinear_iterateImages]
  exact Module.End.iterate_injective integralInjective k

omit [T2Space E] in
/-- The chosen word period remains in the statement. This is not an
inference of the original one-step equation from a power equation. -/
theorem ambient_prefixTiles_tileEquation (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (fixed : FixedPrefix (iterateImages s k) w)
    (cofinal : CofinalImages (iterateImages s k) w) :
    TileEquation (iterateImages s k) (ambientAction s B ^ k) (ambientStar s pi)
      (prefixTiles w (ambientStar s pi)) :=
  prefixTiles_tileEquation (iterateImages s k) w (ambientAction s B ^ k) (ambientStar s pi)
    fixed cofinal (ambient_block_commute s B pi commute k)
    (ambientAction_pow_isClosedEmbedding s B closedB integralInjective k).continuous
    (ambientAction_pow_isClosedEmbedding s B closedB integralInjective k).isClosedMap

omit [T2Space E] in
/-- Complete actual inverse occurrences cover the defined prefix overlap;
the tile equation has been derived from literal prefixes. -/
theorem ambient_prefix_overlap_cover (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (fixed : FixedPrefix (iterateImages s k) w)
    (cofinal : CofinalImages (iterateImages s k) w) (p : Packet) :
    overlap (ambientStar s pi) (prefixTiles w (ambientStar s pi)) p =
      ⋃ u, ⋃ e : InverseOccurrence (iterateImages s k) p u,
        affine (ambientAction s B ^ k) (ambientStar s pi (parikhZ e.topMark.before)) ''
          overlap (ambientStar s pi) (prefixTiles w (ambientStar s pi)) u :=
  overlap_eq_iUnion_inverse (ambientAction s B ^ k) (ambientStar s pi) _
    (ambientAction_pow_isClosedEmbedding s B closedB integralInjective k).injective
    (ambient_block_commute s B pi commute k) (ambient_block_reflectsIntegralRange s B pi k)
    (ambient_prefixTiles_tileEquation s k w B pi closedB integralInjective commute fixed cofinal) p

omit [T2Space E] in
/-- Every finite depth has a complete, finitely indexed literal history
cover with the stated budget. No finite global ancestor domain is asserted. -/
theorem ambient_prefix_finite_history_cover (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (fixed : FixedPrefix (iterateImages s k) w)
    (cofinal : CofinalImages (iterateImages s k) w) (n : ℕ) (p : Packet) :
    Finite (History (iterateImages s k) n p) ∧
      Nat.card (History (iterateImages s k) n p) ≤
        ((∑ a, (iterateImages s k a).length) ^ 2) ^ n ∧
      overlap (ambientStar s pi) (prefixTiles w (ambientStar s pi)) p =
        ⋃ h : History (iterateImages s k) n p,
          historyPiece (iterateImages s k) (ambientAction s B ^ k) (ambientStar s pi)
            (prefixTiles w (ambientStar s pi)) n p h := by
  refine ⟨finite_history _ (block_integralInjective s integralInjective k) n p,
    history_card_le _ (block_integralInjective s integralInjective k) n p, ?_⟩
  exact overlap_eq_iUnion_history (ambientAction s B ^ k) (ambientStar s pi) _
    (ambientAction_pow_isClosedEmbedding s B closedB integralInjective k).injective
    (ambient_block_commute s B pi commute k)
    (ambient_prefixTiles_tileEquation s k w B pi closedB integralInjective commute fixed cofinal)
    (ambient_block_reflectsIntegralRange s B pi k) n p

omit [IsTopologicalAddGroup E] in
/-- Compactness follows from an actual compact stable-coordinate window
containing every prefix projection, together with the proved compact factor. -/
theorem prefixTiles_compact_of_window (s : Fin 3 → Word) (w : ℕ → Fin 3)
    (pi : (Fin 3 → ℤ) →+ E)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (C : Set E) (compactC : IsCompact C)
    (enclosed : ∀ n, pi (parikhZ (wordPrefix w n)) ∈ C) (c : Fin 3) :
    IsCompact (prefixTiles w (ambientStar s pi) c) := by
  let : CompactSpace (MadicResidue.Carrier (incidenceLinear s)) :=
    MadicResidue.carrier_compactSpace (incidenceLinear s) integralInjective
  have hp : IsCompact (C ×ˢ (Set.univ : Set (MadicResidue.Carrier (incidenceLinear s)))) :=
    compactC.prod isCompact_univ
  apply hp.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hp.isClosed
  rintro x ⟨n, hn, rfl⟩
  exact ⟨enclosed n, Set.mem_univ _⟩

/-- The finite-history pieces are compact once the stable-window premise
is supplied. No physical interval mass appears in this conclusion. -/
theorem compact_prefix_historyPiece (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (C : Set E) (compactC : IsCompact C)
    (enclosed : ∀ n, pi (parikhZ (wordPrefix w n)) ∈ C)
    (n : ℕ) (p : Packet) (h : History (iterateImages s k) n p) :
    IsCompact (historyPiece (iterateImages s k) (ambientAction s B ^ k) (ambientStar s pi)
      (prefixTiles w (ambientStar s pi)) n p h) :=
  isCompact_historyPiece (iterateImages s k) (ambientAction s B ^ k) (ambientStar s pi) _
    (ambientAction_pow_isClosedEmbedding s B closedB integralInjective k).continuous
    (prefixTiles_compact_of_window s w pi integralInjective C compactC enclosed) n p h

end MatrixAdicProduct
end Psc.PrefixClosure
