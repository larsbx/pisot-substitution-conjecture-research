import PscVerif.NamedGeometricEnclosure
import PscVerif.GeometricPacketCarrier

/-!
# Finite carriers for the two actual named prefix systems

The natural box is chosen from the proved chart bounds, independently of
the substitution power or history depth. Its physical-interior filter
represents every nonempty inverse ancestor. The additional nondiagonal
filter has the same incoming completeness for nondiagonal sources.

Every even substitution power acts on the original matrix-adic product
and has the actual period-two word's tile equation. These facts discharge
all geometric, action, range and tile premises of the finite compact
history covers below. Literal marks and histories remain distinct.

Only nonempty actual ancestors are asserted to lie in the finite box.
The real filters and chosen natural bounds define mathematical finite
sets, not an executable enumeration or an exact overlap detector. No
forward closure, overlap measure, positivity, coincidence or PSC closure
is inferred.

Pre-code gate: `docs/c4-named-finite-carrier-literature-2026-11-11.md`.
-/

namespace Psc.NamedFiniteCarrier

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrencePiece
open Psc.OccurrenceCover Psc.OccurrenceAdmissibility Psc.OccurrenceNewborn
open Psc.OccurrenceResidue Psc.PrefixAddress Psc.PrefixClosure
open Psc.StablePrefixWindow Psc.NamedStableChart Psc.NamedPrefixCompact
open Matrix
open scoped BigOperators

/-! ## A single depth-independent full and strict domain -/

/-- The Archimedean witnesses dominate the authenticated chart estimate.
They are not an externally supplied numerical cutoff. -/
noncomputable def coordinateBudget (fixture : Fin 2) : Fin 3 → ℕ :=
  Classical.choose
    (GeometricPacketCarrier.exists_natural_bounds (NamedGeometricEnclosure.chart fixture))

theorem coordinateBudget_certified (fixture : Fin 2) (j : Fin 3) :
    (NamedGeometricEnclosure.chart fixture).coordinateBound j ≤
      (coordinateBudget fixture j : ℝ) :=
  Classical.choose_spec
    (GeometricPacketCarrier.exists_natural_bounds (NamedGeometricEnclosure.chart fixture)) j

/-- The complete certified box filtered by strict physical interior. -/
noncomputable def packets (fixture : Fin 2) : Finset Packet :=
  GeometricPacketCarrier.carrier physicalRow (coordinateBudget fixture)

theorem mem_packets (fixture : Fin 2) (p : Packet) :
    p ∈ packets fixture ↔
      (∀ j, |p.delta j| ≤ (coordinateBudget fixture j : ℤ)) ∧ p.Interior physicalRow :=
  GeometricPacketCarrier.mem_carrier physicalRow (coordinateBudget fixture) p

theorem packets_card_le (fixture : Fin 2) :
    (packets fixture).card ≤ 9 * ∏ j, (2 * coordinateBudget fixture j + 1) :=
  GeometricPacketCarrier.carrier_card_le physicalRow (coordinateBudget fixture)

theorem packets_swap_closed (fixture : Fin 2) (p : Packet) (hp : p ∈ packets fixture) :
    p.swap ∈ packets fixture :=
  GeometricPacketCarrier.carrier_swap_closed physicalRow (coordinateBudget fixture) p hp

/-- Removing integral diagonals retains exactly the supplied full-domain
membership and a separate nondiagonality condition. -/
noncomputable def strictPackets (fixture : Fin 2) : Finset Packet := by
  classical
  exact (packets fixture).filter (fun p => ¬ p.Diagonal)

theorem mem_strictPackets (fixture : Fin 2) (p : Packet) :
    p ∈ strictPackets fixture ↔ p ∈ packets fixture ∧ ¬ p.Diagonal := by
  classical
  simp only [strictPackets, Finset.mem_filter]

theorem strictPackets_card_le (fixture : Fin 2) :
    (strictPackets fixture).card ≤ 9 * ∏ j, (2 * coordinateBudget fixture j + 1) := by
  classical
  exact (Finset.card_filter_le _ _).trans (packets_card_le fixture)

theorem strictPackets_swap_closed (fixture : Fin 2) (p : Packet)
    (hp : p ∈ strictPackets fixture) : p.swap ∈ strictPackets fixture := by
  obtain ⟨hfull, hnd⟩ := (mem_strictPackets fixture p).mp hp
  apply (mem_strictPackets fixture p.swap).mpr
  refine ⟨packets_swap_closed fixture p hfull, ?_⟩
  intro hdiag
  have hfixed := (packet_swap_eq_iff_diagonal p.swap).mpr hdiag
  rw [packet_swap_swap] at hfixed
  exact hnd ((packet_swap_eq_iff_diagonal p).mp hfixed.symm)

theorem strictPackets_swap_ne (fixture : Fin 2) (p : Packet)
    (hp : p ∈ strictPackets fixture) : p.swap ≠ p := by
  intro hfixed
  exact ((mem_strictPackets fixture p).mp hp).2
    ((packet_swap_eq_iff_diagonal p).mp hfixed)

/-! ## Every nonempty inverse ancestor is represented -/

/-- All actual overlaps in the physical strip are represented, without a
supplied window, chart, contraction or finite-graph premise. -/
theorem nonempty_overlap_mem (fixture : Fin 2) (p : Packet)
    (interior : p.Interior physicalRow)
    (nonempty : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p).Nonempty) :
    p ∈ packets fixture :=
  GeometricPacketCarrier.nonempty_overlap_mem_carrier
    (NamedGeometricEnclosure.chart fixture) physical_row_pos (coordinateBudget fixture)
    (coordinateBudget_certified fixture) p interior nonempty

/-- Completeness holds for every actual block exponent, including zero;
no tile equation is needed for this geometric implication. -/
theorem nonempty_inverse_ancestor_mem (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ packets fixture) (u : Packet)
    (e : InverseOccurrence (iterateImages (substitution fixture) k) p u)
    (nonempty : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty) :
    u ∈ packets fixture :=
  GeometricPacketCarrier.nonempty_inverse_ancestor_represented
    (iterateImages (substitution fixture) k) (NamedGeometricEnclosure.chart fixture)
    physical_row_pos (beta ^ k) (pow_pos beta_pos k)
    (NamedGeometricEnclosure.physicalLength_iterateImages fixture k)
    (coordinateBudget fixture) (coordinateBudget_certified fixture) p hp u e nonempty

/-- Physical interior persists along arbitrary literal inverse paths.
Their intermediate overlaps need not be assumed nonempty. -/
theorem inverse_path_interior (fixture : Fin 2) (k : ℕ) (p u : Packet)
    (path : Relation.ReflTransGen (InverseStep (iterateImages (substitution fixture) k)) p u)
    (interior : p.Interior physicalRow) : u.Interior physicalRow := by
  revert interior
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => h
  | head hedge _ ih =>
      intro hp
      obtain ⟨e⟩ := hedge
      exact ih (e.interior (iterateImages (substitution fixture) k) physicalRow
        (beta ^ k) physical_row_pos (pow_pos beta_pos k)
        (NamedGeometricEnclosure.physicalLength_iterateImages fixture k) hp)

theorem nonempty_inverse_path_mem (fixture : Fin 2) (k : ℕ) (p u : Packet)
    (path : Relation.ReflTransGen (InverseStep (iterateImages (substitution fixture) k)) p u)
    (interior : p.Interior physicalRow)
    (nonempty : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty) :
    u ∈ packets fixture :=
  nonempty_overlap_mem fixture u (inverse_path_interior fixture k p u path interior) nonempty

/-- The set of nonempty actual ancestors over all finite path lengths is
finite. This is not a finiteness claim about empty algebraic ancestors. -/
theorem finite_nonempty_ancestry (fixture : Fin 2) (k : ℕ) (p : Packet)
    (interior : p.Interior physicalRow) :
    {u : Packet |
      Relation.ReflTransGen (InverseStep (iterateImages (substitution fixture) k)) p u ∧
        (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty}.Finite := by
  apply (packets fixture).finite_toSet.subset
  intro u hu
  exact nonempty_inverse_path_mem fixture k p u hu.1 interior hu.2

/-- Nondiagonality is inherited from the source's strict physical strip,
separately from the enclosure needed for the target's box membership. -/
theorem strict_nonempty_inverse_ancestor_mem (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) (u : Packet)
    (e : InverseOccurrence (iterateImages (substitution fixture) k) p u)
    (nonempty : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty) :
    u ∈ strictPackets fixture := by
  obtain ⟨hfull, hnd⟩ := (mem_strictPackets fixture p).mp hp
  apply (mem_strictPackets fixture u).mpr
  exact ⟨nonempty_inverse_ancestor_mem fixture k p hfull u e nonempty,
    e.nondiagonal physicalRow (fun a => (physical_row_pos a).le)
      ((mem_packets fixture p).mp hfull).2 hnd⟩

theorem strict_nonempty_inverse_path_mem (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) (u : Packet)
    (path : Relation.ReflTransGen (InverseStep (iterateImages (substitution fixture) k)) p u)
    (nonempty : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty) :
    u ∈ strictPackets fixture := by
  obtain ⟨hfull, hnd⟩ := (mem_strictPackets fixture p).mp hp
  have hu := inverse_path_interior_nondiagonal (iterateImages (substitution fixture) k)
    physicalRow (beta ^ k) physical_row_pos (pow_pos beta_pos k)
    (NamedGeometricEnclosure.physicalLength_iterateImages fixture k) path
    ((mem_packets fixture p).mp hfull).2 hnd
  exact (mem_strictPackets fixture u).mpr
    ⟨nonempty_overlap_mem fixture u hu.1 nonempty, hu.2⟩

theorem finite_strict_nonempty_ancestry (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) :
    {u : Packet |
      Relation.ReflTransGen (InverseStep (iterateImages (substitution fixture) k)) p u ∧
        (overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u).Nonempty}.Finite := by
  apply (strictPackets fixture).finite_toSet.subset
  intro u hu
  exact strict_nonempty_inverse_path_mem fixture k p hp u hu.1 hu.2

/-- Omitting an actual inverse ancestor from the strict certified carrier
forces its overlap to be empty; a search budget is not used. -/
theorem outside_strict_ancestor_empty (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) (u : Packet)
    (e : InverseOccurrence (iterateImages (substitution fixture) k) p u)
    (outside : u ∉ strictPackets fixture) :
    overlap (ambientStar (substitution fixture) piZ) (tiles fixture) u = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hn
  exact outside (strict_nonempty_inverse_ancestor_mem fixture k p hp u e hn)

/-! ## Actual block actions, local lifting and even-period covers -/

theorem block_action_injective (fixture : Fin 2) (k : ℕ) :
    Function.Injective (ambientAction (substitution fixture) B ^ k) :=
  (ambientAction_pow_isClosedEmbedding (substitution fixture) B B_isClosedEmbedding
    (integralInjective fixture) k).injective

theorem block_commute (fixture : Fin 2) (k : ℕ) (z : Fin 3 → ℤ) :
    (ambientAction (substitution fixture) B ^ k) (ambientStar (substitution fixture) piZ z) =
      ambientStar (substitution fixture) piZ
        (incidenceZ (iterateImages (substitution fixture) k) *ᵥ z) :=
  ambient_block_commute (substitution fixture) B piZ (pi_commute fixture) k z

/-- The residue coordinate is level `k` of the original `H_M`. -/
theorem block_reflectsIntegralRange (fixture : Fin 2) (k : ℕ) :
    ReflectsIntegralRange (iterateImages (substitution fixture) k)
      (ambientAction (substitution fixture) B ^ k) (ambientStar (substitution fixture) piZ) :=
  ambient_block_reflectsIntegralRange (substitution fixture) B piZ k

theorem local_admissible (fixture : Fin 2) (k : ℕ) (p : Packet) :
    LocalAdmissible (iterateImages (substitution fixture) k)
      (ambientAction (substitution fixture) B ^ k)
      (ambientStar (substitution fixture) piZ) (tiles fixture) p :=
  localAdmissible_of_reflects (ambientAction (substitution fixture) B ^ k)
    (ambientStar (substitution fixture) piZ) (tiles fixture)
    (block_reflectsIntegralRange fixture k) p

/-- Every nonempty literal pair has an integral ancestor in the full
carrier. Both selected marks remain part of the pair. -/
theorem representedAt_packets (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ packets fixture) :
    RepresentedAt (iterateImages (substitution fixture) k)
      (ambientAction (substitution fixture) B ^ k)
      (ambientStar (substitution fixture) piZ) (tiles fixture) (packets fixture) p :=
  representedAt_of_local (ambientAction (substitution fixture) B ^ k)
    (ambientStar (substitution fixture) piZ) (tiles fixture)
    (block_action_injective fixture k) (block_commute fixture k) (packets fixture) p
    (local_admissible fixture k p) (nonempty_inverse_ancestor_mem fixture k p hp)

theorem representedAt_strictPackets (fixture : Fin 2) (k : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) :
    RepresentedAt (iterateImages (substitution fixture) k)
      (ambientAction (substitution fixture) B ^ k)
      (ambientStar (substitution fixture) piZ) (tiles fixture) (strictPackets fixture) p :=
  representedAt_of_local (ambientAction (substitution fixture) B ^ k)
    (ambientStar (substitution fixture) piZ) (tiles fixture)
    (block_action_injective fixture k) (block_commute fixture k) (strictPackets fixture) p
    (local_admissible fixture k p) (strict_nonempty_inverse_ancestor_mem fixture k p hp)

/-- Every compatible even power uses the same actual prefix tiles and the
same original matrix-adic factor. The zero power is included. -/
theorem tileEquation_even (fixture : Fin 2) (r : ℕ) :
    TileEquation (iterateImages (substitution fixture) (2 * r))
      (ambientAction (substitution fixture) B ^ (2 * r))
      (ambientStar (substitution fixture) piZ) (tiles fixture) :=
  ambient_prefixTiles_tileEquation (substitution fixture) (2 * r) (word fixture) B piZ
    B_isClosedEmbedding (integralInjective fixture) (pi_commute fixture)
    (fixedPrefix_period_lift (substitution fixture) (word fixture) 2 r (word_fixed_two fixture))
    (cofinalImages_of_nonerasing _ _
      (nonerasing_iterateImages _ (nonerasing fixture) (2 * r)))

/-- All literal finite-history pieces are compact, independently of
whether their overlap is nonempty or their packet lies in either domain. -/
theorem historyPiece_compact (fixture : Fin 2) (k n : ℕ) (p : Packet)
    (h : History (iterateImages (substitution fixture) k) n p) :
    IsCompact (historyPiece (iterateImages (substitution fixture) k)
      (ambientAction (substitution fixture) B ^ k)
      (ambientStar (substitution fixture) piZ) (tiles fixture) n p h) :=
  isCompact_historyPiece (iterateImages (substitution fixture) k)
    (ambientAction (substitution fixture) B ^ k)
    (ambientStar (substitution fixture) piZ) (tiles fixture)
    (ambientAction_pow_isClosedEmbedding (substitution fixture) B B_isClosedEmbedding
      (integralInjective fixture) k).continuous
    (tiles_compact fixture) n p h

/-- An exact finite compact cover at every finite history depth. All
geometric, action, range and tile premises have been discharged. -/
theorem finite_compact_history_cover (fixture : Fin 2) (r n : ℕ)
    (p : Packet) (hp : p ∈ packets fixture) :
    Finite {h : History (iterateImages (substitution fixture) (2 * r)) n p //
      historyWithin (iterateImages (substitution fixture) (2 * r)) (packets fixture) n p h} ∧
      (∀ h : History (iterateImages (substitution fixture) (2 * r)) n p,
        IsCompact (historyPiece (iterateImages (substitution fixture) (2 * r))
          (ambientAction (substitution fixture) B ^ (2 * r))
          (ambientStar (substitution fixture) piZ) (tiles fixture) n p h)) ∧
      overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p =
        ⋃ h : {h : History (iterateImages (substitution fixture) (2 * r)) n p //
          historyWithin (iterateImages (substitution fixture) (2 * r))
            (packets fixture) n p h},
          historyPiece (iterateImages (substitution fixture) (2 * r))
            (ambientAction (substitution fixture) B ^ (2 * r))
            (ambientStar (substitution fixture) piZ) (tiles fixture) n p h.val := by
  obtain ⟨hf, hcover⟩ := GeometricPacketCarrier.finite_carrier_history_cover
    (iterateImages (substitution fixture) (2 * r))
    (ambientAction (substitution fixture) B ^ (2 * r))
    (NamedGeometricEnclosure.chart fixture) physical_row_pos (beta ^ (2 * r))
    (pow_pos beta_pos (2 * r))
    (NamedGeometricEnclosure.physicalLength_iterateImages fixture (2 * r))
    (coordinateBudget fixture) (coordinateBudget_certified fixture)
    (block_action_injective fixture (2 * r)) (block_commute fixture (2 * r))
    (tileEquation_even fixture r) (block_reflectsIntegralRange fixture (2 * r)) n p hp
  exact ⟨hf, historyPiece_compact fixture (2 * r) n p, hcover⟩

/-- The nondiagonal domain retains the same complete cover. The filter
does not assume forward closure or infer positive overlap measure. -/
theorem strict_finite_compact_history_cover (fixture : Fin 2) (r n : ℕ)
    (p : Packet) (hp : p ∈ strictPackets fixture) :
    Finite {h : History (iterateImages (substitution fixture) (2 * r)) n p //
      historyWithin (iterateImages (substitution fixture) (2 * r)) (strictPackets fixture) n p h} ∧
      (∀ h : History (iterateImages (substitution fixture) (2 * r)) n p,
        IsCompact (historyPiece (iterateImages (substitution fixture) (2 * r))
          (ambientAction (substitution fixture) B ^ (2 * r))
          (ambientStar (substitution fixture) piZ) (tiles fixture) n p h)) ∧
      overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p =
        ⋃ h : {h : History (iterateImages (substitution fixture) (2 * r)) n p //
          historyWithin (iterateImages (substitution fixture) (2 * r))
            (strictPackets fixture) n p h},
          historyPiece (iterateImages (substitution fixture) (2 * r))
            (ambientAction (substitution fixture) B ^ (2 * r))
            (ambientStar (substitution fixture) piZ) (tiles fixture) n p h.val := by
  refine ⟨finite_restrictedHistory _ (strictPackets fixture) n p,
    historyPiece_compact fixture (2 * r) n p, ?_⟩
  exact overlap_eq_iUnion_restrictedHistory
    (ambientAction (substitution fixture) B ^ (2 * r))
    (ambientStar (substitution fixture) piZ) (tiles fixture)
    (block_action_injective fixture (2 * r)) (block_commute fixture (2 * r))
    (tileEquation_even fixture r) (block_reflectsIntegralRange fixture (2 * r))
    (strictPackets fixture) (strict_nonempty_inverse_ancestor_mem fixture (2 * r)) n p hp

/-! ## Actual nonempty and strict-boundary controls -/

def diagonalPacket (a : Fin 3) : Packet := ⟨a, a, 0⟩

/-- A diagonal packet has the actual tile itself as overlap. -/
theorem diagonal_overlap_eq (fixture : Fin 2) (a : Fin 3) :
    overlap (ambientStar (substitution fixture) piZ) (tiles fixture) (diagonalPacket a) =
      tiles fixture a := by
  ext x
  change (x ∈ tiles fixture a ∧
    x - ambientStar (substitution fixture) piZ 0 ∈ tiles fixture a) ↔ _
  simp only [map_zero, sub_zero, and_self]

/-- The full domain contains actual nonempty overlaps, while the strict
domain excludes these same integral diagonals by definition. -/
theorem diagonal_control (fixture : Fin 2) (a : Fin 3) :
    diagonalPacket a ∈ packets fixture ∧
      (overlap (ambientStar (substitution fixture) piZ) (tiles fixture)
        (diagonalPacket a)).Nonempty ∧ diagonalPacket a ∉ strictPackets fixture := by
  have hn : (overlap (ambientStar (substitution fixture) piZ) (tiles fixture)
      (diagonalPacket a)).Nonempty := by
    rw [diagonal_overlap_eq]
    exact tiles_nonempty fixture a
  have hi : (diagonalPacket a).Interior physicalRow := by
    apply (Packet.interior_iff_bounds physicalRow physical_row_pos (diagonalPacket a)).mpr
    have ha := physical_row_pos a
    have hz : offset physicalRow (0 : Fin 3 → ℤ) = 0 := by simp [offset, dotProduct]
    change -physicalRow a < offset physicalRow 0 ∧ offset physicalRow 0 < physicalRow a
    rw [hz]
    exact ⟨neg_lt_zero.mpr ha, ha⟩
  refine ⟨nonempty_overlap_mem fixture _ hi hn, hn, ?_⟩
  intro hstrict
  exact ((mem_strictPackets fixture _).mp hstrict).2 ⟨rfl, rfl⟩

/-- Positive and negative physical boundary contacts are excluded by the
strict strip, regardless of the chosen natural coordinate budget. -/
theorem boundary_control (fixture : Fin 2) :
    (⟨0, 0, ![1, 0, 0]⟩ : Packet) ∉ packets fixture ∧
      (⟨0, 0, ![-1, 0, 0]⟩ : Packet) ∉ packets fixture := by
  constructor
  · intro hp
    have hi := (mem_packets fixture _).mp hp |>.2
    have hb := (Packet.interior_iff_bounds physicalRow physical_row_pos _).mp hi
    norm_num [offset, physicalRow, dotProduct, Fin.sum_univ_three] at hb
  · intro hp
    have hi := (mem_packets fixture _).mp hp |>.2
    have hb := (Packet.interior_iff_bounds physicalRow physical_row_pos _).mp hi
    norm_num [offset, physicalRow, dotProduct, Fin.sum_univ_three] at hb

/-- A period-two cover must use physical scale `beta^2`: the unpowered
scale already fails on the actual image of letter zero. -/
theorem wrong_scale_two_control (fixture : Fin 2) :
    physicalLength physicalRow (iterateImages (substitution fixture) 2 0) ≠
      beta * physicalRow 0 := by
  rw [NamedGeometricEnclosure.physicalLength_iterateImages]
  simp only [physicalRow, Matrix.cons_val_zero, mul_one]
  have hb := beta_gt_two
  nlinarith [sq_nonneg (beta - 1)]

end Psc.NamedFiniteCarrier
