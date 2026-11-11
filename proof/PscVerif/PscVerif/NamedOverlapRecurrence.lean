import PscVerif.NamedOverlapHaar
import PscVerif.OccurrencePhysicalBudget
import PscVerif.OverlapContraction

/-!
# Actual named overlap recurrence on complete literal finite domains

The finite rows consist of integral inverse occurrences with both original
marks.  Their geometric pieces use the original matrix-adic product and
the actual period-two prefix tiles.  Complete representability supplies
the cover, and the proved Haar modulus supplies its real subinvariance.

Physical subdivision supplies the dual budget on the same counts.  On
physical-interior domains the existing finite pairing theorem therefore
forces equality and annihilates the product of deficit and overlap mass.
No positive strict-root measure or actual source-loss witness is inferred.

Pre-code gate: `docs/c4-named-overlap-balance-literature-2026-11-11.md`.
-/

namespace Psc.NamedOverlapRecurrence

open Set MeasureTheory
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedFiniteCarrier
open Psc.NamedProductHaar
open Psc.OccurrenceResidue Psc.OccurrenceCover Psc.OccurrencePiece
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceAdmissibility
open Psc.OccurrencePhysicalBudget Psc.OccurrenceMass
open PscVerif.PhysicalMass
open scoped BigOperators ENNReal

variable (f : Fin 2) (ν : Measure (H (substitution f)))
  [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]

local notation "T" => ambientAction (substitution f) B
local notation "star" => ambientStar (substitution f) piZ
local notation "E" => overlap star (tiles f)
local notation "μ" => (volume.prod ν)

/-- Actual finite product-Haar overlap coordinates, never fitted weights. -/
noncomputable def overlapMass (S : Finset Packet) (p : State S) : ℝ :=
  (μ (E p.val)).toReal

theorem overlapMass_nonneg (S : Finset Packet) (p : State S) :
    0 ≤ overlapMass f ν S p := ENNReal.toReal_nonneg

theorem overlapMass_eq_zero_iff (S : Finset Packet) (p : State S) :
    overlapMass f ν S p = 0 ↔ μ (E p.val) = 0 := by
  unfold overlapMass
  exact (ENNReal.toReal_eq_zero_iff _).trans
    (or_iff_left (Psc.NamedProductHaar.overlap_measure_finite f ν p.val))

/-- The literal compact piece for one retained ancestor and two actual marks. -/
def rowPiece (k : ℕ) (S : Finset Packet) (p : State S)
    (e : Row (iterateImages (substitution f) k) S p) : Set (G (substitution f)) :=
  piece (T ^ k) star (tiles f) e.2

theorem measure_rowPiece (k : ℕ) (S : Finset Packet) (p : State S)
    (e : Row (iterateImages (substitution f) k) S p) :
    μ (rowPiece f k S p e) = (ENNReal.ofReal beta⁻¹) ^ k * μ (E e.1.val) := by
  exact Psc.NamedProductHaar.measure_affine_power (substitution f) (incidence_eq f) ν k
    (star (parikhZ e.2.topMark.before)) (E e.1.val)

theorem scaled_measure_rowPiece (k : ℕ) (S : Finset Packet) (p : State S)
    (e : Row (iterateImages (substitution f) k) S p) :
    ENNReal.ofReal (beta ^ k) * μ (rowPiece f k S p e) = μ (E e.1.val) := by
  have cancel : ENNReal.ofReal (beta ^ k) * (ENNReal.ofReal beta⁻¹) ^ k = 1 := by
    rw [ENNReal.ofReal_pow beta_pos.le, ← mul_pow,
      ← ENNReal.ofReal_mul beta_pos.le, mul_inv_cancel₀ beta_ne_zero]
    simp
  rw [measure_rowPiece, ← mul_assoc, cancel, one_mul]

/-- The cover is derived from the literal tile equation and representation
of every nonempty paired piece; it is not an extra numerical premise. -/
theorem overlap_eq_iUnion_rowPiece (r : ℕ) (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S) :
    E p.val = ⋃ e : Row (iterateImages (substitution f) (2 * r)) S p,
      rowPiece f (2 * r) S p e := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, e, he⟩ := overlap_mem_piece_of_represented
      (T ^ (2 * r)) star (tiles f) (block_action_injective f (2 * r))
      (block_commute f (2 * r)) (tileEquation_even f r) S p.val
      (represented p.val p.property) hx
    exact Set.mem_iUnion.mpr ⟨⟨⟨u, hu⟩, e⟩, he⟩
  · intro hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    exact piece_subset_overlap (T ^ (2 * r)) star (tiles f)
      (block_action_injective f (2 * r)) (block_commute f (2 * r))
      (tileEquation_even f r) e.2 he

/-- Authentic cover and Haar scaling imply the real matrix inequality,
with a separate summand for every actual occurrence. -/
theorem subinvariance (r : ℕ) (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S) :
    beta ^ (2 * r) * overlapMass f ν S p ≤
      action (inverseCounts (iterateImages (substitution f) (2 * r)) S)
        (overlapMass f ν S) p := by
  have recurrence := PscVerif.OverlapContraction.recurrence_of_cover
    (Row (iterateImages (substitution f) (2 * r)) S) (fun _ e => e.1)
    μ (fun p : State S => E p.val) (rowPiece f (2 * r) S)
    (beta ^ (2 * r)) (pow_nonneg beta_pos.le _)
    (fun p => Psc.NamedProductHaar.overlap_measure_finite f ν p.val)
    (fun p => (overlap_eq_iUnion_rowPiece f r S represented p).le)
    (fun p e => (scaled_measure_rowPiece f ν (2 * r) S p e).le) p
  simpa only [overlapMass, row_sum_eq_action] using recurrence

/-- Physical positivity comes from the literal interior strip, independently
of whether a compact overlap is nonempty or has positive measure. -/
theorem physicalMass_pos (S : Finset Packet)
    (interior : ∀ p ∈ S, p.Interior physicalRow) (p : State S) :
    0 < packetMass physicalRow p.val :=
  (packetMass_pos_iff_interior physicalRow p.val).mpr (interior p.val p.property)

/-- The same actual counts have the authentic physical transpose budget. -/
theorem physical_budget (r : ℕ) (S : Finset Packet) (p : State S) :
    transposeAction (inverseCounts (iterateImages (substitution f) (2 * r)) S)
      (fun p => packetMass physicalRow p.val) p ≤
      beta ^ (2 * r) * packetMass physicalRow p.val :=
  transpose_budget (iterateImages (substitution f) (2 * r)) S physicalRow
    (beta ^ (2 * r)) (fun a => (physical_row_pos a).le)
    (pow_nonneg beta_pos.le _) (NamedGeometricEnclosure.physicalLength_iterateImages f _) p

/-- Pairing authentic geometric subinvariance and the physical budget
forces an exact recurrence on every complete interior domain. -/
theorem balance (r : ℕ) (S : Finset Packet)
    (interior : ∀ p ∈ S, p.Interior physicalRow)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S) :
    action (inverseCounts (iterateImages (substitution f) (2 * r)) S)
      (overlapMass f ν S) p = beta ^ (2 * r) * overlapMass f ν S p :=
  saturation _ (fun p => packetMass physicalRow p.val) _ _
    (physicalMass_pos S interior) (overlapMass_nonneg f ν S)
    (subinvariance f ν r S represented) (physical_budget f r S) p

/-- At every packet the omitted physical mass annihilates its actual
product-Haar overlap coordinate. -/
theorem deficit_product_zero (r : ℕ) (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S) :
    deficit (inverseCounts (iterateImages (substitution f) (2 * r)) S)
      (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p *
      overlapMass f ν S p = 0 :=
  (products_zero _ (fun p => packetMass physicalRow p.val) _ _
    (fun p => packetMass_nonneg physicalRow p.val) (overlapMass_nonneg f ν S)
    (subinvariance f ν r S represented) (physical_budget f r S)).2 p

/-- Full named-domain recurrence: no cover, chart, scaling or supplied
finite-graph hypothesis remains. -/
theorem packets_subinvariance (r : ℕ) (p : State (packets f)) :
    beta ^ (2 * r) * overlapMass f ν (packets f) p ≤
      action (inverseCounts (iterateImages (substitution f) (2 * r)) (packets f))
        (overlapMass f ν (packets f)) p :=
  subinvariance f ν r (packets f) (representedAt_packets f _) p

/-- The authentic nondiagonal domain has the same complete recurrence. -/
theorem strictPackets_subinvariance (r : ℕ) (p : State (strictPackets f)) :
    beta ^ (2 * r) * overlapMass f ν (strictPackets f) p ≤
      action (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))
        (overlapMass f ν (strictPackets f)) p :=
  subinvariance f ν r (strictPackets f) (representedAt_strictPackets f _) p

theorem packets_balance (r : ℕ) (p : State (packets f)) :
    action (inverseCounts (iterateImages (substitution f) (2 * r)) (packets f))
      (overlapMass f ν (packets f)) p =
      beta ^ (2 * r) * overlapMass f ν (packets f) p :=
  balance f ν r (packets f) (fun p hp => ((mem_packets f p).mp hp).2)
    (representedAt_packets f _) p

theorem strictPackets_balance (r : ℕ) (p : State (strictPackets f)) :
    action (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))
      (overlapMass f ν (strictPackets f)) p =
      beta ^ (2 * r) * overlapMass f ν (strictPackets f) p :=
  balance f ν r (strictPackets f)
    (fun p hp => ((mem_packets f p).mp ((mem_strictPackets f p).mp hp).1).2)
    (representedAt_strictPackets f _) p

theorem packets_deficit_product_zero (r : ℕ) (p : State (packets f)) :
    deficit (inverseCounts (iterateImages (substitution f) (2 * r)) (packets f))
      (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p *
      overlapMass f ν (packets f) p = 0 :=
  deficit_product_zero f ν r (packets f) (representedAt_packets f _) p

theorem strictPackets_deficit_product_zero (r : ℕ) (p : State (strictPackets f)) :
    deficit (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))
      (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p *
      overlapMass f ν (strictPackets f) p = 0 :=
  deficit_product_zero f ν r (strictPackets f) (representedAt_strictPackets f _) p

/-- A genuine positive physical deficit forces the corresponding actual
compact overlap to be null. This theorem does not produce a deficit. -/
theorem null_at_loss (r : ℕ) (S : Finset Packet)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S)
    (loss : 0 < deficit (inverseCounts (iterateImages (substitution f) (2 * r)) S)
      (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p) :
    μ (E p.val) = 0 := by
  apply (overlapMass_eq_zero_iff f ν S p).mp
  exact (mul_eq_zero.mp (deficit_product_zero f ν r S represented p)).resolve_left
    (ne_of_gt loss)

/-- Nullity travels in the row-to-inverse-ancestor direction along actual
positive occurrence counts. -/
theorem null_of_loss_reaches (r : ℕ) (S : Finset Packet)
    (interior : ∀ p ∈ S, p.Interior physicalRow)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) {j p : State S}
    (loss : 0 < deficit (inverseCounts (iterateImages (substitution f) (2 * r)) S)
      (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) j)
    (path : Reach (support (inverseCounts (iterateImages (substitution f) (2 * r)) S)) j p) :
    μ (E p.val) = 0 := by
  apply (overlapMass_eq_zero_iff f ν S p).mp
  exact zero_of_loss_reaches _ (fun p => packetMass physicalRow p.val) _ _
    (inverseCounts_nonneg _ _) (physicalMass_pos S interior)
    (overlapMass_nonneg f ν S) (subinvariance f ν r S represented)
    (physical_budget f r S) loss path

/-- One actual losing vertex per source component suffices for all actual
overlaps to be null. Source loss is retained as a separate hypothesis. -/
theorem null_of_source_loss (r : ℕ) (S : Finset Packet)
    (interior : ∀ p ∈ S, p.Interior physicalRow)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p)
    (loss : SourceLoss
      (support (inverseCounts (iterateImages (substitution f) (2 * r)) S))
      (fun p => 0 < deficit (inverseCounts (iterateImages (substitution f) (2 * r)) S)
        (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p))
    (p : State S) : μ (E p.val) = 0 := by
  apply (overlapMass_eq_zero_iff f ν S p).mp
  exact zero_of_source_loss _ (fun p => packetMass physicalRow p.val) _ _
    (inverseCounts_nonneg _ _) (physicalMass_pos S interior)
    (overlapMass_nonneg f ν S) (subinvariance f ν r S represented)
    (physical_budget f r S) loss p

/-- Any actual nonzero overlap has a conservative source ancestor. This
is necessary for survival, and is not a converse producing positive mass. -/
theorem conservative_source_ancestor (r : ℕ) (S : Finset Packet)
    (interior : ∀ p ∈ S, p.Interior physicalRow)
    (represented : ∀ p ∈ S, RepresentedAt (iterateImages (substitution f) (2 * r))
      (T ^ (2 * r)) star (tiles f) S p) (p : State S)
    (nonzero : μ (E p.val) ≠ 0) :
    ∃ s : State S,
      IsSource (support (inverseCounts (iterateImages (substitution f) (2 * r)) S)) s ∧
      Reach (support (inverseCounts (iterateImages (substitution f) (2 * r)) S)) s p ∧
      ∀ j, SameSCC (support (inverseCounts (iterateImages (substitution f) (2 * r)) S)) s j →
        deficit (inverseCounts (iterateImages (substitution f) (2 * r)) S)
          (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) j = 0 := by
  apply conservative_source_ancestor_of_nonzero _ (fun p => packetMass physicalRow p.val)
    (overlapMass f ν S) (beta ^ (2 * r)) (inverseCounts_nonneg _ _)
    (physicalMass_pos S interior) (overlapMass_nonneg f ν S)
    (subinvariance f ν r S represented) (physical_budget f r S) p
  intro hz
  exact nonzero ((overlapMass_eq_zero_iff f ν S p).mp hz)

/-- The strict named domain is the target of a source-loss certificate.
The full domain retains diagonal components and is used above for balance,
not offered as a domain on which all-source loss should be constructed. -/
theorem strictPackets_null_of_source_loss (r : ℕ)
    (loss : SourceLoss
      (support (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f)))
      (fun p => 0 < deficit
        (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))
        (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) p))
    (p : State (strictPackets f)) : μ (E p.val) = 0 :=
  null_of_source_loss f ν r (strictPackets f)
    (fun p hp => ((mem_packets f p).mp ((mem_strictPackets f p).mp hp).1).2)
    (representedAt_strictPackets f _) loss p

/-- A nonzero strict named overlap requires a zero-deficit source component
in its complete literal inverse graph. -/
theorem strictPackets_conservative_source_ancestor (r : ℕ) (p : State (strictPackets f))
    (nonzero : μ (E p.val) ≠ 0) :
    ∃ s : State (strictPackets f),
      IsSource (support (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))) s ∧
      Reach (support (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))) s p ∧
      ∀ j, SameSCC
        (support (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))) s j →
        deficit (inverseCounts (iterateImages (substitution f) (2 * r)) (strictPackets f))
          (fun p => packetMass physicalRow p.val) (beta ^ (2 * r)) j = 0 :=
  conservative_source_ancestor f ν r (strictPackets f)
    (fun p hp => ((mem_packets f p).mp ((mem_strictPackets f p).mp hp).1).2)
    (representedAt_strictPackets f _) p nonzero

end Psc.NamedOverlapRecurrence
