import PscVerif.NamedProductHaar
import PscVerif.NamedFiniteCarrier

/-! The finite literal history covers give a subinvariant overlap bound. -/

open Set MeasureTheory
open scoped ENNReal
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedFiniteCarrier
open Psc.OccurrenceResidue Psc.OccurrenceCover Psc.OccurrencePiece
open Psc.OccurrenceTransport Psc.OccurrenceInverse
namespace Psc.NamedProductHaar

variable (f : Fin 2) (ν : Measure (H (substitution f))) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]

local notation "T" => ambientAction (substitution f) B
local notation "star" => ambientStar (substitution f) piZ
local notation "E" => overlap star (tiles f)
local notation "μ" => (volume.prod ν)

theorem overlap_measure_finite (p : Packet) : μ (E p) ≠ ⊤ :=
  (isCompact_overlap star (tiles f) (tiles_compact f) p).measure_lt_top.ne

theorem measure_history_piece (k n : ℕ) (p : Packet)
    (h : History (iterateImages (substitution f) k) n p) :
    μ (historyPiece (iterateImages (substitution f) k) (T ^ k) star (tiles f) n p h) =
      (ENNReal.ofReal beta⁻¹) ^ (k * n) *
        μ (E (historyTarget (iterateImages (substitution f) k) n p h)) := by
  have hm : historyMap (iterateImages (substitution f) k) (T ^ k) star n p h =
      fun x => (T ^ (k * n)) x + star
        (historyTopPrefix (iterateImages (substitution f) k) n p h) := by
    funext x
    let A : AddMonoid.End (G (substitution f)) := T
    have hpow : (((A ^ k : AddMonoid.End (G (substitution f))) :
        G (substitution f) → G (substitution f))^[n]) x = (A ^ (k * n)) x :=
      (congrFun (AddMonoid.End.coe_pow (A ^ k) n).symm x).trans
        (congrArg (fun g : AddMonoid.End (G (substitution f)) => g x) (pow_mul A k n).symm)
    exact (historyMap_eq (iterateImages (substitution f) k) (T ^ k) star
      (block_commute f k) n p h x).trans
        (congrArg (fun y => y + star (historyTopPrefix (iterateImages (substitution f) k) n p h))
          hpow)
  calc
    _ = μ (historyMap (iterateImages (substitution f) k) (T ^ k) star n p h ''
        E (historyTarget (iterateImages (substitution f) k) n p h)) :=
      congrArg μ (historyPiece_eq_image (iterateImages (substitution f) k)
        (T ^ k) star (tiles f) n p h)
    _ = μ ((fun x => (T ^ (k * n)) x + star
        (historyTopPrefix (iterateImages (substitution f) k) n p h)) ''
        E (historyTarget (iterateImages (substitution f) k) n p h)) :=
      congrArg (fun g => μ (g '' E (historyTarget (iterateImages (substitution f) k) n p h))) hm
    _ = _ := measure_affine_power (substitution f) (incidence_eq f) ν (k * n)
      (star (historyTopPrefix (iterateImages (substitution f) k) n p h))
      (E (historyTarget (iterateImages (substitution f) k) n p h))

theorem overlap_bound_of_history_cover (k n : ℕ) (p : Packet)
    {ι : Type*} [Finite ι] (h : ι → History (iterateImages (substitution f) k) n p)
    (cover : E p ⊆ ⋃ i, historyPiece (iterateImages (substitution f) k) (T ^ k)
        star (tiles f) n p (h i)) :
    μ (E p) ≤ (ENNReal.ofReal beta⁻¹) ^ (k * n) *
      ∑' i, μ (E (historyTarget (iterateImages (substitution f) k) n p (h i))) := by
  classical
  letI := Fintype.ofFinite ι
  rw [tsum_fintype, Finset.mul_sum]
  calc
    _ ≤ μ (⋃ i, historyPiece (iterateImages (substitution f) k) (T ^ k)
        star (tiles f) n p (h i)) := measure_mono cover
    _ ≤ _ := by
      simpa only [measure_history_piece] using
        (measure_iUnion_fintype_le μ
          (fun i => historyPiece (iterateImages (substitution f) k) (T ^ k)
            star (tiles f) n p (h i)))

theorem overlap_bound (r n : ℕ) (p : Packet) (hp : p ∈ packets f) :
    μ (E p) ≤ (ENNReal.ofReal beta⁻¹) ^ ((2 * r) * n) *
      ∑' h : {h : History (iterateImages (substitution f) (2 * r)) n p //
          historyWithin (iterateImages (substitution f) (2 * r)) (packets f) n p h},
        μ (E (historyTarget (iterateImages (substitution f) (2 * r)) n p h.val)) := by
  obtain ⟨hf, _, hc⟩ := finite_compact_history_cover f r n p hp
  letI := hf
  exact overlap_bound_of_history_cover f ν _ _ _ Subtype.val hc.le

theorem strict_overlap_bound (r n : ℕ) (p : Packet) (hp : p ∈ strictPackets f) :
    μ (E p) ≤ (ENNReal.ofReal beta⁻¹) ^ ((2 * r) * n) *
      ∑' h : {h : History (iterateImages (substitution f) (2 * r)) n p //
          historyWithin (iterateImages (substitution f) (2 * r)) (strictPackets f) n p h},
        μ (E (historyTarget (iterateImages (substitution f) (2 * r)) n p h.val)) := by
  obtain ⟨hf, _, hc⟩ := strict_finite_compact_history_cover f r n p hp
  letI := hf
  exact overlap_bound_of_history_cover f ν _ _ _ Subtype.val hc.le

end Psc.NamedProductHaar
