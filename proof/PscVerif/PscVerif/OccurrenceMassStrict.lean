/-
# Complete strict carriers have conservative physical forward mass

The finite packet support records labels, while every row below counts actual
ordered image digit pairs.  Strict child closure retains every positive-mass
digit packet.  Consequently the complete physical forward matrix is
conservative, including after any correctly weighted transpose transport.

This identifies a boundary of the mass route: finite subdivision and strict
closure alone do not provide a losing vertex.  No geometric inverse matrix,
compact overlap measure, or C4 exclusion is constructed here.
Pre-code review: `docs/c4-overlap-mass-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceMass
import PscVerif.OccurrenceMassCounts
import PscVerif.OccurrenceStrict

namespace Psc.OccurrenceMassStrict

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceMass PscVerif.OccurrenceMassCounts
open scoped BigOperators

/-- Both actual digit positions, before projecting to a packet label. -/
abbrev Positions (s : Fin 3 → Word) (p : Packet) :=
  Fin (s p.top).length × Fin (s p.bottom).length

/-- The complete forward row on a supplied finite label support.  Distinct
position pairs with equal target labels contribute distinct occurrences. -/
noncomputable def forwardCounts (s : Fin 3 → Word) (S : Finset Packet)
    (p q : {p // p ∈ S}) : ℝ :=
  (rowCount (fun e : Positions s p.val => digitPacket s p.val e.1 e.2)
    Finset.univ q.val : ℝ)

theorem forwardCounts_nonneg (s : Fin 3 → Word) (S : Finset Packet)
    (p q : {p // p ∈ S}) : 0 ≤ forwardCounts s S p q := Nat.cast_nonneg _

/-- If the support omits only zero-mass children, grouping its row by packet
labels preserves the full ordered digit sum. -/
theorem action_forwardCounts (s : Fin 3 → Word) (S : Finset Packet)
    (ℓ : Fin 3 → ℝ) (p : {p // p ∈ S})
    (outside : ∀ e : Positions s p.val,
      digitPacket s p.val e.1 e.2 ∉ S →
        packetMass ℓ (digitPacket s p.val e.1 e.2) = 0) :
    PscVerif.PhysicalMass.action (forwardCounts s S)
      (fun q => packetMass ℓ q.val) p =
      ∑ i : Fin (s p.val.top).length, ∑ j : Fin (s p.val.bottom).length,
        packetMass ℓ (digitPacket s p.val i j) := by
  classical
  unfold PscVerif.PhysicalMass.action forwardCounts
  calc
    _ = ∑ q ∈ S,
        (rowCount (fun e : Positions s p.val => digitPacket s p.val e.1 e.2)
          Finset.univ q : ℝ) * packetMass ℓ q :=
      Finset.sum_coe_sort S (fun q =>
        (rowCount (fun e : Positions s p.val => digitPacket s p.val e.1 e.2)
          Finset.univ q : ℝ) * packetMass ℓ q)
    _ = ∑ e : Positions s p.val, packetMass ℓ (digitPacket s p.val e.1 e.2) :=
      sum_rowCount_on_of_zero_outside
        (fun e : Positions s p.val => digitPacket s p.val e.1 e.2)
        Finset.univ S (packetMass ℓ) (fun e _ => outside e)
    _ = _ := Fintype.sum_prod_type _

/-- Every positive actual digit occurrence is represented inside the finite
interior support of a supplied strict carrier. -/
theorem positive_digit_mem (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p : Packet}
    (hp : p ∈ interiorSupport C ℓ)
    (i : Fin (s p.top).length) (j : Fin (s p.bottom).length)
    (hchild : 0 < packetMass ℓ (digitPacket s p i j)) :
    digitPacket s p i j ∈ interiorSupport C ℓ := by
  have hi := (packetMass_pos_iff_interior ℓ (digitPacket s p i j)).mp hchild
  exact mem_interiorSupport.mpr
    ⟨Psc.OccurrenceStrict.realized_closed s ℓ hpos hC
      (mem_interiorSupport.mp hp).1 ⟨digitPacket_digitStep s p i j, hi⟩, hi⟩

/-- An actual digit outside the represented interior support has zero mass;
it is not a positive omitted interval. -/
theorem outside_mass_zero (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {C : Finset WordPair}
    (hC : Psc.StrictSystem.StrictSystem s C) {p : Packet}
    (hp : p ∈ interiorSupport C ℓ)
    (i : Fin (s p.top).length) (j : Fin (s p.bottom).length)
    (hout : digitPacket s p i j ∉ interiorSupport C ℓ) :
    packetMass ℓ (digitPacket s p i j) = 0 := by
  apply le_antisymm _ (packetMass_nonneg ℓ _)
  apply le_of_not_gt
  intro hpositive
  exact hout (positive_digit_mem s ℓ hpos hC hp i j hpositive)

theorem support_mass_pos (C : Finset WordPair) (ℓ : Fin 3 → ℝ)
    (p : {p // p ∈ interiorSupport C ℓ}) : 0 < packetMass ℓ p.val :=
  (packetMass_pos_iff_interior ℓ p.val).mpr (mem_interiorSupport.mp p.property).2

/-- Complete strict child closure is conservative for physical interval
mass.  This is equality, so it supplies no positive-deficit vertex. -/
theorem full_forward_conservative (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    (p : {p // p ∈ interiorSupport C ℓ}) :
    PscVerif.PhysicalMass.action (forwardCounts s (interiorSupport C ℓ))
      (fun q => packetMass ℓ q.val) p = β * packetMass ℓ p.val := by
  rw [action_forwardCounts s (interiorSupport C ℓ) ℓ p
    (fun e => outside_mass_zero s ℓ hpos hC p.property e.1 e.2)]
  exact sum_digitPacket_mass s ℓ β (fun a => (hpos a).le) hβ hscale p.val

/-- Any inverse matrix with a proved weighted count correspondence to this
complete forward carrier has zero weighted physical deficit everywhere.
The correspondence is still an explicit hypothesis about that matrix. -/
theorem weighted_deficit_zero (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {C : Finset WordPair} (hC : Psc.StrictSystem.StrictSystem s C)
    (T : {p // p ∈ interiorSupport C ℓ} → {p // p ∈ interiorSupport C ℓ} → ℝ)
    (m : {p // p ∈ interiorSupport C ℓ} → ℝ)
    (transport : ∀ i j, m i * T i j =
      m j * forwardCounts s (interiorSupport C ℓ) j i)
    (j : {p // p ∈ interiorSupport C ℓ}) :
    PscVerif.PhysicalMass.deficit T (fun i => m i * packetMass ℓ i.val) β j = 0 := by
  rw [PscVerif.PhysicalMass.weighted_deficit T
    (forwardCounts s (interiorSupport C ℓ)) m (fun i => packetMass ℓ i.val)
    β transport j, full_forward_conservative s ℓ β hpos hβ hscale hC j,
    sub_self, mul_zero]

end Psc.OccurrenceMassStrict
