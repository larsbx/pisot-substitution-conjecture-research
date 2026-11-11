import PscVerif.OccurrenceMassCounts
import PscVerif.OccurrenceInverse

/-!
# Literal inverse rows and their physical transpose budget

Every row element retains an integral ancestor and both actual image
positions. The inverse count matrix is the transpose of the complete
retained forward counts. A finite domain can omit positive forward
children, so its physical statement is a budget, not a closure assertion.

The exact difference is the mass of the omitted positional occurrences.
No geometric cover, positive compact measure, strict loss, or swap quotient
is assumed or produced by these finite counting identities.

Pre-code gate: `docs/c4-named-overlap-balance-literature-2026-11-11.md`.
-/

namespace Psc.OccurrencePhysicalBudget

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceMass
open Psc.OccurrenceInverse
open PscVerif.OccurrenceMassCounts PscVerif.PhysicalMass
open scoped BigOperators

/-- Ordered packets retain their full integral offset and track order. -/
abbrev State (S : Finset Packet) := {p : Packet // p ∈ S}

/-- Both actual positions before any packet-label projection. -/
abbrev Positions (s : Fin 3 → Word) (p : Packet) :=
  Fin (s p.top).length × Fin (s p.bottom).length

/-- All represented literal incoming occurrences, with no deduplication. -/
abbrev Row (s : Fin 3 → Word) (S : Finset Packet) (p : State S) :=
  Σ u : State S, InverseOccurrence s p.val u.val

/-- The two positions identify the forward occurrence exactly. -/
def forwardPositionEquiv (s : Fin 3 → Word) (p u : Packet) :
    ForwardOccurrence s u p ≃
      {ij : Positions s u // digitPacket s u ij.1 ij.2 = p} where
  toFun e := ⟨(e.topIndex, e.bottomIndex), e.packet_eq.symm⟩
  invFun ij := ⟨ij.val.1, ij.val.2, ij.property.symm⟩
  left_inv e := by cases e; rfl
  right_inv ij := by cases ij; rfl

/-- Data equivalence between actual inverse marks and actual position pairs. -/
def inversePositionEquiv (s : Fin 3 → Word) (p u : Packet) :
    InverseOccurrence s p u ≃
      {ij : Positions s u // digitPacket s u ij.1 ij.2 = p} :=
  (inverseEquivForward s p u).trans (forwardPositionEquiv s p u)

noncomputable instance inverseOccurrenceFintype (s : Fin 3 → Word) (p u : Packet) :
    Fintype (InverseOccurrence s p u) := by
  classical
  exact Fintype.ofEquiv _ (inversePositionEquiv s p u).symm

noncomputable instance rowFintype (s : Fin 3 → Word) (S : Finset Packet)
    (p : State S) : Fintype (Row s S p) := by
  classical
  unfold Row
  infer_instance

/-- Row child `p`, column inverse ancestor `u`. Parallel positions count
separately through the existing complete row counter. This is definitionally
`OccurrenceMassStrict.forwardCounts s S u p`; the generic budget does not
import the strict-child-system theorems merely to use that definition. -/
noncomputable def inverseCounts (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) : ℝ :=
  (rowCount (fun ij : Positions s u.val => digitPacket s u.val ij.1 ij.2)
    Finset.univ p.val : ℝ)

theorem inverseCounts_nonneg (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) : 0 ≤ inverseCounts s S p u :=
  Nat.cast_nonneg _

/-- Counting actual inverse marks agrees with the literal transpose. -/
theorem inverseCounts_eq_card (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) :
    inverseCounts s S p u = (Fintype.card (InverseOccurrence s p.val u.val) : ℝ) := by
  classical
  rw [Fintype.card_congr (inversePositionEquiv s p.val u.val)]
  simp only [inverseCounts, rowCount, Fintype.card_subtype]

/-- A positive matrix entry is an actual represented incoming occurrence. -/
theorem inverseCounts_pos_iff (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) :
    0 < inverseCounts s S p u ↔ Nonempty (InverseOccurrence s p.val u.val) := by
  rw [inverseCounts_eq_card, Nat.cast_pos, Fintype.card_pos_iff]

/-- Regrouping actual incoming marks preserves their multiplicities. -/
theorem row_sum_eq_action (s : Fin 3 → Word) (S : Finset Packet)
    (v : State S → ℝ) (p : State S) :
    (∑ e : Row s S p, v e.1) = action (inverseCounts s S) v p := by
  classical
  rw [Fintype.sum_sigma]
  unfold action
  apply Finset.sum_congr rfl
  intro u _
  rw [inverseCounts_eq_card]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The retained forward positional sum, with all omitted targets visible. -/
theorem transpose_eq_retained (s : Fin 3 → Word) (S : Finset Packet)
    (h : Packet → ℝ) (u : State S) :
    transposeAction (inverseCounts s S) (fun p => h p.val) u =
      ∑ ij : Positions s u.val,
        if digitPacket s u.val ij.1 ij.2 ∈ S then
          h (digitPacket s u.val ij.1 ij.2) else 0 := by
  classical
  unfold transposeAction inverseCounts
  calc
    _ = ∑ p ∈ S,
        (rowCount (fun ij : Positions s u.val => digitPacket s u.val ij.1 ij.2)
          Finset.univ p : ℝ) * h p :=
      Finset.sum_coe_sort S (fun p =>
        (rowCount (fun ij : Positions s u.val => digitPacket s u.val ij.1 ij.2)
          Finset.univ p : ℝ) * h p)
    _ = _ := sum_rowCount_on
      (fun ij : Positions s u.val => digitPacket s u.val ij.1 ij.2)
      Finset.univ S h

/-- A finite retained domain cannot exceed complete physical subdivision. -/
theorem transpose_budget (s : Fin 3 → Word) (S : Finset Packet)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ∀ a, 0 ≤ ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (u : State S) :
    transposeAction (inverseCounts s S) (fun p => packetMass ℓ p.val) u ≤
      β * packetMass ℓ u.val := by
  classical
  rw [transpose_eq_retained]
  calc
    _ ≤ ∑ ij : Positions s u.val,
        packetMass ℓ (digitPacket s u.val ij.1 ij.2) := by
      apply Finset.sum_le_sum
      intro ij _
      split_ifs
      · exact le_rfl
      · exact packetMass_nonneg ℓ _
    _ = ∑ i : Fin (s u.val.top).length, ∑ j : Fin (s u.val.bottom).length,
        packetMass ℓ (digitPacket s u.val i j) := Fintype.sum_prod_type _
    _ = _ := sum_digitPacket_mass s ℓ β hℓ hβ hscale u.val

/-- The deficit is exactly the omitted *occurrence* mass. Targets with
several positions contribute several terms. -/
theorem deficit_eq_omitted_positions (s : Fin 3 → Word) (S : Finset Packet)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ∀ a, 0 ≤ ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (u : State S) :
    deficit (inverseCounts s S) (fun p => packetMass ℓ p.val) β u =
      ∑ ij : Positions s u.val,
        if digitPacket s u.val ij.1 ij.2 ∈ S then 0
        else packetMass ℓ (digitPacket s u.val ij.1 ij.2) := by
  classical
  have complete :
      (∑ ij : Positions s u.val,
        packetMass ℓ (digitPacket s u.val ij.1 ij.2)) =
      β * packetMass ℓ u.val := by
    rw [Fintype.sum_prod_type]
    exact sum_digitPacket_mass s ℓ β hℓ hβ hscale u.val
  unfold deficit
  rw [transpose_eq_retained, ← complete, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  split_ifs <;> simp

/-- A strictly positive deficit needs an actually omitted positive child.
The criterion counts positions and makes no geometric exclusion claim. -/
theorem deficit_pos_iff (s : Fin 3 → Word) (S : Finset Packet)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ∀ a, 0 ≤ ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (u : State S) :
    0 < deficit (inverseCounts s S) (fun p => packetMass ℓ p.val) β u ↔
      ∃ ij : Positions s u.val,
        digitPacket s u.val ij.1 ij.2 ∉ S ∧
          0 < packetMass ℓ (digitPacket s u.val ij.1 ij.2) := by
  classical
  rw [deficit_eq_omitted_positions s S ℓ β hℓ hβ hscale]
  have nonnegative : ∀ ij : Positions s u.val,
      0 ≤ if digitPacket s u.val ij.1 ij.2 ∈ S then 0
        else packetMass ℓ (digitPacket s u.val ij.1 ij.2) := by
    intro ij
    split_ifs
    · exact le_rfl
    · exact packetMass_nonneg ℓ _
  rw [Finset.sum_pos_iff_of_nonneg (fun ij _ => nonnegative ij)]
  constructor
  · rintro ⟨ij, _, hpositive⟩
    by_cases hin : digitPacket s u.val ij.1 ij.2 ∈ S
    · simp only [hin, if_true, lt_self_iff_false] at hpositive
    · exact ⟨ij, hin, by simpa only [hin, if_false] using hpositive⟩
  · rintro ⟨ij, hout, hpositive⟩
    exact ⟨ij, Finset.mem_univ ij, by simpa only [hout, if_false] using hpositive⟩

end Psc.OccurrencePhysicalBudget
