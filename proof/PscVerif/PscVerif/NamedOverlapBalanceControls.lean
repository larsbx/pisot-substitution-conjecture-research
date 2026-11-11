import PscVerif.OccurrencePhysicalBudget
import Mathlib.Tactic.FinCases

/-!
# Direct controls for the named overlap balance adapter

These controls guard the new literal-count interface rather than substitute
finite experiments for the named geometric theorem. The identity power has
no loss; two different literal positions with the same target remain two
occurrences. Separate scalar witnesses retain the strict physical-positivity
and transpose-budget premises of the saturation argument.

Pre-code gate: `docs/c4-named-overlap-balance-literature-2026-11-11.md`.
-/

namespace Psc.NamedOverlapBalanceControls

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceFinite
open Psc.OccurrenceMass Psc.OccurrencePhysicalBudget
open PscVerif.OccurrenceMassCounts PscVerif.PhysicalMass
open scoped BigOperators

/-- The identity substitution power keeps the complete packet, including
its integral displacement. -/
theorem zero_power_digitPacket (s : Fin 3 → Word) (p : Packet)
    (i : Fin ((iterateImages s 0) p.top).length)
    (j : Fin ((iterateImages s 0) p.bottom).length) :
    digitPacket (iterateImages s 0) p i j = p := by
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp only [digitPacket, incidenceZ_iterateImages, pow_zero, Matrix.one_mulVec]
  apply packet_ext <;> simp [iterateImages, markAt, residual, parikhZ]

/-- Zero block power is the identity count matrix on any represented domain.
It cannot manufacture a strict physical loss. -/
theorem zero_power_inverseCounts (s : Fin 3 → Word) (S : Finset Packet)
    (p u : State S) :
    inverseCounts (iterateImages s 0) S p u = if p = u then 1 else 0 := by
  classical
  unfold inverseCounts rowCount
  simp only [zero_power_digitPacket]
  by_cases h : p = u
  · subst p
    simp [Positions, iterateImages]
  · have hval : u.val ≠ p.val := fun he => h (Subtype.ext he.symm)
    simp [h, hval]

theorem zero_power_deficit (s : Fin 3 → Word) (S : Finset Packet)
    (h : State S → ℝ) (p : State S) :
    deficit (inverseCounts (iterateImages s 0) S) h 1 p = 0 := by
  classical
  simp [deficit, transposeAction, zero_power_inverseCounts]

/-- A constant doubled image gives two distinct diagonal positional pairs. -/
def repeatedImages (_a : Fin 3) : Word := [0, 0]

def diagonal : Packet := ⟨0, 0, 0⟩

def repeatedForward (i : Fin 2) : ForwardOccurrence repeatedImages diagonal diagonal where
  topIndex := i
  bottomIndex := i
  packet_eq := by
    fin_cases i <;>
      apply packet_ext <;>
      simp [digitPacket, repeatedImages, diagonal, markAt, residual, parikhZ]

def repeatedInverse (i : Fin 2) : InverseOccurrence repeatedImages diagonal diagonal :=
  (repeatedForward i).toInverse

theorem repeatedInverse_injective : Function.Injective repeatedInverse := by
  intro i j hij
  have h := congrArg (fun e : InverseOccurrence repeatedImages diagonal diagonal =>
    e.toForward.topIndex) hij
  simpa [repeatedInverse, repeatedForward] using h

/-- Deduplicating by the endpoint would change this genuine literal count. -/
theorem repeated_inverse_count_at_least_two (S : Finset Packet) (hp : diagonal ∈ S) :
    2 ≤ inverseCounts repeatedImages S ⟨diagonal, hp⟩ ⟨diagonal, hp⟩ := by
  rw [inverseCounts_eq_card]
  have h := Fintype.card_le_of_injective repeatedInverse repeatedInverse_injective
  norm_num only [Fintype.card_fin] at h
  exact_mod_cast h

theorem repeated_inverse_count_not_endpoint_support (S : Finset Packet)
    (hp : diagonal ∈ S) :
    inverseCounts repeatedImages S ⟨diagonal, hp⟩ ⟨diagonal, hp⟩ ≠ 1 := by
  have h := repeated_inverse_count_at_least_two S hp
  linarith

/-- Nonnegative physical weights alone can hide positive recurrence slack. -/
theorem zero_physical_weight_does_not_force_balance :
    (∀ i : Fin 1, (0 : ℝ) ≤ 0) ∧
    (∀ i : Fin 1, (1 : ℝ) * 1 ≤ action (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 1) i) ∧
    (∀ i : Fin 1, transposeAction (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 0) i ≤ 1 * 0) ∧
    action (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 1) 0 ≠ 1 * 1 := by
  norm_num [action, transposeAction]

/-- A cover bound without the physical transpose budget cannot give equality. -/
theorem missing_budget_does_not_force_balance :
    (∀ i : Fin 1, (0 : ℝ) < 1) ∧
    (∀ i : Fin 1, (1 : ℝ) * 1 ≤ action (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 1) i) ∧
    ¬ (∀ i : Fin 1, transposeAction (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 1) i ≤ 1 * 1) ∧
    action (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ => 1) 0 ≠ 1 * 1 := by
  norm_num [action, transposeAction]

/-- An exact conservative recurrence still permits the all-zero overlap. -/
theorem conservation_does_not_supply_positive_overlap :
    (∀ i : Fin 1, transposeAction (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ => 1) i = 1) ∧
    (∀ i : Fin 1, action (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ => 0) i = 1 * 0) ∧
    ¬ (∃ i : Fin 1, (0 : ℝ) < 0) := by
  norm_num [action, transposeAction]

end Psc.NamedOverlapBalanceControls
