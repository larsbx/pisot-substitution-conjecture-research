/-
# No strict systems for an unbounded companion family

Bridge the explicit literal witnesses in `EvenCompanionWords` to the existing
`StrictSystem` definitions and its cut-pair exclusion theorem. For every
`r >= 3`, all letter pairs in `(1,2,100 2^r 1)` have left strong coincidence.
The conclusion quantifies over arbitrary finite strict systems; no Pisot,
coincidence-rank, tiling, recognizability or finite-fibre hypothesis is used.
-/
import PscVerif.EvenCompanionWords
import PscVerif.StrictSystemCore

namespace Psc.EvenCompanion

open Psc.Binomial Psc.StrictSystem

/-- The periodic first-letter pair has a level-three witness. -/
theorem pair_one_two (r : ℕ) (hr : 3 ≤ r) : WitnessAt (sigma r) 1 2 3 := by
  obtain ⟨u, v, hu, hv, hbal⟩ := level_three_witness r hr
  exact ⟨topPrefix r, u, bottomPrefix r, v, 2, hu, hv, hbal⟩

/-- The two images begin in the same letter, so empty prefixes witness
coincidence immediately. -/
theorem pair_zero_two (r : ℕ) : WitnessAt (sigma r) 0 2 1 := by
  refine ⟨[], [], [], [0, 0] ++ List.replicate r 2 ++ [1], 1, ?_, ?_, ?_⟩
  · simp [subst, sigma]
  · simp [subst, sigma, word]
  · intro a; rfl

/-- Applying the substitution once changes `(0,1)` into `(1,2)`. -/
theorem pair_zero_one (r : ℕ) (hr : 3 ≤ r) : WitnessAt (sigma r) 0 1 4 := by
  obtain ⟨P, u, Q, v, a, hu, hv, hbal⟩ := pair_one_two r hr
  have hz : (subst (sigma r))^[4] [0] = (subst (sigma r))^[3] [1] := by
    rw [show 4 = 3 + 1 from rfl, Function.iterate_succ_apply]
    simp [subst, sigma]
  have ho : (subst (sigma r))^[4] [1] = (subst (sigma r))^[3] [2] := by
    rw [show 4 = 3 + 1 from rfl, Function.iterate_succ_apply]
    simp [subst, sigma]
  exact ⟨P, u, Q, v, a, hz.trans hu, ho.trans hv, hbal⟩

/-- All six ordered pairs of distinct letters have a literal witness. -/
theorem all_pairs (r : ℕ) (hr : 3 ≤ r) :
    ∀ a b, a ≠ b → StrongCoincidenceWitness (sigma r) a b := by
  apply fin3_all_pairs
  · exact strongCoincidenceWitness_iff_exists_witnessAt.mpr ⟨4, pair_zero_one r hr⟩
  · exact strongCoincidenceWitness_iff_exists_witnessAt.mpr ⟨1, pair_zero_two r⟩
  · exact strongCoincidenceWitness_iff_exists_witnessAt.mpr ⟨3, pair_one_two r hr⟩

/-- Uniform C4 exclusion for this explicit family, with no geometric imports
among the theorem's assumptions. This is not a statement for arbitrary
nilpotent cubic substitutions or a pure discrete spectrum theorem. -/
theorem no_strict_system (r : ℕ) (hr : 3 ≤ r) (C : Finset (Word × Word)) :
    ¬ StrictSystem (sigma r) C :=
  no_strictSystem_of_strongCoincidence (all_pairs r hr) C

/-- The even parameters lie in the range of the same unbounded theorem. -/
theorem no_strict_system_even (n : ℕ) (C : Finset (Word × Word)) :
    ¬ StrictSystem (sigma (2 * n + 4)) C :=
  no_strict_system _ (by omega) C

end Psc.EvenCompanion
