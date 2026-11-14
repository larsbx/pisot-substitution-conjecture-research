import PscVerif.NamedCutNeighborhood
import PscVerif.NamedGeometricEnclosure
import PscVerif.StrictCutCount

/-! The finite integer count and open-neighborhood capture use the same starts. -/

namespace Psc.NamedCutCount

open Psc.Binomial Psc.Descendants Psc.Reduction
open Psc.OccurrenceTransport Psc.OccurrenceNewborn Psc.OccurrenceInverse
open Psc.OccurrenceResidue Psc.PrefixAddress Psc.StablePrefixWindow
open Psc.PrefixClosure Psc.NamedPrefixCompact
open Psc.NamedStableChart Psc.NamedGeometricEnclosure Psc.NamedCutNeighborhood
open Psc.StrictCutCount
open scoped Topology

private theorem physicalLength_iterate (fixture : Fin 2) (k : ℕ) (w : Word) :
    physicalLength physicalRow ((subst (substitution fixture))^[k] w) =
      beta ^ k * physicalLength physicalRow w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', physicalLength_subst, ih, pow_succ]
    ring

/-- Original integer prefix vectors at all reduction factor starts. -/
def integerStarts (fixture : Fin 2) (n : ℕ) (T : WordPair) : Finset (Fin 3 → ℤ) :=
  startVectors (red ((subst (substitution fixture))^[12 * n] T.1)
    ((subst (substitution fixture))^[12 * n] T.2))

/-- A uniform upper bound on the carrier's factor lengths gives the finite
lower count. The same integer vectors lie in the physical strip. -/
theorem integerStarts_count_and_strip (fixture : Fin 2) {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    (L : ℝ) (hL : ∀ B ∈ C, physicalLength physicalRow B.1 ≤ L)
    (n : ℕ) {T : WordPair} (hT : T ∈ C) :
    let X := beta ^ (12 * n) * physicalLength physicalRow T.1
    X ≤ L * ((integerStarts fixture n T).card : ℝ) ∧
      ∀ z ∈ integerStarts fixture n T, 0 ≤ offset physicalRow z ∧ offset physicalRow z < X := by
  dsimp only
  rw [← physicalLength_iterate fixture]
  have hbal := equiv1_iterate_subst (substitution fixture) (12 * n) (strict.equiv1 T hT)
  exact ⟨physicalLength_le_card_reduction_starts physicalRow L hbal
    (fun B hB => hL B (strict.mem_of_red_iterate (12 * n) T hT B hB)),
    fun z hz => offset_mem_strip_of_mem physicalRow physical_row_pos hbal hz⟩

/-- One threshold captures the images of the counted integer starts, uniformly
over the fixed carrier. -/
theorem eventually_integerStarts_mem (fixture : Fin 2) {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    (U : Set (Ambient (substitution fixture) Stable)) (hU : IsOpen U)
    (covered : carrierOverlap fixture C ⊆ U) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T ∈ C, ∀ z ∈ integerStarts fixture n T,
      ambientStar (substitution fixture) piZ z ∈ U := by
  obtain ⟨N, hN⟩ := eventually_carrierOverlap_strict_cuts_mem fixture strict U hU covered
  refine ⟨N, ?_⟩
  intro n hn T hT z hz
  have hbal := equiv1_iterate_subst (substitution fixture) (12 * n) (strict.equiv1 T hT)
  obtain ⟨top, bottom, ht, hb⟩ := exists_balanced_marks_of_mem hbal hz
  have capture := hN n hn T hT
  rw [subst_iterateImages] at capture
  simpa only [ht] using capture top bottom (ht.trans hb.symm)

end Psc.NamedCutCount
