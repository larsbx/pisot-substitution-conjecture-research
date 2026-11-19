/-
Kernel-checked controls for BargeDiamondBridge. They guard occurrence identity,
prefix counts, endpoint sign, label, orientation and synchronized iterations.
All counterexamples to weakened encodings are outside PIP3; none refutes BD,
the conditional rank theorem, C4 or PSC. No native_decide is used.
-/
import PscVerif.BargeDiamondBridge

namespace Psc.GeometricF.BargeDiamond

open Matrix Psc.Binomial Psc.Incidence
open Psc.StrictSystem (IndexWitness)

/-- Non-vacuity on an actual PIP3 specimen: both images begin in 0. -/
theorem trib_wordConclusion : WordConclusion Psc.Descendants.tribSubst :=
  ⟨0, 1, by decide, 1, 0, by decide⟩

/-- The input to #608 is obtained from the word-level conclusion. -/
theorem trib_hBD : ∃ a b, a ≠ b ∧ VertexCoincident Psc.Descendants.tribSubst a b :=
  wordConclusion_iff_hBD.mp trib_wordConclusion

/-- A matching letter and equal prefix lengths are insufficient: 010/110 has
letter 1 at index 1 on each track, but prefixes [0] and [1]. -/
theorem equal_length_wrong_parikh :
    (power bdSubst 1 0)[1]? = (power bdSubst 1 1)[1]? ∧
      ((power bdSubst 1 0).take 1).length = ((power bdSubst 1 1).take 1).length ∧
      pvec ((power bdSubst 1 0).take 1) ≠ pvec ((power bdSubst 1 1).take 1) ∧
      ¬ IndexWitness bdSubst 0 1 1 1 1 := by decide

/-- The actual second edge begins at +e_0. -/
theorem correct_prefix_offset :
    EdgeDescendant bdSubst 1 (0, 0) (1, pvec [0]) :=
  (edgeDescendant_origin_iff).mpr ⟨[0], [0], by decide, rfl⟩

/-- Reversing the sign of the prefix creates no such descendant. -/
theorem wrong_negative_offset :
    ¬ EdgeDescendant bdSubst 1 (0, 0) (1, -pvec [0]) := by
  intro h
  have hn := edgeDescendant_origin_nonneg h 0
  norm_num [pvec] at hn

/-- Forgetting the prefix offset would falsely put the second edge at zero. -/
theorem wrong_zero_offset : ¬ EdgeDescendant bdSubst 1 (0, 0) (1, 0) := by
  rw [edgeDescendant_origin_zero_iff]
  change ¬ ∃ Q : List (Fin 2), [0, 1, 0] = 1 :: Q
  rintro ⟨Q, hQ⟩
  have he := (List.cons.inj hQ).1
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-- Equal endpoints without a common label do not define coincidence. -/
theorem wrong_matching_label :
    pvec ((power Psc.Binomial.thueMorseSubst 1 0).take 0) =
      pvec ((power Psc.Binomial.thueMorseSubst 1 1).take 0) ∧
      ¬ IndexWitness Psc.Binomial.thueMorseSubst 0 1 1 0 0 := by decide

/-- The published non-Pisot control has suffix coincidence and no prefix
coincidence at ANY level. Replacing the paper's prefix by suffix is unsound. -/
theorem wrong_coincidence_orientation :
    RightStrongCoincidenceWitness bdSubst 0 1 ∧ ¬ VertexCoincident bdSubst 0 1 :=
  ⟨bd_right, bd_not_left⟩

/-- The bad prefix-count control cannot secretly have another common edge. -/
theorem bd_no_shared_descendant (n : ℕ) :
    ¬ ∃ z : IntegralEdge (Fin 2), EdgeDescendant bdSubst n (0, 0) z ∧
      EdgeDescendant bdSubst n (1, 0) z := by
  rintro ⟨z, h0, h1⟩
  exact bd_not_left ⟨n, z, h0, h1⟩

/-- An explicit control for accidentally permitting different iterate levels. -/
def swapSubst : Fin 2 → List (Fin 2) := ![[1], [0]]

theorem swap_power (n : ℕ) :
    (power swapSubst n 0 = [0] ∧ power swapSubst n 1 = [1]) ∨
      (power swapSubst n 0 = [1] ∧ power swapSubst n 1 = [0]) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    have hs (a : Fin 2) : power swapSubst (n + 1) a = subst swapSubst (power swapSubst n a) := by
      exact Function.iterate_succ_apply' (subst swapSubst) n [a]
    rcases ih with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · right
      constructor
      · rw [hs, h0]; rfl
      · rw [hs, h1]; rfl
    · left
      constructor
      · rw [hs, h0]; rfl
      · rw [hs, h1]; rfl

theorem swap_not_vertexCoincident : ¬ VertexCoincident swapSubst 0 1 := by
  rw [edgeCoincident_zero_iff]
  rintro ⟨n, P, Q, P', Q', c, h0, h1, _⟩
  have hm0 : c ∈ power swapSubst n 0 := h0.symm ▸ List.mem_append_right P (List.mem_cons_self)
  have hm1 : c ∈ power swapSubst n 1 := h1.symm ▸ List.mem_append_right P' (List.mem_cons_self)
  rcases swap_power n with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩
  · rw [hp0] at hm0
    rw [hp1] at hm1
    simp only [List.mem_singleton] at hm0 hm1
    exact (by decide : (0 : Fin 2) ≠ 1) (hm0.symm.trans hm1)
  · rw [hp0] at hm0
    rw [hp1] at hm1
    simp only [List.mem_singleton] at hm0 hm1
    exact (by decide : (1 : Fin 2) ≠ 0) (hm0.symm.trans hm1)

/-- Comparing level zero to level one gives a spurious same labelled edge;
synchronized levels never do. This is a nonprimitive permutation control. -/
theorem wrong_iteration_levels :
    (∃ z : IntegralEdge (Fin 2), EdgeDescendant swapSubst 0 (0, 0) z ∧
      EdgeDescendant swapSubst 1 (1, 0) z) ∧ ¬ VertexCoincident swapSubst 0 1 := by
  refine ⟨⟨(0, 0), edgeDescendant_zero _ _, ?_⟩, swap_not_vertexCoincident⟩
  exact edgeDescendant_origin_iff.mpr ⟨[], [], by decide, by simp⟩

/-- Requiring literally identical prefixes is too strong: abelianization may
agree for [0,1] and [1,0]. This three-letter specimen is a scope control. -/
def permutedPrefixSubst : Fin 3 → List (Fin 3) := ![[0, 1, 2], [1, 0, 2], [2]]

theorem permuted_prefixes_are_allowed :
    (power permutedPrefixSubst 1 0).take 2 ≠ (power permutedPrefixSubst 1 1).take 2 ∧
      IndexWitness permutedPrefixSubst 0 1 1 2 2 := by decide

end Psc.GeometricF.BargeDiamond
