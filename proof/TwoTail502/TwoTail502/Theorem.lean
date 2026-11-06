import TwoTail502.Prefixes

namespace TwoTail502
open Letter Tail

theorem simultaneous_pairwise (σ : Substitution) (n : ℕ) (p q : Word)
    (hb : Balanced p q) (hp : (p ++ [o]).IsPrefix (iterate σ n [z]))
    (hq1 : (q ++ [o]).IsPrefix (iterate σ n [o]))
    (hq2 : (q ++ [o]).IsPrefix (iterate σ n [t])) : PairwiseAt σ n := by
  let pre : Letter → Word := fun c => match c with | z => p | _ => q
  have hm (i j : Letter) : Balanced (pre i) (pre j) := by
    cases i <;> cases j <;> first | exact rfl | exact hb | exact hb.symm
  have hw (i : Letter) : (pre i ++ [o]).IsPrefix (iterate σ n [i]) := by
    cases i
    · exact hp
    · exact hq1
    · exact hq2
  intro i j
  exact ⟨pre i,pre j,o,hm i j,hw i,hw j⟩

theorem positive102_pairwise4 (k b : ℕ) : PairwiseAt (source t102 (k+1) b) 4 := by
  have hp := positive102_prefixes k b
  have h := level_four t102 (k+1) b
  exact simultaneous_pairwise _ _ _ _ (positive102_mass (k+1) b)
    (h.1.symm ▸ hp.1) (h.2.1.symm ▸ hp.2.1) (h.2.2.symm ▸ hp.2.2)

theorem positive120_pairwise4 (k b : ℕ) : PairwiseAt (source t120 (k+1) b) 4 := by
  have hp := positive120_prefixes k b
  have h := level_four t120 (k+1) b
  exact simultaneous_pairwise _ _ _ _ (positive120_mass (k+1) b)
    (h.1.symm ▸ hp.1) (h.2.1.symm ▸ hp.2.1) (h.2.2.symm ▸ hp.2.2)

theorem pairwise_from_three (σ : Substitution) (hne : Nonerasing σ) (n : ℕ)
    (h01 : SourceWitness σ n z o) (h02 : SourceWitness σ n z t)
    (h12 : SourceWitness σ n o t) : PairwiseAt σ n := by
  intro i j
  cases i <;> cases j
  · exact witness_refl (iterate_nonerasing σ hne n (by decide : [z] ≠ []))
  · exact h01
  · exact h02
  · exact witness_symm h01
  · exact witness_refl (iterate_nonerasing σ hne n (by decide : [o] ≠ []))
  · exact h12
  · exact witness_symm h02
  · exact witness_symm h12
  · exact witness_refl (iterate_nonerasing σ hne n (by decide : [t] ≠ []))

theorem boundary120_pairwise5 (k : ℕ) : PairwiseAt (source t120 0 (k+1)) 5 := by
  have hn := source_nonerasing t120 0 (k+1)
  exact pairwise_from_three _ hn 5
    (source_propagate _ hn (by decide : 4 ≤ 5) (boundary120_pair01 k))
    (boundary120_pair02 k)
    (source_propagate _ hn (by decide : 3 ≤ 5) (boundary120_pair12 k))

theorem boundary102_pair12 (k : ℕ) : SourceWitness (source t102 0 (k+1)) 5 o t := by
  cases k with
  | zero =>
    exact source_propagate _ (source_nonerasing t102 0 1)
      (by decide : 4 ≤ 5) exceptional102_b1
  | succ l =>
    cases l with
    | zero =>
      exact source_propagate _ (source_nonerasing t102 0 2)
        (by decide : 4 ≤ 5) exceptional102_b2
    | succ m => exact large102_pair12 m

theorem boundary102_pairwise5 (k : ℕ) : PairwiseAt (source t102 0 (k+1)) 5 := by
  have hn := source_nonerasing t102 0 (k+1)
  exact pairwise_from_three _ hn 5
    (source_propagate _ hn (by decide : 2 ≤ 5) (boundary102_pair01 (k+1)))
    (source_propagate _ hn (by decide : 2 ≤ 5) (boundary102_pair02 k))
    (boundary102_pair12 k)

/-- PR502's parameter-uniform source-letter theorem, with literal tail order. -/
theorem uniform_pairwise_five (tail : Tail) (a b : ℕ) (hab : 1 ≤ a+b) :
    PairwiseAt (source tail a b) 5 := by
  cases a with
  | zero =>
    cases b with
    | zero => omega
    | succ k =>
      cases tail with
      | t102 => exact boundary102_pairwise5 k
      | t120 => exact boundary120_pairwise5 k
  | succ k =>
    have hp : PairwiseAt (source tail (k+1) b) 4 := by
      cases tail with
      | t102 => exact positive102_pairwise4 k b
      | t120 => exact positive120_pairwise4 k b
    intro i j
    exact source_propagate _ (source_nonerasing tail (k+1) b)
      (by decide : 4 ≤ 5) (hp i j)

/-- Every nonempty balanced root has a literal singleton diagonal after five
inflations. The prefixes and suffixes on both sides are balanced. -/
theorem uniform_balanced_root_productivity (tail : Tail) (a b : ℕ) (hab : 1 ≤ a+b)
    (u v : Word) (hu : u ≠ []) (hv : v ≠ []) (hb : Balanced u v) :
    DiagonalFactor (iterate (source tail a b) 5 u) (iterate (source tail a b) 5 v) :=
  pairwise_diagonal_productivity _ 5 (uniform_pairwise_five tail a b hab) hu hv hb

#print axioms uniform_pairwise_five
#print axioms uniform_balanced_root_productivity
end TwoTail502
