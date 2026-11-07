/-
# `K₄ ∈ Lie₄` and `Q₄ S = Φ₄ Q₄` with `Φ₄ = M^{⊗4}|_{Lie₄}`

`docs/c4-concentration-attack-2026-11-06.md` §8;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `thm:defect-intertwiner`
at `r = 4` over three letters: every `K₄(T)` lies in `Lie₄(ℚ³)`, and
`Q₄ S = Φ₄ Q₄` with `Φ₄ = M^{⊗4}|_{Lie₄}`.

The link between `PscVerif.Defect4` (the word-level shuffle relations of `K₄`,
`k4_shuffle_left`, `k4_shuffle_two`, and the column identity `k4_rep`) and
`PscVerif.LieWeights` (Ree's theorem at degree four on three letters), as
`Psc.Lie3.k3Vec_mem_span_lyndon` and `Psc.SignedIntertwiner.q3_col_mem_lie3`
are at degree three.  `α = Fin 3`; `Lie₄` is the span over `ℚ` of the 18
Lyndon brackets `Psc.LieWeights.lyndon4`, and `M = (inc S.s).map Nat.cast` over
`ℚ`.

## Proved here, in full

* `k4Vec u v`: the vector `(K4 u v a b c d)_{abcd}` of `(ℚ³)^{⊗4}`;
  `shuffleAnnih4_k4Vec`: if `Equiv3 u v` it satisfies
  `Psc.LieWeights.ShuffleAnnih4` (its `R1`, `R2` are `k4_shuffle_left`,
  `k4_shuffle_two`); `k4Vec_mem_span_lyndon4`: hence `K₄ ∈ Lie₄`
  (`Psc.LieWeights.shuffleAnnih4_iff_mem_span`).
* `q4_col_mem_lie4`: on a `Psc.SignedCocycle.Normalisation` whose states are
  all `Equiv3`, every column of `Q₄` lies in `Lie₄`.
* `phi4_k4Vec_rep`: `phi4 M (k4Vec j) = Σ_i S i j • k4Vec i` (`k4_rep` over
  `ℚ`), and `phi4Lie_k4Lie`: the same identity for `Φ₄ = phi4Lie M`, the
  restriction of `M^{⊗4}` to `Lie₄`, on the columns `k4Lie j ∈ Lie₄`.  This is
  `Q₄ S = Φ₄ Q₄`, column `j`, with `Φ₄ = M^{⊗4}|_{Lie₄}`.
* Non-vacuity controls: `w4_k4Vec_ne` (`S = (1)`) and `exT_k4Vec_ne`
  (`S = (-1)`, `M` the letter swap): the hypotheses of `q4_col_mem_lie4`,
  `phi4_k4Vec_rep`, `phi4Lie_k4Lie` hold on `Psc.Defect4.w4Norm`,
  `Psc.Defect4.exTNorm` (`w4_equiv3`, `exT_equiv3`), with a nonzero column;
  `exT_phi4Lie`: `Φ₄ K₄(t₃, t̄₃) = - K₄(t₃, t̄₃)` in `Lie₄`.

## Not proved here

* The first-defect selection (the hypotheses are `Equiv3` on every state, not
  that `4` is the least degree with a nonzero defect), and any spectral
  consequence for `Q₄` (`ρ(Φ₄|_{im Q₄}) ≤ β`, `thm:sieve` at `r = 4`).
* Other alphabets: `Lie₄` is only available over `Fin 3`.  None of the
  controls is a PIP specimen.
-/
import PscVerif.Defect4
import PscVerif.LieWeights

namespace Psc.Defect4Lie

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.Defect4 Psc.LieWeights

/-- The degree-four defect of a pair of words over `Fin 3`, as a vector of
`(ℚ³)^{⊗4}` in the word basis. -/
def k4Vec (u v : List (Fin 3)) : Vec4 ℚ := fun a b c d => (K4 u v a b c d : ℚ)

/-- On a 3-binomially equivalent pair, `K₄` satisfies both shuffle relations. -/
theorem shuffleAnnih4_k4Vec {u v : List (Fin 3)} (h : Equiv3 u v) :
    ShuffleAnnih4 (k4Vec u v) := fun a b c d => by
  simp only [k4Vec]
  exact ⟨by exact_mod_cast k4_shuffle_left h a b c d, by exact_mod_cast k4_shuffle_two h a b c d⟩

/-- **`K₄ ∈ Lie₄`** (`thm:defect-intertwiner`, `r = 4`, first assertion). -/
theorem k4Vec_mem_span_lyndon4 {u v : List (Fin 3)} (h : Equiv3 u v) :
    k4Vec u v ∈ Submodule.span ℚ (Set.range (lyndon4 (R := ℚ))) :=
  (shuffleAnnih4_iff_mem_span _).mp (shuffleAnnih4_k4Vec h)

section Rep

variable {S : ChildSystem (Fin 3)} (P : Normalisation S) (hbal : ∀ T ∈ S.C, Equiv3 T.1 T.2)

include hbal in
/-- Every column of `Q₄` lies in `Lie₄`. -/
theorem q4_col_mem_lie4 (j : P.Rep) :
    k4Vec j.1.1 j.1.2 ∈ Submodule.span ℚ (Set.range (lyndon4 (R := ℚ))) :=
  k4Vec_mem_span_lyndon4 (hbal j.1 (P.sub j.2))

include hbal in
/-- **`Q₄ S = M^{⊗4} Q₄` over `ℚ`**, column `j`, in the coordinates of `phi4`. -/
theorem phi4_k4Vec_rep (j : P.Rep) :
    phi4 ((inc S.s).map (Nat.cast : ℕ → ℚ)) (k4Vec j.1.1 j.1.2) =
      ∑ i : P.Rep, (P.Ssign i j : ℚ) • k4Vec i.1.1 i.1.2 := by
  funext a b c d
  simp only [phi4, Matrix.map_apply, k4Vec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact_mod_cast k4_rep P hbal j a b c d

/-- The column `j` of `Q₄` as an element of `Lie₄`. -/
def k4Lie (j : P.Rep) : Submodule.span ℚ (Set.range (lyndon4 (R := ℚ))) :=
  ⟨k4Vec j.1.1 j.1.2, q4_col_mem_lie4 P hbal j⟩

/-- **`Q₄ S = Φ₄ Q₄` with `Φ₄ = M^{⊗4}|_{Lie₄}`** (`thm:defect-intertwiner`,
`r = 4`), column `j`. -/
theorem phi4Lie_k4Lie (j : P.Rep) :
    phi4Lie ((inc S.s).map (Nat.cast : ℕ → ℚ)) (k4Lie P hbal j) =
      ∑ i : P.Rep, (P.Ssign i j : ℚ) • k4Lie P hbal i := by
  apply Subtype.ext
  simp only [phi4Lie, Submodule.coe_sum, Submodule.coe_smul, k4Lie]
  exact phi4_k4Vec_rep P hbal j

end Rep

/-! ### Non-vacuity controls -/

/-- The column of `w4` (`S = (1)`) is a nonzero element of `Lie₄`. -/
theorem w4_k4Vec_ne : k4Vec w4Pair.1 w4Pair.2 ≠ 0 := fun h => by
  have := congrFun (congrFun (congrFun (congrFun h 0) 1) 0) 1
  simp [k4Vec, w4_k4_ne] at this

/-- The column of `exT` (`S = (-1)`) is a nonzero element of `Lie₄`. -/
theorem exT_k4Vec_ne : k4Vec exTPair.1 exTPair.2 ≠ 0 := fun h => by
  have := congrFun (congrFun (congrFun (congrFun h 0) 1) 0) 1
  simp [k4Vec, exT_k4_ne] at this

/-- `phi4Lie_k4Lie` on `exT`: `Φ₄ K₄(t₃, t̄₃) = - K₄(t₃, t̄₃)` in `Lie₄`. -/
theorem exT_phi4Lie :
    phi4Lie ((inc exT.s).map (Nat.cast : ℕ → ℚ)) (k4Lie exTNorm exT_equiv3 exTRep) =
      -k4Lie exTNorm exT_equiv3 exTRep := by
  have : Subsingleton exTNorm.Rep :=
    ⟨fun i j => (exTNorm_rep i).trans (exTNorm_rep j).symm⟩
  rw [phi4Lie_k4Lie, Fintype.sum_subsingleton _ exTRep, exT_ssign, Int.cast_neg, Int.cast_one]
  exact neg_one_smul ℚ (k4Lie exTNorm exT_equiv3 exTRep)

end Psc.Defect4Lie
