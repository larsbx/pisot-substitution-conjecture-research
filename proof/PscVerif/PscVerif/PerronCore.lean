/-
# Perron core: equality cases of the Perron–Frobenius comparison

`docs/c4-concentration-attack-2026-11-06.md` §§2, 3, 8 use, for a non-negative
matrix `N` with a positive left eigenvector `L` (eigenvalue `β`), the equality
case of the comparison `|μ| |x| = |S x| ≤ |S| |x| ≤ N |x|` for a matrix `S`
dominated entrywise by `N` and an eigenvector `S x = μ x` with `|μ| = β`.
This module proves that equality case from first principles, without invoking
the Perron–Frobenius theorem.

Standing data (each a hypothesis only of the theorems that use it):

* `ι` a finite index type;
* `N : Matrix ι ι ℝ`;
* `hN : ∀ i j, 0 ≤ N i j` — `N` is entrywise non-negative (used by
  `pos_of_eigen`; in the complex statements it follows from the domination
  hypothesis `‖S i j‖ ≤ N i j` and is not assumed separately);
* `L : ι → ℝ` with `hL : ∀ i, 0 < L i` and `hLN : L ᵥ* N = β • L` — a strictly
  positive left eigenvector of `N` for the real number `β`;
* `StronglyConnected N` — every ordered pair `(i, j)` is joined by a directed
  path of positive entries of length `≥ 1` (`Relation.TransGen`), so in
  particular every vertex lies on a cycle.

Proved:

1. `super_eigen_eq`: if `β • v ≤ N *ᵥ v` entrywise then `N *ᵥ v = β • v`.
   (`L ⬝ (N v − β v) = (L N − β L) ⬝ v = 0`, the summands are `≥ 0`, `L > 0`.)
2. `pos_of_eigen`: if `N ≥ 0` is strongly connected, `0 ≤ v`, `N *ᵥ v = β • v`
   and `v ≠ 0`, then every `v i > 0` (a zero coordinate propagates along every
   edge, hence along every `TransGen` path).
3. `norm_eigen`: if `‖S i j‖ ≤ N i j`, `‖μ‖ = β` and `S *ᵥ x = μ • x`, then with
   `w i = ‖x i‖` we have `N *ᵥ w = β • w`, and the triangle inequality is an
   equality row by row: `‖∑ j, S i j * x j‖ = ∑ j, ‖S i j * x j‖`.
   `norm_eigen_pos`: if moreover `N` is strongly connected and `x ≠ 0`, then
   every `‖x i‖ > 0` and `‖S i j‖ = N i j` for all `i, j`.
4. `abs_eigen_real`, `abs_eigen_real_pos`: the specialisation to a real matrix
   `Sr` with `|Sr i j| ≤ N i j`, applied through `Sr.map (↑)`; the conclusion
   `|Sr i j| = N i j` is stated for the real entries.

Not formalized here: the Perron–Frobenius / Wielandt theorems themselves (the
existence of `L`, the identification of `β` as the spectral radius, the
phase/diagonal-similarity conclusion `S = e^{iθ} D N D⁻¹`), and the
substitution-specific matrices of the attack document; those are supplied by
the callers.

Deviations from the original task statement, all of which only weaken
hypotheses: `super_eigen_eq` does not assume `0 ≤ v`, `N ≥ 0` or `β > 0`
(none is needed); no theorem assumes `β > 0`; the complex statements derive
`N ≥ 0` from `‖S i j‖ ≤ N i j` instead of assuming it.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false

namespace Psc.PerronCore

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strong connectivity of the positive-entry digraph of `N`: every ordered pair
is joined by a directed path of length `≥ 1` along positive entries. -/
def StronglyConnected (N : Matrix ι ι ℝ) : Prop :=
  ∀ i j, Relation.TransGen (fun a b => 0 < N a b) i j

/-- **(1)** A super-eigenvector for `β` is an eigenvector, given a strictly
positive left eigenvector `L` for `β`. -/
theorem super_eigen_eq (N : Matrix ι ι ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* N = β • L) (v : ι → ℝ) (hv : β • v ≤ N *ᵥ v) :
    N *ᵥ v = β • v := by
  have hv' : ∀ i, β * v i ≤ (N *ᵥ v) i := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using hv i
  have h1 : L ⬝ᵥ (N *ᵥ v) = (L ᵥ* N) ⬝ᵥ v := dotProduct_mulVec L N v
  rw [hLN] at h1
  have key : ∑ i, L i * ((N *ᵥ v) i - β * v i) = 0 := by
    have h2 : ∑ i, L i * (N *ᵥ v) i = ∑ i, β * L i * v i := by
      simpa [dotProduct, Pi.smul_apply, smul_eq_mul] using h1
    simp only [mul_sub, Finset.sum_sub_distrib, h2]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hL i).le (sub_nonneg.2 (hv' i)))).1 key
  funext i
  rcases mul_eq_zero.1 (hz i (Finset.mem_univ i)) with h | h
  · exact absurd h (hL i).ne'
  · simp only [Pi.smul_apply, smul_eq_mul]
    linarith

/-- A zero coordinate of a non-negative eigenvector of a non-negative matrix
propagates along a positive edge. -/
theorem eq_zero_of_edge (N : Matrix ι ι ℝ) (hN : ∀ i j, 0 ≤ N i j) (β : ℝ) (v : ι → ℝ)
    (hv0 : 0 ≤ v) (hvN : N *ᵥ v = β • v) {a b : ι} (hab : 0 < N a b) (ha : v a = 0) :
    v b = 0 := by
  have hrow : ∑ j, N a j * v j = 0 := by
    have := congrFun hvN a
    simpa [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ha] using this
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hN a j) (hv0 j))).1 hrow b (Finset.mem_univ b)
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hab.ne'
  · exact h

/-- A zero coordinate propagates along any `TransGen` path of positive edges. -/
theorem eq_zero_of_transGen (N : Matrix ι ι ℝ) (hN : ∀ i j, 0 ≤ N i j) (β : ℝ) (v : ι → ℝ)
    (hv0 : 0 ≤ v) (hvN : N *ᵥ v = β • v) {a b : ι}
    (hab : Relation.TransGen (fun a b => 0 < N a b) a b) (ha : v a = 0) : v b = 0 := by
  induction hab with
  | single h => exact eq_zero_of_edge N hN β v hv0 hvN h ha
  | tail _ h ih => exact eq_zero_of_edge N hN β v hv0 hvN h ih

/-- **(2)** A non-zero non-negative eigenvector of a strongly connected
non-negative matrix is strictly positive. -/
theorem pos_of_eigen (N : Matrix ι ι ℝ) (hN : ∀ i j, 0 ≤ N i j) (hSC : StronglyConnected N)
    (β : ℝ) (v : ι → ℝ) (hv0 : 0 ≤ v) (hvN : N *ᵥ v = β • v) (hv : v ≠ 0) :
    ∀ i, 0 < v i := by
  intro i
  rcases (hv0 i).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hv
    funext j
    exact eq_zero_of_transGen N hN β v hv0 hvN (hSC i j) h.symm

/-- The basic row comparison `‖μ‖ ‖x i‖ = ‖(S x) i‖ ≤ ∑ ‖S i j x j‖ ≤ (N |x|) i`. -/
theorem row_chain (N : Matrix ι ι ℝ) (S : Matrix ι ι ℂ) (hS : ∀ i j, ‖S i j‖ ≤ N i j)
    (x : ι → ℂ) (μ : ℂ) (hx : S *ᵥ x = μ • x) (i : ι) :
    ‖μ‖ * ‖x i‖ = ‖∑ j, S i j * x j‖ ∧
      ‖∑ j, S i j * x j‖ ≤ ∑ j, ‖S i j * x j‖ ∧
      ∑ j, ‖S i j * x j‖ ≤ (N *ᵥ fun k => ‖x k‖) i := by
  refine ⟨?_, norm_sum_le _ _, ?_⟩
  · have := congrFun hx i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [this, norm_mul]
  · simp only [mulVec, dotProduct]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hS i j) (norm_nonneg _)

/-- **(3)** Equality case of `|μ| |x| = |S x| ≤ |S| |x| ≤ N |x|`: the modulus
vector `|x|` is a `β`-eigenvector of `N`, and every row of `S x` is an
equality case of the triangle inequality. -/
theorem norm_eigen (N : Matrix ι ι ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℂ) (hS : ∀ i j, ‖S i j‖ ≤ N i j)
    (x : ι → ℂ) (μ : ℂ) (hμ : ‖μ‖ = β) (hx : S *ᵥ x = μ • x) :
    (N *ᵥ fun i => ‖x i‖) = β • (fun i => ‖x i‖) ∧
      ∀ i, ‖∑ j, S i j * x j‖ = ∑ j, ‖S i j * x j‖ := by
  have hw : (N *ᵥ fun i => ‖x i‖) = β • (fun i => ‖x i‖) := by
    apply super_eigen_eq N L hL β hLN
    intro i
    obtain ⟨h1, h2, h3⟩ := row_chain N S hS x μ hx i
    simp only [Pi.smul_apply, smul_eq_mul, ← hμ, h1]
    exact h2.trans h3
  refine ⟨hw, fun i => ?_⟩
  obtain ⟨h1, h2, h3⟩ := row_chain N S hS x μ hx i
  have h4 : (N *ᵥ fun k => ‖x k‖) i = ‖μ‖ * ‖x i‖ := by
    rw [hw, hμ]; simp [Pi.smul_apply, smul_eq_mul]
  rw [h4, h1] at h3
  exact le_antisymm h2 h3

/-- **(3), positive part** Under strong connectivity and `x ≠ 0`, every
coordinate of `x` is non-zero and the domination `‖S i j‖ ≤ N i j` is an
equality everywhere. -/
theorem norm_eigen_pos (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℂ)
    (hS : ∀ i j, ‖S i j‖ ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : S *ᵥ x = μ • x) :
    (∀ i, 0 < ‖x i‖) ∧ ∀ i j, ‖S i j‖ = N i j := by
  have hN : ∀ i j, 0 ≤ N i j := fun i j => (norm_nonneg _).trans (hS i j)
  obtain ⟨hw, htri⟩ := norm_eigen N L hL β hLN S hS x μ hμ hx
  have hpos : ∀ i, 0 < ‖x i‖ := by
    refine pos_of_eigen N hN hSC β (fun i => ‖x i‖) (fun i => norm_nonneg _) hw ?_
    intro h
    apply hx0
    funext i
    exact norm_eq_zero.1 (congrFun h i)
  refine ⟨hpos, fun i j => ?_⟩
  obtain ⟨h1, h2, h3⟩ := row_chain N S hS x μ hx i
  have h4 : (N *ᵥ fun k => ‖x k‖) i = ‖μ‖ * ‖x i‖ := by
    rw [hw, hμ]; simp [Pi.smul_apply, smul_eq_mul]
  have heq : ∑ k, ‖S i k * x k‖ = ∑ k, N i k * ‖x k‖ := by
    have : (N *ᵥ fun k => ‖x k‖) i = ∑ k, N i k * ‖x k‖ := by simp [mulVec, dotProduct]
    rw [← this]
    apply le_antisymm h3
    rw [h4, h1]; exact h2
  have hsum : ∑ k, (N i k - ‖S i k‖) * ‖x k‖ = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← heq, norm_mul, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_nonneg (sub_nonneg.2 (hS i k)) (norm_nonneg _))).1 hsum j
    (Finset.mem_univ j)
  rcases mul_eq_zero.1 hz with h | h
  · linarith
  · exact absurd h (hpos j).ne'

/-- **(4)** Real specialisation of `norm_eigen`: a real matrix `Sr` with
`|Sr i j| ≤ N i j`, viewed over `ℂ`. -/
theorem abs_eigen_real (N : Matrix ι ι ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* N = β • L) (Sr : Matrix ι ι ℝ) (hS : ∀ i j, |Sr i j| ≤ N i j)
    (x : ι → ℂ) (μ : ℂ) (hμ : ‖μ‖ = β) (hx : Sr.map (↑) *ᵥ x = μ • x) :
    (N *ᵥ fun i => ‖x i‖) = β • (fun i => ‖x i‖) ∧
      ∀ i, ‖∑ j, (Sr i j : ℂ) * x j‖ = ∑ j, ‖(Sr i j : ℂ) * x j‖ := by
  have hS' : ∀ i j, ‖(Sr.map ((↑) : ℝ → ℂ)) i j‖ ≤ N i j := fun i j => by
    simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hS i j
  simpa [Matrix.map_apply] using norm_eigen N L hL β hLN _ hS' x μ hμ hx

/-- **(4), positive part** Real specialisation of `norm_eigen_pos`. -/
theorem abs_eigen_real_pos (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (Sr : Matrix ι ι ℝ)
    (hS : ∀ i j, |Sr i j| ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : Sr.map (↑) *ᵥ x = μ • x) :
    (∀ i, 0 < ‖x i‖) ∧ ∀ i j, |Sr i j| = N i j := by
  have hS' : ∀ i j, ‖(Sr.map ((↑) : ℝ → ℂ)) i j‖ ≤ N i j := fun i j => by
    simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hS i j
  obtain ⟨h1, h2⟩ := norm_eigen_pos N hSC L hL β hLN _ hS' x hx0 μ hμ hx
  refine ⟨h1, fun i j => ?_⟩
  simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using h2 i j

/-! ### Real eigenvectors (shared by `Wielandt` and `PerronSimple`) -/

section Real

variable (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
  (β : ℝ) (hLA : L ᵥ* A = β • L)

include hA hL hLA in
/-- A strictly positive left eigenvector of a non-negative matrix has
eigenvalue `β ≥ 0` (when `ι` is non-empty). -/
theorem beta_nonneg (i : ι) : 0 ≤ β := by
  have h := congrFun hLA i
  simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  have h0 : 0 ≤ ∑ j, L j * A j i :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hL j).le (hA j i))
  by_contra hb
  replace hb := not_le.1 hb
  have : β * L i < 0 := mul_neg_of_neg_of_pos hb (hL i)
  linarith

include hA hL hLA in
/-- The modulus of a real `β`-eigenvector is a `β`-eigenvector. -/
theorem abs_eigen (hβ : 0 ≤ β) (w : ι → ℝ) (hw : A *ᵥ w = β • w) :
    A *ᵥ (fun i => |w i|) = β • (fun i => |w i|) := by
  apply super_eigen_eq A L hL β hLA
  intro i
  have h := congrFun hw i
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h ⊢
  calc β * |w i| = |β * w i| := by rw [abs_mul, abs_of_nonneg hβ]
    _ = |∑ j, A i j * w j| := by rw [h]
    _ ≤ ∑ j, |A i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, A i j * |w j| := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hA i j)]

include hA hL hLA in
/-- Every non-zero real `β`-eigenvector of a strongly connected non-negative
matrix with a positive left `β`-eigenvector has full support. -/
theorem full_support (hSC : StronglyConnected A) (hβ : 0 ≤ β) (w : ι → ℝ)
    (hw : A *ᵥ w = β • w) (hw0 : w ≠ 0) : ∀ i, 0 < |w i| := by
  refine pos_of_eigen A hA hSC β _ (fun i => abs_nonneg _)
    (abs_eigen A hA L hL β hLA hβ w hw) ?_
  intro h
  apply hw0
  funext i
  exact abs_eq_zero.1 (congrFun h i)

end Real

end Psc.PerronCore
