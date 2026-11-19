/-
# A PIP3 member with the derived Pisot contraction: Tribonacci

Tribonacci `0 ↦ 01`, `1 ↦ 02`, `2 ↦ 0` (census word `01/02/0`) with incidence matrix
`M = [[1,1,1],[1,0,0],[0,1,0]]` and `χ_M = X³ - X² - X - 1`.

* `tribonacci_mem_PIP3`: it is in the standing class PIP3 — nonerasing, primitive (`M³ > 0`),
  `χ_M` irreducible over `ℚ` (no rational root), and its Perron root `τ ∈ (1, 2)` is Pisot.
* `tribonacciSpectral`: `χ_M = (X - τ) Q` with `Q = X² + (τ - 1) X + (τ² - τ - 1)`,
  `Q(τ) = (3τ + 1)(τ - 1) ≠ 0`, and every complex root of `Q` has `|μ|² = τ² - τ - 1 = 1/τ < 1`.
* `tribonacciSpectralPIP3`: the same hypothesis from the PIP3 conditions alone
  (`SpectralPisot.ofIrreducible`).
* `tribonacciPisot`: the `PisotData` obtained from it by `SpectralPisot.toPisotData`.  The
  contraction is derived, not supplied.

Recognizability, BDS and finite fibres are not discharged here.
-/
import PscVerif.PeriodicPartnerSpectral
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.LinearCombination

namespace Psc.PeriodicPartnerSpectralModels

open Matrix Polynomial Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization
  Psc.PeriodicPartnerSpectral

/-! ## The Tribonacci number -/

theorem exists_root : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 3 - x ^ 2 - x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Set.Icc 1 2) := by fun_prop
  exact intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hc ⟨by norm_num, by norm_num⟩

/-- The real root of `X³ - X² - X - 1` in `[1, 2]`. -/
noncomputable def τ : ℝ := exists_root.choose

theorem τ_cube : τ ^ 3 = τ ^ 2 + τ + 1 := by
  have := exists_root.choose_spec.2; unfold τ; linarith

theorem one_lt_τ : 1 < τ := by
  have h1 : 1 ≤ τ := exists_root.choose_spec.1.1
  refine lt_of_le_of_ne h1 fun h => ?_
  have := τ_cube; rw [← h] at this; norm_num at this

theorem τ_lt_two : τ < 2 := by
  have h2 : τ ≤ 2 := exists_root.choose_spec.1.2
  refine lt_of_le_of_ne h2 fun h => ?_
  have := τ_cube; rw [h] at this; norm_num at this

/-- `τ (τ² - τ - 1) = 1`. -/
theorem τ_mul_t : τ * (τ ^ 2 - τ - 1) = 1 := by linear_combination τ_cube

/-! ## The substitution -/

/-- Tribonacci, `0 ↦ 01`, `1 ↦ 02`, `2 ↦ 0`, with lengths `(τ, τ² - τ, 1)`. -/
noncomputable def tribonacci : LengthSubst (Fin 3) where
  σ := ![[0, 1], [0, 2], [0]]
  ne_nil a := by fin_cases a <;> simp
  ℓ := ![τ, τ ^ 2 - τ, 1]
  ℓ_pos a := by
    have h1 := one_lt_τ
    fin_cases a <;> simp <;> nlinarith
  β := τ
  eigen a := by
    fin_cases a <;> simp
    · ring
    · linear_combination -τ_cube

theorem tribonacci_mat : mat tribonacci = !![1, 1, 1; 1, 0, 0; 0, 1, 0] := by
  ext b a; fin_cases b <;> fin_cases a <;> simp [mat, tribonacci]

theorem tribonacci_charpoly : (mat tribonacci).charpoly = X ^ 3 - X ^ 2 - X - 1 := by
  rw [tribonacci_mat, Matrix.charpoly, det_fin_three]
  simp
  ring

/-! ## Membership in PIP3 -/

theorem tribonacci_primitive : ∀ i j, 0 < ((mat tribonacci) ^ 3) i j := by
  rw [tribonacci_mat]
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

/-- `X³ - X² - X - 1` over `ℚ`. -/
noncomputable def tribPolyℚ : ℚ[X] := X ^ 3 - X ^ 2 - X - 1

theorem tribPolyℚ_natDegree : tribPolyℚ.natDegree = 3 := by
  unfold tribPolyℚ; compute_degree!

theorem tribPolyℚ_no_root (x : ℚ) : ¬ tribPolyℚ.IsRoot x := by
  intro hx
  set p : ℤ[X] := X ^ 3 - X ^ 2 - X - 1
  have hp : p.Monic := by unfold p; monicity!
  have hr : aeval x p = 0 := by
    simpa [p, tribPolyℚ, IsRoot] using hx
  obtain ⟨r, rfl, hr0⟩ := exists_integer_of_is_root_of_monic hp hr
  have hc : p.coeff 0 = -1 := by simp [p]
  rw [hc] at hr0
  have hu : IsUnit r := isUnit_of_dvd_one (by simpa using hr0)
  have hx' : ((r : ℚ)) ^ 3 - (r : ℚ) ^ 2 - r - 1 = 0 := by simpa [tribPolyℚ, IsRoot] using hx
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num at hx'

theorem tribPolyℚ_irreducible : Irreducible tribPolyℚ :=
  irreducible_of_degree_le_three_of_not_isRoot (by simp [tribPolyℚ_natDegree])
    tribPolyℚ_no_root

theorem tribonacci_charpoly_eq_map :
    (mat tribonacci).charpoly = tribPolyℚ.map (algebraMap ℚ ℝ) := by
  simp [tribonacci_charpoly, tribPolyℚ]

/-! ## The spectral factorization -/

/-- The cofactor `Q = X² + (τ - 1) X + (τ² - τ - 1)`. -/
noncomputable def Q : ℝ[X] := X ^ 2 + (C τ - 1) * X + (C τ ^ 2 - C τ - 1)

theorem factor : (mat tribonacci).charpoly = (X - C tribonacci.β) * Q := by
  have h : C τ ^ 3 = C τ ^ 2 + C τ + (1 : ℝ[X]) := by
    simp only [← C_pow, ← C_add, ← C_1, τ_cube]
  rw [tribonacci_charpoly, Q, show tribonacci.β = τ from rfl]
  linear_combination h

theorem Q_eval : Q.eval τ = (3 * τ + 1) * (τ - 1) := by
  simp [Q]; ring

/-- A root of `Q` has `|μ|² = τ² - τ - 1 < 1`: the discriminant `(τ - 1)² - 4/τ` is negative. -/
theorem norm_lt_one_of_root {μ : ℂ} (hμ : (Q.map (algebraMap ℝ ℂ)).IsRoot μ) : ‖μ‖ < 1 := by
  have h : μ ^ 2 + ((τ : ℂ) - 1) * μ + ((τ : ℂ) ^ 2 - τ - 1) = 0 := by
    simpa [Q, IsRoot] using hμ
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have h1 := one_lt_τ
  have h2 := τ_lt_two
  have ht := τ_mul_t
  have hnsq : Complex.normSq μ < 1 := by
    rw [Complex.normSq_apply]
    by_cases hy : μ.im = 0
    · rw [hy] at hre
      nlinarith [sq_nonneg (2 * μ.re + (τ - 1))]
    · have hx : μ.re = -(τ - 1) / 2 := by
        have : μ.im * (2 * μ.re + (τ - 1)) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left hy
        linarith
      rw [hx] at hre ⊢
      nlinarith
  rw [Complex.normSq_eq_norm_sq] at hnsq
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg μ]

/-- The spectral hypothesis for Tribonacci. -/
noncomputable def tribonacciSpectral : SpectralPisot tribonacci where
  Q := Q
  factor := factor
  simple := by
    rw [show tribonacci.β = τ from rfl, Q_eval]
    have := one_lt_τ
    exact mul_ne_zero (by linarith) (by linarith)
  small _ := norm_lt_one_of_root

/-- **Tribonacci is in PIP3**: nonerasing, primitive, irreducible characteristic polynomial over
`ℚ`, Perron root `τ > 1` with every other root in the open unit disc. -/
theorem tribonacci_mem_PIP3 :
    (∀ a, tribonacci.σ a ≠ []) ∧ (∀ i j, 0 < ((mat tribonacci) ^ 3) i j) ∧
      Irreducible tribPolyℚ ∧ (mat tribonacci).charpoly = tribPolyℚ.map (algebraMap ℚ ℝ) ∧
      1 < tribonacci.β ∧ (mat tribonacci).charpoly.IsRoot tribonacci.β ∧
      ∀ μ : ℂ, ((mat tribonacci).charpoly.map (algebraMap ℝ ℂ)).IsRoot μ →
        μ = tribonacci.β ∨ ‖μ‖ < 1 := by
  refine ⟨tribonacci.ne_nil, tribonacci_primitive, tribPolyℚ_irreducible,
    tribonacci_charpoly_eq_map, one_lt_τ, ?_, fun μ hμ => ?_⟩
  · rw [factor]; simp
  · rw [factor, Polynomial.map_mul, IsRoot, eval_mul, mul_eq_zero] at hμ
    rcases hμ with h | h
    · left; simpa [sub_eq_zero] using h
    · exact Or.inr (norm_lt_one_of_root h)

/-- The same hypothesis reached from the PIP3 conditions alone, through
`SpectralPisot.ofIrreducible` (`Q = χ_M /ₘ (X - τ)`). -/
noncomputable def tribonacciSpectralPIP3 : SpectralPisot tribonacci :=
  SpectralPisot.ofIrreducible tribPolyℚ tribPolyℚ_irreducible tribonacci_charpoly_eq_map
    fun μ hμ hne => (tribonacci_mem_PIP3.2.2.2.2.2.2 μ hμ).resolve_left hne

/-- **The derived contraction for a PIP3 member.** -/
noncomputable def tribonacciPisot : PisotData tribonacci := tribonacciSpectralPIP3.toPisotData

end Psc.PeriodicPartnerSpectralModels
