/-
# Controls for the geometric realization

Exact instances and failures for the hypotheses of `PeriodicPartnerRealization`:

* `thueMorsePisot`: the contraction input holds for Thue--Morse (`ker ℓ` is killed by `M`);
  `thueMorse_torusMap_not_injective`: its torus endomorphism is not injective (`det M = 0`), so
  the torus map alone has no invertible target and the solenoid is needed.
* `fibonacciPisot`: the contraction input for Fibonacci, `ρ = |ψ|`;
  `fibonacci_torusMap_injective`: the unit case, in which the solenoid's first coordinate is
  already injective (`coord_zero_injective`).
* `doubled_not_pisot`: for `0 ↦ 011`, `1 ↦ 100` (`β = 3`, second eigenvalue `-1`) no
  `PisotData` exists.  The contraction is a genuine restriction.

None of these instances discharges recognizability, BDS or finite fibres, and none is a PIP3
member.  Thue--Morse is not irreducible Pisot.
-/
import PscVerif.PeriodicPartnerRealization
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

namespace Psc.PeriodicPartnerRealizationModels

open Function Filter Matrix Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
  Psc.PeriodicPartnerRealization
open scoped Topology goldenRatio

/-- An eigenvector of `M` is an eigenvector of its powers. -/
theorem pow_mulVec_of_eigen {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℝ}
    {v : α → ℝ} {c : ℝ} (h : A *ᵥ v = c • v) (n : ℕ) : (A ^ n) *ᵥ v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ, mul_comm]

/-! ## Thue--Morse: nonunit -/

theorem thueMorse_mat : mat thueMorse = !![1, 1; 1, 1] := by
  ext b a; fin_cases b <;> fin_cases a <;> simp [mat, thueMorse]

theorem thueMorse_mulVec (v : Fin 2 → ℝ) :
    mat thueMorse *ᵥ v = ![v 0 + v 1, v 0 + v 1] := by
  ext b; fin_cases b <;> simp [thueMorse_mat, mulVec, dotProduct, Fin.sum_univ_two]

theorem thueMorse_dot (v : Fin 2 → ℝ) : thueMorse.ℓ ⬝ᵥ v = v 0 + v 1 := by
  simp [dotProduct, Fin.sum_univ_two, thueMorse]

/-- Thue--Morse satisfies the contraction input with `C = 1`, `ρ = 0`. -/
noncomputable def thueMorsePisot : PisotData thueMorse where
  u := ![1 / 2, 1 / 2]
  u_eigen := by
    rw [thueMorse_mulVec]; ext b; fin_cases b <;> simp [thueMorse] <;> norm_num
  dot_u := by rw [thueMorse_dot]; norm_num
  C := 1
  C_nonneg := zero_le_one
  ρ := 0
  ρ_nonneg := le_rfl
  ρ_lt_one := zero_lt_one
  contract v hv n := by
    rw [thueMorse_dot] at hv
    cases n with
    | zero => simp
    | succ n =>
      have h0 : mat thueMorse *ᵥ v = 0 := by
        rw [thueMorse_mulVec, hv]; ext b; fin_cases b <;> rfl
      rw [pow_succ, ← mulVec_mulVec, h0, mulVec_zero]
      simp

theorem half_not_int : (1 / 2 : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨n, hn⟩
  have h1 : (0 : ℝ) < n := by rw [hn]; norm_num
  have h2 : (n : ℝ) < 1 := by rw [hn]; norm_num
  have : (0 : ℤ) < n := by exact_mod_cast h1
  have : n < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- The Thue--Morse torus endomorphism identifies `(1/2, 0)` and `(0, 1/2)`. -/
theorem thueMorse_torusMap_not_injective : ¬ Injective (torusMap thueMorse) := by
  intro h
  have heq : torusMap thueMorse ((![1 / 2, 0] : Fin 2 → ℝ) : Torus (Fin 2)) =
      torusMap thueMorse ((![0, 1 / 2] : Fin 2 → ℝ) : Torus (Fin 2)) := by
    rw [torusMap_mk, torusMap_mk, thueMorse_mulVec, thueMorse_mulVec]
    simp
  have hmem := QuotientAddGroup.eq.mp (h heq)
  obtain ⟨n, hn⟩ := hmem 1
  exact half_not_int ⟨n, by rw [hn]; simp⟩

/-! ## Fibonacci: unit -/

/-- Fibonacci, `0 ↦ 01`, `1 ↦ 0`, with lengths `(φ, 1)` and `β = φ`. -/
noncomputable def fibonacci : LengthSubst (Fin 2) where
  σ := ![[0, 1], [0]]
  ne_nil a := by fin_cases a <;> simp
  ℓ := ![φ, 1]
  ℓ_pos a := by fin_cases a <;> simp; positivity
  β := φ
  eigen a := by
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, List.map_cons, List.map_nil,
        Matrix.cons_val_one, List.sum_cons, List.sum_nil, add_zero]
      nlinarith [Real.goldenRatio_sq]
    · simp

theorem fibonacci_mat : mat fibonacci = !![1, 1; 1, 0] := by
  ext b a; fin_cases b <;> fin_cases a <;> simp [mat, fibonacci]

theorem fibonacci_mulVec (v : Fin 2 → ℝ) : mat fibonacci *ᵥ v = ![v 0 + v 1, v 0] := by
  ext b; fin_cases b <;> simp [fibonacci_mat, mulVec, dotProduct, Fin.sum_univ_two]

theorem fibonacci_dot (v : Fin 2 → ℝ) : fibonacci.ℓ ⬝ᵥ v = φ * v 0 + v 1 := by
  simp [dotProduct, Fin.sum_univ_two, fibonacci]

/-- Fibonacci satisfies the contraction input with `C = 1`, `ρ = |ψ|`: on `ker ℓ` the matrix
acts as multiplication by `ψ`. -/
noncomputable def fibonacciPisot : PisotData fibonacci where
  u := (φ ^ 2 + 1)⁻¹ • ![φ, 1]
  u_eigen := by
    have hβ : fibonacci.β = φ := rfl
    rw [mulVec_smul, fibonacci_mulVec, hβ, smul_comm]
    congr 1
    have h : φ + 1 = φ * φ := by nlinarith [Real.goldenRatio_sq]
    ext b; fin_cases b
    · change φ + 1 = φ * φ
      exact h
    · change φ = φ * 1
      ring
  dot_u := by
    rw [fibonacci_dot]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
  C := 1
  C_nonneg := zero_le_one
  ρ := |ψ|
  ρ_nonneg := abs_nonneg _
  ρ_lt_one := abs_lt.mpr ⟨Real.neg_one_lt_goldenConj, by linarith [Real.goldenConj_neg]⟩
  contract v hv n := by
    rw [fibonacci_dot] at hv
    have heig : mat fibonacci *ᵥ v = ψ • v := by
      rw [fibonacci_mulVec]
      have hv1 : v 1 = -(φ * v 0) := by linarith
      ext b; fin_cases b
      · change v 0 + v 1 = ψ * v 0
        rw [hv1]
        linear_combination (-(v 0)) * Real.goldenRatio_add_goldenConj
      · change v 0 = ψ * v 1
        rw [hv1]
        linear_combination (v 0) * Real.goldenConj_mul_goldenRatio
    rw [pow_mulVec_of_eigen heig, norm_smul, norm_pow, Real.norm_eq_abs, one_mul]

/-- Fibonacci is unimodular: its torus endomorphism is injective. -/
theorem fibonacci_torusMap_injective : Injective (torusMap fibonacci) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using QuotientAddGroup.induction_on with
  | H v =>
    rw [torusMap_mk, QuotientAddGroup.eq_zero_iff, fibonacci_mulVec] at hz
    obtain ⟨m, hm⟩ := hz 0
    obtain ⟨n, hn⟩ := hz 1
    refine (QuotientAddGroup.eq_zero_iff _).mpr fun b => ?_
    fin_cases b
    · exact ⟨n, hn⟩
    · refine ⟨m - n, ?_⟩
      change ((m - n : ℤ) : ℝ) = v 1
      change (m : ℝ) = v 0 + v 1 at hm
      change (n : ℝ) = v 0 at hn
      push_cast
      linarith

/-- In the Fibonacci (unit) case the solenoid is the torus. -/
theorem fibonacci_coord_zero_injective :
    Injective fun z : Solenoid fibonacci => z.1 0 :=
  coord_zero_injective fibonacci fibonacci_torusMap_injective

/-! ## A non-Pisot control: the contraction fails -/

/-- `0 ↦ 011`, `1 ↦ 100` with unit lengths: `β = 3`, and `M` acts as `-1` on `ker ℓ`. -/
def doubled : LengthSubst (Fin 2) where
  σ := ![[0, 1, 1], [1, 0, 0]]
  ne_nil a := by fin_cases a <;> simp
  ℓ _ := 1
  ℓ_pos _ := one_pos
  β := 3
  eigen a := by fin_cases a <;> norm_num

theorem doubled_mulVec (v : Fin 2 → ℝ) : mat doubled *ᵥ v = ![v 0 + 2 * v 1, 2 * v 0 + v 1] := by
  have : mat doubled = !![1, 2; 2, 1] := by
    ext b a; fin_cases b <;> fin_cases a <;> simp [mat, doubled]
  ext b; fin_cases b <;> simp [this, mulVec, dotProduct, Fin.sum_univ_two]

/-- No contraction input exists for `doubled`: `‖Mⁿ (1, -1)‖ = 1` for every `n`. -/
theorem doubled_not_pisot : IsEmpty (PisotData doubled) := by
  refine ⟨fun P => ?_⟩
  set v : Fin 2 → ℝ := ![1, -1]
  have hv : doubled.ℓ ⬝ᵥ v = 0 := by simp [dotProduct, Fin.sum_univ_two, doubled, v]
  have heig : mat doubled *ᵥ v = (-1 : ℝ) • v := by
    rw [doubled_mulVec]; ext b; fin_cases b <;> simp [v] <;> norm_num
  have hnorm : ‖v‖ = 1 := by
    simp [v, Pi.norm_def, Fin.univ_succ]
  have hlim : Tendsto (fun n : ℕ => P.C * P.ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one P.ρ_nonneg P.ρ_lt_one).const_mul P.C
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  have := P.contract v hv n
  rw [pow_mulVec_of_eigen heig, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    hnorm, mul_one] at this
  linarith

end Psc.PeriodicPartnerRealizationModels
