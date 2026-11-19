/-
# The Pisot contraction from the characteristic polynomial

`PeriodicPartnerRealization` takes the contraction of `M` on `ker ℓ` as a field of `PisotData`.
This module derives it.  The input `SpectralPisot S` is a factorization

  `χ_M = (X - β) · Q`,   `Q(β) ≠ 0`,   every complex root of `Q` has modulus `< 1`,

which is what "`β` is a Pisot number and `χ_M` is its minimal polynomial up to the factor" says
for a primitive irreducible Pisot substitution.  From it:

* `u = Q(M) ℓ / (ℓ ⬝ Q(M) ℓ)` is a right `β`-eigenvector with `ℓ ⬝ u = 1`: Cayley--Hamilton gives
  `(M - β) Q(M) = 0`, and `ℓ ⬝ Q(M) v = Q(β) (ℓ ⬝ v)`.
* Over `ℂ`, `ker ℓ` contains no `β`-eigenvector: with `u` it would give a two-dimensional
  eigenspace, while the geometric multiplicity is at most the root multiplicity `1`.
* `B = M - β u ℓᵀ` agrees with `M` on `ker ℓ` and maps everything into `ker ℓ`.  A nonzero
  eigenvalue `μ` of `B` has its eigenvector in `ker ℓ`, so it is an eigenvalue of `M` other
  than `β`, hence a root of `Q`, hence `|μ| < 1`.  So the spectral radius of `B` is `< 1`.
* Gelfand's formula gives `‖Bⁿ‖ ≤ C ρⁿ` with `ρ < 1` (`ℓ^∞` operator norm), which is the
  contraction field.

`SpectralPisot.toPisotData` is the result.  `SpectralPisot.ofIrreducible` produces the input
from the PIP3 conditions themselves: `χ_M` the image of an irreducible polynomial over `ℚ`
(hence separable, so `Q(β) ≠ 0`) and every complex root other than `β` in the open unit disc;
that `β` is a root of `χ_M` follows from the positive left eigenvector `ℓ`.
-/
import PscVerif.PeriodicPartnerRealization
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Separable

namespace Psc.PeriodicPartnerSpectral

open Filter Matrix Polynomial Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization
open scoped Topology NNReal ENNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ## Polynomials in a matrix on eigenvectors -/

section Eigen

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_mulVec_eigen {A : Matrix ι ι K} {x : ι → K} {c : K} (h : A *ᵥ x = c • x) (n : ℕ) :
    (A ^ n) *ᵥ x = c ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ, mul_comm]

theorem aeval_mulVec_eigen {A : Matrix ι ι K} {x : ι → K} {c : K} (h : A *ᵥ x = c • x)
    (p : K[X]) : (aeval A p) *ᵥ x = p.eval c • x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      pow_mulVec_eigen h, eval_monomial, smul_smul]

theorem vecMul_pow_eigen {A : Matrix ι ι K} {w : ι → K} {c : K} (h : w ᵥ* A = c • w) (n : ℕ) :
    w ᵥ* (A ^ n) = c ^ n • w := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, h, smul_smul, pow_succ]

theorem vecMul_aeval_eigen {A : Matrix ι ι K} {w : ι → K} {c : K} (h : w ᵥ* A = c • w)
    (p : K[X]) : w ᵥ* (aeval A p) = p.eval c • w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, vecMul_add, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, vecMul_smul,
      vecMul_pow_eigen h, eval_monomial, smul_smul, mul_comm]

end Eigen

/-! ## Gelfand's formula as a uniform bound -/

/-- Spectral radius `< 1` gives `‖aⁿ‖ ≤ C ρⁿ` with `0 < ρ < 1`. -/
theorem exists_pow_norm_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * ρ ^ n := by
  obtain ⟨r, hr, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  set ρ : ℝ := max (r : ℝ) (1 / 2)
  have hρ0 : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hρ1 : ρ < 1 := max_lt hr1' (by norm_num)
  have hlt : spectralRadius ℂ a < ENNReal.ofReal ρ := by
    refine hr.trans_le ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually (gt_mem_nhds hlt))
  have hbig : ∀ n, N + 1 ≤ n → ‖a ^ n‖ ≤ ρ ^ n := by
    intro n hn
    have h1 := (ENNReal.ofReal_lt_ofReal_iff hρ0).mp (hN n (by omega))
    have hn0 : n ≠ 0 := by omega
    have h2 : ‖a ^ n‖ = (‖a ^ n‖ ^ (1 / n : ℝ)) ^ n := by
      rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn0]
    rw [h2]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) h1.le n
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / ρ ^ k, ρ, ?_, hρ0, hρ1, fun n => ?_⟩
  · have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range (N + 1)) =>
      div_nonneg (norm_nonneg (a ^ k)) (pow_pos hρ0 k).le
    linarith
  · have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / ρ ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_pos hρ0 k).le
    have hpos := pow_pos hρ0 n
    rcases lt_or_ge n (N + 1) with hn | hn
    · have hterm : ‖a ^ n‖ / ρ ^ n ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / ρ ^ k :=
        Finset.single_le_sum (f := fun k => ‖a ^ k‖ / ρ ^ k)
          (fun k _ => div_nonneg (norm_nonneg _) (pow_pos hρ0 k).le) (Finset.mem_range.mpr hn)
      have : ‖a ^ n‖ = ‖a ^ n‖ / ρ ^ n * ρ ^ n := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hpos.le
    · calc ‖a ^ n‖ ≤ ρ ^ n := hbig n hn
        _ ≤ _ := le_mul_of_one_le_left hpos.le (by linarith)

/-! ## The spectral hypothesis -/

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Pisot hypothesis as a factorization of the characteristic polynomial. -/
structure SpectralPisot (S : LengthSubst α) where
  Q : ℝ[X]
  factor : (mat S).charpoly = (X - C S.β) * Q
  simple : Q.eval S.β ≠ 0
  small : ∀ μ : ℂ, (Q.map (algebraMap ℝ ℂ)).IsRoot μ → ‖μ‖ < 1

namespace SpectralPisot

variable {S : LengthSubst α} (H : SpectralPisot S)

theorem vecMul_mat : S.ℓ ᵥ* mat S = S.β • S.ℓ := by
  funext a
  have h := dot_mat_mulVec S (Pi.single a 1)
  rw [dotProduct_mulVec, dotProduct_single, mul_one, dotProduct_single, mul_one] at h
  simpa using h

theorem dot_aeval (p : ℝ[X]) (v : α → ℝ) :
    S.ℓ ⬝ᵥ (aeval (mat S) p *ᵥ v) = p.eval S.β * (S.ℓ ⬝ᵥ v) := by
  rw [dotProduct_mulVec, vecMul_aeval_eigen vecMul_mat, smul_dotProduct, smul_eq_mul]

theorem aeval_charpoly_factor :
    (mat S - algebraMap ℝ _ S.β) * aeval (mat S) H.Q = 0 := by
  have h := aeval_self_charpoly (mat S)
  rwa [H.factor, map_mul, map_sub, aeval_X, aeval_C] at h

/-- The un-normalised eigenvector `Q(M) ℓ`. -/
noncomputable def w : α → ℝ := aeval (mat S) H.Q *ᵥ S.ℓ

theorem dot_w : S.ℓ ⬝ᵥ H.w = H.Q.eval S.β * (S.ℓ ⬝ᵥ S.ℓ) := dot_aeval _ _

theorem dot_self_pos [Nonempty α] : 0 < S.ℓ ⬝ᵥ S.ℓ := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine Finset.sum_pos' (fun b _ => mul_self_nonneg _) ⟨a, Finset.mem_univ _, ?_⟩
  exact mul_pos (S.ℓ_pos a) (S.ℓ_pos a)

theorem dot_w_ne [Nonempty α] : S.ℓ ⬝ᵥ H.w ≠ 0 := by
  rw [dot_w]; exact mul_ne_zero H.simple dot_self_pos.ne'

theorem w_eigen : mat S *ᵥ H.w = S.β • H.w := by
  have h := congrArg (· *ᵥ S.ℓ) H.aeval_charpoly_factor
  simp only [zero_mulVec, ← mulVec_mulVec, sub_mulVec, Algebra.algebraMap_eq_smul_one,
    smul_mulVec, one_mulVec] at h
  exact sub_eq_zero.mp h

/-- The normalised right eigenvector: `M u = β u`, `ℓ ⬝ u = 1`. -/
noncomputable def u : α → ℝ := (S.ℓ ⬝ᵥ H.w)⁻¹ • H.w

theorem u_eigen : mat S *ᵥ H.u = S.β • H.u := by
  rw [u, mulVec_smul, H.w_eigen, smul_comm]

theorem dot_u [Nonempty α] : S.ℓ ⬝ᵥ H.u = 1 := by
  rw [u, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ H.dot_w_ne]

/-! ### Complexification -/

local notation "ι" => (algebraMap ℝ ℂ)

/-- `M` over `ℂ`. -/
noncomputable def Mc (S : LengthSubst α) : Matrix α α ℂ := (mat S).map ι

/-- `ℓ` over `ℂ`. -/
noncomputable def ℓc (S : LengthSubst α) : α → ℂ := ι ∘ S.ℓ

/-- `u` over `ℂ`. -/
noncomputable def uc : α → ℂ := ι ∘ H.u

theorem mulVec_ofReal (A : Matrix α α ℝ) (v : α → ℝ) :
    A.map ι *ᵥ (ι ∘ v) = ι ∘ (A *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec ι A v i).symm

theorem Mc_pow (n : ℕ) : (Mc S) ^ n = ((mat S) ^ n).map ι := by
  rw [Mc, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]

theorem dot_ofReal (v w : α → ℝ) : (ι ∘ v) ⬝ᵥ (ι ∘ w) = ι (v ⬝ᵥ w) := by
  simp [dotProduct]

theorem vecMul_Mc : ℓc S ᵥ* Mc S = (S.β : ℂ) • ℓc S := by
  funext a
  have h := RingHom.map_vecMul ι (mat S) S.ℓ a
  rw [vecMul_mat] at h
  simpa [Mc, ℓc] using h.symm

theorem dot_Mc (x : α → ℂ) : ℓc S ⬝ᵥ (Mc S *ᵥ x) = (S.β : ℂ) * (ℓc S ⬝ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_Mc, smul_dotProduct, smul_eq_mul]

theorem uc_eigen : Mc S *ᵥ H.uc = (S.β : ℂ) • H.uc := by
  rw [Mc, uc, mulVec_ofReal, H.u_eigen]
  funext i; simp

theorem dot_uc [Nonempty α] : ℓc S ⬝ᵥ H.uc = 1 := by
  rw [ℓc, uc, dot_ofReal, H.dot_u, map_one]

theorem charpoly_Mc : (Mc S).charpoly = (X - C (S.β : ℂ)) * H.Q.map ι := by
  rw [Mc, charpoly_map, H.factor, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
  rfl

theorem eval_Q_map (z : ℝ) : (H.Q.map ι).eval (z : ℂ) = ((H.Q.eval z : ℝ) : ℂ) := by
  rw [eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply]

theorem Q_map_ne_zero : H.Q.map ι ≠ 0 := by
  intro h
  have := congrArg (eval (S.β : ℂ)) h
  rw [H.eval_Q_map, eval_zero] at this
  exact H.simple (by exact_mod_cast this)

include H in
theorem rootMultiplicity_β : (Mc S).charpoly.rootMultiplicity (S.β : ℂ) = 1 := by
  rw [H.charpoly_Mc, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) H.Q_map_ne_zero),
    rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero, add_zero]
  rw [IsRoot, H.eval_Q_map]
  exact_mod_cast H.simple

include H in
/-- No `β`-eigenvector of `M` lies in `ker ℓ` over `ℂ`: the `β`-eigenspace is a line, spanned by
`u`, and `ℓ ⬝ u = 1`. -/
theorem eq_zero_of_eigen_β [Nonempty α] {v : α → ℂ} (hv : Mc S *ᵥ v = (S.β : ℂ) • v)
    (hℓ : ℓc S ⬝ᵥ v = 0) : v = 0 := by
  set φ := Matrix.toLin' (Mc S)
  have hle : Module.finrank ℂ (Module.End.eigenspace φ (S.β : ℂ)) ≤ 1 := by
    have := LinearMap.finrank_eigenspace_le φ (S.β : ℂ)
    rwa [Matrix.charpoly_toLin', H.rootMultiplicity_β] at this
  obtain ⟨g, hg⟩ := finrank_le_one_iff.mp hle
  have mem : ∀ x : α → ℂ, Mc S *ᵥ x = (S.β : ℂ) • x → x ∈ Module.End.eigenspace φ (S.β : ℂ) := fun x hx => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hx]
  obtain ⟨c₁, hc₁⟩ := hg ⟨H.uc, mem _ H.uc_eigen⟩
  obtain ⟨c₂, hc₂⟩ := hg ⟨v, mem _ hv⟩
  have e₁ : c₁ • (g : α → ℂ) = H.uc := congrArg Subtype.val hc₁
  have e₂ : c₂ • (g : α → ℂ) = v := congrArg Subtype.val hc₂
  have h₁ : c₁ * (ℓc S ⬝ᵥ (g : α → ℂ)) = 1 := by
    rw [← smul_eq_mul, ← dotProduct_smul, e₁, H.dot_uc]
  have h₂ : c₂ * (ℓc S ⬝ᵥ (g : α → ℂ)) = 0 := by
    rw [← smul_eq_mul, ← dotProduct_smul, e₂, hℓ]
  have hg0 : ℓc S ⬝ᵥ (g : α → ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one h₁
  rw [← e₂, (mul_eq_zero.mp h₂).resolve_right hg0, zero_smul]

/-- An eigenvalue of `M` other than `β` is a root of `Q`. -/
theorem isRoot_of_eigen {μ : ℂ} {v : α → ℂ} (hv0 : v ≠ 0) (hv : Mc S *ᵥ v = μ • v)
    (hμ : μ ≠ S.β) : (H.Q.map ι).IsRoot μ := by
  have h := aeval_mulVec_eigen hv (Mc S).charpoly
  rw [aeval_self_charpoly, zero_mulVec, H.charpoly_Mc, eval_mul, eval_sub, eval_X, eval_C] at h
  have := (smul_eq_zero.mp h.symm).resolve_right hv0
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ)

/-! ### The deflated matrix -/

/-- `B = M - β u ℓᵀ` over `ℂ`. -/
noncomputable def B : Matrix α α ℂ := Mc S - (S.β : ℂ) • vecMulVec H.uc (ℓc S)

theorem B_mulVec (x : α → ℂ) :
    H.B *ᵥ x = Mc S *ᵥ x - ((S.β : ℂ) * (ℓc S ⬝ᵥ x)) • H.uc := by
  rw [B, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem dot_B [Nonempty α] (x : α → ℂ) : ℓc S ⬝ᵥ (H.B *ᵥ x) = 0 := by
  rw [B_mulVec, dotProduct_sub, dot_Mc, dotProduct_smul, H.dot_uc, smul_eq_mul, mul_one, sub_self]

theorem B_mulVec_of_dot {x : α → ℂ} (hx : ℓc S ⬝ᵥ x = 0) : H.B *ᵥ x = Mc S *ᵥ x := by
  rw [B_mulVec, hx, mul_zero, zero_smul, sub_zero]

theorem B_pow_mulVec [Nonempty α] (n : ℕ) {x : α → ℂ} (hx : ℓc S ⬝ᵥ x = 0) :
    (H.B ^ n) *ᵥ x = ((Mc S) ^ n) *ᵥ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hMx : ℓc S ⬝ᵥ (Mc S *ᵥ x) = 0 := by rw [dot_Mc, hx, mul_zero]
    rw [pow_succ, ← mulVec_mulVec, H.B_mulVec_of_dot hx, ih hMx, mulVec_mulVec, ← pow_succ]

theorem norm_lt_one_of_mem_spectrum [Nonempty α] {μ : ℂ} (hμ : μ ∈ spectrum ℂ H.B) : ‖μ‖ < 1 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot, Matrix.eval_charpoly] at hμ
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hBx : H.B *ᵥ x = μ • x := by
    rw [sub_mulVec, sub_eq_zero] at hx
    rw [← hx]
    funext i
    simp [scalar_apply, mulVec_diagonal]
  by_cases h0 : μ = 0
  · simp [h0]
  have hℓ : ℓc S ⬝ᵥ x = 0 := by
    have := H.dot_B x
    rw [hBx, dotProduct_smul, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left h0
  have hMx : Mc S *ᵥ x = μ • x := by rw [← H.B_mulVec_of_dot hℓ, hBx]
  have hβ : μ ≠ S.β := by
    rintro rfl
    exact hx0 (H.eq_zero_of_eigen_β hMx hℓ)
  exact H.small μ (H.isRoot_of_eigen hx0 hMx hβ)

theorem spectralRadius_B_lt_one [Nonempty α] : spectralRadius ℂ H.B < 1 := by
  have := spectrum.spectralRadius_lt_of_forall_lt H.B (r := 1) fun z hz => by
    have := H.norm_lt_one_of_mem_spectrum hz
    exact_mod_cast this
  simpa using this

theorem norm_ofReal_comp (v : α → ℝ) : ‖(ι ∘ v : α → ℂ)‖ = ‖v‖ := by
  have : ‖(ι ∘ v : α → ℂ)‖₊ = ‖v‖₊ := by
    simp only [Pi.nnnorm_def, Function.comp_apply, Complex.coe_algebraMap, Complex.nnnorm_real]
  exact congrArg NNReal.toReal this

include H in
/-- The contraction bound, from Gelfand's formula for `B`. -/
theorem exists_contract [Nonempty α] :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ v, S.ℓ ⬝ᵥ v = 0 → ∀ n : ℕ, ‖((mat S) ^ n) *ᵥ v‖ ≤ C * ρ ^ n * ‖v‖ := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hB⟩ := exists_pow_norm_le H.B H.spectralRadius_B_lt_one
  refine ⟨C, ρ, hC, hρ0, hρ1, fun v hv n => ?_⟩
  have hvc : ℓc S ⬝ᵥ (ι ∘ v) = 0 := by rw [ℓc, dot_ofReal, hv, map_zero]
  have key : ι ∘ (((mat S) ^ n) *ᵥ v) = (H.B ^ n) *ᵥ (ι ∘ v) := by
    rw [H.B_pow_mulVec n hvc, Mc_pow, mulVec_ofReal]
  rw [← norm_ofReal_comp, key, ← norm_ofReal_comp v]
  exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))

/-- **The contraction, derived.** A factorization `χ_M = (X - β) Q` with `Q(β) ≠ 0` and all
roots of `Q` in the open unit disc gives `PisotData`. -/
noncomputable def toPisotData [Nonempty α] : PisotData S where
  u := H.u
  u_eigen := H.u_eigen
  dot_u := H.dot_u
  C := H.exists_contract.choose
  C_nonneg := H.exists_contract.choose_spec.choose_spec.1
  ρ := H.exists_contract.choose_spec.choose
  ρ_nonneg := H.exists_contract.choose_spec.choose_spec.2.1.le
  ρ_lt_one := H.exists_contract.choose_spec.choose_spec.2.2.1
  contract := H.exists_contract.choose_spec.choose_spec.2.2.2

/-! ### The PIP3 form of the hypothesis -/

/-- `β` is a root of `χ_M`: the positive vector `ℓ` is a left `β`-eigenvector. -/
theorem isRoot_charpoly_β [Nonempty α] : (mat S).charpoly.IsRoot S.β := by
  rw [IsRoot, Matrix.eval_charpoly]
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨S.ℓ, fun h => ?_, ?_⟩
  · obtain ⟨a⟩ := ‹Nonempty α›
    exact (S.ℓ_pos a).ne' (congrFun h a)
  · rw [vecMul_sub, vecMul_mat, scalar_apply]
    funext a; simp

/-- **PIP3 form.** If `χ_M` is the image of an irreducible rational polynomial and every complex
root other than `β` lies in the open unit disc, the spectral hypothesis holds with
`Q = χ_M /ₘ (X - β)`; `Q(β) ≠ 0` because an irreducible polynomial over `ℚ` is separable. -/
noncomputable def ofIrreducible [Nonempty α] (p : ℚ[X]) (hp : Irreducible p)
    (hχ : (mat S).charpoly = p.map (algebraMap ℚ ℝ))
    (hpisot : ∀ μ : ℂ, ((mat S).charpoly.map (algebraMap ℝ ℂ)).IsRoot μ → μ ≠ S.β → ‖μ‖ < 1) :
    SpectralPisot S :=
  have hfac : (mat S).charpoly = (X - C S.β) * ((mat S).charpoly /ₘ (X - C S.β)) :=
    (mul_divByMonic_eq_iff_isRoot.mpr isRoot_charpoly_β).symm
  have hsimple : ((mat S).charpoly /ₘ (X - C S.β)).eval S.β ≠ 0 := fun h0 => by
    have hsep : (mat S).charpoly.Separable := hχ ▸ hp.separable.map
    refine not_isUnit_X_sub_C S.β (hsep.squarefree _ ?_)
    conv_rhs => rw [hfac]
    exact mul_dvd_mul_left _ (dvd_iff_isRoot.mpr h0)
  { Q := (mat S).charpoly /ₘ (X - C S.β)
    factor := hfac
    simple := hsimple
    small := fun μ hμ => by
      refine hpisot μ ?_ fun hβ => hsimple ?_
      · rw [hfac, Polynomial.map_mul, IsRoot, eval_mul, hμ.eq_zero, mul_zero]
      · have h := hμ.eq_zero
        rw [hβ, eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply] at h
        exact (algebraMap ℝ ℂ).injective (h.trans (map_zero _).symm) }

end SpectralPisot

end Psc.PeriodicPartnerSpectral
