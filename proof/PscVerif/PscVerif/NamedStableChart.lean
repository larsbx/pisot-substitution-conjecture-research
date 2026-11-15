module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# An authentic real stable chart for the named determinant-two incidence

The root is constructed by the intermediate value theorem inside the exact
48-step native bracket. All chart identities are proved over the reals.
`J` is a quotient section, whereas `L` takes values in the invariant plane
annihilated by the physical left eigenrow. Reconstruction and intertwining
identify the stable coordinates without a zero-map or arbitrary-chart
premise. No Haar, tiling, or general Pisot realization theorem is asserted.

Pre-code gate: `docs/c4-named-stable-chart-literature-2026-11-11.md`.
-/

@[expose] public section

namespace Psc.NamedStableChart

open Matrix

abbrev Stable := Fin 2 → ℝ
abbrev AmbientReal := Fin 3 → ℝ

def cubic (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - 2 * x - 2

noncomputable def betaLo : ℝ := 638816140918905 / 281474976710656
noncomputable def betaHi : ℝ := 638816140918906 / 281474976710656

/-- These are the exact canonical 48-step native endpoints, not rounded
decimal inputs. Their strict signs are kernel-checked rational arithmetic. -/
theorem root_bracket :
    2 < betaLo ∧ betaLo < betaHi ∧ betaHi < 5 / 2 ∧
      cubic betaLo < 0 ∧ 0 < cubic betaHi := by
  norm_num [betaLo, betaHi, cubic]

theorem exists_root_in_bracket :
    ∃ x : ℝ, x ∈ Set.Icc betaLo betaHi ∧ cubic x = 0 := by
  have hc : Continuous cubic := by unfold cubic; continuity
  have hz : (0 : ℝ) ∈ Set.Icc (cubic betaLo) (cubic betaHi) :=
    ⟨root_bracket.2.2.2.1.le, root_bracket.2.2.2.2.le⟩
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc root_bracket.2.1.le hc.continuousOn hz
  exact ⟨x, hx, he⟩

noncomputable def beta : ℝ := Classical.choose exists_root_in_bracket

theorem beta_ge_lo : betaLo ≤ beta := (Classical.choose_spec exists_root_in_bracket).1.1
theorem beta_le_hi : beta ≤ betaHi := (Classical.choose_spec exists_root_in_bracket).1.2
theorem beta_cubic : cubic beta = 0 := (Classical.choose_spec exists_root_in_bracket).2

theorem beta_gt_two : 2 < beta := root_bracket.1.trans_le beta_ge_lo
theorem beta_lt_five_halves : beta < 5 / 2 := beta_le_hi.trans_lt root_bracket.2.2.1
theorem beta_pos : 0 < beta := lt_trans (by norm_num : (0 : ℝ) < 2) beta_gt_two
theorem beta_ne_zero : beta ≠ 0 := ne_of_gt beta_pos

/-- The positive root above two is unique; the proof factors a cubic
difference and proves the remaining factor strictly positive. -/
theorem root_unique_ge_two {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hfx : cubic x = 0) (hfy : cubic y = 0) : x = y := by
  have hcoef : 0 < x ^ 2 + x * y + y ^ 2 - x - y - 2 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2),
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hprod : (x - y) * (x ^ 2 + x * y + y ^ 2 - x - y - 2) = 0 := by
    calc
      _ = cubic x - cubic y := by unfold cubic; ring
      _ = 0 := by rw [hfx, hfy]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt hcoef))

theorem beta_unique {x : ℝ} (hx : 2 ≤ x) (hfx : cubic x = 0) : x = beta :=
  root_unique_ge_two hx beta_gt_two.le hfx beta_cubic

noncomputable def a : ℝ := (3 * beta - beta ^ 2) / 2
noncomputable def b : ℝ := (beta ^ 2 - beta - 2) / 2
noncomputable def c : ℝ := beta ^ 2 - beta - 1
noncomputable def kappa : ℝ := 4 * beta - beta ^ 2

theorem a_add_b_add_one : a + b + 1 = beta := by unfold a b; ring

theorem beta_mul_b : beta * b = 1 := by
  have h := beta_cubic
  unfold cubic at h
  unfold b
  nlinarith

theorem beta_mul_a : beta * a = 1 + 2 * b := by
  have h := beta_cubic
  unfold cubic at h
  unfold a b
  nlinarith

theorem beta_mul_a_eq_c : beta * a = c := by
  rw [beta_mul_a]
  unfold b c
  ring

theorem beta_mul_c : beta * c = beta + 2 := by
  have h := beta_cubic
  unfold cubic at h
  unfold c
  nlinarith

theorem a_pos : 0 < a := by
  have h := mul_pos beta_pos (sub_pos.mpr
    (beta_lt_five_halves.trans (by norm_num : (5 / 2 : ℝ) < 3)))
  unfold a
  nlinarith

theorem b_pos : 0 < b := by
  by_contra h
  have hp := mul_nonpos_of_nonneg_of_nonpos beta_pos.le (le_of_not_gt h)
  nlinarith [beta_mul_b]

theorem b_eq_inv_beta : b = 1 / beta := by
  apply (eq_div_iff beta_ne_zero).mpr
  simpa only [mul_comm] using beta_mul_b

theorem c_gt_one : 1 < c := by
  unfold c
  nlinarith [beta_gt_two, sq_nonneg (beta - 2)]

theorem kappa_pos : 0 < kappa := by
  have h := mul_pos beta_pos (sub_pos.mpr
    (beta_lt_five_halves.trans (by norm_num : (5 / 2 : ℝ) < 4)))
  unfold kappa
  nlinarith

theorem kappa_ne_zero : kappa ≠ 0 := ne_of_gt kappa_pos

theorem a_relation : a * a + a * b + a = 1 + 2 * b := by
  have h := congrArg (fun t : ℝ => a * t) a_add_b_add_one
  nlinarith [beta_mul_a]

theorem b_relation : a * b + b * b + b = 1 := by
  have h := congrArg (fun t : ℝ => b * t) a_add_b_add_one
  nlinarith [beta_mul_b]

def MZ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 2; 1, 1, 1; 0, 1, 0]
noncomputable def MR : Matrix (Fin 3) (Fin 3) ℝ := (Int.castRingHom ℝ).mapMatrix MZ
noncomputable def W : Matrix (Fin 2) (Fin 3) ℝ := !![1, -a, 0; 0, -b, 1]
def J : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]
noncomputable def Bmat : Matrix (Fin 2) (Fin 2) ℝ := !![-a, 2 - a; -b, -b]
noncomputable def r : AmbientReal := ![a, 1, b]
noncomputable def physicalRow : AmbientReal := ![1, beta, c]

noncomputable def Blinear : Stable →ₗ[ℝ] Stable := Bmat.mulVecLin
noncomputable def B : AddMonoid.End Stable := Blinear.toAddMonoidHom

def castZ : (Fin 3 → ℤ) →+ AmbientReal where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp

noncomputable def piZ : (Fin 3 → ℤ) →+ Stable :=
  W.mulVecLin.toAddMonoidHom.comp castZ

noncomputable def physical (x : AmbientReal) : ℝ := physicalRow ⬝ᵥ x

/-- The corrected section into the physical-row kernel. `J` itself is
only a quotient section and need not have stable image. -/
noncomputable def L (y : Stable) : AmbientReal :=
  J *ᵥ y - (physical (J *ᵥ y) / kappa) • r

theorem MR_eq : MR = !![0, 1, 2; 1, 1, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [MR, MZ]

theorem MR_mulVec (x : AmbientReal) :
    MR *ᵥ x = ![x 1 + 2 * x 2, x 0 + x 1 + x 2, x 1] := by
  rw [MR_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem W_mulVec (x : AmbientReal) : W *ᵥ x = ![x 0 - a * x 1, x 2 - b * x 1] := by
  ext i
  fin_cases i <;> simp [W, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem J_mulVec (y : Stable) : J *ᵥ y = ![y 0, 0, y 1] := by
  ext i
  fin_cases i <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Bmat_mulVec (y : Stable) :
    Bmat *ᵥ y = ![-a * y 0 + (2 - a) * y 1, -b * y 0 - b * y 1] := by
  ext i
  fin_cases i <;> simp [Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem B_apply (y : Stable) : B y = Bmat *ᵥ y := rfl
theorem piZ_apply (z : Fin 3 → ℤ) : piZ z = W *ᵥ castZ z := rfl

theorem physical_apply (x : AmbientReal) :
    physical x = x 0 + beta * x 1 + c * x 2 := by
  simp [physical, physicalRow, dotProduct, Fin.sum_univ_three]

theorem physical_add (x y : AmbientReal) : physical (x + y) = physical x + physical y := by
  simp only [physical_apply, Pi.add_apply]
  ring

theorem physical_sub (x y : AmbientReal) : physical (x - y) = physical x - physical y := by
  simp only [physical_apply, Pi.sub_apply]
  ring

theorem physical_smul (t : ℝ) (x : AmbientReal) : physical (t • x) = t * physical x := by
  simp only [physical_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A right inverse authenticates full rank of the two real coordinates. -/
theorem WJ_eq_one : W * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W, J, Matrix.mul_apply, Fin.sum_univ_three]

/-- Exact intertwining for the actual named incidence. -/
theorem WM_eq_BW : W * MR = Bmat * W := by
  rw [MR_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W, Bmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    nlinarith [a_relation, b_relation]

theorem perron_eigen : MR *ᵥ r = beta • r := by
  rw [MR_mulVec]
  ext i
  fin_cases i <;> simp [r, Pi.smul_apply, smul_eq_mul] <;>
    nlinarith [a_add_b_add_one, beta_mul_a, beta_mul_b]

theorem perron_vector_pos (i : Fin 3) : 0 < r i := by
  fin_cases i <;> simp [r, a_pos, b_pos]

theorem physical_row_pos (i : Fin 3) : 0 < physicalRow i := by
  fin_cases i <;> simp [physicalRow, beta_pos, lt_trans (by norm_num : (0 : ℝ) < 1) c_gt_one]

theorem physical_eigen (x : AmbientReal) : physical (MR *ᵥ x) = beta * physical x := by
  rw [MR_mulVec]
  simp only [physical_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : 1 + beta + c = beta ^ 2 := by unfold c; ring
  calc
    (x 1 + 2 * x 2) + beta * (x 0 + x 1 + x 2) + c * x 1 =
        beta * x 0 + (1 + beta + c) * x 1 + (beta + 2) * x 2 := by ring
    _ = beta * x 0 + beta ^ 2 * x 1 + (beta * c) * x 2 := by rw [hc, beta_mul_c]
    _ = beta * (x 0 + beta * x 1 + c * x 2) := by ring

theorem W_r_zero : W *ᵥ r = 0 := by
  rw [W_mulVec]
  ext i
  fin_cases i <;> simp [r]

/-- The exact kernel is the expanding eigenline, including its scale. -/
theorem W_kernel_iff (x : AmbientReal) :
    W *ᵥ x = 0 ↔ x = (x 1) • r := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [W_mulVec] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    ext i
    fin_cases i <;> simp [r, Pi.smul_apply, smul_eq_mul] <;> nlinarith
  · intro h
    rw [h, Matrix.mulVec_smul, W_r_zero, smul_zero]

theorem physical_r_eq_kappa : physical r = kappa := by
  have hcb : c * b = a := by
    calc
      c * b = (beta * a) * b := by rw [beta_mul_a_eq_c]
      _ = a * (beta * b) := by ring
      _ = a := by rw [beta_mul_b, mul_one]
  rw [physical_apply]
  change a + beta * 1 + c * b = kappa
  rw [hcb]
  unfold a kappa
  ring

theorem W_L (y : Stable) : W *ᵥ L y = y := by
  unfold L
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, W_r_zero, smul_zero, sub_zero,
    Matrix.mulVec_mulVec, WJ_eq_one, Matrix.one_mulVec]

theorem physical_L (y : Stable) : physical (L y) = 0 := by
  unfold L
  rw [physical_sub, physical_smul, physical_r_eq_kappa]
  field_simp [kappa_ne_zero]
  ring

theorem quotient_reconstruction (x : AmbientReal) :
    x = J *ᵥ (W *ᵥ x) + (x 1) • r := by
  rw [W_mulVec, J_mulVec]
  ext i
  fin_cases i <;> simp [r, Pi.add_apply, smul_eq_mul] <;> ring

/-- The pair of physical and stable coordinates reconstructs the entire
real vector; the quotient section is corrected to the invariant plane. -/
theorem reconstruction (x : AmbientReal) :
    x = L (W *ᵥ x) + (physical x / kappa) • r := by
  have hp := congrArg physical (quotient_reconstruction x)
  rw [physical_add, physical_smul, physical_r_eq_kappa] at hp
  have hs : physical x / kappa - physical (J *ᵥ (W *ᵥ x)) / kappa = x 1 := by
    rw [← sub_div, div_eq_iff kappa_ne_zero]
    nlinarith [hp]
  symm
  unfold L
  calc
    J *ᵥ (W *ᵥ x) - (physical (J *ᵥ (W *ᵥ x)) / kappa) • r +
        (physical x / kappa) • r =
      J *ᵥ (W *ᵥ x) +
        (physical x / kappa - physical (J *ᵥ (W *ᵥ x)) / kappa) • r := by
          rw [sub_smul]
          abel
    _ = J *ᵥ (W *ᵥ x) + (x 1) • r := by rw [hs]
    _ = x := (quotient_reconstruction x).symm

theorem L_W_of_physical_zero (x : AmbientReal) (hx : physical x = 0) : L (W *ᵥ x) = x := by
  have h := reconstruction x
  simpa only [hx, zero_div, zero_smul, add_zero] using h.symm

theorem W_injective_on_stable {x y : AmbientReal}
    (hx : physical x = 0) (hy : physical y = 0) (h : W *ᵥ x = W *ᵥ y) : x = y := by
  rw [← L_W_of_physical_zero x hx, ← L_W_of_physical_zero y hy, h]

/-- Conjugacy with the actual invariant physical-row kernel. -/
theorem M_L (y : Stable) : MR *ᵥ L y = L (Bmat *ᵥ y) := by
  apply W_injective_on_stable
  · rw [physical_eigen, physical_L, mul_zero]
  · exact physical_L _
  · rw [W_L, Matrix.mulVec_mulVec, WM_eq_BW, ← Matrix.mulVec_mulVec, W_L]

theorem MZ_det : MZ.det = 2 := by norm_num [MZ, Matrix.det_fin_three]

theorem MZ_mulVec_injective : Function.Injective (fun z : Fin 3 → ℤ => MZ *ᵥ z) :=
  Matrix.mulVec_injective_of_det_ne_zero (by rw [MZ_det]; norm_num)

theorem Bmat_det : Bmat.det = 2 * b := by
  simp [Bmat, Matrix.det_fin_two]
  ring

theorem Bmat_det_ne_zero : Bmat.det ≠ 0 := by
  rw [Bmat_det]
  exact mul_ne_zero (by norm_num) (ne_of_gt b_pos)

theorem B_isClosedEmbedding : Topology.IsClosedEmbedding B :=
  LinearMap.isClosedEmbedding_of_injective (f := Blinear)
    (LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_of_det_ne_zero Bmat_det_ne_zero))

theorem castZ_mulVec (z : Fin 3 → ℤ) : castZ (MZ *ᵥ z) = MR *ᵥ castZ z := by
  rw [MR_eq]
  ext i
  fin_cases i <;> simp [castZ, MZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem piZ_commute (z : Fin 3 → ℤ) : B (piZ z) = piZ (MZ *ᵥ z) := by
  rw [B_apply, piZ_apply, piZ_apply, castZ_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, WM_eq_BW]

theorem W_MR_pow (n : ℕ) : W * MR ^ n = Bmat ^ n * W := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ MR n, pow_succ Bmat n]
      calc
        W * (MR ^ n * MR) = (W * MR ^ n) * MR := (Matrix.mul_assoc _ _ _).symm
        _ = (Bmat ^ n * W) * MR := by rw [ih]
        _ = Bmat ^ n * (W * MR) := Matrix.mul_assoc _ _ _
        _ = Bmat ^ n * (Bmat * W) := by rw [WM_eq_BW]
        _ = (Bmat ^ n * Bmat) * W := (Matrix.mul_assoc _ _ _).symm

theorem Bmat_pow_eq_WMpJ (n : ℕ) : Bmat ^ n = W * MR ^ n * J := by
  rw [W_MR_pow, Matrix.mul_assoc, WJ_eq_one, Matrix.mul_one]

theorem B_pow_apply_eq_matrix (n : ℕ) (x : Stable) : (B ^ n) x = (Bmat ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ' B n, pow_succ' Bmat n]
      change B ((B ^ n) x) = _
      rw [ih, B_apply, Matrix.mulVec_mulVec]

theorem MZ_pow_two : MZ ^ 2 = !![1, 3, 1; 1, 3, 3; 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, MZ, Matrix.mul_apply, Fin.sum_univ_three]

theorem MZ_pow_four : MZ ^ 4 = !![5, 13, 11; 7, 15, 13; 3, 7, 5] := by
  change MZ ^ (2 + 2) = _
  rw [pow_add, MZ_pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

theorem MZ_pow_eight : MZ ^ 8 = !![149, 337, 279; 179, 407, 337; 79, 179, 149] := by
  change MZ ^ (4 + 4) = _
  rw [pow_add, MZ_pow_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

theorem MZ_pow_twelve : MZ ^ 12 = !![3941, 8945, 7415; 4755, 10791, 8945; 2095, 4755, 3941] := by
  change MZ ^ (8 + 4) = _
  rw [pow_add, MZ_pow_eight, MZ_pow_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

theorem MR_pow_twelve : MR ^ 12 = !![3941, 8945, 7415; 4755, 10791, 8945; 2095, 4755, 3941] := by
  change ((Int.castRingHom ℝ).mapMatrix MZ) ^ 12 = _
  rw [← map_pow, MZ_pow_twelve]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The actual twelfth power is authenticated through the integer power
and the intertwining/right-inverse identities, avoiding a degree-24
expansion in an unverified quotient field. -/
theorem Bmat_pow_twelve : Bmat ^ 12 =
    !![3941 - 4755 * a, 7415 - 8945 * a;
       2095 - 4755 * b, 3941 - 8945 * b] := by
  rw [Bmat_pow_eq_WMpJ, MR_pow_twelve]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, J, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Psc.NamedStableChart
