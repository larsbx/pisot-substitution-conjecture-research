/-
# A kernel-checkable Pisot certificate for three-letter substitutions

`PeriodicPartnerSpectral` derives `PisotData` from a factorization `χ_M = (X - β) Q` with the
roots of `Q` in the open unit disc, and instantiates it for Tribonacci by hand.  This module
replaces the hand proof by a Boolean certificate `check` on integer data that the kernel can
evaluate, and proves it sound: `check s = true` produces a `LengthSubst (Fin 3)` with image map
`s.σ`, its membership in PIP3, and its `PisotData`.

For `M` the incidence matrix of `s` and `p = χ_M = X³ - T X² + U X - D`, `check` asks:

* every image is nonempty;
* `p(1) < 0`, `p(-1) < 0` (Jury's conditions `Q(±1) > 0` for the cofactor);
* `D ≠ 0` and no integer `r` with `|r| ≤ |D|` is a root of `p` (irreducibility over `ℚ`);
* `M⁵ > 0` entrywise (primitivity; Wielandt's exponent for three letters);
* a dyadic bracket `lo/16 < β < hi/16` of a root with `lo/16 ≥ max(1, |D|)`, found by integer
  bisection and re-checked by the sign of `p` at both ends;
* for each column `j`, a lower bound of `c₁ⱼ β² + (c₂ⱼ - T c₁ⱼ) β + D` on the bracket is positive,
  where `c₁, c₂` are the column sums of `M` and `M²`.

Soundness (`subst`, `spectral`, `mem_PIP3`, `pisotData`):

* `β` is a root of `p` in the bracket (intermediate value theorem), so `β > 1` and `β > |D|`;
* `χ_M = (X - β) Q` with `Q = X² + (β - T) X + D/β`, because `p(β) = 0`;
* `p(1) = (1 - β) Q(1)` and `p(-1) = (-1 - β) Q(-1)` give `Q(±1) > 0`, and `|Q(0)| = |D|/β < 1`;
  a real monic quadratic with these three properties has both roots in the open unit disc;
* `ℓ = 𝟙ᵀ Q(M)` is a left `β`-eigenvector by Cayley--Hamilton, and `β ℓⱼ` is the quadratic the
  certificate bounds below, so `ℓ > 0`.

The bracket only certifies; no floating point enters.

The rejection certificate `refute` is the converse side (`refute_spec`): if `s` underlies any
PIP3 length substitution, then `p(1) < 0`, `p(-1) < 0` (Jury's conditions are also necessary,
`jury_of_norm_lt_one`), `p` has no integer root, and `p(|D|) < 0` when `|D| ≥ 2`.  `check` is not
claimed necessary in general; on the census, `PeriodicPartnerSpectralCensus` evaluates
`refute s || check s` on every specimen.
-/
import PscVerif.PeriodicPartnerSpectral
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.LinearCombination

namespace Psc.PeriodicPartnerSpectralCertificate

open Matrix Polynomial Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization
  Psc.PeriodicPartnerSpectral

/-! ## The computable certificate -/

/-- A `3 × 3` integer matrix, row-major, with unrolled arithmetic for the kernel. -/
structure M3 where
  a00 : ℤ
  a01 : ℤ
  a02 : ℤ
  a10 : ℤ
  a11 : ℤ
  a12 : ℤ
  a20 : ℤ
  a21 : ℤ
  a22 : ℤ

namespace M3

/-- The matrix product. -/
def mul (x y : M3) : M3 :=
  ⟨x.a00 * y.a00 + x.a01 * y.a10 + x.a02 * y.a20,
   x.a00 * y.a01 + x.a01 * y.a11 + x.a02 * y.a21,
   x.a00 * y.a02 + x.a01 * y.a12 + x.a02 * y.a22,
   x.a10 * y.a00 + x.a11 * y.a10 + x.a12 * y.a20,
   x.a10 * y.a01 + x.a11 * y.a11 + x.a12 * y.a21,
   x.a10 * y.a02 + x.a11 * y.a12 + x.a12 * y.a22,
   x.a20 * y.a00 + x.a21 * y.a10 + x.a22 * y.a20,
   x.a20 * y.a01 + x.a21 * y.a11 + x.a22 * y.a21,
   x.a20 * y.a02 + x.a21 * y.a12 + x.a22 * y.a22⟩

/-- Every entry is positive. -/
def pos (x : M3) : Bool :=
  decide (0 < x.a00) && decide (0 < x.a01) && decide (0 < x.a02) &&
  decide (0 < x.a10) && decide (0 < x.a11) && decide (0 < x.a12) &&
  decide (0 < x.a20) && decide (0 < x.a21) && decide (0 < x.a22)

/-- `T`, `U`, `D` of `χ = X³ - T X² + U X - D`. -/
def trace (x : M3) : ℤ := x.a00 + x.a11 + x.a22

def minors (x : M3) : ℤ :=
  (x.a00 * x.a11 - x.a01 * x.a10) + (x.a00 * x.a22 - x.a02 * x.a20) +
    (x.a11 * x.a22 - x.a12 * x.a21)

def det (x : M3) : ℤ :=
  x.a00 * (x.a11 * x.a22 - x.a12 * x.a21) - x.a01 * (x.a10 * x.a22 - x.a12 * x.a20) +
    x.a02 * (x.a10 * x.a21 - x.a11 * x.a20)

/-- Column sums. -/
def col (x : M3) : Fin 3 → ℤ
  | 0 => x.a00 + x.a10 + x.a20
  | 1 => x.a01 + x.a11 + x.a21
  | 2 => x.a02 + x.a12 + x.a22

end M3

/-- A substitution on `{0, 1, 2}`, as its three images. -/
abbrev Sub3 := List (Fin 3) × List (Fin 3) × List (Fin 3)

/-- The image map. -/
def Sub3.σ (s : Sub3) : Fin 3 → List (Fin 3)
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2

/-- The incidence matrix, `M b a = |σ a|_b`. -/
def parikh (s : Sub3) : M3 :=
  ⟨(s.1.count 0 : ℤ), (s.2.1.count 0 : ℤ), (s.2.2.count 0 : ℤ),
   (s.1.count 1 : ℤ), (s.2.1.count 1 : ℤ), (s.2.2.count 1 : ℤ),
   (s.1.count 2 : ℤ), (s.2.1.count 2 : ℤ), (s.2.2.count 2 : ℤ)⟩

/-- `p(x) = x³ - T x² + U x - D`, Horner form. -/
def horner (T U D x : ℤ) : ℤ := ((x - T) * x + U) * x - D

/-- `k³ p(x/k)`. -/
def hornerS (T U D k x : ℤ) : ℤ := ((x - T * k) * x + U * k * k) * x - D * k * k * k

/-- No integer `r` with `|r| ≤ n` is a zero of `f`. -/
def noRoot (f : ℤ → ℤ) : ℕ → Bool
  | 0 => f 0 != 0
  | n + 1 => f (n + 1) != 0 && f (-(n + 1 : ℤ)) != 0 && noRoot f n

/-- Integer bisection of a sign change `f lo < 0 ≤ f hi`; the result is re-checked, not
trusted. -/
def bisect (f : ℤ → ℤ) : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, lo, hi => (lo, hi)
  | n + 1, lo, hi =>
    if hi - lo ≤ 1 then (lo, hi) else
      if f ((lo + hi) / 2) < 0 then bisect f n ((lo + hi) / 2) hi
      else bisect f n lo ((lo + hi) / 2)

/-- The dyadic denominator of the bracket. -/
def scale : ℤ := 16

/-- `256 ×` a lower bound of `c₁ β² + k β + D` on `[lo/16, hi/16]` when `c₁ ≥ 0`, `lo ≥ 0`. -/
def posLB (c₁ k D lo hi : ℤ) : ℤ :=
  c₁ * lo * lo + min (k * lo) (k * hi) * scale + D * scale * scale

section Data

variable (s : Sub3)

def tr : ℤ := (parikh s).trace
def mn : ℤ := (parikh s).minors
def dt : ℤ := (parikh s).det
def sq : M3 := (parikh s).mul (parikh s)
def base : ℕ := Nat.max 1 (dt s).natAbs
def top : ℤ := 1 + ((tr s).natAbs + (mn s).natAbs + (dt s).natAbs : ℕ)
def bracket : ℤ × ℤ :=
  bisect (hornerS (tr s) (mn s) (dt s) scale) 64 (base s * scale) (top s * scale)
def lo : ℤ := (bracket s).1
def hi : ℤ := (bracket s).2

/-- The positivity bound for column `j`. -/
def colLB (j : Fin 3) : ℤ :=
  posLB ((parikh s).col j) ((sq s).col j - tr s * (parikh s).col j) (dt s) (lo s) (hi s)

end Data

/-- **The certificate.** -/
def check (s : Sub3) : Bool :=
  decide (s.1 ≠ []) && decide (s.2.1 ≠ []) && decide (s.2.2 ≠ []) &&
  decide (horner (tr s) (mn s) (dt s) 1 < 0) && decide (horner (tr s) (mn s) (dt s) (-1) < 0) &&
  decide (dt s ≠ 0) && noRoot (horner (tr s) (mn s) (dt s)) (dt s).natAbs &&
  ((sq s).mul (sq s) |>.mul (parikh s)).pos &&
  decide (base s * scale ≤ lo s) && decide (lo s ≤ hi s) &&
  decide (hornerS (tr s) (mn s) (dt s) scale (lo s) < 0) &&
  decide (0 < hornerS (tr s) (mn s) (dt s) scale (hi s)) &&
  decide (0 < colLB s 0) && decide (0 < colLB s 1) && decide (0 < colLB s 2)

/-- **The rejection certificate.** One of four necessary conditions of PIP3 fails: `p(1) < 0`,
`p(-1) < 0`, no integer root, and `p(|D|) < 0` when `|D| ≥ 2` (`|D| < β` and `p < 0` on
`[1, β)`). -/
def refute (s : Sub3) : Bool :=
  decide (0 ≤ horner (tr s) (mn s) (dt s) 1) || decide (0 ≤ horner (tr s) (mn s) (dt s) (-1)) ||
  !noRoot (horner (tr s) (mn s) (dt s)) (dt s).natAbs ||
  (decide (2 ≤ (dt s).natAbs) && decide (0 ≤ horner (tr s) (mn s) (dt s) (dt s).natAbs))

/-! ## Integer facts -/

namespace M3

def toMat (x : M3) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![x.a00, x.a01, x.a02; x.a10, x.a11, x.a12; x.a20, x.a21, x.a22]

theorem toMat_mul (x y : M3) : (x.mul y).toMat = x.toMat * y.toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul, toMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem col_eq (x : M3) (j : Fin 3) : x.col j = ∑ i, x.toMat i j := by
  fin_cases j <;> simp [col, toMat, Fin.sum_univ_three]

theorem pos_spec {x : M3} (h : x.pos = true) (i j : Fin 3) : 0 < x.toMat i j := by
  simp only [pos, Bool.and_eq_true, decide_eq_true_eq] at h
  fin_cases i <;> fin_cases j <;> (simp [toMat]; try omega)

theorem charpoly_toMat (x : M3) :
    x.toMat.charpoly = X ^ 3 - C x.trace * X ^ 2 + C x.minors * X - C x.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [toMat, charmatrix_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    cons_val_two, empty_val', cons_val_fin_one, head_cons, tail_cons, head_fin_const,
    Matrix.diagonal_apply, trace, minors, det]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, map_add, map_sub, map_mul]
  ring

end M3

theorem parikh_toMat (s : Sub3) : (parikh s).toMat = fun b a => ((s.σ a).count b : ℤ) := by
  ext b a
  fin_cases b <;> fin_cases a <;> rfl

theorem col_nonneg (s : Sub3) (j : Fin 3) : 0 ≤ (parikh s).col j := by
  fin_cases j <;> simp [M3.col, parikh] <;> positivity

theorem noRoot_spec {f : ℤ → ℤ} : ∀ {n : ℕ}, noRoot f n = true → ∀ r : ℤ, r.natAbs ≤ n → f r ≠ 0
  | 0, h, r, hr => by
    obtain rfl : r = 0 := by omega
    simpa [noRoot] using h
  | n + 1, h, r, hr => by
    simp only [noRoot, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases (show r.natAbs ≤ n ∨ r = n + 1 ∨ r = -(n + 1 : ℤ) by omega) with h' | rfl | rfl
    · exact noRoot_spec h3 r h'
    · exact h1
    · exact h2

theorem noRoot_of_forall {f : ℤ → ℤ} :
    ∀ {n : ℕ}, (∀ r : ℤ, r.natAbs ≤ n → f r ≠ 0) → noRoot f n = true
  | 0, h => by simpa [noRoot] using h 0 (by simp)
  | n + 1, h => by
    simp only [noRoot, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨h _ (by omega), h _ (by omega)⟩, noRoot_of_forall fun r hr => h r (by omega)⟩

/-- The conditions `check` certifies, as propositions. -/
structure Facts (s : Sub3) : Prop where
  ne : ∀ a, s.σ a ≠ []
  p_one : horner (tr s) (mn s) (dt s) 1 < 0
  p_neg_one : horner (tr s) (mn s) (dt s) (-1) < 0
  dt_ne : dt s ≠ 0
  no_root : ∀ r : ℤ, r.natAbs ≤ (dt s).natAbs → horner (tr s) (mn s) (dt s) r ≠ 0
  prim : ∀ i j, 0 < ((parikh s).toMat ^ 5) i j
  base_le : (base s : ℤ) * scale ≤ lo s
  lo_le : lo s ≤ hi s
  p_lo : hornerS (tr s) (mn s) (dt s) scale (lo s) < 0
  p_hi : 0 < hornerS (tr s) (mn s) (dt s) scale (hi s)
  col_pos : ∀ j, 0 < colLB s j

theorem facts {s : Sub3} (h : check s = true) : Facts s := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hp1⟩, hm1⟩, hD⟩, hr⟩, hP⟩, hb⟩, hlh⟩, hlo⟩, hhi⟩, c0⟩, c1⟩,
    c2⟩ := h
  refine ⟨fun a => ?_, hp1, hm1, hD, noRoot_spec hr, fun i j => ?_, hb, hlh, hlo, hhi,
    fun j => ?_⟩
  · fin_cases a <;> assumption
  · have e : (parikh s).toMat ^ 5 = (((sq s).mul (sq s)).mul (parikh s)).toMat := by
      simp only [sq, M3.toMat_mul]; noncomm_ring
    rw [e]; exact M3.pos_spec hP i j
  · fin_cases j <;> assumption

/-! ## The real root -/

section Real

variable {s : Sub3}

/-- `p` over `ℝ`. -/
noncomputable def pR (s : Sub3) (x : ℝ) : ℝ := ((x - tr s) * x + mn s) * x - dt s

theorem horner_cast (x : ℤ) : ((horner (tr s) (mn s) (dt s) x : ℤ) : ℝ) = pR s x := by
  simp [horner, pR]

theorem hornerS_cast (x : ℤ) :
    ((hornerS (tr s) (mn s) (dt s) scale x : ℤ) : ℝ) = 16 ^ 3 * pR s (x / 16) := by
  simp only [hornerS, scale, pR]; push_cast; field_simp

theorem exists_root (F : Facts s) :
    ∃ β ∈ Set.Icc ((lo s : ℝ) / 16) ((hi s : ℝ) / 16), pR s β = 0 := by
  have hc : ContinuousOn (pR s) (Set.Icc ((lo s : ℝ) / 16) ((hi s : ℝ) / 16)) := by
    unfold pR; fun_prop
  have hlo : pR s ((lo s : ℝ) / 16) < 0 := by
    have := F.p_lo; have e := hornerS_cast (s := s) (lo s)
    have : ((hornerS (tr s) (mn s) (dt s) scale (lo s) : ℤ) : ℝ) < 0 := by exact_mod_cast this
    nlinarith
  have hhi : 0 < pR s ((hi s : ℝ) / 16) := by
    have := F.p_hi; have e := hornerS_cast (s := s) (hi s)
    have : (0 : ℝ) < ((hornerS (tr s) (mn s) (dt s) scale (hi s) : ℤ) : ℝ) := by exact_mod_cast this
    nlinarith
  have hle : (lo s : ℝ) / 16 ≤ (hi s : ℝ) / 16 := by
    have : (lo s : ℝ) ≤ hi s := by exact_mod_cast F.lo_le
    linarith
  obtain ⟨β, hβ, e⟩ := intermediate_value_Icc hle hc ⟨hlo.le, hhi.le⟩
  exact ⟨β, hβ, e⟩

/-- The certified root. -/
noncomputable def beta (F : Facts s) : ℝ := (exists_root F).choose

theorem beta_mem (F : Facts s) : beta F ∈ Set.Icc ((lo s : ℝ) / 16) ((hi s : ℝ) / 16) :=
  (exists_root F).choose_spec.1

theorem pR_beta (F : Facts s) : pR s (beta F) = 0 := (exists_root F).choose_spec.2

/-- `β > lo/16 ≥ max(1, |D|)`. -/
theorem lo_lt_beta (F : Facts s) : (lo s : ℝ) / 16 < beta F := by
  refine lt_of_le_of_ne (beta_mem F).1 fun h => ?_
  have e := hornerS_cast (s := s) (lo s)
  have : ((hornerS (tr s) (mn s) (dt s) scale (lo s) : ℤ) : ℝ) < 0 := by exact_mod_cast F.p_lo
  rw [h, pR_beta] at e; linarith

theorem base_le_lo (F : Facts s) : (1 : ℝ) ≤ (lo s : ℝ) / 16 ∧ |(dt s : ℝ)| ≤ (lo s : ℝ) / 16 := by
  have hb : ((base s : ℤ) : ℝ) * 16 ≤ lo s := by exact_mod_cast F.base_le
  have h1 : (1 : ℝ) ≤ (base s : ℝ) := by exact_mod_cast Nat.le_max_left 1 _
  have h2 : |(dt s : ℝ)| ≤ (base s : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast Nat.le_max_right 1 _
  push_cast at hb
  constructor <;> linarith

theorem one_lt_beta (F : Facts s) : 1 < beta F := by
  linarith [lo_lt_beta F, (base_le_lo F).1]

theorem abs_dt_lt_beta (F : Facts s) : |(dt s : ℝ)| < beta F := by
  linarith [lo_lt_beta F, (base_le_lo F).2]

end Real

/-! ## The cofactor at any root -/

section Cofactor

variable {s : Sub3}

/-- The incidence matrix over `ℝ`. -/
noncomputable def matR (s : Sub3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (parikh s).toMat.map (Int.castRingHom ℝ)

theorem charpoly_matR :
    (matR s).charpoly = X ^ 3 - C (tr s : ℝ) * X ^ 2 + C (mn s : ℝ) * X - C (dt s : ℝ) := by
  rw [matR, Matrix.charpoly_map, M3.charpoly_toMat]
  simp [tr, mn, dt]

/-- `X² + (β - T) X + D/β`, the cofactor of `X - β` in `χ_M` when `p(β) = 0`. -/
noncomputable def quad (s : Sub3) (β : ℝ) : ℝ[X] := X ^ 2 + C (β - tr s) * X + C (dt s / β)

theorem pR_factor {β : ℝ} (hβ : pR s β = 0) (hne : β ≠ 0) (x : ℝ) :
    pR s x = (x - β) * (x ^ 2 + (β - tr s) * x + dt s / β) := by
  have h : pR s x - (x - β) * (x ^ 2 + (β - tr s) * x + dt s / β) = x / β * pR s β := by
    unfold pR; field_simp; ring
  rwa [hβ, mul_zero, sub_eq_zero] at h

theorem charpoly_factor {β : ℝ} (hβ : pR s β = 0) (hne : β ≠ 0) :
    (matR s).charpoly = (X - C β) * quad s β := by
  unfold pR at hβ
  have e2 : dt s / β - (β - tr s) * β = mn s := by field_simp; linear_combination -hβ
  have e3 : dt s / β * β = dt s := by field_simp
  rw [charpoly_matR, quad]
  calc X ^ 3 - C (tr s : ℝ) * X ^ 2 + C (mn s : ℝ) * X - C (dt s : ℝ)
      = X ^ 3 + C ((β - tr s) - β) * X ^ 2 +
          C (dt s / β - (β - tr s) * β) * X - C (dt s / β * β) := by
        rw [e2, e3]; simp only [map_sub]; ring
    _ = _ := by simp only [map_sub, map_mul]; ring

end Cofactor

/-! ## Quadratics with both roots in the unit disc -/

/-- Jury's test, sufficiency: `Q(1) > 0`, `Q(-1) > 0`, `|Q(0)| < 1` put every complex root of
the monic real quadratic `Q = X² + a X + b` in the open unit disc. -/
theorem norm_lt_one_of_quadratic {a b : ℝ} (h1 : 0 < 1 + a + b) (h2 : 0 < 1 - a + b)
    (hb : |b| < 1) {μ : ℂ} (hμ : μ ^ 2 + a * μ + b = 0) : ‖μ‖ < 1 := by
  have hre := congrArg Complex.re hμ
  have him := congrArg Complex.im hμ
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  rw [abs_lt] at hb
  have hnsq : Complex.normSq μ < 1 := by
    rw [Complex.normSq_apply]
    by_cases hy : μ.im = 0
    · rw [hy] at hre ⊢
      set x := μ.re
      -- the other root is `y = -a - x`; `Q(1) = (1-x)(1-y)`, `Q(-1) = (1+x)(1+y)`, `b = x y`
      have e1 : 1 + a + b = (1 - x) * (1 + a + x) := by linear_combination hre
      have e2 : 1 - a + b = (1 + x) * (1 - a - x) := by linear_combination hre
      have e3 : b = x * (-a - x) := by linear_combination hre
      by_contra hx
      push Not at hx
      rcases le_or_gt 1 x with hx1 | hx1
      · have : 1 + a + x < 0 := by
          by_contra h'; push Not at h'
          nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : 1 - x ≤ 0) h']
        nlinarith
      · have hx2 : x ≤ -1 := by nlinarith
        have : 1 - a - x < 0 := by
          by_contra h'; push Not at h'
          nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : 1 + x ≤ 0) h']
        nlinarith
    · have hx : μ.re = -a / 2 := by
        have : μ.im * (2 * μ.re + a) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left hy
        linarith
      rw [hx] at hre ⊢
      nlinarith
  rw [Complex.normSq_eq_norm_sq] at hnsq
  nlinarith [norm_nonneg μ]

/-- Jury's test, necessity: if every complex root of `X² + a X + b` lies in the open unit disc,
then `Q(1) > 0`, `Q(-1) > 0` and `|Q(0)| < 1`. -/
theorem jury_of_norm_lt_one {a b : ℝ} (h : ∀ μ : ℂ, μ ^ 2 + a * μ + b = 0 → ‖μ‖ < 1) :
    0 < 1 + a + b ∧ 0 < 1 - a + b ∧ |b| < 1 := by
  rcases le_or_gt 0 (a ^ 2 - 4 * b) with hΔ | hΔ
  · -- two real roots `x₁, x₂ = (-a ± r)/2`, both in `(-1, 1)`
    set r := Real.sqrt (a ^ 2 - 4 * b)
    have hr : r ^ 2 = a ^ 2 - 4 * b := Real.sq_sqrt hΔ
    have root : ∀ x : ℝ, x ^ 2 + a * x + b = 0 → |x| < 1 := fun x hx => by
      have := h x (by exact_mod_cast hx)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have r1 := root ((-a + r) / 2) (by linear_combination hr / 4)
    have r2 := root ((-a - r) / 2) (by linear_combination hr / 4)
    have hb : b = ((-a + r) / 2) * ((-a - r) / 2) := by linear_combination hr / 4
    obtain ⟨l1, u1⟩ := abs_lt.mp r1
    obtain ⟨l2, u2⟩ := abs_lt.mp r2
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_pos (sub_pos.2 u1) (sub_pos.2 u2)]
    · nlinarith [mul_pos (neg_lt_iff_pos_add.mp l1) (neg_lt_iff_pos_add.mp l2)]
    · rw [hb, abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) r2.le).trans_lt r1
  · -- a conjugate pair with `|μ|² = b`
    set y := Real.sqrt (4 * b - a ^ 2) / 2
    have hy : y ^ 2 = (4 * b - a ^ 2) / 4 := by
      rw [div_pow, Real.sq_sqrt (by linarith)]; norm_num
    have hμ : (⟨-a / 2, y⟩ : ℂ) ^ 2 + a * ⟨-a / 2, y⟩ + b = 0 := by
      apply Complex.ext <;> simp [pow_two] <;> nlinarith
    have hn := h _ hμ
    have hns : Complex.normSq ⟨-a / 2, y⟩ = b := by
      rw [Complex.normSq_mk]; nlinarith
    have hb1 : b < 1 := by
      rw [← hns, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (⟨-a / 2, y⟩ : ℂ)]
    refine ⟨by nlinarith [sq_nonneg (1 + a / 2)], by nlinarith [sq_nonneg (1 - a / 2)], ?_⟩
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg a]

/-! ## The substitution, its spectral factorization and its contraction -/

section Build

variable {s : Sub3} (F : Facts s)

/-- The cofactor `Q = X² + (β - T) X + D/β`. -/
noncomputable def cofactor : ℝ[X] := quad s (beta F)

theorem beta_ne : beta F ≠ 0 := (zero_lt_one.trans (one_lt_beta F)).ne'

theorem factor : (matR s).charpoly = (X - C (beta F)) * cofactor F :=
  charpoly_factor (pR_beta F) (beta_ne F)

/-- `Q(1) > 0`, `Q(-1) > 0`, `|Q(0)| < 1`. -/
theorem jury : 0 < 1 + (beta F - tr s) + dt s / beta F ∧
    0 < 1 - (beta F - tr s) + dt s / beta F ∧ |(dt s : ℝ) / beta F| < 1 := by
  have h1 := one_lt_beta F
  have hp1 : pR s 1 < 0 := by
    have := horner_cast (s := s) 1; push_cast at this; rw [← this]; exact_mod_cast F.p_one
  have hm1 : pR s (-1) < 0 := by
    have := horner_cast (s := s) (-1); push_cast at this; rw [← this]; exact_mod_cast F.p_neg_one
  rw [pR_factor (pR_beta F) (beta_ne F)] at hp1 hm1
  refine ⟨?_, ?_, ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < beta F), div_lt_one (by linarith)]
    exact abs_dt_lt_beta F

theorem cofactor_small (μ : ℂ) (hμ : ((cofactor F).map (algebraMap ℝ ℂ)).IsRoot μ) :
    ‖μ‖ < 1 := by
  obtain ⟨j1, j2, j3⟩ := jury F
  refine norm_lt_one_of_quadratic j1 j2 j3 ?_
  simpa [cofactor, quad, IsRoot] using hμ

/-- `ℓ = 𝟙ᵀ Q(M)`. -/
noncomputable def ell : Fin 3 → ℝ := (fun _ => 1) ᵥ* aeval (matR s) (cofactor F)

theorem ell_vecMul : ell F ᵥ* matR s = beta F • ell F := by
  have h : aeval (matR s) (cofactor F) * matR s = beta F • aeval (matR s) (cofactor F) := by
    have e : cofactor F * X = (matR s).charpoly + C (beta F) * cofactor F := by
      rw [factor F]; ring
    have := congrArg (aeval (matR s)) e
    simpa [aeval_self_charpoly, Algebra.smul_def] using this
  rw [ell, vecMul_vecMul, h, vecMul_smul]

theorem sum_map_count (w : List (Fin 3)) (f : Fin 3 → ℝ) :
    (w.map f).sum = ∑ b, (w.count b : ℝ) * f b := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons, beq_iff_eq]
    push_cast
    simp [add_mul, Finset.sum_add_distrib]
    ring

theorem matR_apply (b a : Fin 3) : matR s b a = ((s.σ a).count b : ℝ) := by
  rw [matR, parikh_toMat]; exact Int.cast_natCast _

theorem eigen (a : Fin 3) : ((s.σ a).map (ell F)).sum = beta F * ell F a := by
  rw [sum_map_count]
  have := congrFun (ell_vecMul F) a
  simp only [vecMul, dotProduct, matR_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem matR_sq : matR s ^ 2 = (sq s).toMat.map (Int.castRingHom ℝ) := by
  rw [matR, sq, M3.toMat_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, pow_two,
    map_mul]

/-- `β ℓⱼ = c₁ⱼ β² + (c₂ⱼ - T c₁ⱼ) β + D`. -/
theorem beta_mul_ell (j : Fin 3) :
    beta F * ell F j = ((parikh s).col j : ℝ) * beta F ^ 2 +
      (((sq s).col j : ℝ) - tr s * (parikh s).col j) * beta F + dt s := by
  have hne := beta_ne F
  have hcol : ∀ x : M3, ((x.col j : ℤ) : ℝ) = ∑ i, (x.toMat.map (Int.castRingHom ℝ)) i j := by
    intro x; simp [M3.col_eq]
  rw [hcol, hcol, ← matR_sq, ← matR]
  simp only [ell, cofactor, quad, map_add, map_mul, aeval_X_pow, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, vecMul, dotProduct, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, one_mul]
  simp only [Fin.sum_univ_three, Fin.isValue]
  fin_cases j <;> simp <;> field_simp <;> ring

theorem ell_pos (j : Fin 3) : 0 < ell F j := by
  have hβ0 : 0 < beta F := zero_lt_one.trans (one_lt_beta F)
  have hmem := beta_mem F
  have hlo1 := (base_le_lo F).1
  have hc : (0 : ℝ) ≤ (parikh s).col j := by exact_mod_cast col_nonneg s j
  have hpos : (0 : ℝ) < colLB s j := by exact_mod_cast F.col_pos j
  simp only [colLB, posLB, scale] at hpos
  push_cast at hpos
  set c₁ : ℝ := ((parikh s).col j : ℝ)
  set k : ℝ := ((sq s).col j : ℝ) - (tr s : ℝ) * ((parikh s).col j : ℝ)
  set L : ℝ := (lo s : ℝ)
  set H : ℝ := (hi s : ℝ)
  -- the bound: `256 (c₁ β² + k β + D) ≥ c₁ L² + 16 min(kL, kH) + 256 D`
  have hq : c₁ * L * L ≤ 256 * (c₁ * beta F ^ 2) := by
    have : L ≤ 16 * beta F := by linarith [hmem.1]
    have hL : 0 ≤ L := by linarith
    nlinarith [mul_le_mul this this hL (by linarith)]
  have hl : min (k * L) (k * H) * 16 ≤ 256 * (k * beta F) := by
    rcases le_total 0 k with hk0 | hk0
    · have := mul_le_mul_of_nonneg_left (show L ≤ 16 * beta F by linarith [hmem.1]) hk0
      nlinarith [min_le_left (k * L) (k * H)]
    · have := mul_le_mul_of_nonpos_left (show 16 * beta F ≤ H by linarith [hmem.2]) hk0
      nlinarith [min_le_right (k * L) (k * H)]
  have key := beta_mul_ell F j
  have : 0 < beta F * ell F j := by rw [key]; nlinarith
  exact pos_of_mul_pos_right this hβ0.le

/-- **The certified substitution.** -/
noncomputable def subst : LengthSubst (Fin 3) where
  σ := s.σ
  ne_nil := F.ne
  ℓ := ell F
  ℓ_pos := ell_pos F
  β := beta F
  eigen := eigen F

theorem mat_subst : mat (subst F) = matR s := by
  ext b a; rw [matR_apply]; rfl

/-- **The spectral hypothesis, certified.** -/
noncomputable def spectral : SpectralPisot (subst F) where
  Q := cofactor F
  factor := by rw [mat_subst]; exact factor F
  simple := fun h0 => by
    have hb : 1 < (subst F).β := one_lt_beta F
    have := cofactor_small F _ (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) h0)
    rw [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)] at this
    exact (lt_asymm hb this).elim
  small := cofactor_small F

/-- **The derived contraction for a certified substitution.** -/
noncomputable def pisotData : PisotData (subst F) := (spectral F).toPisotData

/-! ## Membership in PIP3 -/

/-- The cubic over `ℚ`. -/
noncomputable def pQ (s : Sub3) : ℚ[X] := X ^ 3 - C (tr s : ℚ) * X ^ 2 + C (mn s : ℚ) * X - C (dt s : ℚ)

theorem pQ_natDegree (s : Sub3) : (pQ s).natDegree = 3 := by unfold pQ; compute_degree!

theorem pQ_irreducible (hF : Facts s) : Irreducible (pQ s) := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by simp [pQ_natDegree]) fun x hx => ?_
  set p : ℤ[X] := X ^ 3 - C (tr s) * X ^ 2 + C (mn s) * X - C (dt s)
  have hp : p.Monic := by unfold p; monicity!
  have hr : aeval x p = 0 := by simpa [p, pQ, IsRoot] using hx
  obtain ⟨r, rfl, hr0⟩ := exists_integer_of_is_root_of_monic hp hr
  have hc : p.coeff 0 = -dt s := by simp [p]
  rw [hc, dvd_neg] at hr0
  have hle : r.natAbs ≤ (dt s).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hF.dt_ne) (Int.natAbs_dvd_natAbs.mpr hr0)
  refine hF.no_root r hle ?_
  have hx' : ((horner (tr s) (mn s) (dt s) r : ℤ) : ℚ) = 0 := by
    simp only [pQ, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
    simp only [horner]; push_cast; linear_combination hx
  exact_mod_cast hx'

theorem charpoly_eq_map : (mat (subst F)).charpoly = (pQ s).map (algebraMap ℚ ℝ) := by
  rw [mat_subst, charpoly_matR]; simp [pQ]

end Build

/-- The standing class PIP3 for a length substitution: nonerasing, primitive, characteristic
polynomial irreducible over `ℚ`, Perron root `β > 1` with every other root in the open unit
disc. -/
def PIP3 {α : Type*} [Fintype α] [DecidableEq α] (S : LengthSubst α) : Prop :=
  (∀ a, S.σ a ≠ []) ∧ (∃ n, ∀ i j, 0 < ((mat S) ^ n) i j) ∧
    (∃ p : ℚ[X], Irreducible p ∧ (mat S).charpoly = p.map (algebraMap ℚ ℝ)) ∧
    1 < S.β ∧ (mat S).charpoly.IsRoot S.β ∧
    ∀ μ : ℂ, ((mat S).charpoly.map (algebraMap ℝ ℂ)).IsRoot μ → μ = S.β ∨ ‖μ‖ < 1

/-- **A certified substitution is in PIP3.** -/
theorem mem_PIP3 {s : Sub3} (F : Facts s) : PIP3 (subst F) := by
  refine ⟨F.ne, ⟨5, fun i j => ?_⟩, ⟨pQ s, pQ_irreducible F, charpoly_eq_map F⟩,
    one_lt_beta F, ?_, fun μ hμ => ?_⟩
  · rw [mat_subst, matR, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact Int.cast_pos.mpr (F.prim i j)
  · rw [(spectral F).factor]; simp
  · rw [(spectral F).factor, Polynomial.map_mul, IsRoot, eval_mul, mul_eq_zero] at hμ
    rcases hμ with h | h
    · left; simpa [sub_eq_zero] using h
    · exact Or.inr ((spectral F).small μ h)

/-- **Soundness of the certificate.** -/
theorem sound {s : Sub3} (h : check s = true) :
    ∃ S : LengthSubst (Fin 3), S.σ = s.σ ∧ PIP3 S ∧ Nonempty (PisotData S) :=
  ⟨subst (facts h), rfl, mem_PIP3 (facts h), ⟨pisotData (facts h)⟩⟩

/-! ## Completeness of the rejection certificate -/

/-- **A rejected substitution is not in PIP3**, whatever lengths `ℓ` and root `β` it is given. -/
theorem refute_spec {s : Sub3} {S : LengthSubst (Fin 3)} (hS : S.σ = s.σ) (hP : PIP3 S) :
    refute s = false := by
  obtain ⟨-, -, ⟨p, hp, hχ⟩, h1, hroot, hsmall⟩ := hP
  have hmat : mat S = matR s := by ext b a; rw [matR_apply]; simp [mat, hS]
  have hpQ : p = pQ s := by
    apply Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [← hχ, hmat, charpoly_matR]; simp [pQ]
  subst hpQ
  have hβ0 : S.β ≠ 0 := by linarith
  have hβ : pR s S.β = 0 := by
    rw [hmat, charpoly_matR] at hroot
    simp only [IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hroot
    unfold pR; linear_combination hroot
  -- the cofactor is `quad s β`, with its roots in the open unit disc
  let H := SpectralPisot.ofIrreducible (pQ s) hp hχ fun μ hμ hne => (hsmall μ hμ).resolve_left hne
  have hQ : H.Q = quad s S.β := by
    refine mul_left_cancel₀ (X_sub_C_ne_zero S.β) ?_
    rw [← H.factor, hmat, charpoly_factor hβ hβ0]
  obtain ⟨j1, j2, j3⟩ := jury_of_norm_lt_one (a := S.β - tr s) (b := dt s / S.β) fun μ hμ =>
    H.small μ (by rw [hQ]; simpa [quad, IsRoot] using hμ)
  have hpos : 0 < S.β := by linarith
  have hD : |(dt s : ℝ)| < S.β := by
    rwa [abs_div, abs_of_pos hpos, div_lt_one hpos] at j3
  have hf := pR_factor hβ hβ0
  by_contra hr
  have hr' : refute s = true := by simpa using hr
  simp only [refute, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hr'
  rcases hr' with ((h | h) | h) | ⟨h2, h3⟩
  · have e := horner_cast (s := s) 1
    push_cast at e
    have : (0 : ℝ) ≤ pR s 1 := by rw [← e]; exact_mod_cast h
    rw [hf] at this; nlinarith
  · have e := horner_cast (s := s) (-1)
    push_cast at e
    have : (0 : ℝ) ≤ pR s (-1) := by rw [← e]; exact_mod_cast h
    rw [hf] at this; nlinarith
  · -- an integer root makes `pQ` reducible
    by_contra hall
    have : ∀ r : ℤ, r.natAbs ≤ (dt s).natAbs → horner (tr s) (mn s) (dt s) r ≠ 0 := by
      intro r _ hr0
      have hx : (pQ s).IsRoot (r : ℚ) := by
        have : ((horner (tr s) (mn s) (dt s) r : ℤ) : ℚ) = 0 := by exact_mod_cast hr0
        simp only [horner] at this; push_cast at this
        simp only [pQ, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
        linear_combination this
      have := Polynomial.degree_eq_one_of_irreducible_of_root hp hx
      rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero hp), pQ_natDegree] at this
      exact absurd this (by decide)
    rw [noRoot_of_forall this] at h; exact absurd h (by decide)
  · -- `|D| ≥ 2` and `p(|D|) ≥ 0`, while `|D| < β` and `p < 0` on `[1, β)`
    set n := (dt s).natAbs
    have hx : (n : ℝ) = |(dt s : ℝ)| := by simp [n, Nat.cast_natAbs]
    have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have e := horner_cast (s := s) (n : ℤ)
    rw [Int.cast_natCast] at e
    have h0 : (0 : ℝ) ≤ pR s n := by rw [← e]; exact_mod_cast h3
    rw [hf] at h0
    have hb := abs_lt.mp j3
    have hq : 0 < (n : ℝ) ^ 2 + (S.β - tr s) * n + dt s / S.β := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < n - 1)
        (by linarith : (0 : ℝ) < n + 1 + (S.β - tr s))]
    nlinarith [mul_neg_of_neg_of_pos (by linarith : (n : ℝ) - S.β < 0) hq]

/-! ## Controls -/

/-- Tribonacci `01/02/0` is certified. -/
theorem check_tribonacci : check ([0, 1], [0, 2], [0]) = true := by decide +kernel

/-- `doubled` cannot be written on three letters; its three-letter analogue with root `-1`,
`0 ↦ 0 1 1, 1 ↦ 1 0 0, 2 ↦ 2`, is reducible and rejected. -/
theorem check_reducible : check ([0, 1, 1], [1, 0, 0], [2]) = false := by decide +kernel

end Psc.PeriodicPartnerSpectralCertificate
