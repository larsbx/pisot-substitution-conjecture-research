/-
# Wielandt's equality case, the real gauge, and the `(2,2,0)` eigenvalue

`docs/c4-concentration-attack-2026-11-06.md` §2 (Theorem A(ii), A(iii)) applies
Wielandt's theorem to a matrix `S` dominated entrywise by a non-negative,
strongly connected matrix `N` with a positive left eigenvector `L` for `β`, and
an eigenvector `S x = μ x` with `|μ| = β`.  This module proves the equality case
of Wielandt's theorem from first principles on top of `PscVerif.PerronCore`
(without the Perron–Frobenius theorem) and assembles the `(2,2,0)` exclusion
with `PscVerif.Degree4Sector`.

Standing data (each a hypothesis only of the theorems that use it):

* `ι` a finite index type, `N : Matrix ι ι ℝ`;
* `hSC : StronglyConnected N` (from `PerronCore`): every ordered pair is joined
  by a directed path of length `≥ 1` along positive entries;
* `L : ι → ℝ`, `hL : ∀ i, 0 < L i`, `hLN : L ᵥ* N = β • L`: a strictly positive
  left eigenvector of `N` for the real number `β`;
* domination: `‖S i j‖ ≤ N i j` (complex `S`) or `|S i j| ≤ N i j` (real `S`);
* an eigenvector `x ≠ 0` of `S` for `μ` with `‖μ‖ = β`.

Proved:

1. `eq_norm_mul_of_norm_sum_eq` (triangle equality): if
   `‖∑ j, z j‖ = ∑ j, ‖z j‖` and `∑ j, z j ≠ 0`, then every
   `z j = ‖z j‖ * (∑ z / ‖∑ z‖)`.
2. `wielandt`: with `c = μ / β` and `d i = x i / ‖x i‖`, `‖c‖ = 1`, every
   `‖d i‖ = 1`, and `S i j = c * d i * N i j * (d j)⁻¹` for all `i, j`.
   (`beta_pos`: in this setting `β > 0` automatically.)
3. `gauge_of_real` (Theorem A(iii)): if `S` is real, `s = ±1` and
   `S x = (s β) x`, then `S i j = s * D i * N i j * D j` for a sign vector
   `D : ι → {±1}`.
4. `cycle_relation`: if `S` is real and `S x = μ x` with `‖μ‖ = β`, then
   `(μ / β) ^ (2 ℓ) = 1` for some `ℓ ≥ 1` (the length of a directed cycle).
5. `no_220_eigenvalue` (Theorem A(ii), `(2,2,0)` case): for an irreducible
   rational cubic with a real root `β > 1` and a non-real root `α`, `|α| < 1`,
   with `β α ᾱ = d`, `d² = 1`, no real `S` dominated by `N` (in the setting
   above, with this `β`) has the eigenvalue `β² α²`.

Not formalized here: the Perron–Frobenius theorem (existence of `L`, `β` as the
spectral radius of `N`), the identification of `N`, `S`, `β` with the
substitution data of the attack document (incidence matrix, cocycle,
`thm:parikh`, `prop:cocycle`), the Witt-formula weight decomposition of `Lie₄`,
and the remaining sectors of Theorem A.

Deviations from the original task statement, all of which only weaken
hypotheses: no theorem assumes `N ≥ 0` (it follows from the domination
hypothesis) and no theorem assumes `β > 0` (it follows from the other
hypotheses, `beta_pos`); `no_220_eigenvalue` needs no separate `β > 0`.
-/
import PscVerif.PerronCore
import PscVerif.Degree4Sector

set_option linter.unusedSectionVars false

namespace Psc.Wielandt

open Matrix Finset Psc.PerronCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `Re (conj u * w) = ‖w‖` with `‖u‖ = 1`, then `w = ‖w‖ * u`. -/
theorem eq_norm_mul_of_re_eq {u w : ℂ} (hu : ‖u‖ = 1)
    (h : ((starRingEnd ℂ) u * w).re = ‖w‖) : w = (‖w‖ : ℂ) * u := by
  set v := (starRingEnd ℂ) u * w with hv
  have hvn : ‖v‖ = ‖w‖ := by rw [hv, norm_mul, Complex.norm_conj, hu, one_mul]
  have him : v.im = 0 := by
    apply Complex.abs_re_eq_norm.1
    rw [h, hvn, abs_of_nonneg (norm_nonneg _)]
  have hvr : v = (‖w‖ : ℂ) := by
    apply Complex.ext
    · simp [h]
    · simp [him]
  have huu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj', hu]; norm_num
  calc w = (u * (starRingEnd ℂ) u) * w := by rw [huu, one_mul]
    _ = v * u := by rw [hv]; ring
    _ = (‖w‖ : ℂ) * u := by rw [hvr]

/-- **(1)** Equality case of the triangle inequality for a finite sum of complex
numbers: every summand points in the direction of the (non-zero) sum. -/
theorem eq_norm_mul_of_norm_sum_eq {κ : Type*} [Fintype κ] (z : κ → ℂ)
    (h : ‖∑ j, z j‖ = ∑ j, ‖z j‖) (hs : ∑ j, z j ≠ 0) :
    ∀ j, z j = (‖z j‖ : ℂ) * ((∑ k, z k) / (‖∑ k, z k‖ : ℂ)) := by
  set s := ∑ k, z k with hsdef
  have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs
  have hsnC : (‖s‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsn
  set u := s / (‖s‖ : ℂ) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hsn]
  have hus : (starRingEnd ℂ) u * s = (‖s‖ : ℂ) := by
    rw [hudef, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
      Complex.mul_conj', pow_two, mul_div_assoc, div_self hsnC, mul_one]
  have hle : ∀ j ∈ (Finset.univ : Finset κ), ((starRingEnd ℂ) u * z j).re ≤ ‖z j‖ := by
    intro j _
    calc ((starRingEnd ℂ) u * z j).re ≤ ‖(starRingEnd ℂ) u * z j‖ := Complex.re_le_norm _
      _ = ‖z j‖ := by rw [norm_mul, Complex.norm_conj, hu, one_mul]
  have hsum : ∑ j, ((starRingEnd ℂ) u * z j).re = ∑ j, ‖z j‖ := by
    rw [← Complex.re_sum, ← Finset.mul_sum, ← hsdef, hus, Complex.ofReal_re, h]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  intro j
  exact eq_norm_mul_of_re_eq hu (heq j (Finset.mem_univ j))

/-- In the setting of `wielandt`, `β > 0` automatically. -/
theorem beta_pos (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℂ)
    (hS : ∀ i j, ‖S i j‖ ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : S *ᵥ x = μ • x) : 0 < β := by
  have hN : ∀ i j, 0 ≤ N i j := fun i j => (norm_nonneg _).trans (hS i j)
  obtain ⟨hpos, -⟩ := norm_eigen_pos N hSC L hL β hLN S hS x hx0 μ hμ hx
  obtain ⟨hw, -⟩ := norm_eigen N L hL β hLN S hS x μ hμ hx
  rcases (show 0 ≤ β from hμ ▸ norm_nonneg μ).lt_or_eq with hb | hb
  · exact hb
  · exfalso
    obtain ⟨i, -⟩ := Function.ne_iff.1 hx0
    obtain ⟨j, hij, -⟩ := Relation.TransGen.head'_iff.1 (hSC i i)
    have hrow := congrFun hw i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← hb, zero_mul] at hrow
    have hle : N i j * ‖x j‖ ≤ ∑ k, N i k * ‖x k‖ :=
      Finset.single_le_sum (f := fun k => N i k * ‖x k‖)
        (fun k _ => mul_nonneg (hN i k) (norm_nonneg _)) (Finset.mem_univ j)
    have := mul_pos hij (hpos j)
    linarith

/-- **(2) Wielandt's equality case.**  If `‖S i j‖ ≤ N i j`, `S x = μ x`,
`x ≠ 0` and `‖μ‖ = β`, then with `c = μ / β` and `d i = x i / ‖x i‖` we have
`‖c‖ = 1`, `‖d i‖ = 1` and `S = c · D N D⁻¹` with `D = diag d`. -/
theorem wielandt (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℂ)
    (hS : ∀ i j, ‖S i j‖ ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : S *ᵥ x = μ • x) :
    ‖μ / (β : ℂ)‖ = 1 ∧ (∀ i, ‖x i / (‖x i‖ : ℂ)‖ = 1) ∧
      ∀ i j, S i j = μ / (β : ℂ) * (x i / (‖x i‖ : ℂ)) * (N i j : ℂ) *
        (x j / (‖x j‖ : ℂ))⁻¹ := by
  have hβ : 0 < β := beta_pos N hSC L hL β hLN S hS x hx0 μ hμ hx
  obtain ⟨hpos, hNeq⟩ := norm_eigen_pos N hSC L hL β hLN S hS x hx0 μ hμ hx
  obtain ⟨-, htri⟩ := norm_eigen N L hL β hLN S hS x μ hμ hx
  have hβC : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hnC : ∀ i, (‖x i‖ : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hpos i).ne'
  have hxne : ∀ i, x i ≠ 0 := fun i => norm_pos_iff.1 (hpos i)
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_div, hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ, div_self hβ.ne']
  · intro i
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (hpos i).ne']
  · intro i j
    have hrowsum : ∑ k, S i k * x k = μ * x i := by
      have := congrFun hx i
      simpa [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
    have hμne : μ ≠ 0 := by
      intro h; rw [h, norm_zero] at hμ; exact hβ.ne' hμ.symm
    have hne : ∑ k, S i k * x k ≠ 0 := by
      rw [hrowsum]; exact mul_ne_zero hμne (hxne i)
    have hz := eq_norm_mul_of_norm_sum_eq (fun k => S i k * x k) (htri i) hne j
    rw [hrowsum, norm_mul, norm_mul, hNeq, hμ] at hz
    push_cast at hz
    have hxj := hxne j
    have hni := hnC i
    have hnj := hnC j
    field_simp at hz
    field_simp
    linear_combination hz

/-- A complex number that equals a real number and has modulus one is `±1`. -/
theorem eq_one_or_neg_one_of_real {q : ℂ} (r : ℝ) (hqr : q = r) (hq : ‖q‖ = 1) :
    q = 1 ∨ q = -1 := by
  rw [hqr, Complex.norm_real, Real.norm_eq_abs] at hq
  rcases abs_eq (zero_le_one) |>.1 hq with h | h
  · left; rw [hqr, h]; simp
  · right; rw [hqr, h]; simp

/-- **(3) Theorem A(iii): the real gauge.**  If `S` is real with
`|S i j| ≤ N i j`, `s = ±1` and `S x = (s β) x` for some `x ≠ 0`, then
`S = s · D N D` for a diagonal matrix `D` of signs. -/
theorem gauge_of_real (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℝ)
    (hS : ∀ i j, |S i j| ≤ N i j) (s : ℝ) (hs : s = 1 ∨ s = -1) (x : ι → ℂ)
    (hx0 : x ≠ 0) (hx : S.map ((↑) : ℝ → ℂ) *ᵥ x = ((s * β : ℝ) : ℂ) • x) :
    ∃ D : ι → ℝ, (∀ i, D i = 1 ∨ D i = -1) ∧ ∀ i j, S i j = s * D i * N i j * D j := by
  have hN : ∀ i j, 0 ≤ N i j := fun i j => (abs_nonneg _).trans (hS i j)
  obtain ⟨i0, -⟩ := Function.ne_iff.1 hx0
  have hβ0 : 0 ≤ β := beta_nonneg N hN L hL β hLN i0
  have hS' : ∀ i j, ‖(S.map ((↑) : ℝ → ℂ)) i j‖ ≤ N i j := fun i j => by
    simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hS i j
  have hsabs : |s| = 1 := by rcases hs with h | h <;> simp [h]
  have hμ : ‖((s * β : ℝ) : ℂ)‖ = β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, hsabs, one_mul, abs_of_nonneg hβ0]
  have hβ : 0 < β := beta_pos N hSC L hL β hLN _ hS' x hx0 _ hμ hx
  obtain ⟨-, hd, hW⟩ := wielandt N hSC L hL β hLN _ hS' x hx0 _ hμ hx
  set d : ι → ℂ := fun i => x i / (‖x i‖ : ℂ) with hddef
  have hβC : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hc : ((s * β : ℝ) : ℂ) / (β : ℂ) = (s : ℂ) := by
    push_cast; field_simp
  have hW' : ∀ i j, (S i j : ℂ) = (s : ℂ) * d i * (N i j : ℂ) * (d j)⁻¹ := by
    intro i j
    have := hW i j
    rw [hc, Matrix.map_apply] at this
    exact this
  have hdne : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i; simp only [hddef] at h; rw [h, norm_zero] at this; exact zero_ne_one this
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> simp [h]
  -- on a positive edge, `d a / d b = ±1`
  have hedge : ∀ a b, 0 < N a b → d a * (d b)⁻¹ = 1 ∨ d a * (d b)⁻¹ = -1 := by
    intro a b hab
    apply eq_one_or_neg_one_of_real (S a b / (s * N a b))
    · have h := hW' a b
      have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0
      have hNC : (N a b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hab.ne'
      push_cast
      rw [h]
      field_simp
    · rw [norm_mul, norm_inv, hd a, hd b]; norm_num
  -- propagate from the base vertex `i0`
  have hprop : ∀ i, d i / d i0 = 1 ∨ d i / d i0 = -1 := by
    intro i
    induction hSC i0 i with
    | single h =>
      rename_i b
      rcases hedge i0 b h with h1 | h1
      · left
        have : d i0 = d b := by
          have := congrArg (· * d b) h1; simp only [one_mul] at this
          rw [← this]; field_simp [hdne b]
        rw [this, div_self (hdne b)]
      · right
        have : d i0 = -d b := by
          have := congrArg (· * d b) h1
          rw [← neg_one_mul, ← this]; field_simp [hdne b]
        rw [this, div_neg, div_self (hdne b)]
    | tail _ h ih =>
      rename_i a b _
      have key : d b / d i0 = (d a / d i0) * (d a * (d b)⁻¹)⁻¹ := by
        field_simp [hdne a, hdne b, hdne i0]
      rw [key]
      rcases ih with h1 | h1 <;> rcases hedge a b h with h2 | h2 <;>
        simp [h1, h2]
  classical
  refine ⟨fun i => if d i / d i0 = 1 then 1 else -1, fun i => by
    by_cases h : d i / d i0 = 1 <;> simp [h], fun i j => ?_⟩
  have hD : ∀ i, (((if d i / d i0 = 1 then (1 : ℝ) else -1 : ℝ)) : ℂ) = d i / d i0 := by
    intro i
    rcases hprop i with h | h
    · simp [h]
    · have hne : ¬ (d i / d i0 = 1) := by rw [h]; norm_num
      simp only [hne, ite_false]; push_cast; rw [h]
  apply Complex.ofReal_injective
  push_cast
  rw [hD i, hD j, hW' i j]
  have hsq : (d j / d i0)⁻¹ = d j / d i0 := by
    rcases hprop j with h | h <;> rw [h] <;> norm_num
  calc (s : ℂ) * d i * (N i j : ℂ) * (d j)⁻¹
      = (s : ℂ) * (d i / d i0) * (N i j : ℂ) * (d j / d i0)⁻¹ := by
        field_simp [hdne j, hdne i0]
    _ = (s : ℂ) * (d i / d i0) * (N i j : ℂ) * (d j / d i0) := by rw [hsq]

/-- **(4) Cycle relation.**  If `S` is real with `|S i j| ≤ N i j` and
`S x = μ x` with `x ≠ 0` and `‖μ‖ = β`, then `(μ / β) ^ (2 ℓ) = 1` for some
`ℓ ≥ 1` (the length of a directed cycle of `N`). -/
theorem cycle_relation (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℝ)
    (hS : ∀ i j, |S i j| ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : S.map ((↑) : ℝ → ℂ) *ᵥ x = μ • x) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ (μ / (β : ℂ)) ^ (2 * ℓ) = 1 := by
  have hS' : ∀ i j, ‖(S.map ((↑) : ℝ → ℂ)) i j‖ ≤ N i j := fun i j => by
    simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hS i j
  obtain ⟨hc, hd, hW⟩ := wielandt N hSC L hL β hLN _ hS' x hx0 μ hμ hx
  set c := μ / (β : ℂ) with hcdef
  set d : ι → ℂ := fun i => x i / (‖x i‖ : ℂ) with hddef
  have hdne : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i; simp only [hddef] at h; rw [h, norm_zero] at this; exact zero_ne_one this
  have hedge : ∀ a b, 0 < N a b → (c * d a * (d b)⁻¹) ^ 2 = 1 := by
    intro a b hab
    have hNC : (N a b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hab.ne'
    have hreal : c * d a * (d b)⁻¹ = ((S a b / N a b : ℝ) : ℂ) := by
      have h := hW a b
      rw [Matrix.map_apply] at h
      push_cast
      rw [h]
      simp only [hddef]
      field_simp
    have hn : ‖c * d a * (d b)⁻¹‖ = 1 := by
      rw [norm_mul, norm_mul, norm_inv, hc, hd a, hd b]; norm_num
    rcases eq_one_or_neg_one_of_real _ hreal hn with h | h <;> rw [h] <;> norm_num
  have hpath : ∀ a b, Relation.TransGen (fun a b => 0 < N a b) a b →
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ (c ^ ℓ * d a * (d b)⁻¹) ^ 2 = 1 := by
    intro a b hab
    induction hab with
    | single h =>
      rename_i b'
      exact ⟨1, le_refl _, by simpa using hedge a b' h⟩
    | tail _ h ih =>
      rename_i b' e _
      obtain ⟨ℓ, hℓ, hq⟩ := ih
      refine ⟨ℓ + 1, by omega, ?_⟩
      have he := hedge b' e h
      have : c ^ (ℓ + 1) * d a * (d e)⁻¹ =
          (c ^ ℓ * d a * (d b')⁻¹) * (c * d b' * (d e)⁻¹) := by
        field_simp [hdne b']
        ring
      rw [this, mul_pow, hq, he, one_mul]
  obtain ⟨i, -⟩ := Function.ne_iff.1 hx0
  obtain ⟨ℓ, hℓ, hq⟩ := hpath i i (hSC i i)
  refine ⟨ℓ, hℓ, ?_⟩
  have : c ^ ℓ * d i * (d i)⁻¹ = c ^ ℓ := by field_simp [hdne i]
  rw [this, ← pow_mul, mul_comm] at hq
  exact hq

/-- **(5) Theorem A(ii), the `(2,2,0)` case.**  Let `f` be an irreducible
rational cubic with a real root `β > 1` and a non-real root `α` with `|α| < 1`
and `β α ᾱ = d`, `d² = 1`.  If `N`, `L` are as in `PerronCore` for this `β`,
then no real matrix `S` with `|S i j| ≤ N i j` has the eigenvalue `β² α²`.
Since `d = β|α|² > 0` here, `d² = 1` is equivalent to `d = 1` (`|det M| = 1`
with `det M = β|α|²` positive).  Which eigenvalue of `S` lies in the
`(2,2,0)` orbit is a Galois-orbit question, not formalized in this module. -/
theorem no_220_eigenvalue (f : Polynomial ℚ) (hf : Irreducible f) (hdeg : f.natDegree = 3)
    (β : ℝ) (hβ1 : 1 < β) (hβf : Polynomial.aeval (β : ℂ) f = 0) (α : ℂ)
    (hαf : Polynomial.aeval α f = 0) (hnr : α.im ≠ 0) (hα1 : ‖α‖ < 1) (d : ℂ)
    (hdet : (β : ℂ) * α * (starRingEnd ℂ) α = d) (hd : d ^ 2 = 1)
    (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℝ) (hS : ∀ i j, |S i j| ≤ N i j)
    (x : ι → ℂ) (hx0 : x ≠ 0)
    (hx : S.map ((↑) : ℝ → ℂ) *ᵥ x = ((β : ℂ) ^ 2 * α ^ 2) • x) : False := by
  have hβ0 : 0 < β := by linarith
  have hα0 : α ≠ 0 := fun h => hnr (by rw [h]; simp)
  have hconj0 : (starRingEnd ℂ) α ≠ 0 := (map_ne_zero _).2 hα0
  -- `β |α|² = 1`
  have hdn : ‖d‖ = 1 := by
    have h := congrArg (‖·‖) hd
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg d) two_ne_zero).1 h
  have hβα : β * ‖α‖ ^ 2 = 1 := by
    have h := congrArg (‖·‖) hdet
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ0, hdn] at h
    rw [← h]; ring
  have hμ : ‖(β : ℂ) ^ 2 * α ^ 2‖ = β := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
    calc β ^ 2 * ‖α‖ ^ 2 = β * (β * ‖α‖ ^ 2) := by ring
      _ = β := by rw [hβα, mul_one]
  obtain ⟨ℓ, hℓ, hcyc⟩ := cycle_relation N hSC L hL β hLN S hS x hx0 _ hμ hx
  have hβC : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ0.ne'
  have hc : (β : ℂ) ^ 2 * α ^ 2 / (β : ℂ) = (β : ℂ) * α ^ 2 := by
    field_simp
  rw [hc] at hcyc
  have hpow := Psc.Degree4Sector.pow_eq_conj_pow_of_cycle (β : ℂ) α d hα0 hconj0 hdet hd ℓ hcyc
  have hβn : 1 < ‖(β : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  exact Psc.Degree4Sector.no_220_sector f hf hdeg (β : ℂ) α hβf hαf hnr hβn hα1 (2 * ℓ)
    (by omega) hpow

end Psc.Wielandt
