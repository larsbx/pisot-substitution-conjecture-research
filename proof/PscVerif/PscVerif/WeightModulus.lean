/-
# Theorem A(ii) at degree four: the modulus eliminations

`docs/c4-concentration-attack-2026-11-06.md` §2.  The weights of `Lie₄(ℚ³)` are
the permutations of `(3,1,0)`, `(2,2,0)` and `(2,1,1)`; an eigenvalue of `Φ`
that can occur on `im Q₄` must have modulus at most `ρ(S) ≤ β`.  This module
proves the elementary modulus inequalities that eliminate or constrain each
weight orbit.

## Standing setting (each theorem assumes only the subset it uses)

* `β : ℝ` with `1 < β` — the Perron (Pisot) root;
* `α γ : ℂ` with `‖α‖ < 1`, `‖γ‖ < 1` — the two conjugates inside the unit disc;
* `d : ℂ` with `(β : ℂ) * α * γ = d` — `d = det M` is the product of the three
  roots;
* `1 ≤ ‖d‖` — `d` is a nonzero rational integer (the norm of the algebraic
  integer `β`), so its modulus is at least one.  Only this inequality is used,
  not integrality.

## What is proved

* `inv_lt_norm_left`, `inv_lt_norm_right`: `β⁻¹ < ‖α‖` and `β⁻¹ < ‖γ‖`.
* `weight_310`: `β² < ‖β³α‖`, `β² < ‖β³γ‖`, and hence `β < ‖β³α‖`,
  `β < ‖β³γ‖`: the moduli of `β³α`, `β³γ` exceed `β`.  Excluding the whole
  `(3,1,0)` orbit also needs the Galois-orbit step (some conjugate of an
  eigenvalue puts the exponent `3` on `β`), not formalized in this module.
* `weight_220`: if `‖β²α²‖ ≤ β` and `‖β²γ²‖ ≤ β`, then `‖d‖ = 1`,
  `‖α‖ = ‖γ‖` and `‖β²α²‖ = β` (the `(2,2,0)` orbit survives the modulus test
  only if `|d| = 1` and `|α| = |γ|`, with modulus exactly `β`; that `α` is then
  non-real uses irreducibility and is not formalized in this module).  This
  theorem does not need `‖α‖ < 1`, `‖γ‖ < 1`, so they are omitted from it.
* `weight_211`: if `‖d β‖ ≤ β` then `‖d‖ = 1`.
* `weight_211_moduli`: if `‖d‖ = 1`, the three `(2,1,1)` eigenvalues
  `dβ, dα, dγ` have moduli `β, ‖α‖, ‖γ‖`, each at most `β`.
* `weight_111`: the degree-three analogue: `‖βαγ‖ = ‖d‖` and `‖d‖ < β`.
* `aeval_monomial_algHom`, `gal_monomial_relation`: Galois transport of a
  rational polynomial relation satisfied by a monomial `β^a α^b γ^c`: any
  `ℚ`-algebra endomorphism `σ` (in particular any element of `f.Gal` acting on
  the splitting field of `f`) carries it to the same relation for
  `(σβ)^a (σα)^b (σγ)^c`, and sends roots of `f` to roots of `f`.

## What is NOT formalized

* The identification of the weights of `Lie₄(ℚ³)` (Witt formula), the bound
  `ρ(S) ≤ β` (`prop:cocycle`), Wielandt's theorem, and the semisimplicity of
  `Φ`; these are the surrounding steps of Theorem A and are not touched here.
* The cycle argument closing the `(2,2,0)` case (`(βα²)^{2ℓ} = 1`); its
  algebraic tail is `PscVerif.Degree4Sector.no_220_sector`.
* That `d` is an integer: only `1 ≤ ‖d‖` is assumed.
* In the Galois lemma, the statement that `σ` permutes the three roots
  `β, α, γ` (it is only shown that `σ` maps each root of `f` to a root of `f`),
  and the extension of an element of `Gal(f)` to an automorphism of `ℂ`.  The
  lemma is stated for an arbitrary `ℚ`-algebra endomorphism of an arbitrary
  `ℚ`-algebra and, separately, for `f.Gal` acting on `f.SplittingField`;
  irreducibility and distinctness of roots are not needed for it and are not
  assumed.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace Psc.WeightModulus

open Polynomial

section Moduli

variable {β : ℝ} {α γ d : ℂ}

/-- `‖d‖ = β ‖α‖ ‖γ‖`. -/
theorem norm_d (hβ : 1 < β) (hdet : (β : ℂ) * α * γ = d) :
    ‖d‖ = β * ‖α‖ * ‖γ‖ := by
  rw [← hdet, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

/-- The small conjugate `α` satisfies `β⁻¹ < ‖α‖`. -/
theorem inv_lt_norm_left (hβ : 1 < β) (hγ : ‖γ‖ < 1)
    (hdet : (β : ℂ) * α * γ = d) (hd : 1 ≤ ‖d‖) : β⁻¹ < ‖α‖ := by
  have hn := norm_d hβ hdet
  have hβ0 : 0 < β := by linarith
  have hα0 : 0 ≤ ‖α‖ := norm_nonneg _
  have hγ0 : 0 ≤ ‖γ‖ := norm_nonneg _
  -- 1 ≤ β ‖α‖ ‖γ‖ < β ‖α‖
  have h1 : 1 < β * ‖α‖ := by
    have hpos : 0 < β * ‖α‖ := by
      rcases hα0.lt_or_eq with h | h
      · positivity
      · rw [← h] at hn; nlinarith
    nlinarith [mul_lt_mul_of_pos_left hγ hpos]
  rw [inv_lt_iff_one_lt_mul₀' hβ0]
  linarith

/-- Symmetrically, `β⁻¹ < ‖γ‖`. -/
theorem inv_lt_norm_right (hβ : 1 < β) (hα : ‖α‖ < 1)
    (hdet : (β : ℂ) * α * γ = d) (hd : 1 ≤ ‖d‖) : β⁻¹ < ‖γ‖ := by
  have hdet' : (β : ℂ) * γ * α = d := by rw [← hdet]; ring
  exact inv_lt_norm_left hβ hα hdet' hd

private theorem cube_bound (hβ : 1 < β) {x : ℂ} (hx : β⁻¹ < ‖x‖) :
    β ^ 2 < ‖(β : ℂ) ^ 3 * x‖ := by
  have hβ0 : 0 < β := by linarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have : β ^ 3 * β⁻¹ = β ^ 2 := by field_simp
  calc β ^ 2 = β ^ 3 * β⁻¹ := this.symm
    _ < β ^ 3 * ‖x‖ := mul_lt_mul_of_pos_left hx (by positivity)

/-- **Weight `(3,1,0)`.** Both `β³α` and `β³γ` have modulus exceeding `β²`,
hence exceeding `β`. -/
theorem weight_310 (hβ : 1 < β) (hα : ‖α‖ < 1) (hγ : ‖γ‖ < 1)
    (hdet : (β : ℂ) * α * γ = d) (hd : 1 ≤ ‖d‖) :
    β ^ 2 < ‖(β : ℂ) ^ 3 * α‖ ∧ β ^ 2 < ‖(β : ℂ) ^ 3 * γ‖ ∧
      β < ‖(β : ℂ) ^ 3 * α‖ ∧ β < ‖(β : ℂ) ^ 3 * γ‖ := by
  have h1 := cube_bound hβ (inv_lt_norm_left hβ hγ hdet hd)
  have h2 := cube_bound hβ (inv_lt_norm_right hβ hα hdet hd)
  have hsq : β < β ^ 2 := by nlinarith
  exact ⟨h1, h2, hsq.trans h1, hsq.trans h2⟩

/-- **Weight `(2,2,0)`.** If both `β²α²` and `β²γ²` have modulus at most `β`,
then `|d| = 1`, `|α| = |γ|`, and `|β²α²| = β`. -/
theorem weight_220 (hβ : 1 < β)
    (hdet : (β : ℂ) * α * γ = d) (hd : 1 ≤ ‖d‖)
    (h1 : ‖(β : ℂ) ^ 2 * α ^ 2‖ ≤ β) (h2 : ‖(β : ℂ) ^ 2 * γ ^ 2‖ ≤ β) :
    ‖d‖ = 1 ∧ ‖α‖ = ‖γ‖ ∧ ‖(β : ℂ) ^ 2 * α ^ 2‖ = β := by
  have hβ0 : 0 < β := by linarith
  have hn := norm_d hβ hdet
  have ea : ‖(β : ℂ) ^ 2 * α ^ 2‖ = β ^ 2 * ‖α‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ0]
  have eg : ‖(β : ℂ) ^ 2 * γ ^ 2‖ = β ^ 2 * ‖γ‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ0]
  rw [ea] at h1 ⊢
  rw [eg] at h2
  set a := ‖α‖ with ha_def
  set g := ‖γ‖ with hg_def
  have ha0 : 0 ≤ a := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hA : 0 ≤ β ^ 2 * a ^ 2 := by positivity
  have hG : 0 ≤ β ^ 2 * g ^ 2 := by positivity
  -- (β²a²)(β²g²) = β² ‖d‖²
  have hprod : (β ^ 2 * a ^ 2) * (β ^ 2 * g ^ 2) = β ^ 2 * ‖d‖ ^ 2 := by
    rw [hn]; ring
  have hle : (β ^ 2 * a ^ 2) * (β ^ 2 * g ^ 2) ≤ β * β :=
    mul_le_mul h1 h2 hG hβ0.le
  have hd2 : ‖d‖ ^ 2 ≤ 1 := by
    have : β ^ 2 * ‖d‖ ^ 2 ≤ β ^ 2 * 1 := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hd1 : ‖d‖ = 1 := by nlinarith [norm_nonneg d]
  -- now the product equals β², and each factor is ≤ β
  have hprod' : (β ^ 2 * a ^ 2) * (β ^ 2 * g ^ 2) = β * β := by
    rw [hprod, hd1]; ring
  have hAeq : β ^ 2 * a ^ 2 = β := by
    by_contra hne
    have hlt : β ^ 2 * a ^ 2 < β := lt_of_le_of_ne h1 hne
    have : (β ^ 2 * a ^ 2) * (β ^ 2 * g ^ 2) < β * β := by
      rcases hG.lt_or_eq with hGp | hG0
      · calc (β ^ 2 * a ^ 2) * (β ^ 2 * g ^ 2) < β * (β ^ 2 * g ^ 2) :=
              mul_lt_mul_of_pos_right hlt hGp
          _ ≤ β * β := mul_le_mul_of_nonneg_left h2 hβ0.le
      · rw [← hG0]; nlinarith
    linarith
  have hGeq : β ^ 2 * g ^ 2 = β := by
    rw [hAeq] at hprod'
    exact mul_left_cancel₀ hβ0.ne' hprod'
  have hag : a ^ 2 = g ^ 2 := by
    have : β ^ 2 * a ^ 2 = β ^ 2 * g ^ 2 := by rw [hAeq, hGeq]
    exact mul_left_cancel₀ (by positivity) this
  refine ⟨hd1, ?_, hAeq⟩
  exact (pow_left_inj₀ ha0 hg0 two_ne_zero).mp hag

/-- **Weight `(2,1,1)`, first half.** If the eigenvalue `dβ` has modulus at
most `β`, then `|d| = 1`. -/
theorem weight_211 (hβ : 1 < β) (hd : 1 ≤ ‖d‖) (h : ‖d * (β : ℂ)‖ ≤ β) :
    ‖d‖ = 1 := by
  have hβ0 : 0 < β := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0] at h
  have : ‖d‖ ≤ 1 := by nlinarith
  linarith

/-- **Weight `(2,1,1)`, second half.** When `|d| = 1`, the three eigenvalues
`dβ, dα, dγ` have moduli `β, |α|, |γ|`, all at most `β`. -/
theorem weight_211_moduli (hβ : 1 < β) (hα : ‖α‖ < 1) (hγ : ‖γ‖ < 1)
    (hd1 : ‖d‖ = 1) :
    ‖d * (β : ℂ)‖ = β ∧ ‖d * α‖ = ‖α‖ ∧ ‖d * γ‖ = ‖γ‖ ∧
      ‖d * (β : ℂ)‖ ≤ β ∧ ‖d * α‖ ≤ β ∧ ‖d * γ‖ ≤ β := by
  have hβ0 : 0 < β := by linarith
  have e1 : ‖d * (β : ℂ)‖ = β := by
    rw [norm_mul, hd1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0, one_mul]
  have e2 : ‖d * α‖ = ‖α‖ := by rw [norm_mul, hd1, one_mul]
  have e3 : ‖d * γ‖ = ‖γ‖ := by rw [norm_mul, hd1, one_mul]
  refine ⟨e1, e2, e3, e1.le, ?_, ?_⟩
  · rw [e2]; linarith
  · rw [e3]; linarith

/-- **Degree three, weight `(1,1,1)`.** `|βαγ| = |d|` and `|d| < β`. -/
theorem weight_111 (hβ : 1 < β) (hα : ‖α‖ < 1) (hγ : ‖γ‖ < 1)
    (hdet : (β : ℂ) * α * γ = d) :
    ‖(β : ℂ) * α * γ‖ = ‖d‖ ∧ ‖d‖ < β := by
  refine ⟨by rw [hdet], ?_⟩
  have hβ0 : 0 < β := by linarith
  rw [norm_d hβ hdet]
  have hag : ‖α‖ * ‖γ‖ < 1 := by
    have := mul_le_mul hα.le hγ.le (norm_nonneg _) zero_le_one
    rcases (norm_nonneg α).lt_or_eq with h | h
    · calc ‖α‖ * ‖γ‖ < ‖α‖ * 1 := mul_lt_mul_of_pos_left hγ h
        _ < 1 := by linarith
    · rw [← h]; norm_num
  calc β * ‖α‖ * ‖γ‖ = β * (‖α‖ * ‖γ‖) := by ring
    _ < β * 1 := mul_lt_mul_of_pos_left hag hβ0
    _ = β := mul_one β

end Moduli

section Galois

/-- **Galois transport of monomial relations.** Let `K` be any `ℚ`-algebra,
`β α γ : K`, `σ` a `ℚ`-algebra endomorphism of `K`, and `q` a rational
polynomial vanishing at `β^a α^b γ^c`.  Then `q` vanishes at
`(σβ)^a (σα)^b (σγ)^c`. -/
theorem aeval_monomial_algHom {K : Type*} [CommRing K] [Algebra ℚ K]
    (σ : K →ₐ[ℚ] K) (β α γ : K) (a b c : ℕ) (q : ℚ[X])
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    aeval (σ β ^ a * σ α ^ b * σ γ ^ c) q = 0 := by
  have : σ (β ^ a * α ^ b * γ ^ c) = σ β ^ a * σ α ^ b * σ γ ^ c := by
    simp [map_mul, map_pow]
  rw [← this, aeval_algHom_apply, hq, map_zero]

/-- **Galois orbit of a monomial relation, for `Gal(f)`.** Let `f : ℚ[X]`,
`β α γ` roots of `f` in its splitting field, and `q` a rational polynomial
vanishing at `β^a α^b γ^c`.  For every `σ ∈ Gal(f)`, the images `σβ, σα, σγ`
are again roots of `f`, and `q` vanishes at `(σβ)^a (σα)^b (σγ)^c`. -/
theorem gal_monomial_relation (f : ℚ[X]) (σ : f.Gal) (β α γ : f.SplittingField)
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (a b c : ℕ) (q : ℚ[X]) (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    aeval (σ β) f = 0 ∧ aeval (σ α) f = 0 ∧ aeval (σ γ) f = 0 ∧
      aeval (σ β ^ a * σ α ^ b * σ γ ^ c) q = 0 := by
  have root : ∀ x : f.SplittingField, aeval x f = 0 → aeval (σ x) f = 0 := by
    intro x hx
    rw [show σ x = σ.toAlgHom x from rfl, aeval_algHom_apply, hx, map_zero]
  exact ⟨root β hβ, root α hα, root γ hγ,
    aeval_monomial_algHom σ.toAlgHom β α γ a b c q hq⟩

end Galois

end Psc.WeightModulus
