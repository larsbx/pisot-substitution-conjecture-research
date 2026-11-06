/-
# Theorem A(ii): the `(2,2,0)` sector is empty for every PIP

`docs/c4-concentration-attack-2026-11-06.md` §2.  In the complex unimodular
case, Wielandt's theorem applied to the eigenvalue `β²α²` yields
`(βα²)^{2ℓ} = 1` along a directed cycle of length `ℓ`; that step is
`PscVerif.Wielandt.cycle_relation`, and the end-to-end exclusion is
`PscVerif.Wielandt.no_220_eigenvalue`.  This module proves the algebraic tail:

* `pow_eq_conj_pow_of_cycle`: if `βαᾱ = d` with `d² = 1` and
  `(βα²)^{2ℓ} = 1`, then `α^{2ℓ} = ᾱ^{2ℓ}`;
* `root_pow_eq_of_pow_eq_conj_pow`: if `α` is a non-real root of an irreducible
  rational cubic and `αⁿ = ᾱⁿ`, then every root `ρ` satisfies `ρⁿ = αⁿ`.
  (`αⁿ` is real, so `ℚ(αⁿ) ≠ ℚ(α)`; the degree divides 3, so `αⁿ ∈ ℚ` and the
  minimal polynomial divides `Xⁿ - αⁿ`.)
* `no_220_sector`: hence a PIP-type configuration (a root `β` with `|β| > 1`
  and a non-real root `α` with `|α| < 1`) admits no such cycle relation.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Analysis.Complex.Basic

namespace Psc.Degree4Sector

open Polynomial IntermediateField

theorem pow_eq_conj_pow_of_cycle (β α d : ℂ) (hα : α ≠ 0) (hconj : (starRingEnd ℂ) α ≠ 0)
    (hdet : β * α * (starRingEnd ℂ) α = d) (hd : d ^ 2 = 1) (ℓ : ℕ)
    (hcyc : (β * α ^ 2) ^ (2 * ℓ) = 1) :
    α ^ (2 * ℓ) = ((starRingEnd ℂ) α) ^ (2 * ℓ) := by
  set γ := (starRingEnd ℂ) α
  have hβ : β * α ^ 2 = d * α / γ := by
    rw [← hdet]; field_simp
  rw [hβ, div_pow, mul_pow, pow_mul d, hd, one_pow, one_mul] at hcyc
  have hγ : γ ^ (2 * ℓ) ≠ 0 := pow_ne_zero _ hconj
  exact (div_eq_one_iff_eq hγ).mp hcyc

theorem root_pow_eq_of_pow_eq_conj_pow (f : ℚ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 3)
    (α : ℂ) (hα : aeval α f = 0) (hnr : α.im ≠ 0) (n : ℕ)
    (h : α ^ n = ((starRingEnd ℂ) α) ^ n) (ρ : ℂ) (hρ : aeval ρ f = 0) : ρ ^ n = α ^ n := by
  have hint : IsIntegral ℚ α := (isAlgebraic_iff_isIntegral).mp ⟨f, hf.ne_zero, hα⟩
  have hmin : f * C f.leadingCoeff⁻¹ = minpoly ℚ α := minpoly.eq_of_irreducible hf hα
  have hlc : f.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hf.ne_zero)
  have hdegmin : (minpoly ℚ α).natDegree = 3 := by
    rw [← hmin, natDegree_mul_C hlc, hdeg]
  set x := α ^ n with hxdef
  have hxreal : (starRingEnd ℂ) x = x := by rw [hxdef, map_pow, ← h]
  have hxQ : x ∈ (⊥ : IntermediateField ℚ ℂ) := by
    by_contra hx
    have hle : ℚ⟮x⟯ ≤ ℚ⟮α⟯ :=
      adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self ℚ α) n)
    have : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hint
    have h3 : Module.finrank ℚ ℚ⟮α⟯ = 3 := by rw [adjoin.finrank hint, hdegmin]
    have hdvd := finrank_dvd_of_le_right hle
    rw [h3] at hdvd
    have hne1 : Module.finrank ℚ ℚ⟮x⟯ ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff]; exact hx
    have h3' : Module.finrank ℚ ℚ⟮x⟯ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact absurd h1 hne1
      · exact h1
    have heq : ℚ⟮x⟯ = ℚ⟮α⟯ := eq_of_le_of_finrank_eq hle (by rw [h3', h3])
    have hαx : α ∈ ℚ⟮x⟯ := heq ▸ mem_adjoin_simple_self ℚ α
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff ℚ α).mp hαx
    have hconj : ∀ p : ℚ[X], (starRingEnd ℂ) (aeval x p) = aeval x p := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial k a => simp [aeval_monomial, map_mul, map_pow, hxreal]
    have hfix : (starRingEnd ℂ) α = α := by rw [hrs, map_div₀, hconj, hconj]
    exact hnr (Complex.conj_eq_iff_im.mp hfix)
  obtain ⟨q, hq⟩ := (mem_bot).mp hxQ
  have hαroot : aeval α (X ^ n - C q) = 0 := by
    simp [hq, hxdef]
  obtain ⟨g, hg⟩ := minpoly.dvd ℚ α hαroot
  have hρmin : aeval ρ (minpoly ℚ α) = 0 := by rw [← hmin]; simp [aeval_mul, hρ]
  have : aeval ρ (X ^ n - C q) = 0 := by rw [hg, aeval_mul, hρmin, zero_mul]
  simp only [map_sub, map_pow, aeval_X, aeval_C] at this
  rw [sub_eq_zero] at this
  rw [this, hq]

/-- **No `(2,2,0)` cycle relation in a PIP-type cubic.**  If `f` is an
irreducible rational cubic with a root `β`, `|β| > 1`, and a non-real root
`α`, `|α| < 1`, then `α^m ≠ ᾱ^m` for every `m ≥ 1`. -/
theorem no_220_sector (f : ℚ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 3)
    (β α : ℂ) (hβ : aeval β f = 0) (hα : aeval α f = 0) (hnr : α.im ≠ 0)
    (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (m : ℕ) (hm : 0 < m) :
    α ^ m ≠ ((starRingEnd ℂ) α) ^ m := by
  intro h
  have := root_pow_eq_of_pow_eq_conj_pow f hf hdeg α hα hnr m h β hβ
  have hn := congrArg (‖·‖) this
  simp only [norm_pow] at hn
  have h1 : 1 < ‖β‖ ^ m := one_lt_pow₀ hβ1 hm.ne'
  have h2 : ‖α‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) hα1 hm.ne'
  linarith

end Psc.Degree4Sector
