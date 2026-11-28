import PscVerif.BetaMetallic
import PscVerif.C4FamilyFixedWord

/-!
# Uniquely represented transcendental numbers from the literal family

For `k ≥ 1`, `m ≥ 4` let `w = fixedWord k` be the fixed word of `σ_k²` from `0`
and `ξ_{k,m} = ∑_{n ≥ 1} (w_n + 1) β_m^{-n}` with `β_m² = m β_m + 1`.

Proved here (the deep input is the hypothesis `ABCorollary1`, never an axiom):

* `xi_isUnique`: the digit stream `w + 1` is the only `{0,…,m}` stream with value
  `ξ_{k,m}` — uniqueness among *all* expansions, not a selected representative;
* `xi_mem`: `β_m⁻¹ < ξ_{k,m} < 1`;
* `renyi_xi`: `w + 1` is the greedy (Rényi) `β_m`-expansion of `ξ_{k,m}`;
* `xi_transcendental`: given Adamczewski–Bugeaud, Corollary 1, `ξ_{k,m}` is
  transcendental.

The word-level inputs are `Psc.ParameterFamilyFixedWord.not_eventuallyPeriodic`
and `frequently_linear`; the shift `a ↦ a + 1` transfers both
(`Psc.WordComplexity.complexity_comp`, `EventuallyPeriodic.of_comp`).
No novelty is claimed for the family, and no PSC claim or status changes.
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.FamilyBetaTranscendence

open Psc.BetaNumeration Psc.BetaMetallic Psc.ParameterFamilyFixedWord Psc.WordComplexity

/-- The shifted coding `a ↦ a + 1`. -/
def code (a : Fin 3) : ℕ := (a : ℕ) + 1

theorem code_injective : Function.Injective code := fun a b h => by
  simp only [code] at h
  exact Fin.ext (by omega)

/-- The digit stream `w_n + 1`. -/
def digits (k : ℕ) : ℕ → ℕ := code ∘ fixedWord k

/-- `ξ_{k,m}`. -/
noncomputable def xi (k m : ℕ) : ℝ := value (beta m) (digits k)

theorem digits_interior (k : ℕ) {m : ℕ} (hm : 4 ≤ m) (n : ℕ) :
    1 ≤ digits k n ∧ digits k n + 1 ≤ m := by
  have := (fixedWord k n).isLt
  simp only [digits, Function.comp_apply, code]
  omega

theorem xi_isUnique (k : ℕ) {m : ℕ} (hm : 4 ≤ m) : IsUnique (beta m) m (digits k) :=
  isUnique_interior (by omega) (digits_interior k hm)

theorem xi_mem (k : ℕ) {m : ℕ} (hm : 4 ≤ m) : (beta m)⁻¹ < xi k m ∧ xi k m < 1 :=
  interior_value_mem (by omega) (digits_interior k hm)

theorem renyi_xi (k : ℕ) {m : ℕ} (hm : 4 ≤ m) : renyiExpansion (beta m) (xi k m) = digits k :=
  interior_renyi (by omega) (digits_interior k hm)

theorem digits_not_eventuallyPeriodic {k : ℕ} (hk : 1 ≤ k) : ¬ EventuallyPeriodic (digits k) :=
  fun h => not_eventuallyPeriodic k hk (EventuallyPeriodic.of_comp code_injective h)

theorem digits_frequently_linear {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℕ, ∀ N, ∃ n, N ≤ n ∧ complexity (digits k) n ≤ C * n := by
  obtain ⟨C, hC⟩ := frequently_linear k hk
  refine ⟨C, fun N => ?_⟩
  obtain ⟨n, hn, hle⟩ := hC N
  exact ⟨n, hn, by rw [digits, complexity_comp code_injective]; exact hle⟩

/-- **Transcendence**, conditional only on Adamczewski–Bugeaud, Corollary 1. -/
theorem xi_transcendental (hAB : ABCorollary1) {k m : ℕ} (hk : 1 ≤ k) (hm : 4 ≤ m) :
    Transcendental ℚ (xi k m) :=
  transcendental_of_greedy hAB (isPisot (by omega)) (m := m)
    (fun n => by have := digits_interior k hm n; omega)
    (fun n => value_lt_one_of_low (by omega)
      (fun j => show digits k (j + n) ≤ m - 1 by have := digits_interior k hm (j + n); omega))
    (digits_not_eventuallyPeriodic hk) (digits_frequently_linear hk)

end Psc.FamilyBetaTranscendence
