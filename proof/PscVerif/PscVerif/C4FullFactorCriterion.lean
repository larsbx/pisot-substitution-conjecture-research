/-
# One criterion definition: `FullFactorCriterion`

Stage F3 of `docs/c4-family-lean-dynamical-roadmap-2026-11-21.md`: a single structure over
actual substituted words, replacing the unbundled conjunction that
`ParameterFamilyBridge.spectral_criterion_inputs` and `full_factor_termination` carry.

* `FullFactorCriterion s T`: the irreducible factors of all actual iterates of the seed `T`
  form a finite set, and each of them has a singleton coincidence in some later actual iterate.
* `terminates_iff_fullFactorCriterion`: for an irreducible balanced seed this is exactly
  `TerminatesWithCoincidence`; it is a repackaging of
  `TerminationFactors.terminates_iff_finite_factors_and_coincidences`.
* `family_fullFactorCriterion`: the σₖ family at the seed `01/10`, for `k ≥ 2`.
* `spectral_criterion_inputs_bundled`: the family's criterion inputs with the criterion as
  one conjunct.
* `identity_not_fullFactorCriterion`: the `productive` field is not implied by `finite`.

No new mathematics enters; this fixes the interface F4 is to consume.

Source decision: `docs/c4-hull-flow-homeomorphism-stop-go-2026-11-22.md`.
-/
import PscVerif.C4ParameterFamilyBridge

namespace Psc.FullFactorCriterion

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence Psc.StrictSystem
open Psc.ParameterFamilyRows (substitution)

variable {α : Type*} [DecidableEq α]

/-- The full-factor criterion at a seed `T`: finitely many irreducible factors across all
actual iterates, each productive of a singleton coincidence. -/
structure _root_.Psc.FullFactorCriterion (s : α → List α) (T : List α × List α) : Prop where
  finite : {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite
  productive : ∀ U, (∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)) →
    ∃ m a, ([a], [a]) ∈ red ((subst s)^[m] U.1) ((subst s)^[m] U.2)

/-- For an irreducible balanced seed the criterion is termination with coincidence. -/
theorem terminates_iff_fullFactorCriterion [Finite α] {s : α → List α}
    {T : List α × List α} (hT : IsBlock T) :
    TerminatesWithCoincidence s T ↔ Psc.FullFactorCriterion s T :=
  (Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences hT).trans
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.finite, h.productive⟩⟩

/-- The σₖ family satisfies the criterion at `01/10` for every `k ≥ 2`. -/
theorem family_fullFactorCriterion (k : ℕ) (hk : 2 ≤ k) :
    Psc.FullFactorCriterion (substitution k) ([0, 1], [1, 0]) :=
  ⟨(Psc.ParameterFamilyBridge.full_factor_termination k hk).1,
    (Psc.ParameterFamilyBridge.full_factor_termination k hk).2⟩

/-- The family's spectral-criterion inputs, with the full-factor criterion as one conjunct. -/
theorem spectral_criterion_inputs_bundled (k : ℕ) (hk : 2 ≤ k) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (substitution k) ^ n) a c) ∧
    Irreducible ((inc (substitution k)).map (Nat.cast : ℕ → ℚ)).charpoly ∧
    (∃ b : ℝ, 2 < b ∧ Irrational b ∧
      Polynomial.aeval (b : ℂ)
        ((inc (substitution k)).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
      (∀ z : ℂ,
        Polynomial.aeval z
          ((inc (substitution k)).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
        z ≠ b → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
        Matrix.vecMul w ((inc (substitution k)).map (Nat.cast : ℕ → ℝ)) = b • w) ∧
    Psc.FullFactorCriterion (substitution k) ([0, 1], [1, 0]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Psc.ParameterFamilyBridge.spectral_criterion_inputs k hk
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Control: `finite` does not imply `productive`.  The identity substitution has the single
noncoincident factor `01/10`. -/
theorem identity_not_fullFactorCriterion :
    {U | ∃ n, U ∈ red ((subst (fun a : Fin 2 => [a]))^[n] [0, 1])
      ((subst (fun a : Fin 2 => [a]))^[n] [1, 0])}.Finite ∧
    ¬ Psc.FullFactorCriterion (fun a : Fin 2 => [a]) ([0, 1], [1, 0]) := by
  obtain ⟨hfin, hnot⟩ := Psc.TerminationFactors.identity_finite_without_coincidence
  exact ⟨hfin, fun h => hnot ((terminates_iff_fullFactorCriterion
    (seed_isBlock (by decide : (0 : Fin 2) ≠ 1))).2 h)⟩

end Psc.FullFactorCriterion
