import PscVerif.C4ParameterFamilyPisot
import PscVerif.C4ParameterFamilyCarrier
import PscVerif.TerminationFactors

/-!
# Literal family inputs for the published balanced-pair spectral criterion

The endpoints below prove the actual incidence hypotheses and the exact
single-seed full-iterate factor condition. They do not introduce a spectral
axiom or a formal tiling-space conclusion. The external implication is
Barge--Stimac--Williams, Corollary 2, with its standing hypotheses retained.
-/

namespace Psc.ParameterFamilyBridge

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence
open Psc.ParameterFamilyRows (substitution)

/-- Every irreducible factor in every actual iterate belongs to a finite set,
and each such factor has a singleton coincidence in some actual later iterate.
This is the full-factor condition for the one literal seed `01/10`. -/
theorem full_factor_termination (k : Nat) (hk : 2 ≤ k) :
    {U | ∃ n, U ∈ red ((subst (substitution k))^[n] [0, 1])
      ((subst (substitution k))^[n] [1, 0])}.Finite ∧
      ∀ U, (∃ n, U ∈ red ((subst (substitution k))^[n] [0, 1])
        ((subst (substitution k))^[n] [1, 0])) →
        ∃ m a, ([a], [a]) ∈ red ((subst (substitution k))^[m] U.1)
          ((subst (substitution k))^[m] U.2) := by
  exact (Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences
    (seed_isBlock (by decide : (0 : Fin 3) ≠ 1))).1
      (Psc.ParameterFamily.terminates_with_coincidence k hk)

/-- The literal family supplies the primitive incidence, irreducible rational
characteristic polynomial, irrational expanding root, positive left length
vector, contracting other roots, and full-factor termination hypotheses.
No finiteness, root, coincidence or spectral premise is supplied by the caller. -/
theorem spectral_criterion_inputs (k : Nat) (hk : 2 ≤ k) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (substitution k) ^ n) a c) ∧
    Irreducible ((inc (substitution k)).map (Nat.cast : Nat → Rat)).charpoly ∧
    (∃ b : Real, 2 < b ∧ Irrational b ∧
      Polynomial.aeval (b : Complex)
        ((inc (substitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 ∧
      (∀ z : Complex,
        Polynomial.aeval z
          ((inc (substitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 →
        z ≠ b → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → Real, (∀ a, 0 < w a) ∧
        Matrix.vecMul w ((inc (substitution k)).map (Nat.cast : Nat → Real)) = b • w) ∧
    {U | ∃ n, U ∈ red ((subst (substitution k))^[n] [0, 1])
      ((subst (substitution k))^[n] [1, 0])}.Finite ∧
    ∀ U, (∃ n, U ∈ red ((subst (substitution k))^[n] [0, 1])
      ((subst (substitution k))^[n] [1, 0])) →
      ∃ m a, ([a], [a]) ∈ red ((subst (substitution k))^[m] U.1)
        ((subst (substitution k))^[m] U.2) := by
  have hk1 : 1 ≤ k := by omega
  refine ⟨Psc.ParameterFamilyPisot.primitive k hk1,
    Psc.ParameterFamilyPisot.irreducible k hk1, ?_, full_factor_termination k hk⟩
  obtain ⟨b, hb2, hb, hother⟩ := Psc.ParameterFamilyPisot.pisot k hk1
  have hbR : b ^ 3 - (k : Real) * b ^ 2 - 2 * b - 2 = 0 := by
    have h := hb
    rw [Psc.ParameterFamilyPisot.charpoly_eq,
      Psc.ParameterFamilyPisot.aeval_polynomial] at h
    exact_mod_cast h
  exact ⟨b, hb2, Psc.ParameterFamilyPisot.root_irrational k hk1 hbR, hb, hother,
    Psc.ParameterFamilyPisot.positive_left_eigenvector k hb2 hbR⟩

end Psc.ParameterFamilyBridge
