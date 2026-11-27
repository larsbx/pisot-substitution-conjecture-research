import PscVerif.BHPisotFiniteBPA
import PscVerif.BHThreeBandClosure

/-!
# Finite full-factor coincidence for every seed in the three bands

Actual Pisot contraction supplies a finite carrier closed under every
literal strict child. The all-source theorem then supplies labelled exits.
Thus arbitrary irreducible balanced seeds, and in particular every swap
seed on distinct letters, have finite balanced-pair termination with
coincidence. The public parameter-only endpoints have no carrier premise.
The published dynamical implication is not imported as a Lean axiom.
-/

namespace Psc.BHThreeBandBPA

open Psc.Binomial Psc.Reduction Psc.OccurrenceTransport
open Psc.BHNearDiagonalLiteral Psc.BHThreeBandClosure

/-- The assembled arithmetic and actual paths supply both parts of
termination: finite reachability and productivity of every reached factor. -/
theorem terminates_of_family_closure {r k : ℕ} {β : ℝ}
    (h : FamilyClosure r k β) (T : WordPair) (hT : IsBlock T) :
    Psc.StrictSystem.TerminatesWithCoincidence (sigma r k) T := by
  apply BHPisotFiniteBPA.terminates_of_pisot_all_source_exit
    (sigma r k) (lengths r β) β h.positive_lengths (zero_lt_one.trans h.expanding)
    h.lengths_scale h.irreducible h.contracting ?_ T hT
  intro p hp
  obtain ⟨q, xs, hpath, hlabel, hzero⟩ := h.all_source p hp
  exact ⟨q, hpath.interiorPath, hlabel, hzero⟩

/-- Every irreducible balanced seed terminates, from natural parameters
alone. No geometric or finite-carrier certificate is an assumption. -/
theorem all_blocks_terminate (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) (T : WordPair) (hT : IsBlock T) :
    Psc.StrictSystem.TerminatesWithCoincidence (sigma r k) T := by
  obtain ⟨β, h⟩ := family_closure r k hr hklo hkhi
  exact terminates_of_family_closure h T hT

/-- The complete full-iterate condition used by balanced-pair criteria.
Coincidence depth may depend on the actual factor. -/
theorem all_blocks_full_factor_coincidence (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) (T : WordPair) (hT : IsBlock T) :
    {U | ∃ n, U ∈ red ((subst (sigma r k))^[n] T.1)
      ((subst (sigma r k))^[n] T.2)}.Finite ∧
    ∀ U, (∃ n, U ∈ red ((subst (sigma r k))^[n] T.1)
      ((subst (sigma r k))^[n] T.2)) →
      ∃ m a, ([a], [a]) ∈ red ((subst (sigma r k))^[m] U.1)
        ((subst (sigma r k))^[m] U.2) :=
  (Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences hT).mp
    (all_blocks_terminate r k hr hklo hkhi T hT)

/-- In particular every distinct-letter swap seed has full finite
balanced-pair termination with coincidence. -/
theorem all_swap_seeds_terminate (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) (a b : Fin 3) (hab : a ≠ b) :
    Psc.StrictSystem.TerminatesWithCoincidence (sigma r k) ([a,b], [b,a]) :=
  all_blocks_terminate r k hr hklo hkhi _ (Psc.Descendants.seed_isBlock hab)

end Psc.BHThreeBandBPA
