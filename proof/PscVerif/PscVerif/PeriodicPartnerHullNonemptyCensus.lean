/-
# Nonempty hulls for PIP3, the census and Tribonacci

Corollaries of `LengthSubst.hull_nonempty` (`PeriodicPartnerHullNonempty`), kept separate so
that the generic theorem does not depend on the 4,554-specimen census.

See `docs/c4-hull-nonempty-2026-11-21.md`.
-/
import PscVerif.PeriodicPartnerHullNonempty
import PscVerif.PeriodicPartnerSpectralCensus
import PscVerif.PeriodicPartnerSpectralModels

namespace Psc.PeriodicPartnerHull

/-! ## The census class -/

open Psc.PeriodicPartnerSpectralCertificate

/-- Every PIP3 length substitution has a nonempty legal hull. -/
theorem PIP3.hull_nonempty {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (h : PIP3 S) : Nonempty S.Hull :=
  S.hull_nonempty h.2.2.2.1

/-- Every member of the 4,554-specimen census underlies a PIP3 length substitution with
derived `PisotData` and a nonempty legal hull. -/
theorem census_hull_nonempty (σ : Fin 3 → List (Fin 3))
    (hlen : ∀ a, 1 ≤ (σ a).length ∧ (σ a).length ≤ 3)
    (hmem : (σ 0, σ 1, σ 2) ∈ Psc.PeriodicPartnerSpectralCensus.corpus) :
    ∃ S : LengthSubst (Fin 3), S.σ = σ ∧ PIP3 S ∧
      Nonempty (Psc.PeriodicPartnerRealization.PisotData S) ∧ Nonempty S.Hull := by
  obtain ⟨S, hσ, hP, hD⟩ := (Psc.PeriodicPartnerSpectralCensus.census σ hlen).2 hmem
  exact ⟨S, hσ, hP, hD, PIP3.hull_nonempty hP⟩

/-- The Tribonacci hull is nonempty. -/
theorem tribonacci_hull_nonempty : Nonempty Psc.PeriodicPartnerSpectralModels.tribonacci.Hull :=
  Psc.PeriodicPartnerSpectralModels.tribonacci.hull_nonempty
    Psc.PeriodicPartnerSpectralModels.one_lt_τ

end Psc.PeriodicPartnerHull
