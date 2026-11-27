import PscVerif.BHDiagonalConsequences
import PscVerif.BHDiagonalPisot
import PscVerif.BHNearDiagonalPisot

/-!
# Actual arithmetic and literal coincidence on one constructed root

For `r ≥ 12` and `r ≤ k ≤ r+2`, all conclusions refer to the original
substitution `(1, 0 1^k 2, 0^r 1)` and the same constructed real root.
The package retains full integral offsets and original occurrence ordinals.
No root, classification, carrier, entry, descent or coincidence certificate
is supplied as an input. Spectral dynamics is outside this Lean endpoint.
-/

namespace Psc.BHThreeBandClosure

open Matrix Polynomial Psc.Binomial Psc.Incidence
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.ClassAMinusPrefixAssembly
open Psc.BHNearDiagonalLiteral

/-- All fields concern the actual words, actual incidence and one root. -/
structure FamilyClosure (r k : ℕ) (β : ℝ) : Prop where
  lower : (k : ℝ) < β
  upper : β < (k : ℝ)+1
  cubic : β^3 = (k : ℝ)*β^2+2*β+r
  primitive : ∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c
  determinant : (BHNearDiagonalPisot.incidenceQ r k).det = r
  irreducible : Irreducible (BHNearDiagonalPisot.incidenceQ r k).charpoly
  expanding : 1 < β
  root : aeval (β : ℂ) (BHNearDiagonalPisot.incidenceQ r k).charpoly = 0
  contracting : ∀ z : ℂ,
    aeval z (BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 →
    z ≠ (β : ℂ) → ‖z‖ < 1
  positive_lengths : ∀ a, 0 < lengths r β a
  lengths_scale : ∀ a,
    physicalLength (lengths r β) (sigma r k a) = β * lengths r β a
  positive_left_eigenvector : ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
    w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w
  all_source : ∀ p : Packet, p.Interior (lengths r β) →
    ∃ (q : Packet) (xs : List (ℕ × ℕ)),
      OrderedInteriorPath (sigma r k) (lengths r β) p xs q ∧
      q.top = q.bottom ∧ q.delta = 0
  strong_coincidence : ∀ a b,
    Psc.StrictSystem.StrongCoincidenceWitness (sigma r k) a b
  no_strict_system : ∀ C : Finset WordPair,
    ¬ Psc.StrictSystem.StrictSystem (sigma r k) C

/-- Only the three natural parameter bounds are assumptions. -/
theorem family_closure (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, FamilyClosure r k β := by
  obtain ⟨β, hlo, hhi, hcubic, hexit⟩ :=
    BHDiagonalAllSources.three_band_all_source_exit r k hr hklo hkhi
  have hrun : RunFamily r k β := ⟨by omega, hlo, hcubic⟩
  have hirr : Irreducible (BHNearDiagonalPisot.incidenceQ r k).charpoly := by
    by_cases hk : k = r
    · subst k
      exact BHDiagonalPisot.irreducible r hr
    · exact BHNearDiagonalPisot.irreducible r k hr (by omega) hkhi
  have hconj : ∀ z : ℂ,
      aeval z (BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 →
      z ≠ (β : ℂ) → ‖z‖ < 1 := by
    intro z hz hzb
    rw [BHNearDiagonalPisot.charpoly_eq, BHNearDiagonalPisot.aeval_polynomial] at hz
    by_cases hk : k = r
    · subst k
      exact (BHDiagonalPisot.other_root (⟨hr, hlo, hhi, hcubic⟩ :
        BHDiagonalLiteral.Family r β) hz hzb).2.2
    · exact (BHNearDiagonalPisot.other_root (⟨hr, by omega, hkhi, hlo, hhi, hcubic⟩ :
        Family r k β) hz hzb).2.2
  have heigen : ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
      w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w := by
    by_cases hk : k = r
    · subst k
      exact BHDiagonalPisot.positive_left_eigenvector ⟨hr, hlo, hhi, hcubic⟩
    · exact BHNearDiagonalPisot.positive_left_eigenvector
        ⟨hr, by omega, hkhi, hlo, hhi, hcubic⟩
  refine ⟨β, {
    lower := hlo
    upper := hhi
    cubic := hcubic
    primitive := BHNearDiagonalPisot.primitive r k (by omega)
    determinant := BHNearDiagonalPisot.determinant r k
    irreducible := hirr
    expanding := ?_
    root := ?_
    contracting := hconj
    positive_lengths := fun a => zero_lt_one.trans_le (hrun.lengths_ge_one a)
    lengths_scale := BHThirdLevelEntry.run_lengths_scale hrun
    positive_left_eigenvector := heigen
    all_source := ?_
    strong_coincidence := BHDiagonalConsequences.three_band_strong_coincidence r k hr hklo hkhi
    no_strict_system := BHDiagonalConsequences.three_band_no_strict_system r k hr hklo hkhi
  }⟩
  · have hk : (12 : ℝ) ≤ k := by exact_mod_cast (le_trans hr hklo)
    linarith
  · rw [BHNearDiagonalPisot.charpoly_eq, BHNearDiagonalPisot.aeval_polynomial]
    exact_mod_cast (show β^3-(k : ℝ)*β^2-2*β-r = 0 by linarith [hcubic])
  · intro p hp
    obtain ⟨q, hpath, hlabel, hzero⟩ := hexit p hp
    obtain ⟨xs, hordered⟩ := BHThirdLevelEntry.interior_path_ordered
      (sigma r k) (lengths r β) hp hpath
    exact ⟨q, xs, hordered, hlabel, hzero⟩

end Psc.BHThreeBandClosure
