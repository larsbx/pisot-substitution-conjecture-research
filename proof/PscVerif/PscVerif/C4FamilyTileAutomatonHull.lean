import PscVerif.C4FamilyTileAutomatonWords
import PscVerif.C4ParameterFamilyTiling

/-!
# Actual legal-hull witnesses for the finite tile automaton

Each signed edge is realized by two tiles in an actual legal hull member.
The construction uses the existing seam hull, finite inflation, literal
supertile occurrences, and translation.  Different edges may use different
hull members: this does not make a signed walk one legal substitution word.

Source decision: `docs/c4-finite-hull-witnesses-2026-11-21.md`.
-/

set_option autoImplicit false

namespace Psc.C4FamilyTileAutomatonHull

open Function Set
open Psc.C4FiniteTileAutomaton
open Psc.C4FamilyTileAutomatonWords
open Psc.ParameterFamilyTiling
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerEvenTails

/-- Interpret a formal integer output by the existing tile-length functional. -/
def lengthOutput (S : LengthSubst (Fin 3)) (v : Vector) : ℝ :=
  ∑ i, S.ℓ i * (v i : ℝ)

@[simp] theorem lengthOutput_zero (S : LengthSubst (Fin 3)) :
    lengthOutput S 0 = 0 := by simp [lengthOutput]

@[simp] theorem lengthOutput_add (S : LengthSubst (Fin 3)) (v w : Vector) :
    lengthOutput S (v + w) = lengthOutput S v + lengthOutput S w := by
  simp [lengthOutput, mul_add, Finset.sum_add_distrib]

@[simp] theorem lengthOutput_neg (S : LengthSubst (Fin 3)) (v : Vector) :
    lengthOutput S (-v) = -lengthOutput S v := by
  simp [lengthOutput, Finset.sum_neg_distrib]

@[simp] theorem lengthOutput_basis (S : LengthSubst (Fin 3)) (a : Label) :
    lengthOutput S (basis a) = S.ℓ a := by
  simp [lengthOutput, basis]

/-- A complete finite supertile embeds at its original coordinates in an
actual hull member. Only finite inflation and translation are required. -/
theorem supertile_hull (k : ℕ) (hk : 1 ≤ k) (c : Label) (n : ℕ) :
    ∃ H : (geometry k hk).Hull, (geometry k hk).supertile c n ⊆ H.1 := by
  let S := geometry k hk
  obtain ⟨V, _, hV, _⟩ := fixed_hull_tiling k hk
  obtain ⟨y, hy⟩ := every_letter_in_square k hk c 1
  have hpart : S.supertile 1 2 ⊆ S.inflate^[2] V.1 := by
    simpa only [mul_zero, neg_zero, shift_zero] using S.shifted_supertile_subset_inflate hV 2
  have hc : (c, y) ∈ (inflateH^[2] V).1 := by
    rw [hull_iterate_val]
    exact hpart hy
  let U := translate y (inflateH^[2] V)
  have hcU : (c, 0) ∈ U.1 := by
    change (c, 0 + y) ∈ (inflateH^[2] V).1
    simpa using hc
  refine ⟨inflateH^[n] U, ?_⟩
  rw [hull_iterate_val]
  simpa only [mul_zero, neg_zero, shift_zero] using S.shifted_supertile_subset_inflate hcU n

/-- A literal adjacent occurrence yields both adjacent tiles at any exact
requested placement in some actual legal hull member. -/
theorem occurrence_hull_bridge (k : ℕ) (hk : 1 ≤ k) {n : ℕ} {a b : Label}
    (h : OccursInIterate k n a b) (x : ℝ) :
    ∃ H : (geometry k hk).Hull,
      (a, x) ∈ H.1 ∧ (b, x + (geometry k hk).ℓ a) ∈ H.1 := by
  let S := geometry k hk
  obtain ⟨c, before, after, hw⟩ := h
  have hw' : S.iterWord n c = before ++ [a, b] ++ after := by
    exact hw
  obtain ⟨H, hH⟩ := supertile_hull k hk c n
  let y := (before.map S.ℓ).sum
  have hpair : ∀ q ∈ S.place [a, b] y, q ∈ H.1 := by
    intro q hq
    apply hH
    rw [S.supertile_eq_place, hw']
    simp only [mem_ofPred_eq, place_append, zero_add, List.mem_append]
    exact Or.inl (Or.inr hq)
  have ha : (a, y) ∈ H.1 := hpair _ (by simp [LengthSubst.place])
  have hb : (b, y + S.ℓ a) ∈ H.1 := hpair _ (by simp [LengthSubst.place])
  refine ⟨translate (y - x) H, ?_, ?_⟩
  · change (a, x + (y - x)) ∈ H.1
    simpa only [add_sub_cancel] using ha
  · change (b, x + S.ℓ a + (y - x)) ∈ H.1
    convert hb using 2
    ring

/-- All forward automaton edges carry actual legal-hull witnesses, with
their formal output interpreted by the same tile-length functional. -/
theorem forward_edge_hull_bridge (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    (e : Edge) (he : e.val < 5) (x : ℝ) :
    ∃ H : (geometry k hk).Hull,
      (source e, x) ∈ H.1 ∧
      (target e, x + lengthOutput (geometry k hk) (edgeOutput e)) ∈ H.1 := by
  obtain ⟨n, _, hn⟩ := all_forward_edges_have_literal_witness k hk₂ ⟨e.val, he⟩
  have hn' : OccursInIterate k n (source e) (target e) := hn
  simpa only [edgeOutput, ite_eq_left he, lengthOutput_basis] using
    occurrence_hull_bridge k hk hn' x

/-- Every signed edge has the exact pair of marked tiles in an actual
legal hull. A reversed edge uses the forward pair in reverse order; it
does not require a reversed substitution word to be legal. -/
theorem signed_edge_hull_bridge (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    (e : Edge) (x : ℝ) :
    ∃ H : (geometry k hk).Hull,
      (source e, x) ∈ H.1 ∧
      (target e, x + lengthOutput (geometry k hk) (edgeOutput e)) ∈ H.1 := by
  by_cases he : e.val < 5
  · exact forward_edge_hull_bridge k hk hk₂ e he x
  · have hi : (inverse e).val < 5 := by
      simp only [inverse, dite_eq_right he]
      omega
    obtain ⟨H, hleft, hright⟩ := forward_edge_hull_bridge k hk hk₂ (inverse e) hi
      (x + lengthOutput (geometry k hk) (edgeOutput e))
    refine ⟨H, ?_, ?_⟩
    · simpa only [inverse_target, inverse_output, lengthOutput_neg, add_neg_cancel_right] using hright
    · simpa only [inverse_source] using hleft

end Psc.C4FamilyTileAutomatonHull
