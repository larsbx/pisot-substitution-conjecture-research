import PscVerif.C4ParameterFamilyWords
import PscVerif.C4FiniteTileAutomaton
import Mathlib.Logic.Function.Iterate

/-!
# Literal word witnesses for the finite tile-chain automaton

Every forward edge of `C4FiniteTileAutomaton` occurs in a finite iterate of
the existing literal substitution `ParameterFamilyRows.substitution k`,
uniformly for `k ≥ 2`.  All witnesses have depth at most two.  Reversed
edges traverse one of those literal co-occurrences in the opposite direction;
they are not asserted to be reversed bigrams in the substitution language.

These are exact finite-word statements.  Realization of legal words in the
actual hull, and transfer along chains of those realizations, are separate
interfaces.  See `docs/c4-finite-tile-automaton-2026-11-21.md`.
-/

namespace Psc.C4FamilyTileAutomatonWords

open Psc.ParameterFamilyWords (Word ones)
open Psc.ParameterFamilyRows (substitution subst)
open Psc.C4FiniteTileAutomaton (Label Edge source target)

/-- A literal adjacent occurrence in the `n`-fold substituted singleton. -/
def OccursInIterate (k n : ℕ) (a b : Label) : Prop :=
  ∃ (c : Label) (before after : Word),
    (subst (substitution k))^[n] [c] = before ++ [a, b] ++ after

private theorem subst_singleton (k : ℕ) (a : Label) :
    subst (substitution k) [a] = substitution k a := by
  simp [subst]

private theorem subst_append (k : ℕ) (u v : Word) :
    subst (substitution k) (u ++ v) =
      subst (substitution k) u ++ subst (substitution k) v := by
  simp [subst]

theorem zero_zero (k : ℕ) : OccursInIterate k 1 0 0 := by
  exact ⟨2, [], [1], rfl⟩

theorem zero_one (k : ℕ) : OccursInIterate k 1 0 1 := by
  exact ⟨2, [0], [], rfl⟩

/-- The first two `1`s in the middle image, retaining the whole suffix. -/
theorem split_one_one (k : ℕ) (hk : 2 ≤ k) :
    substitution k 1 = [0] ++ [1, 1] ++ (ones (k - 2) ++ [2]) := by
  have hones : ones k = [1, 1] ++ ones (k - 2) := by
    calc
      ones k = ones (2 + (k - 2)) := by congr 1; omega
      _ = [1, 1] ++ ones (k - 2) := by
        simp only [ones, List.replicate_add]
        rfl
  simp [substitution, hones]

theorem one_one (k : ℕ) (hk : 2 ≤ k) : OccursInIterate k 1 1 1 := by
  refine ⟨1, [0], ones (k - 2) ++ [2], ?_⟩
  change subst (substitution k) [1] = _
  rw [subst_singleton, split_one_one k hk]

/-- The final `1` and `2` in the middle image. -/
theorem one_two (k : ℕ) (hk : 2 ≤ k) : OccursInIterate k 1 1 2 := by
  have hones : ones k = ones (k - 1) ++ [1] := by
    calc
      ones k = ones ((k - 1) + 1) := by congr 1; omega
      _ = ones (k - 1) ++ [1] := by
        simp only [ones, List.replicate_add]
        rfl
  refine ⟨1, [0] ++ ones (k - 1), [], ?_⟩
  change subst (substitution k) [1] = _
  rw [subst_singleton]
  simp [substitution, hones, List.append_assoc]

/-- The image boundary of the first two adjacent `1`s is `20`.
The displayed prefix has length `k + 2`; no parameter scan is used. -/
theorem two_zero (k : ℕ) (hk : 2 ≤ k) : OccursInIterate k 2 2 0 := by
  refine ⟨1, [1, 0] ++ ones k,
    ones k ++ [2] ++ subst (substitution k) (ones (k - 2) ++ [2]), ?_⟩
  change subst (substitution k) (subst (substitution k) [1]) = _
  rw [subst_singleton, split_one_one k hk, subst_append, subst_append]
  simp [subst, substitution, List.append_assoc]

/-- All five forward edge IDs are bound to the actual family words. -/
theorem all_forward_edges_have_literal_witness (k : ℕ) (hk : 2 ≤ k)
    (i : Fin 5) :
    ∃ n ≤ 2, OccursInIterate k n
      (source ⟨i.val, by omega⟩) (target ⟨i.val, by omega⟩) := by
  fin_cases i
  · exact ⟨1, by decide, zero_zero k⟩
  · exact ⟨1, by decide, zero_one k⟩
  · exact ⟨1, by decide, one_one k hk⟩
  · exact ⟨1, by decide, one_two k hk⟩
  · exact ⟨2, by decide, two_zero k hk⟩

/-- A reversed automaton edge uses a legal forward co-occurrence, without
asserting that the reversed word is legal. -/
theorem all_signed_edges_have_literal_witness (k : ℕ) (hk : 2 ≤ k)
    (e : Edge) :
    ∃ n ≤ 2, OccursInIterate k n (source e) (target e) ∨
      OccursInIterate k n (target e) (source e) := by
  fin_cases e
  · exact ⟨1, by decide, Or.inl (zero_zero k)⟩
  · exact ⟨1, by decide, Or.inl (zero_one k)⟩
  · exact ⟨1, by decide, Or.inl (one_one k hk)⟩
  · exact ⟨1, by decide, Or.inl (one_two k hk)⟩
  · exact ⟨2, by decide, Or.inl (two_zero k hk)⟩
  · exact ⟨1, by decide, Or.inr (zero_zero k)⟩
  · exact ⟨1, by decide, Or.inr (zero_one k)⟩
  · exact ⟨1, by decide, Or.inr (one_one k hk)⟩
  · exact ⟨1, by decide, Or.inr (one_two k hk)⟩
  · exact ⟨2, by decide, Or.inr (two_zero k hk)⟩

end Psc.C4FamilyTileAutomatonWords
