/-
# Uniform literal witnesses in the even companion family

For `sigma_r = (1, 2, 100 2^r 1)`, prove the actual third-level
word decompositions and equal prefix counts for every `r >= 3`.
This is an unbounded word theorem, not a finite-corpus extrapolation.
The literature decision is `docs/c4-even-companion-family-2026-11-19.md`.
-/
import PscVerif.Binomial
import Mathlib.Tactic.FinCases

namespace Psc.EvenCompanion

open Psc.Binomial

abbrev Word := List (Fin 3)

/-- The only long image. -/
def word (r : ℕ) : Word := [1, 0, 0] ++ List.replicate r 2 ++ [1]

/-- The substitution, with its actual literal image order. -/
def sigma (r : ℕ) (a : Fin 3) : Word :=
  if a = 0 then [1] else if a = 1 then [2] else word r

/-- Repeated blocks, retaining their literal order. -/
def copies (n : ℕ) (w : Word) : Word := (List.replicate n w).flatten

@[simp] theorem copies_zero (w : Word) : copies 0 w = [] := rfl

@[simp] theorem copies_succ (n : ℕ) (w : Word) :
    copies (n + 1) w = w ++ copies n w := by
  simp [copies, List.replicate_succ]

theorem subst_copies (s : Fin 3 → Word) (n : ℕ) (w : Word) :
    subst s (copies n w) = copies n (subst s w) := by
  induction n with
  | zero => simp [subst]
  | succ n ih => simp [subst_append, ih]

/-- The second iterate of the long-image letter. -/
def second (r : ℕ) : Word := [2, 1, 1] ++ copies r (word r) ++ [2]

theorem subst_word (r : ℕ) : subst (sigma r) (word r) = second r := by
  simp [word, second, copies, subst, sigma, List.map_replicate]

theorem subst_second (r : ℕ) :
    subst (sigma r) (second r) =
      word r ++ [2, 2] ++ copies r (second r) ++ word r := by
  change subst (sigma r) ([2, 1, 1] ++ copies r (word r) ++ [2]) = _
  rw [subst_append, subst_append, subst_copies, subst_word]
  simp [subst, sigma, List.append_assoc]

theorem iterate_three_one (r : ℕ) : (subst (sigma r))^[3] [1] = second r := by
  change subst (sigma r) (subst (sigma r) (subst (sigma r) [1])) = _
  have h1 : subst (sigma r) [1] = [2] := by simp [subst, sigma]
  have h2 : subst (sigma r) [2] = word r := by simp [subst, sigma]
  rw [h1, h2, subst_word]

theorem iterate_three_two (r : ℕ) :
    (subst (sigma r))^[3] [2] =
      word r ++ [2, 2] ++ copies r (second r) ++ word r := by
  change subst (sigma r) (subst (sigma r) (subst (sigma r) [2])) = _
  have h : subst (sigma r) [2] = word r := by simp [subst, sigma]
  rw [h, subst_word, subst_second]

/-- Prefix before the matching `2` on the first track. -/
def topPrefix (r : ℕ) : Word := [2, 1, 1] ++ word r ++ [1, 0, 0, 2, 2]

/-- Prefix before the matching `2` on the second track. -/
def bottomPrefix (r : ℕ) : Word := word r ++ [2, 2, 2, 1, 1, 1, 0, 0]

theorem prefixes_balanced (r : ℕ) : Equiv1 (topPrefix r) (bottomPrefix r) := by
  intro a
  fin_cases a <;> simp [topPrefix, bottomPrefix, List.count_append]

theorem prefix_lengths (r : ℕ) :
    (topPrefix r).length = r + 12 ∧ (bottomPrefix r).length = r + 12 := by
  simp [topPrefix, bottomPrefix, word]

theorem prefix_counts (r : ℕ) :
    (topPrefix r).count 0 = 4 ∧ (topPrefix r).count 1 = 5 ∧
      (topPrefix r).count 2 = r + 3 := by
  simp [topPrefix, word, List.count_replicate]

theorem small_prefix (n : ℕ) :
    ([1, 0, 0, 2, 2, 2] : Word) <+: word (n + 3) := by
  refine ⟨List.replicate n 2 ++ [1], ?_⟩
  simp [word, show n + 3 = 3 + n by omega, List.replicate_add]

theorem word_prefix_copies (n : ℕ) (w : Word) : w <+: copies (n + 1) w := by
  rw [copies_succ]
  exact List.prefix_append _ _

theorem top_followed_by_two (n : ℕ) :
    topPrefix (n + 3) ++ [2] <+: second (n + 3) := by
  have hc : word (n + 3) ++ word (n + 3) <+: copies (n + 3) (word (n + 3)) := by
    refine ⟨copies (n + 1) (word (n + 3)), ?_⟩
    simp [show n + 3 = (n + 1) + 1 + 1 by omega, List.append_assoc]
  have hs := small_prefix n
  obtain ⟨t, ht⟩ := hs
  obtain ⟨u, hu⟩ := hc
  refine ⟨t ++ u ++ [2], ?_⟩
  simp only [topPrefix, second, List.append_assoc, List.cons_append,
    List.nil_append]
  rw [← hu]
  simp only [List.append_assoc]
  rw [← ht]
  simp

theorem bottom_followed_by_two (n : ℕ) :
    bottomPrefix (n + 3) ++ [2] <+:
      word (n + 3) ++ [2, 2] ++ copies (n + 3) (second (n + 3)) ++ word (n + 3) := by
  have hs := small_prefix n
  have hw := word_prefix_copies (n + 2) (word (n + 3))
  have hv := word_prefix_copies (n + 2) (second (n + 3))
  obtain ⟨t, ht⟩ := hs
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hv
  refine ⟨[2, 2] ++ t ++ u ++ [2] ++ v ++ word (n + 3), ?_⟩
  unfold bottomPrefix
  rw [← hv]
  unfold second
  rw [← hu, ← ht]
  simp [List.append_assoc]

/-- An exact uniform level-three witness: both displayed prefixes are followed
by tile `2` in the literal iterates and have identical Parikh vectors. -/
theorem level_three_witness (r : ℕ) (hr : 3 ≤ r) :
    ∃ u v : Word,
      (subst (sigma r))^[3] [1] = topPrefix r ++ 2 :: u ∧
      (subst (sigma r))^[3] [2] = bottomPrefix r ++ 2 :: v ∧
      Equiv1 (topPrefix r) (bottomPrefix r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 3 := ⟨r - 3, by omega⟩
  obtain ⟨u, hu⟩ := top_followed_by_two n
  obtain ⟨v, hv⟩ := bottom_followed_by_two n
  refine ⟨u, v, ?_, ?_, prefixes_balanced _⟩
  · simpa only [iterate_three_one, List.append_assoc, List.cons_append,
      List.nil_append] using hu.symm
  · simpa only [iterate_three_two, List.append_assoc, List.cons_append,
      List.nil_append] using hv.symm

end Psc.EvenCompanion
