/-
Finite part of docs/c4-nmv-eventual-range-2026-11-19.md.
One noninjective endpoint map bounds the cycle rank of a connected eventual
range by two. Equality forces the complete product with side sizes two and
three. The example below checks legal bigrams, the stable image, the incidence
and address, and the common suffixes at all finite levels.
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Infix
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FinCases

namespace Psc.VertexAsymptoteRange

open Function

abbrev Letter := Fin 3
abbrev Word := List Letter
abbrev Seam := Letter × Letter

/-- Every periodic letter of a noninjective three-letter map lies in a set of
size at most two. The sixth-iterate test is checked in PeriodicPartnerSelection. -/
theorem periodic_letters_card_le_two (g : Letter → Letter) (h : ¬ Injective g) :
    (Finset.univ.filter (fun a => g^[6] a = a)).card ≤ 2 := by
  let S := Finset.univ.filter (fun a => g^[6] a = a)
  change S.card ≤ 2
  by_contra! hb
  have hcard : S.card = Fintype.card Letter := by
    have hu := Finset.card_le_univ S
    change S.card ≤ 3 at hu
    change S.card = 3
    omega
  have hall := Finset.eq_univ_of_card S hcard
  have hfix (a : Letter) : g^[6] a = a := by
    have hm : a ∈ S := hall ▸ Finset.mem_univ a
    exact (Finset.mem_filter.mp hm).2
  apply h
  intro a b hab
  have h5 := congrArg (g^[5]) hab
  calc
    a = g^[6] a := (hfix a).symm
    _ = g^[6] b := by simpa only [iterate_succ_apply] using h5
    _ = b := hfix b

private theorem count_with_small_side (m n e : ℕ) (hm : m ≤ 2) (hn : n ≤ 3)
    (hcap : e ≤ m * n) :
    (e : ℤ) - m - n + 1 ≤ 2 ∧
      (2 ≤ (e : ℤ) - m - n + 1 → m = 2 ∧ n = 3 ∧ e = 6) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with hm' | hm' | hm'
  · subst m
    simp only [Nat.zero_mul] at hcap
    omega
  · subst m
    simp only [Nat.one_mul] at hcap
    omega
  · subst m
    simp only [two_mul] at hcap
    omega

/-- The edge excess of a connected simple bipartite graph with sides in
`Fin 3` is at most two when one side has at most two letters. At two, all
six possible edges occur. -/
theorem cycle_rank_bound (L R : Finset Letter) (E : Finset Seam) (hE : E ⊆ L ×ˢ R)
    (hsmall : L.card ≤ 2 ∨ R.card ≤ 2) :
    (E.card : ℤ) - L.card - R.card + 1 ≤ 2 ∧
      (2 ≤ (E.card : ℤ) - L.card - R.card + 1 →
        ((L.card = 2 ∧ R.card = 3) ∨ (L.card = 3 ∧ R.card = 2)) ∧ E = L ×ˢ R) := by
  have hL : L.card ≤ 3 := Finset.card_le_univ L
  have hR : R.card ≤ 3 := Finset.card_le_univ R
  have hcap : E.card ≤ L.card * R.card := Finset.card_product L R ▸ Finset.card_le_card hE
  rcases hsmall with hl | hr
  · obtain ⟨hbound, heq⟩ := count_with_small_side L.card R.card E.card hl hR hcap
    refine ⟨hbound, fun h => ?_⟩
    obtain ⟨h2, h3, h6⟩ := heq h
    exact ⟨Or.inl ⟨h2, h3⟩, Finset.eq_of_subset_of_card_le hE (by
      rw [Finset.card_product, h2, h3, h6])⟩
  · have hcap' : E.card ≤ R.card * L.card := by simpa only [Nat.mul_comm] using hcap
    obtain ⟨hbound, heq⟩ := count_with_small_side R.card L.card E.card hr hL hcap'
    refine ⟨by omega, fun h => ?_⟩
    obtain ⟨h2, h3, h6⟩ := heq (by omega)
    exact ⟨Or.inr ⟨h3, h2⟩, Finset.eq_of_subset_of_card_le hE (by
      rw [Finset.card_product, h2, h3, h6])⟩

/-! ## The substitution 01 / 210 / 1021 -/

def exampleSubst : Letter → Word := ![[0, 1], [2, 1, 0], [1, 0, 2, 1]]

def exampleImage (w : Word) : Word := w.flatMap exampleSubst

def firstLetter : Letter → Letter := ![0, 2, 1]

def lastLetter : Letter → Letter := ![1, 0, 1]

theorem example_endpoints :
    (∀ a, (exampleSubst a).head? = some (firstLetter a)) ∧
    (∀ a, (exampleSubst a).getLast? = some (lastLetter a)) := by
  decide

def seamImage (e : Seam) : Seam := (lastLetter e.1, firstLetter e.2)

def internalBigrams : Finset Seam := {(0, 1), (0, 2), (1, 0), (2, 1)}

theorem example_internal_bigrams (e : Seam) :
    e ∈ internalBigrams ↔ ∃ a : Letter, [e.1, e.2].IsInfix (exampleSubst a) := by
  revert e
  decide

def exampleLegalBigrams : Finset Seam := internalBigrams ∪ internalBigrams.image seamImage

/-- The proposed legal set is closed, and every member is forced by an internal
bigram or its first boundary image. -/
theorem example_legal_bigrams :
    (∀ e ∈ exampleLegalBigrams, seamImage e ∈ exampleLegalBigrams) ∧
      ∀ S : Finset Seam, internalBigrams ⊆ S →
        (∀ e ∈ S, seamImage e ∈ S) → exampleLegalBigrams ⊆ S := by
  refine ⟨by decide, ?_⟩
  intro S hint hclosed e he
  rcases Finset.mem_union.mp he with hi | him
  · exact hint hi
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp him
    exact hclosed p (hint hp)

def exampleRange : Finset Seam := ({0, 1} : Finset Letter) ×ˢ (Finset.univ : Finset Letter)

theorem example_eventual_range :
    exampleLegalBigrams.image seamImage = exampleRange ∧
      exampleRange.image seamImage = exampleRange ∧ exampleRange.card = 6 := by
  decide

def exampleMatrix : Matrix Letter Letter ℤ := ![![1, 1, 1], ![1, 1, 2], ![0, 1, 1]]

theorem example_matrix_counts :
    ∀ i a : Letter, exampleMatrix i a = ((exampleSubst a).count i : ℤ) := by
  intro i a
  fin_cases i <;> fin_cases a <;> decide

theorem example_primitive_square : ∀ i j : Letter, 0 < (exampleMatrix * exampleMatrix) i j := by
  decide

def exampleAddress : Letter → ℤ := ![-1, 0, 1]

/-- The retained 2 is internal and has the same right endpoint as the vertex
ray's initial 0, in integer strand coordinates. -/
theorem example_address :
    exampleSubst 2 = [1, 0] ++ [2] ++ [1] ∧
    exampleMatrix.mulVec exampleAddress - exampleAddress = ![1, 1, 0] ∧
    (fun i => (([1, 0] : Word).count i : ℤ)) = ![1, 1, 0] ∧
    -exampleAddress + (![0, 0, 1] : Letter → ℤ) = ![1, 0, 0] := by
  decide

/-- Each finite inflation has the same suffix after the initial 0 and after
the retained interior 2. Inflation prepends 1 to the substituted suffix. -/
theorem example_common_suffixes (n : ℕ) :
    ∃ p u : Word, exampleImage^[n] [0] = 0 :: u ∧
      exampleImage^[n] [2] = p ++ (2 :: u) := by
  induction n with
  | zero => exact ⟨[], [], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨p, u, h0, h2⟩ := ih
    have w0 : exampleSubst 0 = [0, 1] := by decide
    have w2 : exampleSubst 2 = [1, 0, 2, 1] := by decide
    refine ⟨exampleImage p ++ [1, 0], 1 :: exampleImage u, ?_, ?_⟩
    · rw [iterate_succ_apply', h0]
      simp only [exampleImage, List.flatMap_cons, w0, List.cons_append, List.nil_append]
    · rw [iterate_succ_apply', h2]
      simp only [exampleImage, List.flatMap_append, List.flatMap_cons, w2,
        List.append_assoc, List.cons_append, List.nil_append]

end Psc.VertexAsymptoteRange
