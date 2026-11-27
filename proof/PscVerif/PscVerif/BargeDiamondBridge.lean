/-
# Barge–Diamond Theorem 1: the word-level interface

Source: Barge–Diamond, Bull. SMF 130 (2002), 619–626,
DOI 10.24033/bsmf.2433, Theorem 1 p. 620, definitions p. 621,
geometric restatement p. 622. Originally reviewed against PR #608 at
6b175ce350b8691563d8ea254e33bd84445860ef; ported independently to
main ec026774e666fb8e8ac43b1ba975b9a4df8891b2. No rank theorem is changed.

The paper's one-based position k is the zero-based index i = k - 1 here.
`WordConclusion` is an explicitly supplied conclusion of the external theorem,
not an axiom or a proof of its existence. The bridge uses the existing
`IndexWitness`, `WitnessAt`, `EdgeDescendant` and `VertexCoincident` definitions.
It preserves the iterate, the matching label and the positive prefix offset.
No Pisot hypothesis is needed for the correspondence itself.

The PIP3 algebraic adapter checks nonzero roots; primitivity is also bound to
word iteration. It does not formalize the paper's configuration
compactness/existence proof or BBK's geometric coincidence-rank identification.
See docs/barge-diamond-correspondence-2026-11-19.md.
-/
import PscVerif.GeometricFOrientation

namespace Psc.GeometricF.BargeDiamond

open Matrix Polynomial Psc.Binomial Psc.Incidence
open Psc.StrictSystem (IndexWitness WitnessAt)

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The exact coordinate of the descendant at a supplied labelled occurrence.
In particular the prefix is added, not subtracted. -/
theorem edgeDescendant_of_occurrence {s : α → List α} {n : ℕ} {a c : α}
    {P Q : List α} (x : α → ℤ) (h : power s n a = P ++ c :: Q) :
    EdgeDescendant s n (a, x) (c, incZ s ^ n *ᵥ x + pvec P) :=
  ⟨P, Q, h, rfl⟩

/-- At the origin the descendant's lattice coordinate is exactly the prefix
Parikh vector. No stable-space projection or state-coordinate sign occurs. -/
theorem edgeDescendant_origin_iff {s : α → List α} {n : ℕ} {a c : α} {v : α → ℤ} :
    EdgeDescendant s n (a, 0) (c, v) ↔
      ∃ P Q : List α, power s n a = P ++ c :: Q ∧ v = pvec P := by
  simp [EdgeDescendant]

/-- Origin descendants have nonnegative prefix coordinates. -/
theorem edgeDescendant_origin_nonneg {s : α → List α} {n : ℕ} {a c : α} {v : α → ℤ}
    (h : EdgeDescendant s n (a, 0) (c, v)) (b : α) : 0 ≤ v b := by
  obtain ⟨P, Q, _, rfl⟩ := edgeDescendant_origin_iff.mp h
  exact Int.natCast_nonneg _

/-- Zero offset selects the initial letter, not an arbitrary later occurrence. -/
theorem edgeDescendant_origin_zero_iff {s : α → List α} {n : ℕ} {a c : α} :
    EdgeDescendant s n (a, 0) (c, 0) ↔ ∃ Q, power s n a = c :: Q := by
  rw [edgeDescendant_origin_iff]
  constructor
  · rintro ⟨P, Q, hw, hp⟩
    have he : Equiv1 P [] := pvec_eq_iff.mp (by simpa using hp.symm)
    have hP : P = [] := List.length_eq_zero_iff.mp he.length_eq
    exact ⟨Q, by simpa [hP] using hw⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨[], Q, hQ, by simp⟩

/-- Fixed-level word witnesses and shared labelled descendants agree, with the
same n on both tracks. This refines the existing existential edge bridge. -/
theorem witnessAt_iff_shared_descendant {s : α → List α} {a b : α} {n : ℕ} :
    WitnessAt s a b n ↔
      ∃ z : IntegralEdge α, EdgeDescendant s n (a, 0) z ∧
        EdgeDescendant s n (b, 0) z := by
  constructor
  · rintro ⟨P, Q, P', Q', c, ha, hb, he⟩
    refine ⟨(c, pvec P), ⟨P, Q, ha, by simp⟩, P', Q', hb, ?_⟩
    simpa using pvec_eq_iff.mpr he
  · rintro ⟨⟨c, v⟩, ha, hb⟩
    obtain ⟨P, Q, hwa, hva⟩ := edgeDescendant_origin_iff.mp ha
    obtain ⟨P', Q', hwb, hvb⟩ := edgeDescendant_origin_iff.mp hb
    exact ⟨P, Q, P', Q', c, hwa, hwb, pvec_eq_iff.mp (hva.symm.trans hvb)⟩

omit [Fintype α] in
/-- Equal prefix abelianizations force the same index: the repository's two
indices do not weaken the common-position requirement in the paper. -/
theorem witnessAt_iff_aligned_index {s : α → List α} {a b : α} {n : ℕ} :
    WitnessAt s a b n ↔ ∃ i, IndexWitness s a b n i i := by
  constructor
  · intro h
    obtain ⟨i, j, hij⟩ := Psc.StrictSystem.witnessAt_iff_index.mp h
    have he := hij.aligned
    subst j
    exact ⟨i, hij⟩
  · rintro ⟨i, h⟩
    exact Psc.StrictSystem.witnessAt_iff_index.mpr ⟨i, i, h⟩

/-- The common-position version of left coincidence is exactly the predicate
used by PR #608. -/
theorem vertexCoincident_iff_aligned_index {s : α → List α} {a b : α} :
    VertexCoincident s a b ↔ ∃ n i, IndexWitness s a b n i i := by
  rw [vertexCoincident_iff_strongCoincidenceWitness,
    Psc.StrictSystem.strongCoincidenceWitness_iff_exists_witnessAt]
  simp only [witnessAt_iff_aligned_index]

/-- Barge–Diamond 2002 Theorem 1, p. 620: its word-level *conclusion* only.
Supplying this proposition is the external existence import. The theorem is
not asserted by this definition. Indices are zero-based; n is shared. -/
def WordConclusion (s : α → List α) : Prop :=
  ∃ a b, a ≠ b ∧ ∃ n i, IndexWitness s a b n i i

/-- Neither a stronger coincidence convention nor an existence axiom is needed
to translate the published conclusion into the exact hBD premise. -/
theorem wordConclusion_iff_hBD {s : α → List α} :
    WordConclusion s ↔ ∃ a b, a ≠ b ∧ VertexCoincident s a b := by
  simp only [WordConclusion, vertexCoincident_iff_aligned_index]

omit [Fintype α] in
/-- Distinct seed letters cannot coincide at iteration zero. Thus allowing
zero in the existing witness definition adds no distinct-pair import. -/
theorem indexWitness_level_pos {s : α → List α} {a b : α} {n i j : ℕ}
    (hab : a ≠ b) (h : IndexWitness s a b n i j) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  have hi : i = 0 := by simpa using h.1
  have hj : j = 0 := h.aligned.symm.trans hi
  subst i
  subst j
  have he : a = b := by simpa using h.2.1
  exact hab he

/-- Matrix primitivity uses the same iterate and letter convention as word
primitivity in the primary source. -/
theorem primitive_word_iteration {s : α → List α}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    ∃ k ≥ 1, ∀ a b, b ∈ power s k a := by
  obtain ⟨k, hk, hp⟩ := hprim
  refine ⟨k, hk, fun a b => ?_⟩
  apply List.count_pos_iff.mp
  simpa [power, count_iterate_subst] using hp b a

/-- The lower modulus bound in the paper is not lost in PIP3: irreducibility
of a degree-three rational characteristic polynomial excludes zero roots. -/
theorem pip3_complex_root_ne_zero {s : Fin 3 → List (Fin 3)}
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) : z ≠ 0 := by
  intro he
  subst z
  have hq : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.eval 0 ≠ 0 :=
    hirr.not_isRoot_of_natDegree_ne_one (by simp)
  rw [← Psc.BPrime.aeval_charpoly, ← Polynomial.coeff_zero_eq_aeval_zero'] at hz
  have hcoeff : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.coeff 0 = 0 := by
    apply (algebraMap ℚ ℂ).injective
    simpa only [map_zero] using hz
  exact hq (by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hcoeff)

end Psc.GeometricF.BargeDiamond
