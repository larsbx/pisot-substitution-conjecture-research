/-
# Letter involutions of a unique-partner strict component

`docs/c4-unique-partner-exclusion-2026-11-18.md`, steps 4–5 of Theorem UP.  Under the round-4
vertex-asymptote condition (NM_V), if every tiling has a unique strict partner, the partner map
induces fixed-point-free involutions `λ` on the
left letters `L` and `ρ` on the right letters `R` of the Barge–Diamond eventual-range graph
`E ⊆ L × R`.  Over three letters this forces `|L| = |R| = 2`, hence `β₁(E) ≤ 1`.

**Proved here** (no `sorry`): `card_eq_two_of_involution`, `beta1_le_one`, and for Theorem UP′
`regular_cases` (an `n`-regular simple graph, `n ≥ 1`, on at most three letters has `n = 1` and
two letters, or `n = 2` and three).
**Not proved here:** the tiling-space steps 1–3 that produce `λ` and `ρ`, and (NM_V).
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Psc.UniquePartnerLetters

/-- `f` restricts to a fixed-point-free involution of `L`. -/
def FreeInvolutionOn (L : Finset (Fin 3)) (f : Fin 3 → Fin 3) : Prop :=
  ∀ x ∈ L, f x ∈ L ∧ f x ≠ x ∧ f (f x) = x

instance (L : Finset (Fin 3)) (f : Fin 3 → Fin 3) : Decidable (FreeInvolutionOn L f) := by
  unfold FreeInvolutionOn; infer_instance

/-- **A nonempty set of at most three letters with a fixed-point-free involution has two
elements.** -/
theorem card_eq_two_of_involution :
    ∀ (L : Finset (Fin 3)) (f : Fin 3 → Fin 3), L ≠ ∅ → FreeInvolutionOn L f →
      L.card = 2 := by
  decide

/-- **`β₁ ≤ 1`** for an edge set whose left and right letter sets carry fixed-point-free
involutions. -/
theorem beta1_le_one (E : Finset (Fin 3 × Fin 3)) (hE : E.Nonempty) (lam rho : Fin 3 → Fin 3)
    (hl : FreeInvolutionOn (E.image Prod.fst) lam)
    (hr : FreeInvolutionOn (E.image Prod.snd) rho) :
    (E.card : ℤ) - (E.image Prod.fst).card - (E.image Prod.snd).card + 1 ≤ 1 := by
  have hL := card_eq_two_of_involution _ lam (hE.image _).ne_empty hl
  have hR := card_eq_two_of_involution _ rho (hE.image _).ne_empty hr
  have hsub : E ⊆ (E.image Prod.fst) ×ˢ (E.image Prod.snd) := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, hL, hR] at hcard
  rw [hL, hR]
  omega

/-! ### Coverings: regular letter relations (Theorem UP′) -/

/-- `nbr` is an `n`-regular simple graph on `L`: symmetric, loopless, every vertex of degree `n`. -/
def RegularOn (L : Finset (Fin 3)) (nbr : Fin 3 → Finset (Fin 3)) (n : ℕ) : Prop :=
  ∀ x ∈ L, nbr x ⊆ L ∧ x ∉ nbr x ∧ (nbr x).card = n ∧ ∀ y ∈ nbr x, x ∈ nbr y

instance (L : Finset (Fin 3)) (nbr : Fin 3 → Finset (Fin 3)) (n : ℕ) :
    Decidable (RegularOn L nbr n) := by
  unfold RegularOn; infer_instance

/-- Three letters carry no perfect matching. -/
theorem no_matching_on_three :
    ∀ nbr : Fin 3 → Finset (Fin 3), ¬ RegularOn Finset.univ nbr 1 := by
  intro nbr h
  obtain ⟨-, h0, c0, s0⟩ := h 0 (Finset.mem_univ _)
  obtain ⟨-, h1, c1, s1⟩ := h 1 (Finset.mem_univ _)
  obtain ⟨-, h2, c2, s2⟩ := h 2 (Finset.mem_univ _)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 c0
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 c1
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 c2
  have key : ∀ y, nbr y = {![a, b, c] y} := by
    intro y; fin_cases y <;> simp [ha, hb, hc]
  have e0 := s0 a (by simp [ha])
  have e1 := s1 b (by simp [hb])
  have e2 := s2 c (by simp [hc])
  rw [key] at h0 h1 h2 e0 e1 e2
  simp only [Finset.mem_singleton] at h0 h1 h2 e0 e1 e2
  clear key ha hb hc s0 s1 s2 c0 c1 c2 h
  revert h0 h1 h2 e0 e1 e2
  revert a b c
  decide

/-- **An `n`-regular simple graph with `n ≥ 1` on at most three letters** is a perfect matching
on two letters (`n = 1`) or the triangle (`n = 2`). -/
theorem regular_cases (L : Finset (Fin 3)) (nbr : Fin 3 → Finset (Fin 3)) (n : ℕ) (hL : L ≠ ∅)
    (hn : 1 ≤ n) (h : RegularOn L nbr n) : (n = 1 ∧ L.card = 2) ∨ (n = 2 ∧ L.card = 3) := by
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hL
  obtain ⟨hsub, hnot, hcard, -⟩ := h x hx
  have hle : n + 1 ≤ L.card := by
    rw [← hcard]
    exact Finset.card_lt_card ⟨hsub, fun hL' => hnot (hL' hx)⟩
  have h3 : L.card ≤ 3 := by simpa using Finset.card_le_univ L
  rcases (show L.card = 2 ∨ L.card = 3 by omega) with h2 | h3'
  · left; omega
  · right
    refine ⟨?_, h3'⟩
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | h2
    · exfalso
      have hu : L = Finset.univ := Finset.eq_univ_of_card L (by simpa using h3')
      exact no_matching_on_three nbr (hu ▸ h)
    · exact h2

end Psc.UniquePartnerLetters
