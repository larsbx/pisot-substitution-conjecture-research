/-
# Letter involutions of a unique-partner strict component

`docs/c4-unique-partner-exclusion-2026-11-18.md`, steps 4–5 of Theorem UP.  Under the round-4
vertex-asymptote condition (NM_V), if every tiling has a unique strict partner, the partner map
induces fixed-point-free involutions `λ` on the
left letters `L` and `ρ` on the right letters `R` of the Barge–Diamond eventual-range graph
`E ⊆ L × R`.  Over three letters this forces `|L| = |R| = 2`, hence `β₁(E) ≤ 1`.

**Proved here** (no `sorry`): `card_eq_two_of_involution`, `beta1_le_one`.
**Not proved here:** the tiling-space steps 1–3 that produce `λ` and `ρ`, and (NM_V).
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod

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

end Psc.UniquePartnerLetters
