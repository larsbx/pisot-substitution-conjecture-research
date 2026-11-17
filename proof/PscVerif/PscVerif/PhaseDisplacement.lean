import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Cardinality of lattice unit-step supports

The sign changes are inputs. In a literal overlap phase they come from
the centred-displacement argument and the occurrence of every tile label.
-/

namespace Psc.PhaseDisplacement

universe u v

variable {A : Type u} {V : Type v}

def UnitStep (x y : A → ℤ) : Prop :=
  ∃ a, (y a = x a + 1 ∨ y a = x a - 1) ∧ ∀ b ≠ a, y b = x b

private theorem walk_crosses {G : SimpleGraph V} {x y : V} (w : G.Walk x y)
    (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ a b, G.Adj a b ∧ P a ∧ ¬ P b := by
  classical
  induction w with
  | nil => exact (hy hx).elim
  | @cons _ z _ hadj _ ih =>
    by_cases hz : P z
    · exact ih hz hy
    · exact ⟨_, _, hadj, hx, hz⟩

private def threshold (upper : Bool) : ℤ := if upper then 0 else -1

private theorem threshold_injective : Function.Injective threshold := by
  intro a b h
  cases a <;> cases b <;> simp_all [threshold]

private theorem cut_signature {x y : A → ℤ} (c : A × Bool) (h : UnitStep x y)
    (hx : x c.1 ≤ threshold c.2) (hy : ¬ y c.1 ≤ threshold c.2) :
    x c.1 = threshold c.2 ∧ y c.1 = threshold c.2 + 1 ∧ ∀ a ≠ c.1, y a = x a := by
  obtain ⟨a, hstep, hrest⟩ := h
  have ha : c.1 = a := by
    by_contra hne
    exact hy ((hrest c.1 hne).symm ▸ hx)
  rw [← ha] at hstep hrest
  exact ⟨by omega, by omega, hrest⟩

/-- Each of the two sign thresholds in each coordinate needs a different
edge of a spanning tree. This gives the bound before the median argument. -/
theorem card_of_both_signs [Fintype A] [Fintype V] (G : SimpleGraph V) (z : V → A → ℤ)
    (hG : G.Connected) (hunit : ∀ ⦃x y⦄, G.Adj x y → UnitStep (z x) (z y))
    (hsgn : ∀ a, (∃ x, z x a < 0) ∧ (∃ y, 0 < z y a)) :
    2 * Fintype.card A + 1 ≤ Fintype.card V := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have hn (c : A × Bool) : ∃ x y, T.Adj x y ∧
      z x c.1 ≤ threshold c.2 ∧ ¬ z y c.1 ≤ threshold c.2 := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hsgn c.1
    obtain ⟨w⟩ := hT.connected.preconnected x y
    obtain ⟨hmin, hmax⟩ : -1 ≤ threshold c.2 ∧ threshold c.2 ≤ 0 := by
      cases c.2 <;> simp [threshold]
    exact walk_crosses w (fun v => z v c.1 ≤ threshold c.2) (by omega) (by omega)
  choose x y he hlo hhi using hn
  let edge (c : A × Bool) : T.edgeSet := ⟨s(x c, y c), he c⟩
  have hs (c : A × Bool) := cut_signature c (hunit (hTG (he c))) (hlo c) (hhi c)
  have hi : Function.Injective edge := by
    intro c d h
    have hp : s(x c, y c) = s(x d, y d) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hd := hs d
      rw [← hx, ← hy] at hd
      have hc := hs c
      have ha : c.1 = d.1 := by
        by_contra hne
        have heq := hc.2.2 d.1 (Ne.symm hne)
        omega
      exact Prod.ext ha (threshold_injective (by rw [← hc.1, ha, hd.1]))
    · have hd := hs d
      rw [← hx, ← hy] at hd
      have hc := hs c
      have ha : c.1 = d.1 := by
        by_contra hne
        have heq := hc.2.2 d.1 (Ne.symm hne)
        omega
      rw [ha] at hc
      omega
  have hc := Fintype.card_le_of_injective edge hi
  rw [Fintype.card_prod, Fintype.card_bool, T.card_edgeSet] at hc
  rw [Nat.mul_comm, ← hT.card_edgeFinset]
  exact Nat.add_le_add_right hc 1

end Psc.PhaseDisplacement
