import Std.Tactic

/-!
Universally quantified integer lemmas for the class-B certificate interface.
No Perron sign, carrier membership, descent hypothesis or PSC is supplied
by these theorems. The executable certificate must establish those premises.
-/
namespace PscVerif.ClassBRegime

theorem segment_difference (a b c d z : Int) (hab : a ≤ b) (hcd : c ≤ d) :
    (∃ i j : Int, a ≤ i ∧ i ≤ b ∧ c ≤ j ∧ j ≤ d ∧ j - i = z) ↔
      c - b ≤ z ∧ z ≤ d - a := by
  constructor
  · rintro ⟨i, j, h⟩
    omega
  · intro h
    by_cases ha : a ≤ c - z
    · exact ⟨c - z, c, by omega⟩
    · exact ⟨a, a + z, by omega⟩

theorem plus_partition (g r : Int) (_hg : 16 ≤ g) (hr : 0 ≤ r) (hrg : r < g) :
    (0 ≤ r ∧ r ≤ 1) ∨ (2 ≤ r ∧ r ≤ g - 14) ∨
      (1 ≤ g - r ∧ g - r ≤ 13) := by omega

theorem minus_partition (g r : Int) (_hg : 12 ≤ g) (hr : 0 ≤ r) (hrg : r < g) :
    (0 ≤ r ∧ r ≤ 5) ∨ (6 ≤ r ∧ r ≤ g - 6) ∨
      (1 ≤ g - r ∧ g - r ≤ 5) := by omega

inductive Reach {α : Type} (edge : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Reach edge x x
  | step {x y z : α} : edge x y → Reach edge y z → Reach edge x z

theorem rank_reaches {α : Type} (carrier target : α → Prop)
    (edge : α → α → Prop) (rank : α → Nat)
    (descend : ∀ x, carrier x → ¬target x →
      ∃ y, carrier y ∧ edge x y ∧ rank y < rank x)
    (x : α) (hx : carrier x) : ∃ y, target y ∧ Reach edge x y := by
  have aux : ∀ n, ∀ v, rank v = n → carrier v →
      ∃ y, target y ∧ Reach edge v y := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro v hv hc
      by_cases ht : target v
      · exact ⟨v, ht, .refl v⟩
      · obtain ⟨w, hw, he, hd⟩ := descend v hc ht
        obtain ⟨y, hy, hp⟩ := ih (rank w) (by omega) w rfl hw
        exact ⟨y, hy, .step he hp⟩
  exact aux (rank x) x rfl hx

inductive Steps {α : Type} (edge : α → α → Prop) : Nat → α → α → Prop where
  | refl (x : α) : Steps edge 0 x x
  | step {n : Nat} {x y z : α} : edge x y → Steps edge n y z →
      Steps edge (n + 1) x z

theorem rank_reaches_with_bound {α : Type} (carrier target : α → Prop)
    (edge : α → α → Prop) (rank : α → Nat)
    (descend : ∀ x, carrier x → ¬target x →
      ∃ y, carrier y ∧ edge x y ∧ rank y < rank x)
    (x : α) (hx : carrier x) :
    ∃ y n, target y ∧ Steps edge n x y ∧ n ≤ rank x := by
  have aux : ∀ n, ∀ v, rank v = n → carrier v →
      ∃ y m, target y ∧ Steps edge m v y ∧ m ≤ rank v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro v hv hc
      by_cases ht : target v
      · exact ⟨v, 0, ht, .refl v, Nat.zero_le _⟩
      · obtain ⟨w, hw, he, hd⟩ := descend v hc ht
        obtain ⟨y, m, hy, hp, hm⟩ := ih (rank w) (by omega) w rfl hw
        exact ⟨y, m + 1, hy, .step he hp, by omega⟩
  exact aux (rank x) x rfl hx

end PscVerif.ClassBRegime
