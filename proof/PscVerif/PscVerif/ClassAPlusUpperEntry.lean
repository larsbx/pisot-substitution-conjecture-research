/-
# Upper plus-Class-A entry inequalities

The arithmetic case split for the original LAST/FIRST boundary, adjacent
RUN occurrences and strict RUN/RUN range. The final lemma isolates the
finite growth argument from literal occurrence transport.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Psc.ClassAPlusUpperEntry

def length (X K : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then X else if a = 1 then K else 1

def first (a : Fin 3) : Fin 3 := if a = 1 then 1 else 0

def last (a : Fin 3) : Fin 3 := if a = 2 then 1 else 0

noncomputable def threshold (β X K : ℝ) (a b : Fin 3) : ℝ :=
  (length X K (last a) + length X K (first b) + 1/2) / β

theorem threshold_lt (β X K : ℝ) (hβ : 11 < β) (hX : X < 10/3) (hK : K < 1)
    (a b : Fin 3) : threshold β X K a b < 2/3 := by
  unfold threshold
  apply (div_lt_iff₀ (by linarith : 0 < β)).2
  have hfirst : length X K (first b) < 10/3 := by
    unfold first
    split <;> simp [length] <;> linarith
  have hlast : length X K (last a) < 10/3 := by
    unfold last
    split <;> simp [length] <;> linarith
  linarith

theorem y_threshold_lt (β X K : ℝ) (hβ : 11 < β) (hX : X < 10/3) (hK : K < 1)
    (b : Fin 3) : threshold β X K 2 b < 1/2 := by
  unfold threshold
  apply (div_lt_iff₀ (by linarith : 0 < β)).2
  have hfirst : length X K (first b) < 10/3 := by
    unfold first
    split <;> simp [length] <;> linarith
  have hlast : length X K (last 2) = K := by simp [last, length]
  linarith

theorem threshold_sum (β X K : ℝ)
    (hβ : 11 < β) (hXlo : 2 < X) (hXhi : X < 10/3)
    (hKlo : 10/11 < K) (hKhi : K < 1) (a b : Fin 3) :
    threshold β X K (first b) (last a) + threshold β X K 2 (first b) <
      length X K (first b) := by
  have h₁ := threshold_lt β X K hβ hXhi hKhi (first b) (last a)
  have h₂ := threshold_lt β X K hβ hXhi hKhi 2 (first b)
  have hc : threshold β X K 2 1 < 5/22 := by
    unfold threshold
    apply (div_lt_iff₀ (by linarith : 0 < β)).2
    simp [first, last, length]
    linarith
  by_cases hb : b = 1
  · simp [first, hb, length] at h₁ ⊢
    linarith
  · simp [first, hb, length] at h₁ h₂ ⊢
    linarith

/-- The exact range of first-RUN displacement where a nearest integer is
realizable by ordered RUN positions. -/
theorem direct_gap_window {β u Ftop Fbottom G D : ℝ} {Rtop Rbottom : ℕ}
    (hu : 0 ≤ u) (hβ : 0 ≤ β) (hFtop : Ftop < 10/3) (hFbottom : 0 < Fbottom)
    (hRbottom : 7 ≤ Rbottom)
    (hD : β*u + Fbottom - Ftop = Rtop + (G+Fbottom) - D)
    (hdirect : G+Fbottom+1/2 < D) :
    1/2-(Rbottom : ℝ) < β*u+Fbottom-Ftop ∧
      β*u+Fbottom-Ftop < (Rtop : ℝ)-1/2 := by
  have hprod := mul_nonneg hβ hu
  have hn : (7 : ℝ) ≤ Rbottom := by exact_mod_cast hRbottom
  constructor <;> linarith

/-- With half ties excluded, the gap window gives two actual RUN ordinals. -/
theorem ordered_run_indices (s : ℝ) (Rtop Rbottom : ℕ)
    (htop : 1 ≤ Rtop) (hbottom : 1 ≤ Rbottom)
    (hlo : 1/2-(Rbottom : ℝ) < s) (hhi : s < (Rtop : ℝ)-1/2)
    (hnoTie : ∀ z : ℤ, s ≠ (z : ℝ)+1/2) :
    ∃ i j : ℕ, 1 ≤ i ∧ i ≤ Rtop ∧ 1 ≤ j ∧ j ≤ Rbottom ∧
      |s+(j : ℝ)-(i : ℝ)| < 1/2 := by
  let e : ℤ := ⌊s+1/2⌋
  have he_le : (e : ℝ) ≤ s+1/2 := Int.floor_le _
  have he_hi : s+1/2 < (e : ℝ)+1 := Int.lt_floor_add_one _
  have he_lo : (e : ℝ) < s+1/2 := by
    refine lt_of_le_of_ne he_le ?_
    intro ht
    apply hnoTie (e-1)
    simp only [Int.cast_sub, Int.cast_one]
    linarith
  have hetopR : (e : ℝ) < Rtop := by linarith
  have hebottomR : -(Rbottom : ℝ) < e := by linarith
  have hetop : e < (Rtop : ℤ) := by exact_mod_cast hetopR
  have hebottom : -(Rbottom : ℤ) < e := by exact_mod_cast hebottomR
  by_cases hs : 0 ≤ e
  · have he_nat : (e.toNat : ℤ) = e := Int.toNat_of_nonneg hs
    have he_real : (e.toNat : ℝ) = (e : ℝ) := by exact_mod_cast he_nat
    refine ⟨e.toNat+1, 1, by omega, by omega, by omega, hbottom, ?_⟩
    rw [abs_lt]
    simp only [Nat.cast_add, Nat.cast_one, he_real]
    exact ⟨by linarith, by linarith⟩
  · have he_nat : ((-e).toNat : ℤ) = -e := Int.toNat_of_nonneg (by omega)
    have he_real : ((-e).toNat : ℝ) = -(e : ℝ) := by exact_mod_cast he_nat
    refine ⟨1, (-e).toNat+1, by omega, htop, by omega, by omega, ?_⟩
    rw [abs_lt]
    simp only [Nat.cast_add, Nat.cast_one, he_real]
    exact ⟨by linarith, by linarith⟩

/-- The arithmetic of the boundary table. Each non-growth branch carries
the strict sign bounds and the positive margin for immediate RUN entry. -/
theorem boundary_cases (β X K D : ℝ)
    (hβ : 11 < β) (hXlo : 2 < X) (hXhi : X < 10/3)
    (hKlo : 10/11 < K) (hKhi : K < 1)
    (a b : Fin 3) (hD : 0 < D)
    (hwall : D ≤ length X K (last a) + length X K (first b) + 1/2) :
    let A := last a
    let B := first b
    let G := length X K A
    let F := length X K B
    let E := G + F
    (0 ≤ G-D ∧ G-D < G ∧ G-(G-D) = D) ∨
    (-F < G-D ∧ G-D < 0 ∧ threshold β X K B A < E-D) ∨
    (0 ≤ G+1-D ∧ G+1-D < 1 ∧ threshold β X K 2 B < D-G) ∨
    (-F < G+1-D ∧ G+1-D < 0 ∧ threshold β X K B 2 < E+1-D) ∨
    (-(1 : ℝ) < E-D ∧ E-D ≤ 0 ∧ threshold β X K 2 A < 1+(E-D)) := by
  dsimp only
  set A := last a
  set B := first b
  set G := length X K A
  set F := length X K B
  set E := G+F
  by_cases hg : D ≤ G
  · exact Or.inl ⟨by linarith, by linarith, by ring⟩
  by_cases he : E ≤ D
  · have ht := y_threshold_lt β X K hβ hXhi hKhi A
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)))
  by_cases ht : threshold β X K B A < E-D
  · exact Or.inr (Or.inl ⟨by linarith [show E = G+F from rfl], by linarith, ht⟩)
  by_cases hmiddle : D ≤ G+1
  · have hsum := threshold_sum β X K hβ hXlo hXhi hKlo hKhi a b
    change threshold β X K B A + threshold β X K 2 B < F at hsum
    exact Or.inr (Or.inr (Or.inl
      ⟨by linarith, by linarith, by linarith [show E = G+F from rfl]⟩))
  · have hlast := threshold_lt β X K hβ hXhi hKhi B 2
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by linarith [show E = G+F from rfl], by linarith, by linarith⟩)))

inductive Steps {α : Type} (edge : α → α → Prop) : ℕ → α → α → Prop
  | nil (source : α) : Steps edge 0 source source
  | cons {k : ℕ} {source middle target : α} :
      edge source middle → Steps edge k middle target →
      Steps edge (k+1) source target

/-- If the literal boundary alternative scales the same positive margin
and all other alternatives exit within two moves, the growth cannot
repeat past the first power of the inflation reaching the uniform wall. -/
theorem bounded_entry_of_growth {α : Type} (edge : α → α → Prop)
    (ready : α → Prop) (margin : α → ℝ) (β : ℝ)
    (next : ∀ source, 0 < margin source →
      (∃ j target, j ≤ 2 ∧ Steps edge j source target ∧ ready target) ∨
      ∃ child, edge source child ∧ 0 < margin child ∧ margin child = β*margin source)
    (hwall : ∀ source, margin source < 4) (k : ℕ) (source : α)
    (hpos : 0 < margin source) (hk : 4 ≤ β^k*margin source) :
    ∃ j target, j ≤ k+1 ∧ Steps edge j source target ∧ ready target := by
  induction k generalizing source with
  | zero =>
    simp at hk
    exact (not_le_of_gt (hwall source) hk).elim
  | succ k ih =>
    rcases next source hpos with ⟨j, target, hj, hp, hr⟩ | ⟨child, hc, hchild, hchange⟩
    · exact ⟨j, target, by omega, hp, hr⟩
    · have hk' : 4 ≤ β^k * margin child := by
        rw [hchange, ← mul_assoc, ← pow_succ]
        exact hk
      obtain ⟨j, target, hj, hp, hr⟩ := ih child hchild hk'
      exact ⟨j+1, target, by omega, .cons hc hp, hr⟩

theorem exists_entry_power (β m : ℝ) (hβ : 1 < β) (hm : 0 < m) :
    ∃ k : ℕ, 4 ≤ β^k*m := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4/m) hβ
  exact ⟨k, ((div_lt_iff₀ hm).1 hk).le⟩

end Psc.ClassAPlusUpperEntry
