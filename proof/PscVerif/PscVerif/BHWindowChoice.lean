import Init

/-! Finite selection used by the two-track geometric entry. -/

namespace Psc.BHWindowChoice

/-- Two sets each containing at most one of three slots cannot cover all
three. No geometry or choice of the first track is assumed. -/
theorem exists_clean_slot (F G : Fin 3 → Prop)
    (hF : ∀ i j, F i → F j → i = j)
    (hG : ∀ i j, G i → G j → i = j) :
    ∃ i : Fin 3, ¬F i ∧ ¬G i := by
  classical
  by_cases h : ∃ i : Fin 3, ¬F i ∧ ¬G i
  · exact h
  · have hx (i : Fin 3) : F i ∨ G i := by
      by_cases hfi : F i
      · exact Or.inl hfi
      · exact Or.inr (Classical.byContradiction (fun hgi => h ⟨i, hfi, hgi⟩))
    rcases hx 0 with h0 | h0 <;> rcases hx 1 with h1 | h1 <;> rcases hx 2 with h2 | h2
    all_goals
      first
      | exact False.elim ((by decide : (0 : Fin 3) ≠ 1) (hF 0 1 h0 h1))
      | exact False.elim ((by decide : (0 : Fin 3) ≠ 2) (hF 0 2 h0 h2))
      | exact False.elim ((by decide : (1 : Fin 3) ≠ 2) (hF 1 2 h1 h2))
      | exact False.elim ((by decide : (0 : Fin 3) ≠ 1) (hG 0 1 h0 h1))
      | exact False.elim ((by decide : (0 : Fin 3) ≠ 2) (hG 0 2 h0 h2))
      | exact False.elim ((by decide : (1 : Fin 3) ≠ 2) (hG 1 2 h1 h2))

end Psc.BHWindowChoice
