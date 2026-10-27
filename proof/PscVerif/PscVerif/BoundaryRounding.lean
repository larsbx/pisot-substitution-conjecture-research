import Mathlib

/-!
Exact integer rounding used by the class-A boundary child star.
These lemmas assume the rational open chambers. They do not prove the
Perron-root bounds, realization, carrier closure, or boundary hitting.
-/
namespace PscVerif.BoundaryRounding

theorem first_run (j r : ℤ) (u : ℚ)
    (hr : (r : ℚ) < u) (hr' : u < (r : ℚ) + 1) :
    (j : ℚ) < 1 + u ↔ j ≤ r + 1 := by
  constructor
  · intro h
    have hq : (j : ℚ) < ((r + 2 : ℤ) : ℚ) := by
      push_cast
      linarith
    have hz : j < r + 2 := by exact_mod_cast hq
    omega
  · intro h
    have hq : (j : ℚ) ≤ (r : ℚ) + 1 := by exact_mod_cast h
    linarith

theorem run_run (m r : ℤ) (u : ℚ)
    (hr : (r : ℚ) < u) (hr' : u < (r : ℚ) + 1) :
    (-1 < (m : ℚ) - u ∧ (m : ℚ) - u < 1) ↔
      (m = r ∨ m = r + 1) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have lo : ((r - 1 : ℤ) : ℚ) < (m : ℚ) := by
      push_cast
      linarith
    have hi : (m : ℚ) < ((r + 2 : ℤ) : ℚ) := by
      push_cast
      linarith
    have lo' : r - 1 < m := by exact_mod_cast lo
    have hi' : m < r + 2 := by exact_mod_cast hi
    omega
  · intro h
    rcases h with h | h
    · subst m
      constructor <;> linarith
    · subst m
      push_cast
      constructor <;> linarith

theorem run_last (n i r s : ℤ) (u b : ℚ)
    (hr : (r : ℚ) < u) (hr' : u < (r : ℚ) + 1)
    (hs : (s : ℚ) < b) (hs' : b < (s : ℚ) + 1) :
    (-(b + u) < (n : ℚ) - (i : ℚ) + 1 - u ∧
      (n : ℚ) - (i : ℚ) + 1 - u < 1) ↔
      (n - r ≤ i ∧ i ≤ n + s + 1) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have lo : ((n - r - 1 : ℤ) : ℚ) < (i : ℚ) := by
      push_cast
      linarith
    have hi : (i : ℚ) < ((n + s + 2 : ℤ) : ℚ) := by
      push_cast
      linarith
    have lo' : n - r - 1 < i := by exact_mod_cast lo
    have hi' : i < n + s + 2 := by exact_mod_cast hi
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    have lo : (n : ℚ) - (r : ℚ) ≤ (i : ℚ) := by exact_mod_cast hlo
    have hi : (i : ℚ) ≤ (n : ℚ) + (s : ℚ) + 1 := by exact_mod_cast hhi
    constructor <;> linarith

end PscVerif.BoundaryRounding
