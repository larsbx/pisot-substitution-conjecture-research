/-
Integral grouping coefficients for simple cycles in a ternary bipartite
eventual range. These finite statements do not formalize integral cycle
decomposition or the geometric stack quotient. See
docs/c4-even-seam-integrality-2026-11-19.md for that boundary.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

namespace Psc.EvenSeamCycles

open scoped BigOperators

/-- Membership in the chosen grouped cell. `true` names group zero. -/
def corner (row col : Bool) : ℤ := if row && col then 1 else 0

/-- The coefficient in grouped cell `(0,0)` of the alternating cycle
`+(r_i,c_i) -(r_i,c_(i+1))`. The cycle has `2 * (n + 2)` edges.
The other grouped cells are its negative, negative, and itself because
all row and column sums vanish. -/
def squareCoefficient (n : ℕ) (rows cols : Fin (n + 2) → Bool) : ℤ :=
  ∑ i, (corner (rows i) (cols i) - corner (rows i) (cols (i + 1)))

/-- Complete enumeration of the sixteen group assignments on a four-cycle. -/
theorem four_cycle_coefficient :
    ∀ rows cols : Fin 2 → Bool,
      squareCoefficient 0 rows cols = -1 ∨
      squareCoefficient 0 rows cols = 0 ∨
      squareCoefficient 0 rows cols = 1 := by decide

/-- Complete enumeration of the sixty-four group assignments on a six-cycle. -/
theorem six_cycle_coefficient :
    ∀ rows cols : Fin 3 → Bool,
      squareCoefficient 1 rows cols = -1 ∨
      squareCoefficient 1 rows cols = 0 ∨
      squareCoefficient 1 rows cols = 1 := by decide

/-- A nonzero four-cycle image is a generator, up to orientation. -/
theorem four_cycle_nonzero_is_unit (rows cols : Fin 2 → Bool)
    (h : squareCoefficient 0 rows cols ≠ 0) :
    squareCoefficient 0 rows cols = -1 ∨
      squareCoefficient 0 rows cols = 1 := by
  rcases four_cycle_coefficient rows cols with hm | hz | hp
  · exact Or.inl hm
  · exact False.elim (h hz)
  · exact Or.inr hp

/-- A nonzero six-cycle image is a generator, up to orientation. -/
theorem six_cycle_nonzero_is_unit (rows cols : Fin 3 → Bool)
    (h : squareCoefficient 1 rows cols ≠ 0) :
    squareCoefficient 1 rows cols = -1 ∨
      squareCoefficient 1 rows cols = 1 := by
  rcases six_cycle_coefficient rows cols with hm | hz | hp
  · exact Or.inl hm
  · exact False.elim (h hz)
  · exact Or.inr hp

/-- Alternating row and column groups for the eight-edge control. -/
def alternatingFour (i : Fin 4) : Bool := i.val % 2 == 0

/-- Four vertices on each side already allow a twice-wound grouped square. -/
theorem eight_cycle_coefficient_two :
    squareCoefficient 2 alternatingFour alternatingFour = 2 := by decide

/-- Thus the four/six-cycle trichotomy cannot be extended to all eight-cycles. -/
theorem eight_cycle_unit_bound_fails :
    ¬ (squareCoefficient 2 alternatingFour alternatingFour = -1 ∨
       squareCoefficient 2 alternatingFour alternatingFour = 0 ∨
       squareCoefficient 2 alternatingFour alternatingFour = 1) := by decide

end Psc.EvenSeamCycles
