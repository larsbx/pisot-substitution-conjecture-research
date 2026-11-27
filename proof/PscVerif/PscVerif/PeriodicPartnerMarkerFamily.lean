/- Uniform literal marker witnesses with unbounded image lengths. -/
module

public import PscVerif.PeriodicPartnerMarkerParity
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

public section

namespace Psc.PeriodicPartnerMarkerFamily

open Psc.PeriodicPartnerMarkerParity
open Polynomial

abbrev Word := List (Fin 3)

/-- The shared incidence parameter is `t = n + 4`. -/
def sigma (n : ℕ) (a : Fin 3) : Word :=
  if a = 0 then
    ([0, 2, 1, 0] ++ List.replicate (n + 1) 0 ++ List.replicate (n + 3) 1 ++
      List.replicate (n + 3) 2) ++ [0]
  else if a = 1 then
    ([1, 2, 0, 1] ++ List.replicate (n + 1) 1 ++ List.replicate (n + 4) 0 ++
      List.replicate (n + 3) 2) ++ [1]
  else
    ([0, 1] ++ List.replicate (n + 3) 0 ++ List.replicate (n + 3) 1 ++
      List.replicate (n + 4) 2) ++ [1]

def first (a : Fin 3) : Fin 3 := if a = 1 then 1 else 0

def last (a : Fin 3) : Fin 3 := if a = 0 then 0 else 1

def mark (a b : Fin 3) : Bool := last a == 0 && first b == 0

/-- The incidence is `t J + E₀₁ + E₁₂`, with `J` the all-ones matrix. -/
theorem incidence (n : ℕ) (a b : Fin 3) :
    (sigma n b).count a = n + 4 + (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp [sigma, List.count_append, List.count_replicate]

theorem charpoly (n : ℕ) :
    let t : ℤ := (n : ℤ) + 4
    (Matrix.of fun i j : Fin 3 => ((sigma n j).count i : ℤ)).charpoly =
      X ^ 3 - C (3 * t) * X ^ 2 - C (2 * t) * X - C t := by
  let t : ℤ := (n : ℤ) + 4
  have hmat : (Matrix.of fun i j : Fin 3 => ((sigma n j).count i : ℤ)) =
      !![t, t + 1, t; t, t, t + 1; t, t, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [incidence, t]
  rw [hmat, Matrix.charpoly, Matrix.det_fin_three]
  simp [t]
  ring

theorem even_incidence_nilpotent (n : ℕ) :
    (Matrix.of fun i j : Fin 3 => ((sigma (2 * n) j).count i : ZMod 2)) ^ 3 = 0 := by
  have hmat : (Matrix.of fun i j : Fin 3 => ((sigma (2 * n) j).count i : ZMod 2)) =
      !![0, 1, 0; 0, 0, 1; 0, 0, 0] := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hfour : (4 : ZMod 2) = 0 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;> simp [incidence, Nat.cast_add, Nat.cast_mul, htwo, hfour]
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem endpoints (n : ℕ) (a : Fin 3) :
    (sigma n a).head? = some (first a) ∧ (sigma n a).getLast? = some (last a) := by
  fin_cases a <;> constructor
  all_goals first | rfl | (change (_ ++ [_]).getLast? = _; rw [List.getLast?_append]; rfl)

theorem endpoint_maps_idempotent (a : Fin 3) :
    first (first a) = first a ∧ last (last a) = last a := by
  fin_cases a <;> decide

def HasSeam (n : ℕ) (a b : Fin 3) : Prop :=
  ∃ c, ∃ pre post : Word, sigma n c = pre ++ a :: b :: post

/-- All four seams occur in literal images and their endpoints are fixed. -/
theorem periodic_seams (n : ℕ) :
    HasSeam n 0 0 ∧ HasSeam n 0 1 ∧ HasSeam n 1 0 ∧ HasSeam n 1 1 := by
  refine ⟨⟨0, [0, 2, 1], ?_⟩, ⟨2, [], ?_⟩, ⟨2, [0], ?_⟩, ⟨1, [1, 2, 0], ?_⟩⟩ <;>
    exact ⟨_, rfl⟩

/-- The third cut is balanced, its two-sided endpoints are opposite, and
its marker parity is odd while the required parity is even. -/
theorem three_letter_violation (n : ℕ) :
    let u := (sigma n 0).take 3
    let v := (sigma n 1).take 3
    u.Perm v ∧ u.head?.map first = some 0 ∧ v.head?.map first = some 1 ∧
    u.getLast?.map last = some 1 ∧ v.getLast?.map last = some 0 ∧
    (sigma n 0)[3]?.map first = some 0 ∧ (sigma n 1)[3]?.map first = some 1 ∧
    (adjacentCount mark u : ZMod 2) - adjacentCount mark v ≠ 1 + 0 + 1 := by
  change ([0, 2, 1] : Word).Perm [1, 2, 0] ∧ some (first 0) = some 0 ∧
    some (first 1) = some 1 ∧ some (last 1) = some 1 ∧ some (last 0) = some 0 ∧
    some (first 0) = some 0 ∧ some (first 1) = some 1 ∧
    (adjacentCount mark [0, 2, 1] : ZMod 2) - adjacentCount mark [1, 2, 0] ≠ 1 + 0 + 1
  decide

/-- Swapping the two interior letters in the first prefix preserves
its Parikh vector and group tests but removes the violation at this cut. -/
theorem reordered_prefix_control :
    ([0, 1, 2] : Word).Perm [0, 2, 1] ∧ last 2 = last 1 ∧
    (adjacentCount mark [0, 1, 2] : ZMod 2) - adjacentCount mark [1, 2, 0] = 1 + 0 + 1 := by
  decide

end Psc.PeriodicPartnerMarkerFamily
