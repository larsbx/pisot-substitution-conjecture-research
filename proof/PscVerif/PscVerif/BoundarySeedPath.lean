import Mathlib

/-!
Conditional finite algebra for the selected minus boundary seed path.
The rational interval lemma does not assert that the Perron root is rational,
nor prove its field embedding or the actual substitution-word theorem.
-/
namespace PscVerif.BoundarySeedPath

def Inside (a b s : ℚ) : Prop := -b < s ∧ s < a

def move (n d x c y tx tc ty bx bc byy : ℤ) : ℤ × ℤ × ℤ :=
  (2*x+c+y+bx-tx, c+y+bc-tc,
   (n+d)*x+n*c+(n-1)*y+byy-ty)

theorem six_parikh_updates (k t : ℤ) :
    let n := k+3+t
    let d := 2*n-1-k
    move n d 0 0 0 1 0 0 0 1 1 = (-1,1,1) ∧
    move n d (-1) 1 1 0 0 0 1 0 t = (1,2,-3) ∧
    move n d 1 2 (-3) 1 0 (d+1) 0 0 0 = (0,-1,2) ∧
    move n d 0 (-1) 2 1 0 (n-1) 0 0 0 = (0,1,-1) ∧
    move n d 0 1 (-1) 0 1 0 0 0 0 = (0,-1,1) ∧
    move n d 0 (-1) 1 1 0 0 1 0 1 = (0,0,0) := by
  dsimp only []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [move, Prod.mk.injEq] <;> omega

theorem actual_word_bounds (k t : ℤ) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    let n := k+3+t
    let d := 2*n-1-k
    3 ≤ n ∧ 5 ≤ d ∧ 1 ≤ t+1 ∧ t+1 ≤ n-1 ∧
    1 ≤ d+2 ∧ d+2 ≤ n+d ∧ 2 ≤ n-1 ∧ 2 ≤ n+d := by
  dsimp only []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem seven_state_guards (a b u h : ℚ)
    (hh : 0 < h) (hh' : h < 1/2) (hu : 1 < u) (hu' : u < 2)
    (hb : b = 1+h) (ha : a = b+u) :
    Inside a b 0 ∧ Inside 1 1 (1-u) ∧ Inside a 1 (u+3*h) ∧
    Inside 1 a (1-h) ∧ Inside b a h ∧ Inside 1 a (-h) ∧
    Inside 1 1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [Inside] <;> constructor <;> linarith

theorem selected_stage_rank_decreases (i : ℕ) (hi : i < 6) :
    6-(i+1) < 6-i := by omega

end PscVerif.BoundarySeedPath
