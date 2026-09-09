import Mathlib
open Matrix in
example : (1 : Matrix (Fin 3) (Fin 3) ℚ).det = 1 := by simp
