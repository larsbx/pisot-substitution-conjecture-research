/-! Word identities used by the ordered parameter-family carrier. -/

namespace Psc.ParameterFamilyWords
abbrev Word := List (Fin 3)
def ones (n : Nat) : Word := List.replicate n 1
def image (n : Nat) : Word := [0] ++ ones (n + 2) ++ [2]

theorem rotate_repeat {α : Type} (x y : List α) (m : Nat) :
    (List.replicate m (x ++ y)).flatten ++ x =
      x ++ (List.replicate m (y ++ x)).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc] at *
    rw [ih]

theorem long_track (n m : Nat) :
    (List.replicate m (ones n ++ [1, 1, 2, 0])).flatten ++ (ones n ++ [1, 1, 2]) =
      (ones (n + 2) ++ [2]) ++ (List.replicate m (image n)).flatten := by
  have hx : ones (n + 2) ++ [2] = ones n ++ [1, 1, 2] := by
    unfold ones
    rw [← List.replicate_append_replicate (n := n) (m := 2), List.append_assoc]
    rfl
  have hxy : (ones (n + 2) ++ [2]) ++ [0] = ones n ++ [1, 1, 2, 0] := by
    rw [hx, List.append_assoc]
    rfl
  rw [← hx, ← hxy, rotate_repeat]
  rfl

theorem short_track (n m : Nat) :
    (List.replicate m (ones n ++ [2, 0, 1, 1])).flatten ++ (ones n ++ [2]) =
      (ones n ++ [2]) ++ (List.replicate m (image n)).flatten := by
  have hxy : (ones n ++ [2]) ++ [0, 1, 1] = ones n ++ [2, 0, 1, 1] :=
    List.append_assoc _ _ _
  rw [← hxy, rotate_repeat]
  rfl

theorem initial_tracks (n : Nat) :
    [1, 0] ++ ones (n + 1) ++ [1, 2] = [1] ++ image n ∧
      [0, 1] ++ ones (n + 1) ++ [2, 1] = image n ++ [1] := by
  have slide (m : Nat) (rest : Word) : ones m ++ 1 :: rest = 1 :: (ones m ++ rest) := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (List.cons 1) ih
  constructor
  · change 1 :: 0 :: (ones (n + 1) ++ 1 :: [2]) = 1 :: 0 :: (1 :: (ones (n + 1) ++ [2]))
    rw [slide]
  · unfold image
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    rfl

end Psc.ParameterFamilyWords
