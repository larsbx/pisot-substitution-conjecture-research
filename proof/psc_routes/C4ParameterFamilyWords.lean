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

/-! The 25 representative states and complete occurrence-ordered symbolic rows. -/

namespace Psc.ParameterFamilyRows
open Psc.ParameterFamilyWords (Word ones)
abbrev Pair := Word × Word

def subst (s : Fin 3 → Word) (w : Word) : Word := (w.map s).flatten
private theorem subst_append (s : Fin 3 → Word) (x y : Word) :
    subst s (x ++ y) = subst s x ++ subst s y := by simp [subst]





def substitution (k : Nat) (a : Fin 3) : Word :=
  if a = 0 then [1] else if a = 1 then [0] ++ ones k ++ [2] else [0, 0, 1]

def baseState (n : Nat) : Nat → Pair
  | 0 => ([0], [0])
  | 1 => ([0, 1], [1, 0])
  | 2 => ([0, 1, 0] ++ ones (n + 5) ++ [2], ones (n + 5) ++ [2, 0, 0, 1])
  | 3 => ([0, 1, 1], [1, 1, 0])
  | 4 => ([0, 1, 1, 0] ++ ones (n + 5) ++ [2], ones (n + 5) ++ [2, 0, 0, 1, 1])
  | 5 => ([0, 1, 1, 0] ++ ones (n + 5) ++ [2, 0], ones (n + 5) ++ [2, 0, 0, 1, 0, 1])
  | 6 => ([0, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2], ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1])
  | 7 => ([0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2], ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1, 1])
  | 8 => ([0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0], ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1, 0, 1])
  | 9 => ([0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 1, 0], ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1, 0, 1, 1])
  | 10 => ([1], [1])
  | 11 => ([1, 1, 2, 0], [2, 0, 1, 1])
  | 12 => ([1, 1, 2, 0, 0], [2, 0, 0, 1, 1])
  | 13 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones (n + 5) ++ [2])
  | 14 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2])
  | 15 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2])
  | 16 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2])
  | 17 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 1, 0] ++ ones (n + 5) ++ [2])
  | 18 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0], [2, 0, 0, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2])
  | 19 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2])
  | 20 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 0, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 1, 0] ++ ones (n + 5) ++ [2, 0])
  | 21 => ([1, 1, 2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 1, 0] ++ ones (n + 5) ++ [2, 0] ++ ones (n + 5) ++ [2, 1, 0] ++ ones (n + 5) ++ [2])
  | 22 => ([1, 2], [2, 1])
  | 23 => ([1, 2, 0], [2, 0, 1])
  | 24 => ([1, 2, 1, 0], [2, 0, 1, 1])
  | _ => ([], [])

/-- Indices 25 through 49 decode the corresponding track swaps. -/
def state (n i : Nat) : Pair :=
  if i < 25 then baseState n i else (baseState n (i - 25)).swap

private def diags (n : Nat) : List Nat := List.replicate n 10

private def period (n : Nat) (swapped : Bool) : List Nat :=
  diags (n + 3) ++ [if swapped then 36 else 11]

private def pump (n m : Nat) (swapped : Bool) : List Nat :=
  (List.replicate m (period n swapped)).flatten ++ diags (n + 3)

def baseRow (n : Nat) : Nat → List Nat
  | 1 => [26] ++ diags (n + 4) ++ [22]
  | 2 => [26] ++ diags (n + 4) ++ [24] ++ pump n (n + 3) false ++ [14]
  | 3 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [22]
  | 4 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 2) false ++ [16]
  | 5 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 2) false ++ [17]
  | 6 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 2) false ++ [15] ++ [28] ++ pump n (n + 2) false ++ [16]
  | 7 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 1) false ++ [18] ++ [28] ++ pump n (n + 1) false ++ [19]
  | 8 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 1) false ++ [18] ++ [28] ++ pump n (n + 1) false ++ [21]
  | 9 => [26] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [23] ++ diags (n + 4) ++ [24] ++ pump n (n + 1) false ++ [18] ++ [28] ++ pump n (n + 1) false ++ [20] ++ diags (n + 4) ++ [47]
  | 11 => [0] ++ [31]
  | 12 => [0] ++ [32]
  | 13 => [0] ++ [34] ++ pump n (n + 4) true ++ [37] ++ [10]
  | 14 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [39]
  | 15 => [0] ++ [34] ++ pump n (n + 4) true ++ [37] ++ [3] ++ pump n (n + 4) true ++ [37] ++ [10]
  | 16 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [38] ++ [3] ++ pump n (n + 3) true ++ [39]
  | 17 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [38] ++ [1] ++ diags (n + 4) ++ [49] ++ pump n (n + 2) true ++ [41]
  | 18 => [0] ++ [34] ++ pump n (n + 4) true ++ [37] ++ [3] ++ pump n (n + 4) true ++ [37] ++ [3] ++ pump n (n + 4) true ++ [37] ++ [10]
  | 19 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [38] ++ [3] ++ pump n (n + 3) true ++ [38] ++ [3] ++ pump n (n + 3) true ++ [39]
  | 20 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [38] ++ [3] ++ pump n (n + 3) true ++ [38] ++ [1] ++ diags (n + 4) ++ [49] ++ pump n (n + 2) true ++ [42]
  | 21 => [0] ++ [33] ++ diags (n + 4) ++ [49] ++ pump n (n + 3) true ++ [38] ++ [3] ++ pump n (n + 3) true ++ [38] ++ [1] ++ diags (n + 4) ++ [49] ++ pump n (n + 2) true ++ [41]
  | 22 => [0] ++ [27]
  | 23 => [0] ++ [29]
  | 24 => [0] ++ [30] ++ diags (n + 4) ++ [47]
  | _ => []

def swapIndex (i : Nat) : Nat := if i < 25 then i + 25 else i - 25

/-- A signed row decodes to literal ordered pairs. -/
def children (n i : Nat) : List Pair :=
  (if i < 25 then baseRow n i else (baseRow n (i - 25)).map swapIndex).map (state n)

private theorem ones_slide (n : Nat) (w : Word) :
    (1 : Fin 3) :: (ones n ++ w) = ones n ++ 1 :: w := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons 1) ih

private theorem ones_offset (n m : Nat) : ones (n + m) = ones n ++ ones m :=
  (List.replicate_append_replicate (n := n) (m := m) (a := (1 : Fin 3))).symm

private def pieces {α β : Type} (f : α → List β) (xs : List α) : List β :=
  (xs.map f).flatten

private theorem pieces_append {α β : Type} (f : α → List β) (xs ys : List α) :
    pieces f (xs ++ ys) = pieces f xs ++ pieces f ys := by
  simp [pieces]

private theorem pieces_repeat {α β : Type} (f : α → List β) (xs : List α) (m : Nat) :
    pieces f (List.replicate m xs).flatten = (List.replicate m (pieces f xs)).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, List.flatten_cons, pieces_append, ih]

private theorem flatten_repeat_add {α : Type} (w : List α) (m l : Nat) :
    (List.replicate (m + l) w).flatten =
      (List.replicate m w).flatten ++ (List.replicate l w).flatten := by
  rw [← List.replicate_append_replicate (n := m) (m := l), List.flatten_append]

private def largeImage (n : Nat) : Word := [0] ++ ones (n + 5) ++ [2]

private theorem subst_word_run (n m : Nat) :
    subst (substitution (n + 5)) (ones m) =
      (List.replicate m (largeImage n)).flatten := by
  simp [subst, ones, List.map_replicate, substitution, largeImage]

private def top (n : Nat) (i : Nat) : Word := (state n i).1
private def bottom (n : Nat) (i : Nat) : Word := (state n i).2

private theorem diags_track (n m : Nat) :
    pieces (top n) (diags m) = ones m ∧ pieces (bottom n) (diags m) = ones m := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    exact ⟨congrArg (List.cons 1) ih.1, congrArg (List.cons 1) ih.2⟩

private theorem pumped_long (n m : Nat) :
    (List.replicate m (ones (n + 3) ++ [1, 1, 2, 0] : Word)).flatten ++
        (ones (n + 3) ++ [1, 1, 2]) =
      ones (n + 5) ++ [2] ++ (List.replicate m (largeImage n)).flatten := by
  simpa only [List.append_assoc, largeImage, Psc.ParameterFamilyWords.image] using
    Psc.ParameterFamilyWords.long_track (n + 3) m

private theorem pumped_short (n m : Nat) :
    (List.replicate m (ones (n + 3) ++ [2, 0, 1, 1] : Word)).flatten ++
        (ones (n + 3) ++ [2]) =
      ones (n + 3) ++ [2] ++ (List.replicate m (largeImage n)).flatten := by
  simpa only [List.append_assoc, largeImage, Psc.ParameterFamilyWords.image] using
    Psc.ParameterFamilyWords.short_track (n + 3) m

private theorem pieces_cons {α β : Type} (f : α → List β) (x : α) (xs : List α) :
    pieces f (x :: xs) = f x ++ pieces f xs := rfl

private theorem pieces_nil {α β : Type} (f : α → List β) :
    pieces f [] = [] := rfl

private theorem pump_tracks (n m : Nat) :
    (pieces (top n) (pump n m false) ++ [1, 1, 2] =
        ones (n + 5) ++ [2] ++ (List.replicate m (largeImage n)).flatten) ∧
    (pieces (bottom n) (pump n m false) ++ [2] =
        ones (n + 3) ++ [2] ++ (List.replicate m (largeImage n)).flatten) ∧
    (pieces (top n) (pump n m true) ++ [2] =
        ones (n + 3) ++ [2] ++ (List.replicate m (largeImage n)).flatten) ∧
    (pieces (bottom n) (pump n m true) ++ [1, 1, 2] =
        ones (n + 5) ++ [2] ++ (List.replicate m (largeImage n)).flatten) := by
  have ht := fun j => (diags_track n j).1
  have hb := fun j => (diags_track n j).2
  simp only [pump, period, pieces_append, pieces_repeat, ht, hb, pieces_cons, pieces_nil,
    List.append_nil, Bool.false_eq_true, ite_false, ite_true]
  change
    ((List.replicate m (ones (n + 3) ++ [1, 1, 2, 0])).flatten ++ ones (n + 3)) ++ [1, 1, 2] = _ ∧
    ((List.replicate m (ones (n + 3) ++ [2, 0, 1, 1])).flatten ++ ones (n + 3)) ++ [2] = _ ∧
    ((List.replicate m (ones (n + 3) ++ [2, 0, 1, 1])).flatten ++ ones (n + 3)) ++ [2] = _ ∧
    ((List.replicate m (ones (n + 3) ++ [1, 1, 2, 0])).flatten ++ ones (n + 3)) ++ [1, 1, 2] = _
  simp only [List.append_assoc, pumped_long, pumped_short, and_self]

private theorem append_transfer {α : Type} {x y w : List α} (h : x ++ y = w)
    (rest : List α) : x ++ (y ++ rest) = w ++ rest := by
  rw [← List.append_assoc, h]

private theorem subst_one (n : Nat) : substitution (n + 5) 1 = largeImage n := rfl
private theorem subst_zero (n : Nat) : substitution (n + 5) 0 = [1] := rfl
private theorem subst_two (n : Nat) : substitution (n + 5) 2 = [0, 0, 1] := rfl
private theorem subst_cons (s : Fin 3 → Word) (a : Fin 3) (w : Word) :
    subst s (a :: w) = s a ++ subst s w := rfl
private theorem subst_nil (s : Fin 3 → Word) : subst s [] = [] := rfl

private theorem ones_merge_left (x y : Nat) (tail : Word) :
    ones x ++ (ones y ++ tail) = ones (x + y) ++ tail := by
  rw [← List.append_assoc, ← ones_offset]

private def copies (n m : Nat) : Word := (List.replicate m (largeImage n)).flatten

private theorem copies_succ (n m : Nat) :
    copies n (m + 1) = largeImage n ++ copies n m := rfl

private theorem copies_plus (n m j : Nat) :
    copies n (m + j) = copies n m ++ copies n j := flatten_repeat_add _ m j

private theorem subst_word_run' (n m : Nat) : subst (substitution (n + 5)) (ones m) = copies n m :=
  subst_word_run n m

private theorem long_top (n m : Nat) (u : Word) :
    pieces (top n) (pump n m false) ++ 1 :: 1 :: 2 :: u =
      ones (n + 5) ++ 2 :: (copies n m ++ u) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, copies] using
    append_transfer (pump_tracks n m).1 u

private theorem short_bottom (n m : Nat) (u : Word) :
    pieces (bottom n) (pump n m false) ++ 2 :: u =
      ones (n + 3) ++ 2 :: (copies n m ++ u) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, copies] using
    append_transfer (pump_tracks n m).2.1 u

private theorem short_top (n m : Nat) (u : Word) :
    pieces (top n) (pump n m true) ++ 2 :: u =
      ones (n + 3) ++ 2 :: (copies n m ++ u) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, copies] using
    append_transfer (pump_tracks n m).2.2.1 u

private theorem long_bottom (n m : Nat) (u : Word) :
    pieces (bottom n) (pump n m true) ++ 1 :: 1 :: 2 :: u =
      ones (n + 5) ++ 2 :: (copies n m ++ u) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, copies] using
    append_transfer (pump_tracks n m).2.2.2 u


private theorem top_0 (n : Nat) : top n 0 = (baseState n 0).1 := rfl
private theorem bottom_0 (n : Nat) : bottom n 0 = (baseState n 0).2 := rfl
private theorem top_1 (n : Nat) : top n 1 = (baseState n 1).1 := rfl
private theorem bottom_1 (n : Nat) : bottom n 1 = (baseState n 1).2 := rfl
private theorem top_3 (n : Nat) : top n 3 = (baseState n 3).1 := rfl
private theorem bottom_3 (n : Nat) : bottom n 3 = (baseState n 3).2 := rfl
private theorem top_10 (n : Nat) : top n 10 = (baseState n 10).1 := rfl
private theorem bottom_10 (n : Nat) : bottom n 10 = (baseState n 10).2 := rfl
private theorem top_14 (n : Nat) : top n 14 = (baseState n 14).1 := rfl
private theorem bottom_14 (n : Nat) : bottom n 14 = (baseState n 14).2 := rfl
private theorem top_15 (n : Nat) : top n 15 = (baseState n 15).1 := rfl
private theorem bottom_15 (n : Nat) : bottom n 15 = (baseState n 15).2 := rfl
private theorem top_16 (n : Nat) : top n 16 = (baseState n 16).1 := rfl
private theorem bottom_16 (n : Nat) : bottom n 16 = (baseState n 16).2 := rfl
private theorem top_17 (n : Nat) : top n 17 = (baseState n 17).1 := rfl
private theorem bottom_17 (n : Nat) : bottom n 17 = (baseState n 17).2 := rfl
private theorem top_18 (n : Nat) : top n 18 = (baseState n 18).1 := rfl
private theorem bottom_18 (n : Nat) : bottom n 18 = (baseState n 18).2 := rfl
private theorem top_19 (n : Nat) : top n 19 = (baseState n 19).1 := rfl
private theorem bottom_19 (n : Nat) : bottom n 19 = (baseState n 19).2 := rfl
private theorem top_20 (n : Nat) : top n 20 = (baseState n 20).1 := rfl
private theorem bottom_20 (n : Nat) : bottom n 20 = (baseState n 20).2 := rfl
private theorem top_21 (n : Nat) : top n 21 = (baseState n 21).1 := rfl
private theorem bottom_21 (n : Nat) : bottom n 21 = (baseState n 21).2 := rfl
private theorem top_22 (n : Nat) : top n 22 = (baseState n 22).1 := rfl
private theorem bottom_22 (n : Nat) : bottom n 22 = (baseState n 22).2 := rfl
private theorem top_23 (n : Nat) : top n 23 = (baseState n 23).1 := rfl
private theorem bottom_23 (n : Nat) : bottom n 23 = (baseState n 23).2 := rfl
private theorem top_24 (n : Nat) : top n 24 = (baseState n 24).1 := rfl
private theorem bottom_24 (n : Nat) : bottom n 24 = (baseState n 24).2 := rfl
private theorem top_26 (n : Nat) : top n 26 = (baseState n 1).2 := rfl
private theorem bottom_26 (n : Nat) : bottom n 26 = (baseState n 1).1 := rfl
private theorem top_27 (n : Nat) : top n 27 = (baseState n 2).2 := rfl
private theorem bottom_27 (n : Nat) : bottom n 27 = (baseState n 2).1 := rfl
private theorem top_28 (n : Nat) : top n 28 = (baseState n 3).2 := rfl
private theorem bottom_28 (n : Nat) : bottom n 28 = (baseState n 3).1 := rfl
private theorem top_29 (n : Nat) : top n 29 = (baseState n 4).2 := rfl
private theorem bottom_29 (n : Nat) : bottom n 29 = (baseState n 4).1 := rfl
private theorem top_30 (n : Nat) : top n 30 = (baseState n 5).2 := rfl
private theorem bottom_30 (n : Nat) : bottom n 30 = (baseState n 5).1 := rfl
private theorem top_31 (n : Nat) : top n 31 = (baseState n 6).2 := rfl
private theorem bottom_31 (n : Nat) : bottom n 31 = (baseState n 6).1 := rfl
private theorem top_32 (n : Nat) : top n 32 = (baseState n 7).2 := rfl
private theorem bottom_32 (n : Nat) : bottom n 32 = (baseState n 7).1 := rfl
private theorem top_33 (n : Nat) : top n 33 = (baseState n 8).2 := rfl
private theorem bottom_33 (n : Nat) : bottom n 33 = (baseState n 8).1 := rfl
private theorem top_34 (n : Nat) : top n 34 = (baseState n 9).2 := rfl
private theorem bottom_34 (n : Nat) : bottom n 34 = (baseState n 9).1 := rfl
private theorem top_37 (n : Nat) : top n 37 = (baseState n 12).2 := rfl
private theorem bottom_37 (n : Nat) : bottom n 37 = (baseState n 12).1 := rfl
private theorem top_38 (n : Nat) : top n 38 = (baseState n 13).2 := rfl
private theorem bottom_38 (n : Nat) : bottom n 38 = (baseState n 13).1 := rfl
private theorem top_39 (n : Nat) : top n 39 = (baseState n 14).2 := rfl
private theorem bottom_39 (n : Nat) : bottom n 39 = (baseState n 14).1 := rfl
private theorem top_41 (n : Nat) : top n 41 = (baseState n 16).2 := rfl
private theorem bottom_41 (n : Nat) : bottom n 41 = (baseState n 16).1 := rfl
private theorem top_42 (n : Nat) : top n 42 = (baseState n 17).2 := rfl
private theorem bottom_42 (n : Nat) : bottom n 42 = (baseState n 17).1 := rfl
private theorem top_47 (n : Nat) : top n 47 = (baseState n 22).2 := rfl
private theorem bottom_47 (n : Nat) : bottom n 47 = (baseState n 22).1 := rfl
private theorem top_49 (n : Nat) : top n 49 = (baseState n 24).2 := rfl
private theorem bottom_49 (n : Nat) : bottom n 49 = (baseState n 24).1 := rfl

private theorem ones_add_one_tail (x : Nat) (u : Word) :
    ones x ++ 1 :: u = ones (x + 1) ++ u := by
  rw [ones_offset, List.append_assoc]
  rfl

private theorem ones_offset_four (n : Nat) (u : Word) :
    ones (n + 4) ++ 1 :: u = ones (n + 5) ++ u :=
  ones_add_one_tail (n + 4) u

private theorem ones_offset_three (n : Nat) (u : Word) :
    ones (n + 3) ++ 1 :: 1 :: u = ones (n + 5) ++ u := by
  rw [ones_add_one_tail, ones_add_one_tail]

private theorem image_cons (n : Nat) (u : Word) :
    0 :: (ones (n + 5) ++ 2 :: u) = largeImage n ++ u := by
  simp only [largeImage, List.append_assoc, List.cons_append, List.nil_append]

private theorem image_singleton (n : Nat) :
    0 :: (ones (n + 5) ++ [2]) = largeImage n := rfl

private theorem copies_front (n m : Nat) (u : Word) :
    largeImage n ++ (copies n m ++ u) = copies n (m + 1) ++ u := by
  rw [copies_succ, List.append_assoc]

private theorem copies_back (n m : Nat) (u : Word) :
    copies n m ++ (largeImage n ++ u) = copies n (m + 1) ++ u := by
  rw [copies_plus, List.append_assoc]
  simp [copies]

private theorem copies_back_single (n m : Nat) :
    copies n m ++ largeImage n = copies n (m + 1) := by
  rw [copies_plus]
  simp [copies]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 3000000 in
theorem base_tracks (n : Nat) (i : Nat)
    (hi : i < 25)
    (h : (baseState n i).1 ≠ (baseState n i).2) :
    pieces (top n) (baseRow n i) = subst (substitution (n + 5)) (baseState n i).1 ∧
    pieces (bottom n) (baseRow n i) = subst (substitution (n + 5)) (baseState n i).2 := by
  have choices :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try (exfalso; exact h rfl)
  all_goals
    constructor <;>
    simp only [baseRow, pieces_append, pieces_cons, pieces_nil, (diags_track n _).1,
      (diags_track n _).2, List.nil_append, List.append_nil,
      baseState, Prod.fst, Prod.snd, Nat.reduceLT,
      Nat.reduceSub, ite_true, ite_false, subst_append, subst_cons, subst_nil, subst_word_run',
      subst_zero, subst_one, subst_two, List.append_assoc, List.cons_append, List.nil_append]
  all_goals
    simp only [top_0, bottom_0, top_1, bottom_1, top_3, bottom_3, top_10, bottom_10, top_14, bottom_14,
      top_15, bottom_15, top_16, bottom_16, top_17, bottom_17, top_18, bottom_18, top_19, bottom_19,
      top_20, bottom_20, top_21, bottom_21, top_22, bottom_22, top_23, bottom_23, top_24, bottom_24,
      top_26, bottom_26, top_27, bottom_27, top_28, bottom_28, top_29, bottom_29, top_30, bottom_30,
      top_31, bottom_31, top_32, bottom_32, top_33, bottom_33, top_34, bottom_34, top_37, bottom_37,
      top_38, bottom_38, top_39, bottom_39, top_41, bottom_41, top_42, bottom_42, top_47, bottom_47,
      top_49, bottom_49,
      baseState, Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append]
  all_goals
    try simp only [long_top, long_bottom, short_top, short_bottom, ones_slide,
      ones_merge_left, Nat.add_assoc, Nat.reduceAdd, List.append_assoc, List.cons_append,
      List.nil_append]
  all_goals
    try simp only [ones_offset_four, ones_offset_three, image_cons, image_singleton,
      copies_front, copies_back, copies_back_single, Nat.add_assoc, Nat.reduceAdd, List.append_nil]
  all_goals rfl

/-- Both literal concatenations of the representative child row. -/
theorem representative_row_tracks (n i : Nat) (hi : i < 25)
    (h : (state n i).1 ≠ (state n i).2) :
    ((children n i).map Prod.fst).flatten = subst (substitution (n + 5)) (state n i).1 ∧
    ((children n i).map Prod.snd).flatten = subst (substitution (n + 5)) (state n i).2 := by
  have hs : state n i = baseState n i := ite_eq_left hi
  rw [hs] at h ⊢
  simp only [children, ite_eq_left hi, List.map_map, Function.comp_def]
  exact base_tracks n i hi h

theorem swapIndex_lt (i : Nat) (h : i < 50) : swapIndex i < 50 := by
  unfold swapIndex
  split <;> omega

theorem swap_state (n i : Nat) (hi : i < 50) :
    state n (swapIndex i) = (state n i).swap := by
  by_cases h : i < 25
  · simp [swapIndex, state, h, show ¬ i + 25 < 25 by omega]
  · simp [swapIndex, state, h, show i - 25 < 25 by omega]

private theorem pump_lt {n m j : Nat} {swap : Bool} (h : j ∈ pump n m swap) : j < 50 := by
  simp only [pump, List.mem_append, List.mem_flatten] at h
  rcases h with ⟨xs, hxs, hj⟩ | hj
  · have he : xs = period n swap := List.eq_of_mem_replicate hxs
    subst xs
    cases swap <;> simp [period, diags] at hj <;> omega
  · have he : j = 10 := List.eq_of_mem_replicate hj
    omega

theorem base_row_lt (n i j : Nat) (hi : i < 25) (h : j ∈ baseRow n i) :
    j < 50 := by
  have choices :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [baseRow, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, diags, List.mem_replicate] at h
  all_goals
    repeat' first | contradiction | exact pump_lt h | omega | (rcases h with h | h)


theorem base_exit (n i : Nat) (hi : i < 25)
    (hne : (baseState n i).1 ≠ (baseState n i).2) :
    ∃ j ∈ baseRow n i, (state n j).1 = (state n j).2 := by
  have choices :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try (exfalso; exact hne rfl)
  all_goals
    first
    | (refine ⟨10, ?_, rfl⟩; solve | simp [baseRow, diags])
    | (refine ⟨0, ?_, rfl⟩; simp [baseRow])


end Psc.ParameterFamilyRows
