/- Literal left coincidences for `1 / 2 / (1 0^m 2^r 1)` with `0 < m ≤ r`. -/
module

import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Iterate

public section

namespace Psc.PeriodicPartnerCompanionWords

abbrev Word := List (Fin 3)

private def zeroRun (m : ℕ) : Word := 1 :: List.replicate m 0

private def oneRun (m : ℕ) : Word := 2 :: List.replicate m 1

def longWord (m r : ℕ) : Word := zeroRun m ++ List.replicate r 2 ++ [1]

def sigma (m r : ℕ) (a : Fin 3) : Word :=
  if a = 0 then [1] else if a = 1 then [2] else longWord m r

private def copies {α : Type*} (n : ℕ) (w : List α) : List α :=
  (List.replicate n w).flatten

private theorem copies_succ {α : Type*} (n : ℕ) (w : List α) :
    copies (n + 1) w = w ++ copies n w := by
  simp [copies, List.replicate_succ]

private theorem flatMap_copies {α β : Type*} (s : α → List β) (n : ℕ) (w : List α) :
    (copies n w).flatMap s = copies n (w.flatMap s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copies_succ, List.flatMap_append, ih]

private def second (m r : ℕ) : Word := oneRun m ++ copies r (longWord m r) ++ [2]

private theorem image_longWord (m r : ℕ) :
    (longWord m r).flatMap (sigma m r) = second m r := by
  simp [longWord, zeroRun, oneRun, second, copies, List.flatMap_append, List.flatMap_replicate,
    sigma, List.append_assoc]

private theorem image_second (m r : ℕ) :
    (second m r).flatMap (sigma m r) =
      longWord m r ++ List.replicate m 2 ++ copies r (second m r) ++ longWord m r := by
  rw [second, List.flatMap_append, List.flatMap_append, flatMap_copies, image_longWord]
  simp [second, oneRun, List.flatMap_replicate, sigma, List.append_assoc]

/-- Both third iterates have a `2` after prefixes with equal letter counts. -/
theorem level_three_witness (m r : ℕ) (hm : 0 < m) (hr : m < r) :
    ∃ P Q U V : Word,
      ((fun w : Word => w.flatMap (sigma m r))^[3]) [1] = P ++ 2 :: U ∧
      ((fun w : Word => w.flatMap (sigma m r))^[3]) [2] = Q ++ 2 :: V ∧
      ∀ a, P.count a = Q.count a := by
  let w := longWord m r
  let d := second m r
  let a := oneRun m
  let p := zeroRun m
  let q : Word := List.replicate m 2
  let tail₁ : Word := List.replicate (r - m - 1) 2 ++ [1]
  let tail₂ : Word := List.replicate (r - 1) 2 ++ [1]
  have hlong₁ : w = p ++ q ++ 2 :: tail₁ := by
    change p ++ List.replicate r 2 ++ [1] = _
    conv_lhs => rw [show r = m + (r - m - 1 + 1) by omega]
    simp [List.replicate_add, List.replicate_succ, q, tail₁, List.append_assoc]
  have hlong₂ : w = p ++ 2 :: tail₂ := by
    change p ++ List.replicate r 2 ++ [1] = _
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    simp [List.replicate_succ, tail₂, List.append_assoc]
  have hcopies₁ : copies r w = w ++ w ++ copies (r - 2) w := by
    conv_lhs => rw [show r = (r - 2) + 1 + 1 by omega]
    simp [copies_succ, List.append_assoc]
  have hcopies₂ : copies r w = w ++ copies (r - 1) w := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [copies_succ]
  have hcopies₃ : copies r d = d ++ copies (r - 1) d := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [copies_succ]
  have htop : d = (a ++ w ++ p ++ q) ++ 2 :: (tail₁ ++ copies (r - 2) w ++ [2]) := by
    change a ++ copies r w ++ [2] = _
    rw [hcopies₁]
    calc
      a ++ (w ++ w ++ copies (r - 2) w) ++ [2] =
          a ++ (w ++ (p ++ q ++ 2 :: tail₁) ++ copies (r - 2) w) ++ [2] :=
        congrArg (fun t => a ++ (w ++ t ++ copies (r - 2) w) ++ [2]) hlong₁
      _ = _ := by simp [List.append_assoc]
  have hbottom : w ++ q ++ copies r d ++ w =
      (w ++ q ++ a ++ p) ++ 2 :: (tail₂ ++ copies (r - 1) w ++ [2] ++ copies (r - 1) d ++ w) := by
    rw [hcopies₃]
    have hd : d = a ++ (w ++ copies (r - 1) w) ++ [2] := by
      change a ++ copies r w ++ [2] = _
      rw [hcopies₂]
    calc
      w ++ q ++ (d ++ copies (r - 1) d) ++ w =
          w ++ q ++ ((a ++ (w ++ copies (r - 1) w) ++ [2]) ++ copies (r - 1) d) ++ w :=
        congrArg (fun t => w ++ q ++ (t ++ copies (r - 1) d) ++ w) hd
      _ = w ++ q ++
          ((a ++ ((p ++ 2 :: tail₂) ++ copies (r - 1) w) ++ [2]) ++ copies (r - 1) d) ++ w :=
        congrArg (fun t => w ++ q ++
          ((a ++ (t ++ copies (r - 1) w) ++ [2]) ++ copies (r - 1) d) ++ w) hlong₂
      _ = _ := by simp [List.append_assoc]
  let sub (xs : Word) := xs.flatMap (sigma m r)
  have h1 : sub [1] = [2] := by simp [sub, sigma]
  have h2 : sub [2] = w := by simp [sub, sigma, w]
  have hw : sub w = d := image_longWord m r
  have hd : sub d = w ++ q ++ copies r d ++ w := image_second m r
  refine ⟨a ++ w ++ p ++ q, w ++ q ++ a ++ p,
    tail₁ ++ copies (r - 2) w ++ [2], tail₂ ++ copies (r - 1) w ++ [2] ++ copies (r - 1) d ++ w,
    ?_, ?_, ?_⟩
  · change sub (sub (sub [1])) = _
    rw [h1, h2, hw, htop]
  · change sub (sub (sub [2])) = _
    rw [h2, hw, hd, hbottom]
  · intro b
    simp only [List.count_append]
    omega

/-- At the equal-run boundary, the fourth iterates have a `2` after
prefixes with equal counts. The run length is `n + 1`. -/
theorem level_four_equal_run_witness (n : ℕ) :
    let m := n + 1
    ∃ P Q U V : Word,
      ((fun w : Word => w.flatMap (sigma m m))^[4]) [1] = P ++ 2 :: U ∧
      ((fun w : Word => w.flatMap (sigma m m))^[4]) [2] = Q ++ 2 :: V ∧
      ∀ a, P.count a = Q.count a := by
  let m := n + 1
  let w := longWord m m
  let d := second m m
  let a := oneRun m
  let p := zeroRun m
  let q : Word := List.replicate m 2
  let q₀ : Word := List.replicate n 2
  let sub (xs : Word) := xs.flatMap (sigma m m)
  have hqEnd : q = q₀ ++ [2] := by simp [q, q₀, m, List.replicate_add]
  have hwFirst : w = p ++ 2 :: (q₀ ++ [1]) := by
    simp [w, longWord, p, q₀, m, List.replicate_succ]
  have hwLast : w = (p ++ q₀) ++ 2 :: [1] := by
    change p ++ q ++ [1] = _
    simp [hqEnd, List.append_assoc]
  have hcopiesLast : copies m w = copies n w ++ w := by
    simp [copies, m, List.replicate_add]
  have hdSplit : d = a ++ copies n w ++ w ++ [2] := by
    change a ++ copies m w ++ [2] = _
    simp [hcopiesLast, List.append_assoc]
  have hdFirst : d = (a ++ copies n w ++ p) ++ 2 :: (q₀ ++ [1, 2]) := by
    calc
      d = a ++ copies n w ++ w ++ [2] := hdSplit
      _ = a ++ copies n w ++ (p ++ 2 :: (q₀ ++ [1])) ++ [2] :=
        congrArg (fun t => a ++ copies n w ++ t ++ [2]) hwFirst
      _ = _ := by simp [List.append_assoc]
  have h1 : sub [1] = [2] := by simp [sub, sigma]
  have h2 : sub [2] = w := by simp [sub, sigma, w]
  have hw : sub w = d := image_longWord m m
  have hd : sub d = w ++ q ++ copies m d ++ w := image_second m m
  have hq : q.flatMap (sigma m m) = copies m w := by
    simp [q, copies, List.flatMap_replicate, sigma, w]
  have h4 : sub (w ++ q ++ copies m d ++ w) = d ++ copies m w ++ copies m (sub d) ++ d := by
    simp only [sub, List.flatMap_append, hq, flatMap_copies, w, image_longWord]
    rfl
  refine ⟨w ++ q ++ a ++ copies n w ++ p, d ++ p ++ q₀,
    q₀ ++ [1, 2] ++ copies n d ++ w, [1] ++ copies n w ++ copies m (sub d) ++ d,
    ?_, ?_, ?_⟩
  · change sub (sub (sub (sub [1]))) = _
    rw [h1, h2, hw, hd, show copies m d = d ++ copies n d from copies_succ n d]
    calc
      _ = w ++ q ++ (((a ++ copies n w ++ p) ++ 2 :: (q₀ ++ [1, 2])) ++ copies n d) ++ w :=
        congrArg (fun t => w ++ q ++ (t ++ copies n d) ++ w) hdFirst
      _ = _ := by simp [List.append_assoc]
  · change sub (sub (sub (sub [2]))) = _
    conv_lhs => rw [h2, hw, hd, h4, show copies m w = w ++ copies n w from copies_succ n w]
    calc
      _ = d ++ (((p ++ q₀) ++ 2 :: [1]) ++ copies n w) ++ copies m (sub d) ++ d :=
        congrArg (fun t => d ++ (t ++ copies n w) ++ copies m (sub d) ++ d) hwLast
      _ = _ := by simp [List.append_assoc]
  · intro b
    have hdc := congrArg (List.count b) hdSplit
    have hqc := congrArg (List.count b) hqEnd
    simp only [List.count_append] at hdc hqc ⊢
    omega

end Psc.PeriodicPartnerCompanionWords
