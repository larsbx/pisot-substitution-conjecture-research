/- Finite algebra for the marker constraint on original twin words. -/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic

public section

namespace Psc.PeriodicPartnerMarkerParity

/-- An original legal seam joins its last-letter and first-letter vertices. -/
def SeamLink {A B : Type*} (legal : A → B → Prop) : Sum A B → Sum A B → Prop
  | .inl a, .inr b => legal a b
  | _, _ => False

/-- Joining the opposite pairs through the singleton corner identifies both
normalized gauges in a connected original seam graph. -/
theorem normalized_gauges_agree_of_connected {A B C : Type*}
    (legal : A → B → Prop) (a₀ : A) (b₀ : B) (left : A → C) (right : B → C)
    (hleft : ∃ a, a ≠ a₀ ∧ legal a b₀) (hright : ∃ b, b ≠ b₀ ∧ legal a₀ b)
    (hdiag : ∀ a b, a ≠ a₀ → b ≠ b₀ → legal a b → left a = right b)
    (hoff : ∀ a b, a ≠ a₀ → b ≠ b₀ → legal a b₀ → legal a₀ b → left a = right b)
    (hconnected : ∀ x y, Relation.EqvGen (SeamLink legal) x y) :
    ∃ c, (∀ a, a ≠ a₀ → left a = c) ∧ ∀ b, b ≠ b₀ → right b = c := by
  classical
  obtain ⟨a₁, ha₁, ha₁b₀⟩ := hleft
  obtain ⟨b₁, hb₁, ha₀b₁⟩ := hright
  let c := left a₁
  have hc : right b₁ = c := (hoff a₁ b₁ ha₁ hb₁ ha₁b₀ ha₀b₁).symm
  let value : Sum A B → C
    | .inl a => if a = a₀ then c else left a
    | .inr b => if b = b₀ then c else right b
  have step (a b) (hab : legal a b) : value (.inl a) = value (.inr b) := by
    by_cases ha : a = a₀
    · subst a
      by_cases hb : b = b₀
      · simp [value, hb]
      · simpa [value, hb, c] using hoff a₁ b ha₁ hb ha₁b₀ hab
    · by_cases hb : b = b₀
      · subst b
        simpa [value, ha, hc] using hoff a b₁ ha hb₁ hab ha₀b₁
      · simpa [value, ha, hb] using hdiag a b ha hb hab
  have stepEq {x y} (h : SeamLink legal x y) : value x = value y := by
    cases x <;> cases y <;> first | exact step _ _ h | exact False.elim h
  have along {x y} (h : Relation.EqvGen (SeamLink legal) x y) : value x = value y := by
    induction h with
    | rel _ _ h => exact stepEq h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact ⟨c, fun a ha => by simpa [value, ha] using along (hconnected (.inl a) (.inl a₀)),
    fun b hb => by simpa [value, hb] using along (hconnected (.inr b) (.inl a₀))⟩

/-- The marked-pair contribution at a join, with zero for an absent endpoint. -/
@[expose] def countJoin {A : Type*} (mark : A → A → Bool) : Option A → Option A → ℕ
  | some a, some b => if mark a b then 1 else 0
  | _, _ => 0

/-- Count internal marked adjacent pairs of a word. -/
@[expose] def adjacentCount {A : Type*} (mark : A → A → Bool) : List A → ℕ
  | [] => 0
  | a :: as => adjacentCount mark as + countJoin mark (some a) as.head?

theorem adjacentCount_append {A : Type*} (mark : A → A → Bool) (u v : List A) :
    adjacentCount mark (u ++ v) =
      adjacentCount mark u + adjacentCount mark v + countJoin mark u.getLast? v.head? := by
  induction u with
  | nil => simp [adjacentCount, countJoin]
  | cons a u ih =>
    cases u with
    | nil => simp [adjacentCount, countJoin]
    | cons b u =>
      change adjacentCount mark ((b :: u) ++ v) + countJoin mark (some a) ((b :: u) ++ v).head? =
        (adjacentCount mark (b :: u) + countJoin mark (some a) (b :: u).head?) +
          adjacentCount mark v + countJoin mark (a :: b :: u).getLast? v.head?
      rw [ih]
      simp only [List.cons_append, List.head?_cons, List.getLast?_cons_cons]
      omega

theorem head_flatMap {A B : Type*} (s : A → List B) (first : A → B)
    (hfirst : ∀ a, (s a).head? = some (first a)) (w : List A) :
    (w.flatMap s).head? = w.head?.map first := by
  cases w <;> simp [List.flatMap_cons, hfirst]

theorem adjacentCount_flatMap {A B : Type*} (s : A → List B) (mark : B → B → Bool)
    (first last : A → B) (hfirst : ∀ a, (s a).head? = some (first a))
    (hlast : ∀ a, (s a).getLast? = some (last a)) (w : List A) :
    adjacentCount mark (w.flatMap s) = (w.map (fun a => adjacentCount mark (s a))).sum +
      adjacentCount (fun a b => mark (last a) (first b)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.flatMap_cons, adjacentCount_append, ih, hlast a, head_flatMap s first hfirst]
    cases w with
    | nil => simp [adjacentCount, countJoin]
    | cons b w =>
      simp only [List.map_cons, List.sum_cons, List.head?_cons, Option.map_some, adjacentCount,
        countJoin]
      omega

/-- Inflated counts inside individual letter images cancel on balanced
words. Only the projected original cuts contribute to the difference. -/
theorem balanced_marker_difference_of_inflation {A B : Type*}
    (s : A → List B) (mark : B → B → Bool) (first last : A → B)
    (hfirst : ∀ a, (s a).head? = some (first a))
    (hlast : ∀ a, (s a).getLast? = some (last a)) {u v : List A} (h : u.Perm v) :
    (adjacentCount mark (u.flatMap s) : ℤ) - adjacentCount mark (v.flatMap s) =
      (adjacentCount (fun a b => mark (last a) (first b)) u : ℤ) -
        adjacentCount (fun a b => mark (last a) (first b)) v := by
  rw [adjacentCount_flatMap s mark first last hfirst hlast,
    adjacentCount_flatMap s mark first last hfirst hlast,
    (h.map (fun a => adjacentCount mark (s a))).sum_eq]
  omega

/-- The difference at the common cut of opposite seams is one plus the
two endpoint group bits modulo two. -/
theorem marker_difference_of_opposite_seams (left right : Bool) :
    (if !left && !right then 1 else 0 : ZMod 2) - (if left && right then 1 else 0) =
      1 + (if left then 1 else 0) + (if right then 1 else 0) := by
  cases left <;> cases right <;> decide

/-- The common normalized gauge cancels in the parity on a balanced block. -/
theorem marker_parity_of_common_gauge (observed start finish first last c : ZMod 2)
    (hstart : start = c + first + 1) (hfinish : finish = c + last)
    (hcount : observed = finish - start) : observed = 1 + first + last := by
  rw [hcount, hstart, hfinish]
  have self_neg (x : ZMod 2) : -x = x := by decide +revert
  have hc : c + c = 0 := by decide +revert
  simp only [sub_eq_add_neg, self_neg]
  calc
    _ = (c + c) + (1 + first + last) := by ac_rfl
    _ = _ := by rw [hc, zero_add]

/-- The two complementary binary words in Thue–Morse pass the local law. -/
theorem thue_morse_marker_parity_control :
    let mark : Bool → Bool → Bool := fun a b => !a && !b
    ([false, true] : List Bool).Perm [true, false] ∧
      (adjacentCount mark [false, true] : ℤ) - adjacentCount mark [true, false] = 0 ∧
      (1 + 0 + 1 : ℤ) % 2 = 0 := by
  decide

set_option maxRecDepth 4096 in
/-- A literal cubic prefix from the two periodic right rays of
`01/112/021` has opposite endpoint groups and violates the marker law. -/
theorem cubic_marker_parity_control :
    let σ : Fin 3 → List (Fin 3) := fun a =>
      if a = 0 then [0, 1] else if a = 1 then [1, 1, 2] else [0, 2, 1]
    let inflate := fun w : List (Fin 3) => w.flatMap σ
    let power := fun a : Fin 3 => (inflate^[6]) [a]
    let first := fun a : Fin 3 => if a = 1 then 1 else 0
    let last := fun a : Fin 3 => if a = 1 then 1 else 2
    let top := (power 0).take 30
    let bottom := (power 1).take 30
    let mark := fun a b => last a == 1 && first b == 0
    (∀ a, (power a).head? = some (first a) ∧ (power a).getLast? = some (last a)) ∧
    top.Perm bottom ∧ top.getLast? = some 0 ∧ bottom.getLast? = some 1 ∧
    (power 0)[30]? = some 2 ∧ (power 1)[30]? = some 1 ∧
    adjacentCount mark top = 7 ∧ adjacentCount mark bottom = 8 := by
  decide

end Psc.PeriodicPartnerMarkerParity
