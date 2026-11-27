/- A finite marker register on ordered substitution addresses. -/
module

public import PscVerif.PeriodicPartnerMarkerParity
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Abel

public section

namespace Psc.PeriodicPartnerMarkerReachability

open Psc.PeriodicPartnerMarkerParity

variable {A : Type*}

def weight (row : A → ZMod 2) (w : List A) : ZMod 2 := (w.map row).sum

def pull (σ : A → List A) (row : A → ZMod 2) (a : A) : ZMod 2 := weight row (σ a)

private theorem weight_add (r s : A → ZMod 2) (w : List A) :
    weight (fun a => r a + s a) w = weight r w + weight s w := by
  simp [weight, List.sum_map_add]

private theorem pull_add (σ : A → List A) (r s : A → ZMod 2) (a : A) :
    pull σ (fun b => r b + s b) a = pull σ r a + pull σ s a :=
  weight_add r s (σ a)

private theorem weight_flatMap (σ : A → List A) (r : A → ZMod 2) (w : List A) :
    weight r (w.flatMap σ) = weight (pull σ r) w := by
  induction w with
  | nil => simp [weight]
  | cons a w ih =>
    simpa [weight, List.flatMap_cons, List.sum_append, pull] using
      congrArg (weight r (σ a) + ·) ih

def imageWeight (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ) (a : A) : ZMod 2 :=
  adjacentCount (mark j) (σ a)

/-- Three consecutive image rows absorb the internal contribution of inflation. -/
def correction (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ) (a : A) : ZMod 2 :=
  imageWeight σ mark (j - 1) a + pull σ (imageWeight σ mark (j - 2)) a +
    pull σ (pull σ (imageWeight σ mark (j - 3))) a

theorem correction_step (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ)
    (hnil : ∀ row, pull σ (pull σ (pull σ row)) = 0) :
    (fun a => imageWeight σ mark j a + pull σ (correction σ mark j) a) =
      correction σ mark (j + 1) := by
  funext a
  change imageWeight σ mark j a + pull σ (fun b => imageWeight σ mark (j - 1) b +
    pull σ (imageWeight σ mark (j - 2)) b +
    pull σ (pull σ (imageWeight σ mark (j - 3))) b) a = _
  simp only [correction, pull_add, hnil, Pi.zero_apply, add_zero]
  rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega,
    show j + 1 - 3 = j - 2 by omega, add_assoc]

def corrected (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ) (w : List A) : ZMod 2 :=
  (adjacentCount (mark j) w : ZMod 2) + weight (correction σ mark j) w

/-- One inflation changes the phase by one in the corrected marker. -/
theorem corrected_inflation (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ)
    (first last : A → A) (hfirst : ∀ a, (σ a).head? = some (first a))
    (hlast : ∀ a, (σ a).getLast? = some (last a))
    (hphase : ∀ a b, mark j (last a) (first b) = mark (j + 1) a b)
    (hnil : ∀ row, pull σ (pull σ (pull σ row)) = 0) (w : List A) :
    corrected σ mark j (w.flatMap σ) = corrected σ mark (j + 1) w := by
  have hmark : (fun a b => mark j (last a) (first b)) = mark (j + 1) := by
    funext a b
    exact hphase a b
  have hweight : (↑((w.map (fun a => adjacentCount (mark j) (σ a))).sum) : ZMod 2) =
      weight (imageWeight σ mark j) w := by
    induction w with
    | nil => simp [weight]
    | cons a w ih =>
      simpa only [weight, imageWeight, List.map_cons, List.sum_cons, Nat.cast_add] using
        congrArg ((adjacentCount (mark j) (σ a) : ZMod 2) + ·) ih
  rw [corrected, corrected, adjacentCount_flatMap σ (mark j) first last hfirst hlast, hmark,
    Nat.cast_add, hweight, weight_flatMap, ← correction_step σ mark j hnil, weight_add]
  ac_rfl

/-- The correction cancels from the observed parity at a balanced cut. -/
theorem corrected_difference_of_perm (σ : A → List A) (mark : ℤ → A → A → Bool)
    (j : ℤ) {u v : List A} (h : u.Perm v) :
    corrected σ mark j u - corrected σ mark j v =
      (adjacentCount (mark j) u : ZMod 2) - adjacentCount (mark j) v := by
  rw [corrected, corrected, show weight (correction σ mark j) u =
    weight (correction σ mark j) v from (h.map _).sum_eq, add_sub_add_right_eq_sub]

private theorem corrected_append (σ : A → List A) (mark : ℤ → A → A → Bool)
    (j : ℤ) (u v : List A) :
    corrected σ mark j (u ++ v) = corrected σ mark j u + corrected σ mark j v +
      countJoin (mark j) u.getLast? v.head? := by
  simp only [corrected, adjacentCount_append, Nat.cast_add, weight, List.map_append,
    List.sum_append]
  ac_rfl

private theorem last_flatMap (σ : A → List A) (last : A → A)
    (hlast : ∀ a, (σ a).getLast? = some (last a)) (w : List A) :
    (w.flatMap σ).getLast? = w.getLast?.map last := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.flatMap_cons, List.getLast?_append, ih, hlast]
    cases w <;> rfl

/-- The two last letters and one parity bit suffice for the marker component. -/
structure Register (A : Type*) where
  topLast : Option A
  bottomLast : Option A
  parity : ZMod 2

def register (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ)
    (u v : List A) : Register A :=
  ⟨u.getLast?, v.getLast?, corrected σ mark j u - corrected σ mark j v⟩

theorem register_empty (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ) :
    register σ mark j [] [] = ⟨none, none, 0⟩ := by
  simp [register]

theorem register_of_perm (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ)
    {u v : List A} (h : u.Perm v) :
    register σ mark j u v =
      ⟨u.getLast?, v.getLast?, (adjacentCount (mark j) u : ZMod 2) - adjacentCount (mark j) v⟩ := by
  simp only [register, corrected_difference_of_perm σ mark j h]

theorem register_periodic (σ : A → List A) (mark : ℤ → A → A → Bool)
    (hp : ∀ j, mark (j + 6) = mark j) (j : ℤ) (u v : List A) :
    register σ mark (j + 6) u v = register σ mark j u v := by
  have hw (i : ℤ) : imageWeight σ mark (i + 6) = imageWeight σ mark i := by
    funext a
    simp only [imageWeight, hp]
  have h : correction σ mark (j + 6) = correction σ mark j := by
    funext a
    simp only [correction, show j + 6 - 1 = j - 1 + 6 by omega,
      show j + 6 - 2 = j - 2 + 6 by omega, show j + 6 - 3 = j - 3 + 6 by omega, hw]
  simp only [register, corrected, h, hp]

/-- Update by the proper image prefixes preceding the two chosen letters. -/
def advance (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ) (last : A → A)
    (state : Register A) (p q : List A) : Register A :=
  let x := state.topLast.map last
  let y := state.bottomLast.map last
  ⟨p.getLast?.or x, q.getLast?.or y,
    state.parity + (corrected σ mark j p + countJoin (mark j) x p.head?) -
      (corrected σ mark j q + countJoin (mark j) y q.head?)⟩

/-- The register step agrees with literal inflation and prefix extension. -/
theorem advance_register (σ : A → List A) (mark : ℤ → A → A → Bool) (j : ℤ)
    (first last : A → A) (hfirst : ∀ a, (σ a).head? = some (first a))
    (hlast : ∀ a, (σ a).getLast? = some (last a))
    (hphase : ∀ a b, mark j (last a) (first b) = mark (j + 1) a b)
    (hnil : ∀ row, pull σ (pull σ (pull σ row)) = 0) (u v p q : List A) :
    advance σ mark j last (register σ mark (j + 1) u v) p q =
      register σ mark j (u.flatMap σ ++ p) (v.flatMap σ ++ q) := by
  simp only [advance, register, List.getLast?_append, last_flatMap σ last hlast, corrected_append,
    corrected_inflation σ mark j first last hfirst hlast hphase hnil]
  congr 1
  abel

/-- At an intermediate opposite cut, the two interval laws and the seam
contribution combine to the law for their concatenation. -/
theorem combine_interval_laws (first₀ last₁ first₁ last₂ : ZMod 2) :
    (1 + first₀ + last₁) + (1 + last₁ + first₁) + (1 + first₁ + last₂) = 1 + first₀ + last₂ := by
  have double (x : ZMod 2) : x + x = 0 := by decide +revert
  calc
    _ = ((1 + 1) + (last₁ + last₁) + (first₁ + first₁)) + (1 + first₀ + last₂) := by abel
    _ = _ := by simp only [double, zero_add]

/-- Once the first interval obeys the law, testing the whole interval is
equivalent to testing the second interval. -/
theorem extend_interval_iff (first₀ last₁ first₁ last₂ observed : ZMod 2) :
    (1 + first₀ + last₁) + (1 + last₁ + first₁) + observed = 1 + first₀ + last₂ ↔
      observed = 1 + first₁ + last₂ := by
  rw [← combine_interval_laws first₀ last₁ first₁ last₂]
  exact add_left_cancel_iff

def bit (a : Bool) : ZMod 2 := if a then 1 else 0

def zeroPair (a b : Bool) : Bool := !a && !b

/-- Complementary binary words obey the marker law at every even length. -/
theorem complementary_words_parity (a : Bool) (tail : List Bool) :
    (adjacentCount zeroPair (a :: tail) : ZMod 2) -
        adjacentCount zeroPair ((a :: tail).map (! ·)) =
      (tail.length : ZMod 2) + bit a + bit ((a :: tail).getLast?.getD a) := by
  induction tail generalizing a with
  | nil => cases a <;> decide
  | cons b tail ih =>
    let u := adjacentCount zeroPair (b :: tail)
    let v := adjacentCount zeroPair ((b :: tail).map (! ·))
    let x := countJoin zeroPair (some a) (some b)
    let y := countJoin zeroPair (some (!a)) (some (!b))
    have hend : (a :: b :: tail).getLast?.getD a = (b :: tail).getLast?.getD b := by
      cases tail <;> rfl
    have hseam : (x : ZMod 2) - y = 1 + bit a + bit b := by
      cases a <;> cases b <;> decide
    change ((u + x : ℕ) : ZMod 2) - ((v + y : ℕ) : ZMod 2) = _
    rw [Nat.cast_add, Nat.cast_add, hend]
    calc
      _ = ((u : ZMod 2) - v) + ((x : ZMod 2) - y) := by abel
      _ = (tail.length : ZMod 2) + bit b + bit ((b :: tail).getLast?.getD b) +
          (1 + bit a + bit b) := by
        rw [hseam]
        exact congrArg (· + (1 + bit a + bit b)) (ih b)
      _ = _ := by
        have double : bit b + bit b = 0 := by cases b <;> decide
        rw [List.length_cons, Nat.cast_add, Nat.cast_one]
        calc
          _ = (bit b + bit b) + ((tail.length : ZMod 2) + 1 + bit a +
              bit ((b :: tail).getLast?.getD b)) := by abel
          _ = _ := by rw [double, zero_add]

end Psc.PeriodicPartnerMarkerReachability
