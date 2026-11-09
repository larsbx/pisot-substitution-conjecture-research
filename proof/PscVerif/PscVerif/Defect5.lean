/-
# Degree-five scattered-word defects

The word and ordered-child identities are integral. The only balance input is
agreement of scattered counts in degrees one through four.
-/
import PscVerif.Defect4

namespace Psc.Defect5

open Psc.Binomial Psc.Incidence Psc.Intertwiner3 Psc.Defect4 Psc.SignedCocycle
open Psc.SignedIntertwiner
open scoped BigOperators

section General

variable {α : Type*} [DecidableEq α]

/-- Scattered occurrences of a length-five pattern. -/
def n5 : List α → α → α → α → α → α → ℕ
  | [], _, _, _, _, _ => 0
  | x :: t, a, b, c, d, e => (if x = a then n4 t b c d e else 0) + n5 t a b c d e

@[simp] theorem n5_nil (a b c d e : α) : n5 ([] : List α) a b c d e = 0 := rfl

theorem n5_cons (x : α) (t : List α) (a b c d e : α) :
    n5 (x :: t) a b c d e = (if x = a then n4 t b c d e else 0) + n5 t a b c d e := rfl

theorem n5_append (x y : List α) (a b c d e : α) :
    n5 (x ++ y) a b c d e =
      n5 x a b c d e + n4 x a b c d * y.count e + n3 x a b c * n2 y d e
        + n2 x a b * n3 y c d e + x.count a * n4 y b c d e + n5 y a b c d e := by
  induction x with
  | nil => simp [n2]
  | cons p x ih =>
    simp only [List.cons_append, n5, ih, n4_append, n4, n3, n2, List.count_cons]
    by_cases h : p = a
    · subst h; simp only [ite_true, beq_self_eq_true]; ring
    · have h' : (p == a) = false := by simpa using h
      simp [h, h']

/-- Four-binomial equivalence extends the accepted degree-four interface. -/
def Equiv4 (x y : List α) : Prop := Equiv3 x y ∧ ∀ a b c d, n4 x a b c d = n4 y a b c d

theorem Equiv4.append {x x' y y' : List α} (hx : Equiv4 x x') (hy : Equiv4 y y') :
    Equiv4 (x ++ y) (x' ++ y') := by
  refine ⟨hx.1.append hy.1, fun a b c d => ?_⟩
  rw [n4_append, n4_append, hx.2, hx.1.2, hy.1.1.1, hx.1.1.2, hy.1.1.2,
    hx.1.1.1, hy.1.2, hy.2]

theorem equiv4_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv4 T.1 T.2) :
    Equiv4 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => exact ⟨Equiv3.refl [], fun _ _ _ _ => rfl⟩
  | cons T bs ih =>
    exact (h T (by simp)).append (ih (fun U hU => h U (by simp [hU])))

def K5 (u v : List α) (a b c d e : α) : ℤ := (n5 u a b c d e : ℤ) - n5 v a b c d e

theorem k5_swap (u v : List α) (a b c d e : α) :
    K5 v u a b c d e = - K5 u v a b c d e := by
  unfold K5
  ring

theorem k5_additive {x x' y y' : List α} (hx : Equiv4 x x') (hy : Equiv4 y y')
    (a b c d e : α) :
    K5 (x ++ y) (x' ++ y') a b c d e = K5 x x' a b c d e + K5 y y' a b c d e := by
  unfold K5
  rw [n5_append, n5_append, hx.2 a b c d, hy.1.1.1 e, hx.1.2 a b c, hy.1.1.2 d e,
    hx.1.1.2 a b, hy.1.2 c d e, hx.1.1.1 a, hy.2 b c d e]
  push_cast
  ring

/-- Block additivity of `K₅` over a list of 4-binomially equivalent blocks. -/
theorem k5_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv4 T.1 T.2)
    (a b c d e : α) :
    K5 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten a b c d e =
      (bs.map fun T => K5 T.1 T.2 a b c d e).sum := by
  induction bs with
  | nil => simp [K5]
  | cons T bs ih =>
    have hbs : ∀ T' ∈ bs, Equiv4 T'.1 T'.2 := fun T' hT' => h T' (by simp [hT'])
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [k5_additive (h T (by simp)) (equiv4_join bs hbs), ih hbs]

/-- **Block additivity of `K₅` over the children of a state** (raw ordered
children, as `Psc.Intertwiner3.k3_children`): if every child of `T ∈ C` is
4-binomially equivalent, then `K₅(σ T.1, σ T.2) = Σ_{U ∈ children T} K₅(U)`. -/
theorem k5_children (S : ChildSystem α) {T : List α × List α} (hT : T ∈ S.C)
    (hch : ∀ U ∈ S.children T, Equiv4 U.1 U.2) (a b c d e : α) :
    K5 (subst S.s T.1) (subst S.s T.2) a b c d e =
      ((S.children T).map fun U => K5 U.1 U.2 a b c d e).sum := by
  rw [← S.top T hT, ← S.bot T hT]
  exact k5_join _ hch a b c d e

/-- The 1+4 shuffle product including overlapping positions. -/
theorem count_mul_n4 (w : List α) (a b c d e : α) :
    w.count a * n4 w b c d e =
      n5 w a b c d e
      + n5 w b a c d e
      + n5 w b c a d e
      + n5 w b c d a e
      + n5 w b c d e a
      + (if a = e then n4 w b c d a else 0)
      + (if a = d then n4 w b c a e else 0)
      + (if a = c then n4 w b a d e else 0)
      + (if a = b then n4 w a c d e else 0) := by
  induction w with
  | nil => simp [n2]
  | cons z t ih =>
    have key := count_mul_n3 t a c d e
    simp only [n5_cons, n4_cons, List.count_cons, beq_iff_eq]
    split_ifs at * <;> subst_vars <;>
      first | contradiction | linear_combination ih | linear_combination ih + key

theorem k5_shuffle_left {u v : List α} (h : Equiv4 u v) (a b c d e : α) :
    K5 u v a b c d e
      + K5 u v b a c d e
      + K5 u v b c a d e
      + K5 u v b c d a e
      + K5 u v b c d e a = 0 := by
  have hu := count_mul_n4 u a b c d e
  simp only [show ∀ x, u.count x = v.count x from h.1.1.1, h.2] at hu
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hu.symm.trans (count_mul_n4 v a b c d e))
  push_cast at hcast
  unfold K5
  linear_combination hcast

set_option maxHeartbeats 4000000 in
/-- The 2+3 shuffle product including overlapping positions. -/
theorem n2_mul_n3 (w : List α) (a b c d e : α) :
    n2 w a b * n3 w c d e =
      n5 w a b c d e
      + n5 w a c b d e
      + n5 w a c d b e
      + n5 w a c d e b
      + n5 w c a b d e
      + n5 w c a d b e
      + n5 w c a d e b
      + n5 w c d a b e
      + n5 w c d a e b
      + n5 w c d e a b
      + (if b = e then n4 w a c d b else 0)
      + (if b = d then n4 w a c b e else 0)
      + (if b = c then n4 w a b d e else 0)
      + (if b = e then n4 w c a d b else 0)
      + (if b = d then n4 w c a b e else 0)
      + (if b = e then n4 w c d a b else 0)
      + (if a = e then n4 w c d a b else 0)
      + (if a = d then n4 w c a b e else 0)
      + (if a = d then n4 w c a e b else 0)
      + (if a = d then (if b = e then n3 w c a b else 0) else 0)
      + (if a = c then n4 w a b d e else 0)
      + (if a = c then n4 w a d b e else 0)
      + (if a = c then n4 w a d e b else 0)
      + (if a = c then (if b = e then n3 w a d b else 0) else 0)
      + (if a = c then (if b = d then n3 w a b e else 0) else 0) := by
  induction w with
  | nil => simp [n2]
  | cons z t ih =>
    have k1 := Psc.Lie3.count_mul_n2 t b d e
    have k2 := count_mul_n3 t b c d e
    have k3 := n2_mul_n2 t a b d e
    simp only [n5_cons, n4_cons, n3_cons, n2, List.count_cons, beq_iff_eq]
    split_ifs at * <;> subst_vars <;>
      first | contradiction | linear_combination ih | linear_combination ih + k2 | linear_combination ih + k3 | linear_combination ih + k1 + k2 + k3

theorem k5_shuffle_two {u v : List α} (h : Equiv4 u v) (a b c d e : α) :
    K5 u v a b c d e
      + K5 u v a c b d e
      + K5 u v a c d b e
      + K5 u v a c d e b
      + K5 u v c a b d e
      + K5 u v c a d b e
      + K5 u v c a d e b
      + K5 u v c d a b e
      + K5 u v c d a e b
      + K5 u v c d e a b = 0 := by
  have hu := n2_mul_n3 u a b c d e
  simp only [h.1.1.2, h.1.2, h.2] at hu
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hu.symm.trans (n2_mul_n3 v a b c d e))
  push_cast at hcast
  unfold K5
  linear_combination hcast

variable [Fintype α]

set_option maxHeartbeats 1000000 in
/-- Substitution expansion by the 16 compositions of five. -/
theorem n5_subst (s : α → List α) (w : List α) (a b c d e : α) :
    n5 (subst s w) a b c d e =
      (∑ x, ∑ y, ∑ z, ∑ r, ∑ t, inc s a x * inc s b y * inc s c z * inc s d r * inc s e t * n5 w x y z r t)
      + (∑ x, ∑ y, ∑ z, ∑ r, inc s a x * inc s b y * inc s c z * n2 (s r) d e * n4 w x y z r)
      + (∑ x, ∑ y, ∑ z, ∑ r, inc s a x * inc s b y * n2 (s z) c d * inc s e r * n4 w x y z r)
      + (∑ x, ∑ y, ∑ z, ∑ r, inc s a x * n2 (s y) b c * inc s d z * inc s e r * n4 w x y z r)
      + (∑ x, ∑ y, ∑ z, ∑ r, n2 (s x) a b * inc s c y * inc s d z * inc s e r * n4 w x y z r)
      + (∑ x, ∑ y, ∑ z, inc s a x * inc s b y * n3 (s z) c d e * n3 w x y z)
      + (∑ x, ∑ y, ∑ z, inc s a x * n2 (s y) b c * n2 (s z) d e * n3 w x y z)
      + (∑ x, ∑ y, ∑ z, inc s a x * n3 (s y) b c d * inc s e z * n3 w x y z)
      + (∑ x, ∑ y, ∑ z, n2 (s x) a b * inc s c y * n2 (s z) d e * n3 w x y z)
      + (∑ x, ∑ y, ∑ z, n2 (s x) a b * n2 (s y) c d * inc s e z * n3 w x y z)
      + (∑ x, ∑ y, ∑ z, n3 (s x) a b c * inc s d y * inc s e z * n3 w x y z)
      + (∑ x, ∑ y, inc s a x * n4 (s y) b c d e * n2 w x y)
      + (∑ x, ∑ y, n2 (s x) a b * n3 (s y) c d e * n2 w x y)
      + (∑ x, ∑ y, n3 (s x) a b c * n2 (s y) d e * n2 w x y)
      + (∑ x, ∑ y, n4 (s x) a b c d * inc s e y * n2 w x y)
      + (∑ x, n5 (s x) a b c d e * w.count x) := by
  induction w with
  | nil => simp [subst, n2]
  | cons p w ih =>
    rw [subst_cons, n5_append, ih, n4_subst, n3_subst, n2_subst, count_subst]
    simp only [n5, n4, n3, n2, List.count_cons, mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_zero, beq_iff_eq,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, inc_apply]
    simp only [mul_comm, mul_assoc, mul_left_comm]
    ring

theorem equiv4_subst (s : α → List α) {u v : List α} (h : Equiv4 u v) :
    Equiv4 (subst s u) (subst s v) := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨equiv3_subst s ⟨⟨h1, h2⟩, h3⟩, fun a b c d => ?_⟩
  rw [n4_subst, n4_subst]
  simp only [show ∀ x, u.count x = v.count x from h1, h2, h3, h4]

/-- Word-level degree-five intertwining, with the incidence matrix acting on
columns in all five slots. -/
theorem k5_subst (s : α → List α) {u v : List α} (h : Equiv4 u v) (a b c d e : α) :
    K5 (subst s u) (subst s v) a b c d e =
      ∑ x, ∑ y, ∑ z, ∑ r, ∑ t,
        (inc s a x : ℤ) * inc s b y * inc s c z * inc s d r * inc s e t * K5 u v x y z r t := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold K5
  rw [n5_subst, n5_subst]
  simp only [show ∀ x, u.count x = v.count x from h1, h2, h3, h4]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end General

section Signed

variable {α : Type*} [Fintype α] [DecidableEq α] {S : ChildSystem α}
  (P : Normalisation S)

theorem k5_image_children (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) {T : List α × List α}
    (hT : T ∈ S.C) (a b c d e : α) :
    ∑ x, ∑ y, ∑ z, ∑ r, ∑ t, (inc S.s a x : ℤ) * inc S.s b y * inc S.s c z *
      inc S.s d r * inc S.s e t * K5 T.1 T.2 x y z r t =
        ((S.children T).map fun U => K5 U.1 U.2 a b c d e).sum := by
  rw [← k5_subst S.s (hbal T hT)]
  exact k5_children S hT (fun U hU => hbal U (S.closed T hT U hU)) a b c d e

/-- Signed column identity on the same normalisation used in degree four. -/
theorem k5_rep (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) (j : P.Rep) (a b c d e : α) :
    ∑ x, ∑ y, ∑ z, ∑ r, ∑ t, (inc S.s a x : ℤ) * inc S.s b y * inc S.s c z *
      inc S.s d r * inc S.s e t * K5 j.1.1 j.1.2 x y z r t =
        ∑ i : P.Rep, P.Ssign i j * K5 i.1.1 i.1.2 a b c d e := by
  rw [k5_image_children hbal (P.sub j.2)]
  exact sum_children_signed P (fun U => K5 U.1 U.2 a b c d e) (fun i => k5_swap _ _ a b c d e) j

/-- The inherited degree-four column identity retains its original hypotheses. -/
theorem k4_rep_of_equiv4 (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) (j : P.Rep) (a b c d : α) :
    ∑ x, ∑ y, ∑ z, ∑ t, (inc S.s a x : ℤ) * inc S.s b y * inc S.s c z *
      inc S.s d t * K4 j.1.1 j.1.2 x y z t =
        ∑ i : P.Rep, P.Ssign i j * K4 i.1.1 i.1.2 a b c d :=
  k4_rep P (fun T hT => (hbal T hT).1) j a b c d


open scoped Kronecker

/-- Degree-five word-coordinate columns on normalised representatives. -/
def Q5 : Matrix (α × α × α × α × α) P.Rep ℤ :=
  Matrix.of fun ⟨a,b,c,d,e⟩ j => K5 j.1.1 j.1.2 a b c d e

open Matrix in
theorem q5_mul_ssign (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) :
    let M := (inc S.s).map (Nat.cast : ℕ → ℤ)
    Q5 P * P.Ssign = (M ⊗ₖ (M ⊗ₖ (M ⊗ₖ (M ⊗ₖ M)))) * Q5 P := by
  dsimp only
  ext ⟨a,b,c,d,e⟩ j
  simp only [mul_apply, Q5, of_apply, kroneckerMap_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans ?_
  rw [← k5_rep P hbal j a b c d e]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun t _ => ?_
  ring

end Signed

end Psc.Defect5
