/- The graded step and the finite word separation of the nonunit stack argument. -/
import PscVerif.PeriodicPartnerStackWordRigidity
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Sublists
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.NoncommRing

namespace Psc.PeriodicPartnerGradedLift

open Psc.PeriodicPartnerStackWordRigidity

section Step

variable {K E W R : Type*} [Field K] [Fintype E] [DecidableEq E]
  [AddCommGroup W] [Module K W] [Ring R]

/-- The inflation operator on rational edge chains: a basis edge goes to the
sum of the edges of its image path. -/
noncomputable def edgeOp (K : Type*) [Field K] {E : Type*} [Fintype E] [DecidableEq E]
    (f : E → List E) : Module.End K (E → K) :=
  (Pi.basisFun K E).constr K fun e => ((f e).map fun e' => Pi.basisFun K E e').sum

omit [Fintype E] [DecidableEq E] in
/-- With the lower labels fixed, the inflation equation in the top layer is
the homogeneous Sylvester equation on each edge. -/
theorem step_iff (f : E → List E) (base : E → R) (F : R →+* R) (j : W →+ R)
    (D : Module.End K W) (hj : Function.Injective j)
    (hleft : ∀ a t, base a * j t = j t) (hright : ∀ a t, j t * base a = j t)
    (hzero : ∀ s t, j s * j t = 0) (hF : ∀ t, F (j t) = j (D t))
    (res : E → W) (hres : ∀ e, pathProduct base (f e) + j (res e) = F (base e))
    (d : E → W) :
    (∀ e, pathProduct (fun a => base a + j (d a)) (f e) = F (base e + j (d e))) ↔
      ∀ e, D (d e) - ((f e).map d).sum = -res e := by
  refine forall_congr' fun e => ?_
  rw [pathProduct_add_correction base d j hleft hright hzero, map_add, hF, ← hres e,
    add_assoc, add_right_inj, ← map_add, hj.eq_iff]
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    abel

/-- The Sylvester operator applied to the linear extension of a correction. -/
theorem constr_sylvester (f : E → List E) (D : Module.End K W) (d : E → W) :
    D.comp ((Pi.basisFun K E).constr K d) - ((Pi.basisFun K E).constr K d).comp (edgeOp K f) =
      (Pi.basisFun K E).constr K fun e => D (d e) - ((f e).map d).sum := by
  refine (Pi.basisFun K E).ext fun e => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, edgeOp, Module.Basis.constr_basis,
    map_list_sum, List.map_map]
  congr 2
  refine List.map_congr_left fun e' _ => ?_
  simp only [Function.comp_apply, Module.Basis.constr_basis]

/-- **The graded step.** If the labels satisfy the inflation equation up to a
defect in the top layer, and an annihilator of the edge operator acts
injectively on that layer, then exactly one top-layer correction satisfies
the inflation equation. -/
theorem graded_step_exists_unique [FiniteDimensional K W]
    (f : E → List E) (base : E → R) (F : R →+* R) (j : W →+ R)
    (D : Module.End K W) (hj : Function.Injective j)
    (hleft : ∀ a t, base a * j t = j t) (hright : ∀ a t, j t * base a = j t)
    (hzero : ∀ s t, j s * j t = 0) (hF : ∀ t, F (j t) = j (D t))
    (res : E → W) (hres : ∀ e, pathProduct base (f e) + j (res e) = F (base e))
    (p : Polynomial K) (hB : Polynomial.aeval (edgeOp K f) p = 0)
    (hD : Function.Injective (Polynomial.aeval D p)) :
    ∃! d : E → W, ∀ e,
      pathProduct (fun a => base a + j (d a)) (f e) = F (base e + j (d e)) := by
  obtain ⟨C, hC, hu⟩ := sylvester_exists_unique (edgeOp K f) D p hB hD
    ((Pi.basisFun K E).constr K fun e => -res e)
  have key (d : E → W) :
      (∀ e, pathProduct (fun a => base a + j (d a)) (f e) = F (base e + j (d e))) ↔
        (Pi.basisFun K E).constr K d = C := by
    rw [step_iff f base F j D hj hleft hright hzero hF res hres d]
    constructor
    · intro h
      apply hu
      change D.comp _ - _ = _
      rw [constr_sylvester, funext h]
    · intro h e
      have hC' := hC
      change D.comp C - C.comp (edgeOp K f) = _ at hC'
      rw [← h, constr_sylvester] at hC'
      exact congrFun (((Pi.basisFun K E).constr K).injective hC') e
  refine ⟨fun e => C (Pi.basisFun K E e), (key _).2 (Module.Basis.constr_self _ K C), ?_⟩
  intro d hd
  funext e
  rw [← (key d).1 hd, Module.Basis.constr_basis]

end Step

/-- The corrected labels restrict to the lower labels under every ring map
which kills the top layer. No limit over truncations is taken. -/
theorem step_truncates {E W R R' : Type*} [AddCommGroup W] [Ring R] [Ring R']
    (π : R →+* R') (base : E → R) (j : W →+ R)
    (hπ : ∀ t, π (j t) = 0) (d : E → W) (path : List E) :
    π (pathProduct (fun a => base a + j (d a)) path) = π (pathProduct base path) := by
  induction path with
  | nil => rfl
  | cons a path ih =>
    simp only [pathProduct, List.map_cons, List.prod_cons, map_mul, map_add, hπ, add_zero]
      at ih ⊢
    rw [ih]

section Words

variable {α : Type*}

open MonoidAlgebra

/-- All coefficients on words shorter than `k` vanish. -/
def Above (k : ℕ) (x : MonoidAlgebra ℚ (FreeMonoid α)) : Prop :=
  ∀ m : FreeMonoid α, m.toList.length < k → x.coeff m = 0

theorem above_deg_zero (x : MonoidAlgebra ℚ (FreeMonoid α)) : Above 0 x :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

theorem above_zero (k : ℕ) : Above k (0 : MonoidAlgebra ℚ (FreeMonoid α)) := fun _ _ => rfl

theorem Above.mono {k l : ℕ} {x : MonoidAlgebra ℚ (FreeMonoid α)} (h : Above l x)
    (hkl : k ≤ l) : Above k x := fun m hm => h m (lt_of_lt_of_le hm hkl)

theorem Above.add {k : ℕ} {x y : MonoidAlgebra ℚ (FreeMonoid α)} (hx : Above k x)
    (hy : Above k y) : Above k (x + y) := fun m hm => by
  rw [coeff_add, Finsupp.add_apply, hx m hm, hy m hm, add_zero]

theorem Above.mul {k l : ℕ} {x y : MonoidAlgebra ℚ (FreeMonoid α)} (hx : Above k x)
    (hy : Above l y) : Above (k + l) (x * y) := fun m hm => by
  classical
  rw [coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun m₁ _ => ?_
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun m₂ _ => ?_
  split_ifs with h
  · subst h
    rw [FreeMonoid.toList_mul, List.length_append] at hm
    rcases Nat.lt_or_ge m₁.toList.length k with h₁ | h₁
    · rw [hx m₁ h₁, zero_mul]
    · rw [hy m₂ (by omega), mul_zero]
  · rfl

theorem above_single (m : FreeMonoid α) :
    Above m.toList.length (single m (1 : ℚ)) := fun x hx => by
  classical
  rw [coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact absurd hx (lt_irrefl _)
  · rfl

/-- Replacing labels above a degree changes a path product only above it. -/
theorem pathProduct_congr_above {N : ℕ} (g g' : α → MonoidAlgebra ℚ (FreeMonoid α))
    (h : ∀ a, Above N (g a - g' a)) (w : List α) :
    Above N (pathProduct g w - pathProduct g' w) := by
  induction w with
  | nil => simpa [pathProduct] using above_zero N
  | cons a w ih =>
    have e : pathProduct g (a :: w) - pathProduct g' (a :: w) =
        (g a - g' a) * pathProduct g w + g' a * (pathProduct g w - pathProduct g' w) := by
      simp only [pathProduct, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    exact ((h a).mul (above_deg_zero _)).add (((above_deg_zero (g' a)).mul ih).mono (by omega))

variable (k : α → MonoidAlgebra ℚ (FreeMonoid α))

/-- The product of the nonconstant parts along a word is that word plus
terms of larger degree. -/
theorem pathProduct_leading (hk : ∀ a, Above 2 (k a - single (FreeMonoid.of a) 1))
    (m : List α) :
    Above (m.length + 1) (pathProduct k m - single (FreeMonoid.ofList m) 1) := by
  induction m with
  | nil =>
    have : pathProduct k [] - single (FreeMonoid.ofList ([] : List α)) (1 : ℚ) = 0 := by
      simp only [pathProduct, List.map_nil, List.prod_nil]
      exact sub_self _
    rw [this]
    exact above_zero _
  | cons a m ih =>
    have e : pathProduct k (a :: m) - single (FreeMonoid.ofList (a :: m)) (1 : ℚ) =
        (k a - single (FreeMonoid.of a) 1) * (pathProduct k m - single (FreeMonoid.ofList m) 1)
          + single (FreeMonoid.of a) 1 * (pathProduct k m - single (FreeMonoid.ofList m) 1)
          + (k a - single (FreeMonoid.of a) 1) * single (FreeMonoid.ofList m) 1 := by
      have hs : single (FreeMonoid.ofList (a :: m)) (1 : ℚ) =
          single (FreeMonoid.of a) 1 * single (FreeMonoid.ofList m) 1 := by
        rw [single_mul_single, FreeMonoid.ofList_cons, mul_one]
      rw [hs]
      simp only [pathProduct, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    have h1 : Above 1 (single (FreeMonoid.of a) (1 : ℚ)) := above_single (FreeMonoid.of a)
    have hm : Above m.length (single (FreeMonoid.ofList m) (1 : ℚ)) :=
      above_single (FreeMonoid.ofList m)
    refine ((((hk a).mul ih).mono ?_).add ((h1.mul ih).mono ?_)).add (((hk a).mul hm).mono ?_)
    all_goals simp only [List.length_cons]; omega

/-- The ordered product of `1 + k a` is the sum over scattered subwords. -/
theorem pathProduct_one_add (w : List α) :
    pathProduct (fun a => 1 + k a) w = (w.sublists'.map (pathProduct k)).sum := by
  induction w with
  | nil => simp [pathProduct]
  | cons a w ih =>
    have hcons : (fun m => pathProduct k (a :: m)) = fun m => k a * pathProduct k m := rfl
    rw [List.sublists'_cons, List.map_append, List.sum_append, List.map_map]
    change (1 + k a) * pathProduct (fun a => 1 + k a) w = _
    rw [ih, Function.comp_def, hcons, List.sum_map_mul_left, add_mul, one_mul]

private theorem sum_map_indicator [DecidableEq α] (x : List α) (l : List (List α)) :
    (l.map fun m => if m = x then (1 : ℚ) else 0).sum = (l.count x : ℚ) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : m = x <;> simp [h, add_comm]

private theorem sum_map_filter (p : List α → Prop) [DecidablePred p] (h : List α → ℚ)
    (l : List (List α)) :
    (l.map fun m => if p m then h m else 0).sum = ((l.filter fun m => p m).map h).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases hp : p m <;> simp [hp]

/-- The coefficient of the ordered product at a word, by scattered subwords:
the count of the word itself, plus contributions of strictly shorter ones. -/
theorem coeff_pathProduct [DecidableEq α] (hk : ∀ a, Above 2 (k a - single (FreeMonoid.of a) 1))
    (w x : List α) :
    (pathProduct (fun a => 1 + k a) w).coeff (FreeMonoid.ofList x) =
      (w.sublists'.count x : ℚ) +
        ((w.sublists'.filter fun m => m.length < x.length).map fun m =>
          (pathProduct k m - single (FreeMonoid.ofList m) 1).coeff (FreeMonoid.ofList x)).sum := by
  rw [pathProduct_one_add, ← sum_map_indicator, ← sum_map_filter, ← List.sum_map_add]
  have hsum (l : List (List α)) :
      ((l.map (pathProduct k)).sum).coeff (FreeMonoid.ofList x) =
        (l.map fun m => (pathProduct k m).coeff (FreeMonoid.ofList x)).sum := by
    induction l with
    | nil => simp
    | cons m l ih => rw [List.map_cons, List.sum_cons, coeff_add, Finsupp.add_apply, ih,
        List.map_cons, List.sum_cons]
  rw [hsum]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  have hsplit : (pathProduct k m).coeff (FreeMonoid.ofList x) =
      (if m = x then (1 : ℚ) else 0) +
        (pathProduct k m - single (FreeMonoid.ofList m) 1).coeff (FreeMonoid.ofList x) := by
    classical
    rw [coeff_sub, Finsupp.sub_apply, coeff_single, Finsupp.single_apply]
    by_cases hmx : m = x
    · subst hmx
      simp
    · have h2 : FreeMonoid.ofList m ≠ FreeMonoid.ofList x :=
        fun h' => hmx (FreeMonoid.ofList.injective h')
      simp [hmx, h2]
  rw [hsplit]
  congr 1
  by_cases hlt : m.length < x.length
  · simp only [hlt, ite_true]
  · simp only [hlt, ite_false]
    exact pathProduct_leading k hk m (FreeMonoid.ofList x)
      (by rw [FreeMonoid.toList_ofList]; omega)

/-- **Word separation at one finite truncation.** Labels `1 + X_a +` terms of
degree at least two separate words: if two ordered products agree on all
coefficients of degree at most `N` and both words have length at most `N`,
the words are equal. -/
theorem word_separation [DecidableEq α] (hk : ∀ a, Above 2 (k a - single (FreeMonoid.of a) 1))
    (u v : List α) (N : ℕ) (hu : u.length ≤ N) (hv : v.length ≤ N)
    (h : ∀ x : List α, x.length ≤ N →
      (pathProduct (fun a => 1 + k a) u).coeff (FreeMonoid.ofList x) =
        (pathProduct (fun a => 1 + k a) v).coeff (FreeMonoid.ofList x)) : u = v := by
  have hcount : ∀ n, ∀ x : List α, x.length = n → x.length ≤ N →
      u.sublists'.count x = v.sublists'.count x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxN
      have hperm : (u.sublists'.filter fun m => m.length < x.length).Perm
          (v.sublists'.filter fun m => m.length < x.length) := by
        rw [List.perm_iff_count]
        intro m
        by_cases hm : m.length < x.length
        · rw [List.count_filter (by simpa using hm), List.count_filter (by simpa using hm)]
          exact ih m.length (hx ▸ hm) m rfl (by omega)
        · rw [List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem] <;>
            simp [List.mem_filter, hm]
      have hx' := h x hxN
      rw [coeff_pathProduct k hk, coeff_pathProduct k hk, (hperm.map _).sum_eq] at hx'
      exact_mod_cast add_right_cancel hx'
  have huv : List.Sublist u v := by
    rw [← List.mem_sublists', ← List.count_pos_iff, ← hcount u.length u rfl hu,
      List.count_pos_iff, List.mem_sublists']
  have hvu : List.Sublist v u := by
    rw [← List.mem_sublists', ← List.count_pos_iff, hcount v.length v rfl hv,
      List.count_pos_iff, List.mem_sublists']
  exact huv.antisymm hvu

/-- Degree two cannot separate `abba` from `baab`: all scattered subwords of
length at most two occur equally often. The truncation must reach the word. -/
theorem degree_two_control :
    ∀ x : List Bool, x.length ≤ 2 →
      [false, true, true, false].sublists'.count x =
        [true, false, false, true].sublists'.count x := by
  intro x hx
  match x, hx with
  | [], _ => decide
  | [a], _ => revert a; decide
  | [a, b], _ => revert a b; decide

end Words

end Psc.PeriodicPartnerGradedLift
