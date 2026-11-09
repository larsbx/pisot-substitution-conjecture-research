/-
# The degree-three defect intertwiner `K₃(σT) = M^{⊗3} K₃(T)` on words

`docs/c4-concentration-attack-2026-11-06.md`;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`: the proof of
`thm:defect-intertwiner` at `r = 3` from `lem:conc-subst` (i), (ii) (the
word-level identity only).

Scope.  This file formalizes the two word-level steps of the proof of
`thm:defect-intertwiner` at `r = 3`: the *`K`-push-forward* step
(`K₃(σu, σv) = M^{⊗3} K₃(u, v)` when `K₁ = K₂ = 0`, from `lem:conc-subst` (ii))
and the *block-additivity* step (`K₃` of a concatenation of 2-binomially
equivalent blocks is the sum of the blocks' `K₃`, from `lem:conc-subst` (i)),
stated over raw ordered (unsigned) pairs and blocks.  The signed form
`Q_r S = Φ_r Q_r` over normalised representatives with cocycle signs is **not**
formalized here.  (`prop:midarea` is a degree-two statement; its word-level
part is `PscVerif.Intertwiner2`.)

Words are lists over a finite alphabet `α` with decidable equality; a
substitution is any map `s : α → List α` (no primitivity, unimodularity, Pisot
or irreducibility hypothesis is used anywhere in this file).  The incidence
matrix is `M = Psc.Incidence.inc s`, `M a c = |s c|_a`.  `n2 w a b` is the scattered
count of `a b` (`Psc.Binomial.n2`), and `Psc.Incidence.n3 w a b c` is the
scattered count of `a b c`, defined by `n3 [] = 0`,
`n3 (x :: t) a b c = (if x = a then n2 t b c else 0) + n3 t a b c`.
For two words, `K3 u v a b c = n3 u a b c - n3 v a b c` in `ℤ`.
`Psc.Binomial.Equiv2 u v` means `K₁(u,v) = 0` and `K₂(u,v) = 0`.

## What is proved, in full

* (Used from `PscVerif.Incidence`: `Psc.Incidence.n3_append`,
  `lem:conc-subst` (i) at `r = 3`; `Psc.Incidence.n3_subst`, `lem:conc-subst`
  (ii) at `r = 3` with the correction `Λ₃` explicit; `Psc.Incidence.count_subst`,
  `Psc.Incidence.n2_subst`, `Psc.Incidence.equiv2_subst`.)
* `k3_swap`: `K3 v u = - K3 u v` (for any two words).
* `k3_additive`: if `Equiv2 x x'` and `Equiv2 y y'` then
  `K3 (x ++ y) (x' ++ y') = K3 x x' + K3 y y'`; and `k3_join`, its iterate over a
  list of `Equiv2` blocks; `k3_children`, its `ChildSystem` form: for a state
  `T ∈ C` whose children are all `Equiv2`,
  `K3 (σ T.1) (σ T.2) = Σ_{U ∈ children T} K3 U.1 U.2` (raw ordered children,
  as `Psc.Intertwiner2.kw_children` at degree two).
* `k3_subst` (`lem:conc-subst` (ii) on a pair, `thm:defect-intertwiner` at
  `r = 3` on words): if `Equiv2 u v` then
  `K3 (σ u) (σ v) a b e = Σ_{x,y,z} M a x · M b y · M e z · K3 u v x y z`.
* `equiv2_iterate_subst`: `Equiv2` is preserved by every `σⁿ` (iterating
  `Psc.Incidence.equiv2_subst`), so `k3_subst` applies at every level of the
  iteration.

* `equiv2_example`, `k3_example`: non-vacuity — over `Fin 2`, the words `0110`
  and `1001` satisfy `Equiv2` while `K3 … 0 1 0 = 2`.

## What is not proved here

* The signed form `Q_r S = Φ_r Q_r` (normalised representatives, cocycle signs).
* Nothing about `Lie₃`, the shuffle annihilator (`lem:conc-subst` (iii)), the
  restriction of `M^{⊗3}` to `Lie₃`, the cocycle `S`, the operator `Q₃`, or any
  spectral consequence (`thm:deg23`, `prop:cocycle`); this file is the exact
  word-level identity only.
* Nothing about general degree `r`; only `r = 3`.
* No statement about infinite words, fixed points or the balanced-pair
  algorithm; `k3_children` is about a single finite `ChildSystem` state.
-/
import PscVerif.Incidence

namespace Psc.Intertwiner3

open Psc.Binomial Psc.Incidence

section General

variable {α : Type*} [DecidableEq α]

/-- The degree-three defect of a pair of words, in `ℤ`. -/
def K3 (u v : List α) (a b c : α) : ℤ := (n3 u a b c : ℤ) - n3 v a b c

/-- `K3` is antisymmetric in the two words. -/
theorem k3_swap (u v : List α) (a b c : α) : K3 v u a b c = - K3 u v a b c := by
  unfold K3; ring

/-- **Block additivity of `K₃`** (`lem:conc-subst` (i) on a pair with
`K₁ = K₂ = 0` on both blocks). -/
theorem k3_additive {x x' y y' : List α} (hx : Equiv2 x x') (hy : Equiv2 y y')
    (a b c : α) :
    K3 (x ++ y) (x' ++ y') a b c = K3 x x' a b c + K3 y y' a b c := by
  unfold K3
  rw [n3_append, n3_append, hx.1 a, hy.2 b c, hx.2 a b, hy.1 c]
  push_cast
  ring

/-- Block additivity of `K₃` over a list of 2-binomially equivalent blocks. -/
theorem k3_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv2 T.1 T.2)
    (a b c : α) :
    K3 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten a b c =
      (bs.map fun T => K3 T.1 T.2 a b c).sum := by
  induction bs with
  | nil => simp [K3]
  | cons T bs ih =>
    have hbs : ∀ T' ∈ bs, Equiv2 T'.1 T'.2 := fun T' hT' => h T' (by simp [hT'])
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [k3_additive (h T (by simp)) (equiv2_join bs hbs), ih hbs]

/-- **Block additivity of `K₃` over the children of a state** (the `ChildSystem`
form, as `Psc.Intertwiner2.kw_children` at degree two), over the raw ordered
(unsigned) children: if every child of `T ∈ C` is 2-binomially equivalent, then
`K₃(σ T.1, σ T.2) = Σ_{U ∈ children T} K₃(U)`. -/
theorem k3_children (S : ChildSystem α) {T : List α × List α} (hT : T ∈ S.C)
    (hch : ∀ U ∈ S.children T, Equiv2 U.1 U.2) (a b c : α) :
    K3 (subst S.s T.1) (subst S.s T.2) a b c =
      ((S.children T).map fun U => K3 U.1 U.2 a b c).sum := by
  rw [← S.top T hT, ← S.bot T hT]
  exact k3_join _ hch a b c

variable [Fintype α]

/-- **Degree-three defect intertwiner on words** (`lem:conc-subst` (ii) on a
pair; `thm:defect-intertwiner` at `r = 3`): if `K₁(u,v) = K₂(u,v) = 0` then
`K₃(σu, σv) = M^{⊗3} K₃(u,v)`. -/
theorem k3_subst (s : α → List α) {u v : List α} (h : Equiv2 u v) (a b e : α) :
    K3 (subst s u) (subst s v) a b e =
      ∑ x, ∑ y, ∑ z, (inc s a x : ℤ) * inc s b y * inc s e z * K3 u v x y z := by
  unfold K3
  rw [n3_subst, n3_subst]
  have h1 : (∑ x, ∑ z, inc s a x * n2 (s z) b e * n2 u x z) =
      ∑ x, ∑ z, inc s a x * n2 (s z) b e * n2 v x z :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by rw [h.2 x z]
  have h2 : (∑ x, ∑ z, n2 (s x) a b * inc s e z * n2 u x z) =
      ∑ x, ∑ z, n2 (s x) a b * inc s e z * n2 v x z :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by rw [h.2 x z]
  have h3 : (∑ x, u.count x * n3 (s x) a b e) = ∑ x, v.count x * n3 (s x) a b e :=
    Finset.sum_congr rfl fun x _ => by rw [h.1 x]
  rw [h1, h2, h3]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- `Equiv2` is preserved by every iterate of a substitution, so `k3_subst`
applies at every level of `σⁿ`. -/
theorem equiv2_iterate_subst (s : α → List α) {u v : List α} (h : Equiv2 u v) (n : ℕ) :
    Equiv2 ((subst s)^[n] u) ((subst s)^[n] v) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact equiv2_subst s ih

end General

/-! ### Non-vacuity: a 2-binomially equivalent pair with `K₃ ≠ 0` -/

/-- `0110` and `1001` are 2-binomially equivalent. -/
theorem equiv2_example : Equiv2 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] := by
  unfold Equiv2 Equiv1; decide

/-- ... but their degree-three defect at `0 1 0` is `2`, so the hypothesis of
`k3_subst` / `k3_additive` does not force `K₃ = 0`. -/
theorem k3_example : K3 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] 0 1 0 = 2 := by
  decide

end Psc.Intertwiner3
