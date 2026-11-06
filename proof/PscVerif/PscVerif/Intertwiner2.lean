/-
# The degree-two defect intertwiner `K₂(σT) = Λ²M · K₂(T)`

`docs/c4-concentration-attack-2026-11-06.md` §3;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `lem:conc-subst` (degree
two), `prop:midarea` (iii), `thm:defect-intertwiner` (degree two).

Scope.  This file formalizes the *`K`-push-forward* clause
(`K₂(σu, σv) = Λ²M · K₂(u, v)`) and the *block-additivity* clause
(`K₂` of a concatenation of balanced blocks is the sum of the blocks' `K₂`) of
`prop:midarea` (iii) / `lem:conc-subst` at degree two, stated over the *raw
ordered (unsigned) children* of a `Psc.Binomial.ChildSystem` state.  The signed
form `Q_r S = Φ_r Q_r` over normalised representatives with cocycle signs, and
the area / `H` identity of `prop:midarea`, are **not** formalized here.

Words are lists over a finite alphabet `α` with decidable equality; a
substitution is any map `s : α → List α` (no primitivity, unimodularity or
Pisot hypothesis is used anywhere in this file).  The incidence matrix is
`M = Psc.Incidence.inc s`, `M a c = |s c|_a`.  `n2 w a b` is the scattered count of
`a b` in `w` (`Psc.Binomial.n2`), and for a pair of words
`K2 u v a b = n2 u a b - n2 v a b` in `ℤ`.  A pair is *balanced* when
`Psc.Binomial.Equiv1 u v` (equal letter counts).

## What is proved, in full

* (`Psc.Incidence.count_subst`, `Psc.Incidence.n2_subst`: the Parikh identity
  and `lem:conc-subst` at degree two, used here.)
* `n2_add_n2_swap`: for `a ≠ b`, `n2 w a b + n2 w b a = |w|_a · |w|_b`;
  `n2_self`: `n2 w a a = (|w|_a).choose 2`.
* `k2_swap`: `K2 v u a b = - K2 u v a b` (for any two words).
* `k2_subst`: for balanced `u, v`,
  `K2 (σ u) (σ v) a b = Σ_c Σ_d M a c · M b d · K2 u v c d`
  (the local correction term cancels).
* `k2_antisymm`, `k2_self`: for balanced `u, v`, `K2 u v a b = - K2 u v b a`
  and `K2 u v a a = 0`.
* `k2_join`: for a list of balanced pairs, `K2` of the concatenations is the sum
  of the blocks' `K2` (block additivity; the cross terms cancel).
* Over `α = Fin 3`, with the integer incidence matrix
  `(inc s).map (Nat.cast : ℕ → ℤ)` and the wedge coordinates
  `kw u v I = K2 u v (pairFst I) (pairSnd I)` in the basis
  `(e₀∧e₁, e₀∧e₂, e₁∧e₂)` of `Psc.Cyclicity`:
  - `kw_swap`: `kw v u = - kw u v`;
  - `kw_subst`: for balanced `u, v`,
    `kw (σ u) (σ v) = Psc.Cyclicity.wedge2 M *ᵥ kw u v`
    (the `K`-push-forward of `prop:midarea` (iii), `K₂(σT) = Λ²M K₂(T)`, in
    exactly the coordinates of `Psc.Cyclicity.wedge2`);
  - `kw_children`: for a child system `S`, a state `T ∈ S.C` whose children are
    all balanced, `kw (σ T.1) (σ T.2) = Σ_{U ∈ children T} kw U.1 U.2`;
  - `wedge2_mulVec_kw_eq_sum_children`: if moreover `T` is balanced,
    `Λ²M · kw T = Σ_{U ∈ children T} kw U` (the two combined).

## What is not proved here

* The signed form `Q_r S = Φ_r Q_r` (normalised representatives, cocycle signs)
  and the area / `H` identity of `prop:midarea`.
* Nothing about higher degrees (`K₃`, `N₃`, `thm:defect-intertwiner` beyond
  degree two) or about the linear-algebraic consequences (eigenrow arguments,
  `prop:cocycle`, Concentration itself); this file is the exact word-level
  identity only.
* No statement about infinite words, fixed points or the balanced-pair algorithm;
  `kw_children` is about a single finite `ChildSystem` state.
-/
import PscVerif.Incidence
import PscVerif.Cyclicity

namespace Psc.Intertwiner2

open Psc.Binomial Psc.Incidence

section General

variable {α : Type*} [DecidableEq α]

/-- For distinct letters, `n2 w a b + n2 w b a = |w|_a · |w|_b`. -/
theorem n2_add_n2_swap (w : List α) {a b : α} (hab : a ≠ b) :
    n2 w a b + n2 w b a = w.count a * w.count b := by
  induction w with
  | nil => simp [n2]
  | cons c w ih =>
    simp only [n2, List.count_cons]
    by_cases hca : c = a
    · subst hca
      have : (c == b) = false := by simpa using hab
      simp [this, hab]
      nlinarith [ih]
    · by_cases hcb : c = b
      · subst hcb
        have : (c == a) = false := by simpa using hca
        simp [this, hca]
        nlinarith [ih]
      · have h1 : (c == a) = false := by simpa using hca
        have h2 : (c == b) = false := by simpa using hcb
        simp [h1, h2, hca, hcb]
        omega

/-- `n2 w a a = C(|w|_a, 2)`. -/
theorem n2_self (w : List α) (a : α) : n2 w a a = (w.count a).choose 2 := by
  induction w with
  | nil => simp [n2]
  | cons c w ih =>
    simp only [n2, List.count_cons, ih]
    by_cases hca : c = a
    · subst hca
      simp [Nat.choose_succ_succ']
    · have : (c == a) = false := by simpa using hca
      simp [this, hca]

/-- The degree-two defect of a pair of words, in `ℤ`. -/
def K2 (u v : List α) (a b : α) : ℤ := (n2 u a b : ℤ) - n2 v a b

/-- `K2` is antisymmetric in the two words. -/
theorem k2_swap (u v : List α) (a b : α) : K2 v u a b = - K2 u v a b := by
  unfold K2; ring

/-- `K2` is antisymmetric on a balanced pair. -/
theorem k2_antisymm {u v : List α} (h : Equiv1 u v) {a b : α} (hab : a ≠ b) :
    K2 u v a b = - K2 u v b a := by
  unfold K2
  have hu := n2_add_n2_swap u hab
  have hv := n2_add_n2_swap v hab
  rw [h a, h b] at hu
  have : ((n2 u a b : ℕ) : ℤ) + n2 u b a = n2 v a b + n2 v b a := by
    exact_mod_cast hu.trans hv.symm
  linarith

/-- `K2` vanishes on the diagonal for a balanced pair. -/
theorem k2_self {u v : List α} (h : Equiv1 u v) (a : α) : K2 u v a a = 0 := by
  unfold K2
  rw [n2_self, n2_self, h a, sub_self]

theorem equiv1_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv1 T.1 T.2) :
    Equiv1 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => intro a; rfl
  | cons T bs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (h T (by simp)).append (ih fun T' hT' => h T' (by simp [hT']))

/-- Block additivity of `K2` over balanced blocks. -/
theorem k2_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv1 T.1 T.2) (a b : α) :
    K2 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten a b =
      (bs.map fun T => K2 T.1 T.2 a b).sum := by
  induction bs with
  | nil => simp [K2, n2]
  | cons T bs ih =>
    have hT := h T (by simp)
    have hbs : ∀ T' ∈ bs, Equiv1 T'.1 T'.2 := fun T' hT' => h T' (by simp [hT'])
    have hj := equiv1_join bs hbs
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [← ih hbs]
    unfold K2
    rw [n2_append, n2_append, hT a, hj b]
    push_cast
    ring

variable [Fintype α]

/-- **Degree-two intertwiner**: for a balanced pair,
`K2 (σ u) (σ v) a b = Σ_c Σ_d M a c · M b d · K2 u v c d`. -/
theorem k2_subst (s : α → List α) {u v : List α} (h : Equiv1 u v) (a b : α) :
    K2 (subst s u) (subst s v) a b =
      ∑ c, ∑ d, (inc s a c : ℤ) * inc s b d * K2 u v c d := by
  unfold K2
  rw [n2_subst, n2_subst]
  have hc : (∑ c, u.count c * n2 (s c) a b) = ∑ c, v.count c * n2 (s c) a b :=
    Finset.sum_congr rfl fun c _ => by rw [h c]
  rw [hc]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end General

/-! ### The wedge coordinates over `Fin 3` -/

section Fin3

open Psc.Cyclicity Matrix

/-- The wedge coordinates of `K2` in the basis `(e₀∧e₁, e₀∧e₂, e₁∧e₂)`. -/
def kw (u v : List (Fin 3)) : Fin 3 → ℤ :=
  fun I => K2 u v (pairFst I) (pairSnd I)

/-- The wedge coordinates are antisymmetric in the two words. -/
theorem kw_swap (u v : List (Fin 3)) : kw v u = - kw u v := by
  funext I; exact k2_swap u v _ _

/-- **`prop:midarea` (iii), `K`-push-forward**: `K₂(σT) = Λ²M · K₂(T)` for a
balanced pair, in the coordinates of `Psc.Cyclicity.wedge2`, with
`M = (inc s).map (Nat.cast : ℕ → ℤ)`. -/
theorem kw_subst (s : Fin 3 → List (Fin 3)) {u v : List (Fin 3)} (h : Equiv1 u v) :
    kw (subst s u) (subst s v) = wedge2 ((inc s).map (Nat.cast : ℕ → ℤ)) *ᵥ kw u v := by
  have h00 := k2_self h 0
  have h11 := k2_self h 1
  have h22 := k2_self h 2
  have h10 := k2_antisymm h (a := 1) (b := 0) (by decide)
  have h20 := k2_antisymm h (a := 2) (b := 0) (by decide)
  have h21 := k2_antisymm h (a := 2) (b := 1) (by decide)
  funext I
  simp only [kw]
  rw [k2_subst s h]
  fin_cases I <;>
    simp [kw, wedge2, Matrix.map_apply, pairFst, pairSnd, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      h00, h11, h22, h10, h20, h21] <;> ring

/-- **`prop:midarea` (iii), block additivity**, over the raw ordered
(unsigned) children of a child-system state: the wedge coordinates of the image
pair are the sum of those of the children. -/
theorem kw_children (S : ChildSystem (Fin 3)) {T : List (Fin 3) × List (Fin 3)}
    (hT : T ∈ S.C) (hch : ∀ U ∈ S.children T, Equiv1 U.1 U.2) :
    kw (subst S.s T.1) (subst S.s T.2) = ((S.children T).map fun U => kw U.1 U.2).sum := by
  funext I
  rw [← S.top T hT, ← S.bot T hT]
  simp only [kw]
  rw [k2_join _ hch]
  clear hch hT
  induction S.children T with
  | nil => simp
  | cons U us ih => simp [ih, kw]

/-- Combining the two: for a balanced state with balanced children,
`Λ²M · kw T = Σ_{U ∈ children T} kw U`. -/
theorem wedge2_mulVec_kw_eq_sum_children (S : ChildSystem (Fin 3))
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ S.C) (hbal : Equiv1 T.1 T.2)
    (hch : ∀ U ∈ S.children T, Equiv1 U.1 U.2) :
    wedge2 ((inc S.s).map (Nat.cast : ℕ → ℤ)) *ᵥ kw T.1 T.2 = ((S.children T).map fun U => kw U.1 U.2).sum := by
  rw [← kw_subst S.s hbal, kw_children S hT hch]

end Fin3

end Psc.Intertwiner2
