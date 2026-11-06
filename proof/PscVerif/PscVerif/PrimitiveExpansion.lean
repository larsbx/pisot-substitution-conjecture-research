/-
# Primitive substitutions have an expanding, nonerasing power

`docs/c4-concentration-attack-2026-11-06.md` §3 and §8.  This module discharges
the expansion hypothesis `hexp` (and the nonerasing hypothesis `hs`) of
`Psc.FixedPointLimit.reduction_limit` from primitivity of the incidence matrix,
after passing to a power of the substitution.

Setting: a finite alphabet `α` (`[Fintype α] [DecidableEq α]`), a substitution
`s : α → List α`, and its incidence matrix `M a c = |s c|_a` over `ℕ`
(`Psc.Incidence.inc s`).

Proved here, in full (depending only on `propext`, `Classical.choice`,
`Quot.sound`):

* (used from `PscVerif.Incidence` and `PscVerif.Binomial`:
  `Psc.Incidence.count_iterate_subst`, `|σᵏ [c]|_a = (M ^ k) a c`;
  `Psc.Binomial.power`, `Psc.Binomial.subst_power`, the `k`-th power
  substitution `s_k a = σᵏ [a]` with `subst s_k = σᵏ`, re-exported here as
  `power`, `subst_power`; `Psc.Binomial.ChildSystem.pow`, the depth-`k`
  child system of the power substitution on the same states);
* `one_le_of_pos_pow`: if `M ^ k` is entrywise positive and `|α| ≥ 2`, then
  `k ≥ 1`;
* `expanding_of_pos_pow`: if `M ^ k` is entrywise positive and `|α| ≥ 2`, then
  every letter image `σᵏ [a]` has length `≥ |α| ≥ 2`, hence
  `2 * |w| ≤ |σᵏ w|` and `|w| < |σᵏ w|` for every nonempty `w`, and `σᵏ [a] ≠ []`;
* **`expanding_power`**: if `M` is primitive (`∃ k, ∀ a c, 0 < (M ^ k) a c`) and
  `2 ≤ |α|`, then `∃ k ≥ 1` with `|w| < |σᵏ w|` for all nonempty `w`, and
  `σᵏ [a] ≠ []` for all `a`;
* **`reduction_limit_of_pos_pow`**: for `k` with `M ^ k > 0` entrywise and
  `|α| ≥ 2`, and any child system `S` whose substitution is the power
  `S.s = power s k`, the conclusion of `reduction_limit` holds under its
  remaining hypotheses only (a state `T ∈ S.C`, all states 2-binomially
  equivalent, irreducible and noncoincident) -- `hs` and `hexp` are derived;
* **`reduction_limit_primitive`**: the same with `k` existential: if `M` is
  primitive and `|α| ≥ 2`, there is `k ≥ 1` such that for every child system of
  `power s k` the conclusion of `reduction_limit` holds under those remaining
  hypotheses.
* `nonerasing_of_primitive`: if `M` is primitive and `|α| ≥ 2` then `s` itself
  is nonerasing (`s a ≠ []`), so the hypothesis `hs` of `reduction_limit` is a
  consequence of primitivity (no power needed for it).
* **`reduction_limit_of_primitive`**: for a child system `S` of `σ` *itself*
  (no hypothesis that `S.s` is a power), with primitive incidence matrix,
  `|α| ≥ 2`, and all states 2-binomially equivalent, irreducible and
  noncoincident, there is `k ≥ 1` such that the conclusion of `reduction_limit`
  holds for the `k`-step system `S.pow k` (substitution `σᵏ`, children the
  depth-`k` descendants): two limit words with different first letters and
  syndetic `Equiv2` cuts.
* Negative control `card_two_needed`: on a one-letter alphabet the identity
  substitution `a ↦ a` is primitive (`M = (1)`) but no power is expanding, so
  the hypothesis `2 ≤ |α|` cannot be dropped from `expanding_power`.

Notes on the hypotheses of `reduction_limit` that are discharged: `hexp`
requires `|U.i| < |σ U.i|` on both tracks of every state, which needs every
state track nonempty; this follows from `Equiv2` together with noncoincidence
(a balanced pair with an empty track has both tracks empty, hence coincident).

NOT formalized here: any Perron--Frobenius statement (Perron root `> 1`);
primitivity of `power s k` itself; that the child system of balanced pairs of
the power substitution exists or is finite (the `ChildSystem` is a hypothesis);
anything about the substitution being Pisot or irreducible; the two-sided /
tiling picture.
-/
import PscVerif.Incidence
import PscVerif.FixedPointLimit
import Mathlib.Data.Fintype.Card

namespace Psc.PrimitiveExpansion

open Psc.Binomial Psc.Incidence Psc.FixedPointLimit

variable {α : Type*} [DecidableEq α]

/-! ### The power substitution

`power` and `subst_power` live in `PscVerif.Binomial` (next to
`ChildSystem.pow`); they are re-exported under this namespace. -/

export Psc.Binomial (power subst_power)

/-! ### Expansion from a positive power -/

/-- A positive power of the incidence matrix on at least two letters has
positive exponent (`M ^ 0 = 1` has zero off-diagonal entries). -/
theorem one_le_of_pos_pow [Fintype α] (s : α → List α) (hcard : 2 ≤ Fintype.card α)
    {k : ℕ} (hk : ∀ a c, 0 < (inc s ^ k) a c) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
    have := hk a c
    simp [hac] at this
  · exact hpos

/-- Under a positive power, every letter image contains every letter, so has
length at least `|α|`. -/
theorem card_le_length_of_pos_pow [Fintype α] (s : α → List α) {k : ℕ}
    (hk : ∀ a c, 0 < (inc s ^ k) a c) (c : α) :
    Fintype.card α ≤ ((subst s)^[k] [c]).length := by
  have hsub : (Finset.univ : Finset α) ⊆ ((subst s)^[k] [c]).toFinset := by
    intro a _
    rw [List.mem_toFinset, ← List.count_pos_iff, count_iterate_subst]
    exact hk a c
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ ((subst s)^[k] [c]).toFinset.card := Finset.card_le_card hsub
    _ ≤ ((subst s)^[k] [c]).length := List.toFinset_card_le _

/-- If every letter image of `σᵏ` has length at least two, `σᵏ` at least
doubles lengths. -/
theorem two_mul_length_le (s : α → List α) (k : ℕ)
    (h2 : ∀ c, 2 ≤ ((subst s)^[k] [c]).length) (w : List α) :
    2 * w.length ≤ ((subst s)^[k] w).length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have e : (a :: t) = [a] ++ t := rfl
    rw [e, iterate_subst_append, List.length_append, List.length_append]
    have := h2 a
    simp only [List.length_singleton]
    omega

/-- **Expansion at a positive power.**  If `M ^ k > 0` entrywise and `|α| ≥ 2`,
then `k ≥ 1`, `σᵏ` strictly lengthens every nonempty word (indeed
`2 |w| ≤ |σᵏ w|`), and no letter is erased by `σᵏ`. -/
theorem expanding_of_pos_pow [Fintype α] (s : α → List α) (hcard : 2 ≤ Fintype.card α)
    {k : ℕ} (hk : ∀ a c, 0 < (inc s ^ k) a c) :
    1 ≤ k ∧ (∀ w : List α, 2 * w.length ≤ ((subst s)^[k] w).length) ∧
      (∀ w : List α, w ≠ [] → w.length < ((subst s)^[k] w).length) ∧
      ∀ a, (subst s)^[k] [a] ≠ [] := by
  have h2 : ∀ c, 2 ≤ ((subst s)^[k] [c]).length :=
    fun c => hcard.trans (card_le_length_of_pos_pow s hk c)
  refine ⟨one_le_of_pos_pow s hcard hk, two_mul_length_le s k h2, ?_, ?_⟩
  · intro w hw
    have := two_mul_length_le s k h2 w
    have hpos := List.length_pos_of_ne_nil hw
    omega
  · intro a h
    have := h2 a
    rw [h] at this
    simp at this

/-- **(2) Expanding power.**  A primitive substitution on at least two letters
has a power `σᵏ`, `k ≥ 1`, that strictly lengthens every nonempty word and is
nonerasing. -/
theorem expanding_power [Fintype α] (s : α → List α)
    (hprim : ∃ k, ∀ a c, 0 < (inc s ^ k) a c) (hcard : 2 ≤ Fintype.card α) :
    ∃ k ≥ 1, (∀ w : List α, w ≠ [] → w.length < ((subst s)^[k] w).length) ∧
      ∀ a, (subst s)^[k] [a] ≠ [] := by
  obtain ⟨k, hk⟩ := hprim
  obtain ⟨h1, -, h3, h4⟩ := expanding_of_pos_pow s hcard hk
  exact ⟨k, h1, h3, h4⟩

/-- Negative control: the hypothesis `2 ≤ |α|` cannot be dropped.  On a
one-letter alphabet the identity substitution is primitive (`M = (1)`) but no
power lengthens the nonempty word `[()]`. -/
theorem card_two_needed :
    (∃ k, ∀ a c : Unit, 0 < (inc (fun _ : Unit => [()]) ^ k) a c) ∧
      ∀ k, ¬ (([()] : List Unit).length <
        ((subst (fun _ : Unit => [()]))^[k] [()]).length) := by
  have hfix : ∀ k, (subst (fun _ : Unit => [()]))^[k] [()] = [()] :=
    fun k => Function.iterate_fixed (by simp [subst]) k
  refine ⟨⟨1, fun a c => ?_⟩, fun k => by simp [hfix k]⟩
  rw [← count_iterate_subst]
  cases a; cases c
  rw [hfix 1]
  simp

/-! ### Discharging `hexp` and `hs` of `reduction_limit` -/

/-- A balanced noncoincident pair has both tracks nonempty. -/
theorem tracks_ne_nil {u v : List α} (hb : Equiv1 u v) (hnc : u ≠ v) : u ≠ [] ∧ v ≠ [] := by
  have hl := hb.length_eq
  constructor
  · rintro rfl
    exact hnc (List.length_eq_zero_iff.mp hl.symm).symm
  · rintro rfl
    exact hnc (List.length_eq_zero_iff.mp hl)

/-- **(3) Reduction lemma, limit form, at a positive power.**  If `M ^ k > 0`
entrywise and `|α| ≥ 2`, then for every child system of the power substitution
`power s k` (whose word map is `σᵏ`, `subst_power`) all of whose states are
2-binomially equivalent, irreducible and noncoincident, the conclusion of
`reduction_limit` holds: the nonerasing and expansion hypotheses are derived. -/
theorem reduction_limit_of_pos_pow [Fintype α] (s : α → List α)
    (hcard : 2 ≤ Fintype.card α) {k : ℕ} (hk : ∀ a c, 0 < (inc s ^ k) a c)
    (S : ChildSystem α) (hS : S.s = power s k)
    (T : List α × List α) (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, Irreducible U.1 U.2 ∧ U.1 ≠ U.2) :
    ∃ T₀ ∈ S.C, ∃ p ≥ 1, ∃ (_ : T₀.1 <+: (subst S.s)^[p] T₀.1)
      (_ : T₀.2 <+: (subst S.s)^[p] T₀.2)
      (hg : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.1).length)
      (hg' : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.2).length),
      limit S.s T₀.1 p hg 0 ≠ limit S.s T₀.2 p hg' 0 ∧
      ∀ m, ∃ c, m ≤ c ∧ c ≤ m + S.C.sup (fun U => U.1.length) ∧
        Equiv2 (List.ofFn (fun i : Fin c => limit S.s T₀.1 p hg i))
          (List.ofFn (fun i : Fin c => limit S.s T₀.2 p hg' i)) := by
  obtain ⟨-, -, hlt, hne⟩ := expanding_of_pos_pow s hcard hk
  have hs : ∀ a, S.s a ≠ [] := by
    intro a; rw [hS]; exact hne a
  have hexp : ∀ U ∈ S.C,
      U.1.length < (subst S.s U.1).length ∧ U.2.length < (subst S.s U.2).length := by
    intro U hU
    obtain ⟨h1, h2⟩ := tracks_ne_nil (hK2 U hU).1 (hstrict U hU).2
    rw [hS, subst_power]
    exact ⟨hlt _ h1, hlt _ h2⟩
  exact reduction_limit S hs T hT hK2 hstrict hexp

/-- **(3) Reduction lemma, limit form, from primitivity.**  If the incidence
matrix of `s` is primitive and `|α| ≥ 2`, there is `k ≥ 1` such that for every
child system of the power substitution `power s k` all of whose states are
2-binomially equivalent, irreducible and noncoincident, the conclusion of
`reduction_limit` holds. -/
theorem reduction_limit_primitive [Fintype α] (s : α → List α)
    (hprim : ∃ k, ∀ a c, 0 < (inc s ^ k) a c) (hcard : 2 ≤ Fintype.card α) :
    ∃ k ≥ 1, ∀ (S : ChildSystem α), S.s = power s k →
      ∀ (T : List α × List α), T ∈ S.C → (∀ U ∈ S.C, Equiv2 U.1 U.2) →
      (∀ U ∈ S.C, Irreducible U.1 U.2 ∧ U.1 ≠ U.2) →
      ∃ T₀ ∈ S.C, ∃ p ≥ 1, ∃ (_ : T₀.1 <+: (subst S.s)^[p] T₀.1)
        (_ : T₀.2 <+: (subst S.s)^[p] T₀.2)
        (hg : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.1).length)
        (hg' : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.2).length),
        limit S.s T₀.1 p hg 0 ≠ limit S.s T₀.2 p hg' 0 ∧
        ∀ m, ∃ c, m ≤ c ∧ c ≤ m + S.C.sup (fun U => U.1.length) ∧
          Equiv2 (List.ofFn (fun i : Fin c => limit S.s T₀.1 p hg i))
            (List.ofFn (fun i : Fin c => limit S.s T₀.2 p hg' i)) := by
  obtain ⟨k, hk⟩ := hprim
  exact ⟨k, one_le_of_pos_pow s hcard hk, fun S hS T hT hK2 hstrict =>
    reduction_limit_of_pos_pow s hcard hk S hS T hT hK2 hstrict⟩

/-- **Nonerasing from primitivity.**  If the incidence matrix of `s` is
primitive and `|α| ≥ 2`, then `s` itself erases no letter: the hypothesis `hs`
of `reduction_limit` is a consequence of primitivity. -/
theorem nonerasing_of_primitive [Fintype α] (s : α → List α)
    (hprim : ∃ k, ∀ a c, 0 < (inc s ^ k) a c) (hcard : 2 ≤ Fintype.card α) :
    ∀ a, s a ≠ [] := by
  obtain ⟨k, hk⟩ := hprim
  obtain ⟨h1, -, -, hne⟩ := expanding_of_pos_pow s hcard hk
  intro a ha
  apply hne a
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have h0 : subst s [a] = [] := by simp [subst, ha]
  rw [Function.iterate_succ_apply, h0, iterate_subst_nil]

/-- **(3) Reduction lemma, limit form, for a child system of `σ` itself.**  Let
`S` be a child system over a finite alphabet with at least two letters whose
incidence matrix is primitive, all of whose states are 2-binomially
equivalent, irreducible and noncoincident.  No hypothesis that `S.s` is a power
is made: there is `k ≥ 1` such that the conclusion of `reduction_limit` holds
for the `k`-step system `S.pow k` (same states `(S.pow k).C = S.C`,
substitution `power S.s k`, acting on words as `σᵏ` by `subst_power`, children
the depth-`k` descendants).  So the two limit words of `σ^{kp}` have different
first letters and are cut `Equiv2` on a syndetic set of prefix lengths. -/
theorem reduction_limit_of_primitive [Fintype α] (S : ChildSystem α)
    (hprim : ∃ k, ∀ a c, 0 < (inc S.s ^ k) a c) (hcard : 2 ≤ Fintype.card α)
    (T : List α × List α) (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, Irreducible U.1 U.2 ∧ U.1 ≠ U.2) :
    ∃ k ≥ 1, ∃ T₀ ∈ (S.pow k).C, ∃ p ≥ 1,
      ∃ (_ : T₀.1 <+: (subst (S.pow k).s)^[p] T₀.1)
      (_ : T₀.2 <+: (subst (S.pow k).s)^[p] T₀.2)
      (hg : ∀ m, ∃ n, m < ((subst (S.pow k).s)^[p * n] T₀.1).length)
      (hg' : ∀ m, ∃ n, m < ((subst (S.pow k).s)^[p * n] T₀.2).length),
      limit (S.pow k).s T₀.1 p hg 0 ≠ limit (S.pow k).s T₀.2 p hg' 0 ∧
      ∀ m, ∃ c, m ≤ c ∧ c ≤ m + (S.pow k).C.sup (fun U => U.1.length) ∧
        Equiv2 (List.ofFn (fun i : Fin c => limit (S.pow k).s T₀.1 p hg i))
          (List.ofFn (fun i : Fin c => limit (S.pow k).s T₀.2 p hg' i)) := by
  obtain ⟨k, hk⟩ := hprim
  exact ⟨k, one_le_of_pos_pow S.s hcard hk,
    reduction_limit_of_pos_pow S.s hcard hk (S.pow k) rfl T hT hK2 hstrict⟩

end Psc.PrimitiveExpansion
