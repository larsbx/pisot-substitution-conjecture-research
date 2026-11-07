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
* **`expanding_power`**: if `M` is primitive (`∃ k ≥ 1, ∀ a c, 0 < (M ^ k) a c`;
  this is the form of primitivity used throughout the file) and `2 ≤ |α|`, then
  `∃ k ≥ 1` with `|w| < |σᵏ w|` for all nonempty `w`, and `σᵏ [a] ≠ []` for all
  `a`;
* **`reduction_limit_of_pos_pow`**: for `k` with `M ^ k > 0` entrywise and
  `|α| ≥ 2`, and any child system `S` whose substitution is the power
  `S.s = power s k`, the conclusion of `reduction_limit` holds under its
  remaining hypotheses only (a state `T ∈ S.C`, all states 2-binomially
  equivalent, irreducible (`Psc.Binomial.IrreduciblePair`) and noncoincident)
  -- `hs` and `hexp` are derived;
* **`reduction_limit_primitive`**: the same with `k` existential: if `M` is
  primitive and `|α| ≥ 2`, there is `k ≥ 1` such that for every child system of
  `power s k` the conclusion of `reduction_limit` holds under those remaining
  hypotheses.
* `nonerasing_of_primitive`: if `M` is primitive then `s` itself is nonerasing
  (`s a ≠ []`), so the hypothesis `hs` of `reduction_limit` is a consequence of
  primitivity (no power and no bound on `|α|` needed for it).
* **`reduction_limit_of_primitive`**: for a child system `S` of `σ` *itself*
  (no hypothesis that `S.s` is a power), with primitive incidence matrix,
  `|α| ≥ 2`, and all states 2-binomially equivalent, irreducible and
  noncoincident, there is `k ≥ 1` such that the conclusion of `reduction_limit`
  holds for the `k`-step system `S.pow k` (substitution `σᵏ`, children the
  depth-`k` descendants): two limit words with different first letters and
  syndetic `Equiv2` cuts.  This is a reductio premise: its hypothesis set is
  empty on two letters (below) and conjecturally on three (the combinatorial
  form of Concentration, not proved).
* **`binary_no_equiv2`**: over `Fin 2` no irreducible noncoincident pair is
  2-binomially equivalent.  For a balanced pair, `K₂(u,v)_{01} = Σ_j d j` with
  `d j = |u[:j]|_0 - |v[:j]|_0` (`k2_eq_sum_pdef`, from `n2_binary`); `d`
  moves by at most one per step (`pdef_step`), vanishes at no proper cut by
  irreducibility (`pdef_ne_zero`), hence has one sign (`pdef_sign`), and
  `d 1 ≠ 0`; `binary_reduction_premise_empty`: so no child system over `Fin 2`
  meets the hypotheses of `reduction_limit_of_primitive`.
* Control `thueMorse_control`: the Thue–Morse child system
  `Psc.Binomial.thueMorse` (`0 ↦ 01`, `1 ↦ 10`, states `(01, 10)`, `(10, 01)`)
  meets every hypothesis of `reduction_limit_of_primitive` except `hK2`
  (checked by `decide`).
* Negative control `card_two_needed`: on a one-letter alphabet the identity
  substitution `a ↦ a` is primitive (`M = (1)`) but no power is expanding, so
  the hypothesis `2 ≤ |α|` cannot be dropped from `expanding_power`.

Notes on the hypotheses of `reduction_limit` that are discharged: `hexp`
requires `|U.i| < |σ U.i|` on both tracks of every state, which needs every
state track nonempty; this follows from `Equiv2` together with noncoincidence
(a balanced pair with an empty track has both tracks empty, hence coincident:
`Psc.Binomial.Equiv1.tracks_ne_nil`).

NOT formalized here: any Perron--Frobenius statement (Perron root `> 1`);
primitivity of `power s k` itself; that the child system of balanced pairs of
the power substitution exists or is finite (the `ChildSystem` is a hypothesis);
anything about the substitution being Pisot or irreducible; the two-sided /
tiling picture.
-/
import PscVerif.Incidence
import PscVerif.FixedPointLimit
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

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

omit [DecidableEq α] in
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

/-- **(2) Expanding power.**  A primitive substitution (`M ^ k > 0` entrywise
for some `k ≥ 1`) on at least two letters has a power `σᵏ`, `k ≥ 1`, that
strictly lengthens every nonempty word and is nonerasing. -/
theorem expanding_power [Fintype α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (hcard : 2 ≤ Fintype.card α) :
    ∃ k ≥ 1, (∀ w : List α, w ≠ [] → w.length < ((subst s)^[k] w).length) ∧
      ∀ a, (subst s)^[k] [a] ≠ [] := by
  obtain ⟨k, hk1, hk⟩ := hprim
  obtain ⟨-, -, h3, h4⟩ := expanding_of_pos_pow s hcard hk
  exact ⟨k, hk1, h3, h4⟩

/-- Negative control: the hypothesis `2 ≤ |α|` cannot be dropped.  On a
one-letter alphabet the identity substitution is primitive (`M = (1)`, `k = 1`)
but no power lengthens the nonempty word `[()]`. -/
theorem card_two_needed :
    (∃ k ≥ 1, ∀ a c : Unit, 0 < (inc (fun _ : Unit => [()]) ^ k) a c) ∧
      ∀ k, ¬ (([()] : List Unit).length <
        ((subst (fun _ : Unit => [()]))^[k] [()]).length) := by
  have hfix : ∀ k, (subst (fun _ : Unit => [()]))^[k] [()] = [()] :=
    fun k => Function.iterate_fixed (by simp [subst]) k
  refine ⟨⟨1, le_rfl, fun a c => ?_⟩, fun k => by simp [hfix k]⟩
  rw [← count_iterate_subst]
  cases a; cases c
  rw [hfix 1]
  simp

/-! ### Discharging `hexp` and `hs` of `reduction_limit` -/

/-- **(3) Reduction lemma, limit form, at a positive power.**  If `M ^ k > 0`
entrywise and `|α| ≥ 2`, then for every child system of the power substitution
`power s k` (whose word map is `σᵏ`, `subst_power`) all of whose states are
2-binomially equivalent, irreducible and noncoincident, the conclusion of
`reduction_limit` holds: the nonerasing and expansion hypotheses are derived.

This is a reductio premise: its hypotheses describe a hypothetical strict
system with `K₂ ≡ 0`, and on a two-letter alphabet they cannot hold
(`Psc.PrimitiveExpansion.binary_reduction_premise_empty`); on three letters
their emptiness is the open "combinatorial Concentration". -/
theorem reduction_limit_of_pos_pow [Fintype α] (s : α → List α)
    (hcard : 2 ≤ Fintype.card α) {k : ℕ} (hk : ∀ a c, 0 < (inc s ^ k) a c)
    (S : ChildSystem α) (hS : S.s = power s k)
    (T : List α × List α) (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, IrreduciblePair U.1 U.2 ∧ U.1 ≠ U.2) :
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
    obtain ⟨h1, h2⟩ := (hK2 U hU).1.tracks_ne_nil (hstrict U hU).2
    rw [hS, subst_power]
    exact ⟨hlt _ h1, hlt _ h2⟩
  exact reduction_limit S hs T hT hK2 hstrict hexp

/-- **(3) Reduction lemma, limit form, from primitivity.**  If the incidence
matrix of `s` is primitive (`M ^ k > 0` for some `k ≥ 1`) and `|α| ≥ 2`, there
is `k ≥ 1` such that for every child system of the power substitution
`power s k` all of whose states are 2-binomially equivalent, irreducible and
noncoincident, the conclusion of `reduction_limit` holds.  Like
`reduction_limit_of_primitive`, a reductio premise: on two letters no such child
system exists (`binary_reduction_premise_empty`). -/
theorem reduction_limit_primitive [Fintype α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (hcard : 2 ≤ Fintype.card α) :
    ∃ k ≥ 1, ∀ (S : ChildSystem α), S.s = power s k →
      ∀ (T : List α × List α), T ∈ S.C → (∀ U ∈ S.C, Equiv2 U.1 U.2) →
      (∀ U ∈ S.C, IrreduciblePair U.1 U.2 ∧ U.1 ≠ U.2) →
      ∃ T₀ ∈ S.C, ∃ p ≥ 1, ∃ (_ : T₀.1 <+: (subst S.s)^[p] T₀.1)
        (_ : T₀.2 <+: (subst S.s)^[p] T₀.2)
        (hg : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.1).length)
        (hg' : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.2).length),
        limit S.s T₀.1 p hg 0 ≠ limit S.s T₀.2 p hg' 0 ∧
        ∀ m, ∃ c, m ≤ c ∧ c ≤ m + S.C.sup (fun U => U.1.length) ∧
          Equiv2 (List.ofFn (fun i : Fin c => limit S.s T₀.1 p hg i))
            (List.ofFn (fun i : Fin c => limit S.s T₀.2 p hg' i)) := by
  obtain ⟨k, hk1, hk⟩ := hprim
  exact ⟨k, hk1, fun S hS T hT hK2 hstrict =>
    reduction_limit_of_pos_pow s hcard hk S hS T hT hK2 hstrict⟩

/-- **Nonerasing from primitivity.**  If the incidence matrix of `s` is
primitive (`M ^ k > 0` for some `k ≥ 1`), then `s` itself erases no letter: the
hypothesis `hs` of `reduction_limit` is a consequence of primitivity.  No bound
on `|α|` is needed once `k ≥ 1` (an erased letter `a` gives a zero column `a`
of every `M ^ k`, `k ≥ 1`). -/
theorem nonerasing_of_primitive [Fintype α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) : ∀ a, s a ≠ [] := by
  obtain ⟨k, hk1, hk⟩ := hprim
  intro a ha
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk1
  have h0 : subst s [a] = [] := by simp [subst, ha]
  have := hk a a
  rw [← count_iterate_subst, Function.iterate_succ_apply, h0, iterate_subst_nil] at this
  simp at this

/-- **(3) Reduction lemma, limit form, for a child system of `σ` itself.**  Let
`S` be a child system over a finite alphabet with at least two letters whose
incidence matrix is primitive (`M ^ k > 0` for some `k ≥ 1`), all of whose
states are 2-binomially equivalent, irreducible and noncoincident.  No
hypothesis that `S.s` is a power is made: there is `k ≥ 1` such that the
conclusion of `reduction_limit` holds for the `k`-step system `S.pow k` (same
states `(S.pow k).C = S.C`, substitution `power S.s k`, acting on words as `σᵏ`
by `subst_power`, children the depth-`k` descendants).  So the two limit words
of `σ^{kp}` have different first letters and are cut `Equiv2` on a syndetic set
of prefix lengths.

This is a **reductio premise**, not an existence statement: its hypothesis set
is empty on two letters (`binary_reduction_premise_empty`; the Thue–Morse
control `thueMorse_control` meets every hypothesis except `hK2`), and
conjecturally empty on three letters as well (the combinatorial form of
Concentration, `docs/c4-concentration-attack-2026-11-06.md` §7, not proved). -/
theorem reduction_limit_of_primitive [Fintype α] (S : ChildSystem α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) (hcard : 2 ≤ Fintype.card α)
    (T : List α × List α) (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, IrreduciblePair U.1 U.2 ∧ U.1 ≠ U.2) :
    ∃ k ≥ 1, ∃ T₀ ∈ (S.pow k).C, ∃ p ≥ 1,
      ∃ (_ : T₀.1 <+: (subst (S.pow k).s)^[p] T₀.1)
      (_ : T₀.2 <+: (subst (S.pow k).s)^[p] T₀.2)
      (hg : ∀ m, ∃ n, m < ((subst (S.pow k).s)^[p * n] T₀.1).length)
      (hg' : ∀ m, ∃ n, m < ((subst (S.pow k).s)^[p * n] T₀.2).length),
      limit (S.pow k).s T₀.1 p hg 0 ≠ limit (S.pow k).s T₀.2 p hg' 0 ∧
      ∀ m, ∃ c, m ≤ c ∧ c ≤ m + (S.pow k).C.sup (fun U => U.1.length) ∧
        Equiv2 (List.ofFn (fun i : Fin c => limit (S.pow k).s T₀.1 p hg i))
          (List.ofFn (fun i : Fin c => limit (S.pow k).s T₀.2 p hg' i)) := by
  obtain ⟨k, hk1, hk⟩ := hprim
  exact ⟨k, hk1, reduction_limit_of_pos_pow S.s hcard hk (S.pow k) rfl T hT hK2 hstrict⟩

/-! ### Two letters: the premise of `reduction_limit_of_primitive` is empty

On `Fin 2`, for a balanced pair `(u, v)` let `d j = |u[:j]|_0 - |v[:j]|_0` be the
prefix defect (`pdef`).  Then `K₂(u,v)_{01} = Σ_{j < |u|} d j` (`k2_eq_sum_pdef`),
`d` moves by at most one per step and, by irreducibility, vanishes at no proper
cut, so all its nonzero terms have one sign and `K₂ ≠ 0`. -/

section Binary
/-- On two letters every letter is `0` or `1`. -/
theorem count_zero_add_count_one (w : List (Fin 2)) : w.count 0 + w.count 1 = w.length := by
  induction w with
  | nil => rfl
  | cons c w ih => fin_cases c <;> simp <;> omega

/-- On two letters, `n2 w 0 1 + C(|w|_0, 2) = Σ_{j < |w|} |w[:j]|_0`: the `0`s
before a position are counted at each `1` (`n2 w 0 1`) and at each `0`
(`C(|w|_0, 2)`). -/
theorem n2_binary (w : List (Fin 2)) :
    n2 w 0 1 + (w.count 0).choose 2 = ∑ j ∈ Finset.range w.length, (w.take j).count 0 := by
  induction w with
  | nil => simp [n2]
  | cons c w ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.count_cons, Finset.sum_add_distrib, List.take_zero,
      List.count_nil, add_zero, ← ih, n2]
    have h := count_zero_add_count_one w
    fin_cases c <;> simp [Nat.choose_succ_succ']
    omega

/-- The prefix defect `d j = |u[:j]|_0 - |v[:j]|_0`. -/
def pdef (u v : List (Fin 2)) (j : ℕ) : ℤ := ((u.take j).count 0 : ℤ) - (v.take j).count 0

/-- For a balanced binary pair, `K₂(u,v)_{01} = Σ_{j < |u|} d j`. -/
theorem k2_eq_sum_pdef {u v : List (Fin 2)} (h : Equiv1 u v) :
    (n2 u 0 1 : ℤ) - n2 v 0 1 = ∑ j ∈ Finset.range u.length, pdef u v j := by
  have hu := n2_binary u
  have hv := n2_binary v
  rw [← h.length_eq, ← h 0] at hv
  simp only [pdef, Finset.sum_sub_distrib]
  have hu' := congrArg (Nat.cast : ℕ → ℤ) hu
  have hv' := congrArg (Nat.cast : ℕ → ℤ) hv
  push_cast [Nat.cast_sum] at hu' hv'
  linarith

/-- One more letter changes a prefix count of `0` by `0` or `1`. -/
theorem count_take_succ (w : List (Fin 2)) (j : ℕ) :
    (w.take j).count 0 ≤ (w.take (j + 1)).count 0 ∧
      (w.take (j + 1)).count 0 ≤ (w.take j).count 0 + 1 := by
  rw [List.take_add_one, List.count_append]
  cases w[j]? <;> simp [List.count_singleton]
  split_ifs <;> simp

/-- The prefix defect moves by at most one per step. -/
theorem pdef_step (u v : List (Fin 2)) (j : ℕ) :
    pdef u v j - 1 ≤ pdef u v (j + 1) ∧ pdef u v (j + 1) ≤ pdef u v j + 1 := by
  have hu := count_take_succ u j
  have hv := count_take_succ v j
  simp only [pdef]
  omega

/-- Irreducibility: the prefix defect vanishes at no proper cut `0 < j < |u|`
(on two letters, equal `0`-counts of equal-length prefixes mean balanced
prefixes). -/
theorem pdef_ne_zero {u v : List (Fin 2)} (h : Equiv1 u v) (hirr : IrreduciblePair u v)
    {j : ℕ} (h0 : 0 < j) (hj : j < u.length) : pdef u v j ≠ 0 := by
  intro hd
  apply hirr j h0 hj
  have hlen : (u.take j).length = (v.take j).length := by
    simp only [List.length_take, ← h.length_eq]
  have h1 := count_zero_add_count_one (u.take j)
  have h2 := count_zero_add_count_one (v.take j)
  simp only [pdef] at hd
  intro a
  fin_cases a <;> simp <;> omega

/-- Hence the prefix defect has constant sign on `1 ≤ j < |u|`. -/
theorem pdef_sign {u v : List (Fin 2)} (h : Equiv1 u v) (hirr : IrreduciblePair u v)
    {j : ℕ} (h1 : 1 ≤ j) (hj : j < u.length) : 0 < pdef u v 1 * pdef u v j := by
  induction j, h1 using Nat.le_induction with
  | base => exact mul_self_pos.2 (pdef_ne_zero h hirr one_pos hj)
  | succ j hj1 ih =>
    have hprev := ih (by omega)
    have hne := pdef_ne_zero h hirr (by omega) hj
    have hstep := pdef_step u v j
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprev with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_pos ha (by omega)
    · exact mul_pos_of_neg_of_neg ha (by omega)

/-- **No binary `K₂ = 0` strict pair.**  Over `Fin 2` no irreducible
noncoincident pair is 2-binomially equivalent: for a balanced such pair
`K₂(u,v)_{01} = Σ_j d j` with every term of one sign and `d 1 ≠ 0`
(`|u| ≥ 2`).  The binary statement is elementary and standard: on two letters
2-binomial equivalence is determined by the Parikh vector and the position sum
of one letter (Rigo–Salimov, Theoret. Comput. Sci. 601 (2015), binomial
equivalence).  Only its use as the emptiness of the reduction-lemma premise is
specific here. -/
theorem binary_no_equiv2 {u v : List (Fin 2)} (hirr : IrreduciblePair u v) (hnc : u ≠ v) :
    ¬ Equiv2 u v := by
  intro h2
  have h := h2.1
  have hlen : 2 ≤ u.length := by
    by_contra hlt
    apply hnc
    have hl := h.length_eq
    interval_cases hu : u.length
    · rw [List.length_eq_zero_iff.1 hu, List.length_eq_zero_iff.1 (by omega : v.length = 0)]
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hu
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 (by omega : v.length = 1)
      fin_cases a <;> fin_cases b <;> first | rfl | exact absurd (h 0) (by decide)
  have hsum : 0 < pdef u v 1 * ∑ j ∈ Finset.range u.length, pdef u v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_pos' (fun j hj => ?_) ⟨1, Finset.mem_range.2 (by omega),
      pdef_sign h hirr le_rfl (by omega)⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [pdef]
    · exact (pdef_sign h hirr hj0 (Finset.mem_range.1 hj)).le
  rw [← k2_eq_sum_pdef h, h2.2 0 1, sub_self, mul_zero] at hsum
  exact lt_irrefl 0 hsum

/-- **The premise of `reduction_limit_of_primitive` is empty on two letters.**
No child system over `Fin 2` has a state and all states 2-binomially
equivalent, irreducible and noncoincident. -/
theorem binary_reduction_premise_empty (S : ChildSystem (Fin 2))
    {T : List (Fin 2) × List (Fin 2)} (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, IrreduciblePair U.1 U.2 ∧ U.1 ≠ U.2) : False :=
  binary_no_equiv2 (hstrict T hT).1 (hstrict T hT).2 (hK2 T hT)

/-- **Thue–Morse control.**  The Thue–Morse child system
(`Psc.Binomial.thueMorse`: `0 ↦ 01`, `1 ↦ 10`, states `(01, 10)`, `(10, 01)`)
satisfies every hypothesis of `reduction_limit_of_primitive` (`M ^ 1 > 0`, two
letters, a state, all states irreducible and noncoincident) except `hK2`: its
states are not 2-binomially equivalent. -/
theorem thueMorse_control :
    (∃ k ≥ 1, ∀ a c, 0 < (inc thueMorse.s ^ k) a c) ∧ 2 ≤ Fintype.card (Fin 2) ∧
      tmPair ∈ thueMorse.C ∧
      (∀ U ∈ thueMorse.C, IrreduciblePair U.1 U.2 ∧ U.1 ≠ U.2) ∧
      ¬ ∀ U ∈ thueMorse.C, Equiv2 U.1 U.2 := by
  refine ⟨⟨1, le_rfl, fun a c => ?_⟩, by simp, by decide, by decide, by decide⟩
  rw [pow_one, inc_apply]
  fin_cases a <;> fin_cases c <;> decide

end Binary

end Psc.PrimitiveExpansion
