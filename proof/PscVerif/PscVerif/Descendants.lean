/-
# Depth-`n` descendants, swap closure, and reachability from the seeds

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `def:balanced` (the
reduction `red(u, v)`; states are pairs up to side swap), `lem:inherited`
(zero returns inflate to zero returns), `def:bpa` (seeds, children, the
reachable states of `B_σ`), `lem:descendants` (the blocks of
`red(σⁿ u, σⁿ v)` are the depth-`n` descendants, and their boundaries are the
zero returns), `hyp:G1` (finiteness of `B_σ`), and the uses of
`lem:descendants` in the proofs of `thm:G1b1` and `prop:G1-from-overlaps`;
`docs/c4-concentration-attack-2026-11-06.md` §8.

`Psc.Reduction` defines `red` and proves the zero-return factorization unique
(`red_unique`); here uniqueness is used to show that `red` commutes with
concatenation and with inflation, which is `lem:descendants`.

**Which child graph.**  `lem:descendants` is formalised for the *full* child
graph `Child`, in which the children of every state, coincidence blocks
included, are formed.  This reading is required: in `def:bpa`'s `B_σ`, where
coincidence blocks are terminal (`ChildNC`), the lemma read on its paths is
false.  For
Fibonacci `0 ↦ 01`, `1 ↦ 0` the block `(1, 1)` of `red(σ² 01, σ² 10)` is not
reachable in `B_σ` at all (`fib_bpaStatesNC`, `fib_descR_two`).  The two
graphs have the same noncoincident reachable states (`mem_bpaStatesNC_iff`).
They differ only by coincidence blocks `(c, c)` (`bpaStates_subset_union`),
and so they are finite together (`finite_bpaStates_iff`).

Proved here, in full (no finiteness of the alphabet is used except for the
seeds, the G1 bridge and the `decide` controls):

* `red_flatten`: for pieces `bs` that are each balanced,
  `red (⋯ tops ⋯) (⋯ bottoms ⋯) = bs.flatMap (red · ·)`; `red_append`,
  `red_of_isBlock` (`red T.1 T.2 = [T]` for a block), `red_self`
  (`red w w` is the list of coincidence blocks `(c, c)`, `c ∈ w`);
* `inherited` (`lem:inherited`): a zero return `k` of `(u, v)` gives the
  zero return `|σ(u[k])| = |σ(v[k])|` of `(σ u, σ v)`; `equiv1_iterate_subst`:
  `σⁿ` preserves balance;
* **`red_iterate_subst`**, `red_subst`: for balanced `u, v`,
  `red (σⁿ u) (σⁿ v) = (red u v).flatMap (fun T => red (σⁿ T.1) (σⁿ T.2))`;
* **`zero_return_iff`** (the boundary clause): for balanced `u, v` and
  `k ≤ |u|`, `k` is a zero return of `(u, v)` iff it is a partial sum of the
  block lengths of `red u v` (via `take_flatten_map`, `take_red_top`,
  `take_red_bot`);
* **`lem:descendants` in the child graph, with no finiteness assumption**:
  `Child`; `descR s n T`, the ends of the length-`n` paths from `T`, in order
  and with multiplicity (`mem_descR_succ`); **`descR_of_isBlock`**:
  `descR s n T = red (σⁿ T.1) (σⁿ T.2)` for a block `T` and every `n ≥ 0`;
  `descR_succ`: the same for a balanced `T` and `n ≥ 1`; **`descR_zero_return`**:
  the boundaries between the depth-`n` descendants are exactly the zero returns
  of `(σⁿ T.1, σⁿ T.2)`; `reflTransGen_iff_mem_descR`, **`reflTransGen_child_iff`**:
  from a block `T`, `U` is reachable iff it is a block of
  `red (σⁿ T.1) (σⁿ T.2)` for some `n`;
* `lem:descendants` in a child system: `redSystem_desc_eq_descR` (in
  `Psc.Reduction.redSystem`, `desc = descR` on `C`), **`redSystem_desc`**
  (`desc n T = red (σⁿ T.1) (σⁿ T.2)` for `T ∈ C` and `n ≥ 1`),
  `redSystem_desc_of_isBlock` (every `n ≥ 0` for a block), and
  `redSystem_desc_zero_return`;
* `child_swap` (the last sentence of the proof of `lem:descendants`): swapping
  a parent's sides swaps its children's sides;
* swap closure is without loss of generality *for building a normalisation*
  (`Set` and `Finset` forms): it preserves child-closure, balance and
  coincidence-freeness, and it is the least swap-closed superset
  (`swapClosure_childClosed`, `swapClosure_swapClosed`,
  `swapClosure_coincidenceFree`, `swapClosure_balanced`, `subset_swapClosure`,
  `swapClosure_subset`).  The `Finset` forms `swapClosureF_*` feed
  `Psc.Reduction.redSystem`;
* `lexNormalisation`: over a linearly ordered alphabet, a swap-closed,
  coincidence-free `C` has the manuscript's normalized representatives
  `R = {T ∈ C | T.1 < T.2}` (lexicographic), a
  `Psc.SignedCocycle.Normalisation` of `redSystem`.  This discharges the
  `R`-hypotheses of `Psc.Reduction.redNormalisation`;
* reachability (`def:bpa`): `seeds` (`(ab, ba)`, `a ≠ b`, over a `Fintype`
  alphabet), `mem_seeds`, `seed_isBlock`, `seeds_swapClosed`, `seeds_isBlock`;
  `Reachable` (`Relation.ReflTransGen` of `Child` from a seed set) and
  `bpaStates`, the states reachable from the seeds in the full child graph;
  `subset_reachable`, `reachable_childClosed`, `reachable_subset` (the least
  child-closed superset), `reachable_swapClosed`, `reachable_equiv1`,
  `reachable_isBlock`, and their `bpaStates_*` instances;
  **`mem_bpaStates_iff_red`**: without G1, the members of `bpaStates s` are
  exactly the blocks of `red (σⁿ ab) (σⁿ ba)` over seeds `(ab, ba)` and depths
  `n`;
* the manuscript's `B_σ` (terminal coincidence blocks): `child_coincident`,
  `ChildNC`, `reflTransGen_childNC`, `bpaStatesNC` (its vertex set),
  `bpaStatesNC_subset_bpaStates`, `bpaStatesNC_subset` (the least
  `ChildNC`-closed superset of the seeds), `mem_bpaStatesNC_iff` (agreement on
  noncoincident states), `eq_coincidence_of_isBlock` (a coincidence block is
  `([c], [c])`), `bpaStates_subset_union`, **`finite_bpaStates_iff`** (the G1
  bridge), and **`exists_red_of_mem_bpaStatesNC`** (every vertex of `B_σ` is a
  block of some `red (σⁿ ab) (σⁿ ba)`, the step used in `thm:G1b1`);
* `bpaSystem`: under G1 (`bpaStates s` finite, equivalently
  `bpaStatesNC s` finite) the states reachable in the full child graph form a
  `redSystem`.  It is swap-closed (`bpaSystem_swap`), and `lem:descendants`
  holds on it at every depth `n ≥ 0` (`bpaSystem_desc`,
  `bpaSystem_desc_zero_return`);
* calibrations and controls (`decide`):
  * both sides of `red_flatten`, `red_subst` and `red_iterate_subst` on
    concrete pairs, and the failure of `red_flatten` for unbalanced pieces;
  * `tmRedSystem.desc 2 tmPair = red (σ² 01) (σ² 10)`;
  * `tmReducibleSystem`, a `redSystem` with the reducible state
    `(0110, 1001)`.  There `desc 0 ≠ red` but `desc 1`, `desc 2` agree, so
    `1 ≤ n` in `redSystem_desc` is sharp;
  * a child-closed, coincidence-free, not swap-closed `D = {(01, 10)}` for
    `0 ↦ 010, 1 ↦ 101`, and its swap closure;
  * `bpaStates thueMorseSubst = {(01,10), (10,01)}`;
  * Fibonacci: `fib_bpaStates` (four states, with `(1, 1)`) is strictly larger
    than `fib_bpaStatesNC` (three states), and
    `fib_descR_two`/`fib_one_not_mem_bpaStatesNC` refute `lem:descendants` on
    `B_σ` with terminal coincidence blocks;
  * `lexNormalisation` of `tmRedSystem` has the `R = {(01, 10)}` of
    `Psc.Reduction.tmRedNormalisation`.

Not proved here:

* G1 (finiteness of `B_σ`, `hyp:G1`) itself;
* the discrepancy bound of `thm:G1b1` and the gap bound of
  `prop:G1-from-overlaps`: only their `lem:descendants` step is formalised
  (`exists_red_of_mem_bpaStatesNC`, `descR_of_isBlock`);
* any statement about recurrent components or productivity (`conj:producer`);
* legality of the seeds (`rem:legality`);
* the inherited/newborn classification of zero returns beyond `inherited`.
  That every zero return of `(σ u, σ v)` is inherited or interior to an
  inflated block follows from `red_subst` and `zero_return_iff`, through a
  partial-sum decomposition along the `flatMap`, but it is not stated;
* states as unordered pairs (the quotient by side swap).  Everything here is
  on ordered pairs, i.e. on the swap-closed double cover; the "up to side
  swap" of `thm:G1b1` is absorbed by `seeds_swapClosed`;
* that swap closure preserves SCC or recurrence structure, or the spectral
  data of `N_C`.  Only the hypotheses needed to build a `Normalisation` are
  shown to be preserved;
* the depth-`n` path form inside a `ChildSystem` (`ChildSystem.desc`) needs a
  given finite, child-closed `C` (`redSystem_desc`, or `bpaSystem_desc`
  under G1).  Without finiteness, the path form is `descR` together with
  `reflTransGen_child_iff` and `mem_bpaStates_iff_red`.

The `n = 0` case of `redSystem_desc` and `descR_succ` needs `IsBlock T`
(`redSystem_desc_of_isBlock`, `descR_of_isBlock`): a state of `C` need not be
irreducible, and then `desc 0 T = [T] ≠ red T.1 T.2` (`tmReducibleSystem`).
-/
import PscVerif.Reduction

namespace Psc.Descendants

open Psc.Binomial Psc.Reduction Psc.SignedCocycle

variable {α : Type*} [DecidableEq α]

/-! ### `red` commutes with concatenation -/

theorem flatMap_red_top (bs : List (List α × List α))
    (h : ∀ T ∈ bs, T.1.length = T.2.length) :
    ((bs.flatMap fun T => red T.1 T.2).map Prod.fst).flatten = (bs.map Prod.fst).flatten := by
  induction bs with
  | nil => rfl
  | cons T bs ih =>
    simp only [List.flatMap_cons, List.map_append, List.flatten_append, List.map_cons,
      List.flatten_cons, red_top (h T (by simp)), ih fun T' hT' => h T' (by simp [hT'])]

theorem flatMap_red_bot (bs : List (List α × List α))
    (h : ∀ T ∈ bs, T.1.length = T.2.length) :
    ((bs.flatMap fun T => red T.1 T.2).map Prod.snd).flatten = (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => rfl
  | cons T bs ih =>
    simp only [List.flatMap_cons, List.map_append, List.flatten_append, List.map_cons,
      List.flatten_cons, red_bot (h T (by simp)), ih fun T' hT' => h T' (by simp [hT'])]

/-- **(a)** The reduction of a concatenation of balanced pieces is the
concatenation of their reductions. -/
theorem red_flatten (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv1 T.1 T.2) :
    red (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten = bs.flatMap fun T => red T.1 T.2 :=
  (red_unique _ (fun U hU => by
      obtain ⟨T, hT, hU⟩ := List.mem_flatMap.1 hU
      exact red_isBlock (h T hT) U hU)
    (flatMap_red_top bs fun T hT => (h T hT).length_eq)
    (flatMap_red_bot bs fun T hT => (h T hT).length_eq)).symm

theorem red_append {u v u' v' : List α} (h : Equiv1 u v) (h' : Equiv1 u' v') :
    red (u ++ u') (v ++ v') = red u v ++ red u' v' := by
  simpa using red_flatten [(u, v), (u', v')] (by simp [h, h'])

/-- A block is its own reduction. -/
theorem red_of_isBlock {T : List α × List α} (hT : IsBlock T) : red T.1 T.2 = [T] :=
  (red_unique [T] (by simpa using hT) (by simp) (by simp)).symm

/-- The reduction of `(w, w)` consists of the coincidence blocks `(c, c)`. -/
theorem red_self (w : List α) : red w w = w.map fun c => ([c], [c]) := by
  have hw : (w.map fun c => [c]).flatten = w := by
    rw [← List.flatMap_def]; exact List.flatMap_singleton' w
  refine (red_unique _ ?_ (by rw [List.map_map]; exact hw) (by rw [List.map_map]; exact hw)).symm
  simp only [List.mem_map]
  rintro _ ⟨c, _, rfl⟩
  exact ⟨by simp, fun _ => rfl, fun k hk hk' => by simp at hk'; omega⟩

/-! ### Inflation: `lem:inherited` and `red` commuting with `σⁿ` -/

/-- **`lem:inherited`.**  A zero return `k` of `(u, v)` gives the zero return
`K = |σ(u[k])| = |σ(v[k])|` of `(σ u, σ v)`. -/
theorem inherited (s : α → List α) {u v : List α} {k : ℕ}
    (h : Equiv1 (u.take k) (v.take k)) :
    (subst s (u.take k)).length = (subst s (v.take k)).length ∧
      Equiv1 ((subst s u).take (subst s (u.take k)).length)
        ((subst s v).take (subst s (u.take k)).length) := by
  have hK := (equiv1_subst s h).length_eq
  have e (w : List α) (K : ℕ) (hw : (subst s (w.take k)).length = K) :
      (subst s w).take K = subst s (w.take k) := by
    conv_lhs => rw [← List.take_append_drop k w, subst_append]
    exact List.take_left' hw
  refine ⟨hK, ?_⟩
  rw [e u _ rfl, e v _ hK.symm]
  exact equiv1_subst s h

theorem equiv1_iterate_subst (s : α → List α) (n : ℕ) {x y : List α} (h : Equiv1 x y) :
    Equiv1 ((subst s)^[n] x) ((subst s)^[n] y) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact equiv1_subst s ih

/-- **(b)** `red` commutes with inflation: for balanced `u, v`, the blocks of
`red (σⁿ u) (σⁿ v)` are those of the inflated blocks of `red u v`, in order. -/
theorem red_iterate_subst (s : α → List α) (n : ℕ) {u v : List α} (h : Equiv1 u v) :
    red ((subst s)^[n] u) ((subst s)^[n] v) =
      (red u v).flatMap fun T => red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  set f : List α × List α → List α × List α :=
    fun T => ((subst s)^[n] T.1, (subst s)^[n] T.2)
  have hu : (subst s)^[n] u = (((red u v).map f).map Prod.fst).flatten := by
    conv_lhs => rw [← red_top h.length_eq]
    rw [iterate_subst_flatten, List.map_map, List.map_map]; rfl
  have hv : (subst s)^[n] v = (((red u v).map f).map Prod.snd).flatten := by
    conv_lhs => rw [← red_bot h.length_eq]
    rw [iterate_subst_flatten, List.map_map, List.map_map]; rfl
  rw [hu, hv, red_flatten, List.flatMap_map]
  simp only [List.mem_map]
  rintro _ ⟨T, hT, rfl⟩
  exact equiv1_iterate_subst s n (red_isBlock h T hT).2.1

/-- **(b)** The case `n = 1`: the blocks of `red (σ u) (σ v)` are the children
of the blocks of `red u v`. -/
theorem red_subst (s : α → List α) {u v : List α} (h : Equiv1 u v) :
    red (subst s u) (subst s v) = (red u v).flatMap fun T => red (subst s T.1) (subst s T.2) :=
  red_iterate_subst s 1 h

/-! ### The boundaries of `red u v` are the zero returns -/

omit [DecidableEq α] in
/-- The tracks `p` of the first `j` pieces form the prefix of the
concatenation whose length is their partial sum (`List.take_sum_flatten`). -/
theorem take_flatten_map (p : List α × List α → List α) (bs : List (List α × List α))
    (j : ℕ) :
    (bs.map p).flatten.take ((bs.take j).map fun T => (p T).length).sum =
      ((bs.take j).map p).flatten := by
  simpa [List.map_take, List.map_map, Function.comp_def] using List.take_sum_flatten (bs.map p) j

theorem take_red_top {u v : List α} (h : u.length = v.length) (j : ℕ) :
    u.take (((red u v).take j).map fun T => T.1.length).sum =
      (((red u v).take j).map Prod.fst).flatten := by
  have := take_flatten_map Prod.fst (red u v) j
  rwa [red_top h] at this

theorem take_red_bot {u v : List α} (h : u.length = v.length) (j : ℕ) :
    v.take (((red u v).take j).map fun T => T.2.length).sum =
      (((red u v).take j).map Prod.snd).flatten := by
  have := take_flatten_map Prod.snd (red u v) j
  rwa [red_bot h] at this

/-- **(f)** The boundaries between the blocks of `red u v` are exactly the zero
returns: for balanced `u, v` and `k ≤ |u|`, `(u[k], v[k])` is balanced iff `k`
is a partial sum of the block lengths of `red u v`. -/
theorem zero_return_iff {u v : List α} (h : Equiv1 u v) {k : ℕ} (hk : k ≤ u.length) :
    Equiv1 (u.take k) (v.take k) ↔
      ∃ j, (((red u v).take j).map fun T => T.1.length).sum = k := by
  constructor
  · intro hk'
    have hd : Equiv1 (u.drop k) (v.drop k) :=
      equiv1_cancel hk' (by rwa [List.take_append_drop, List.take_append_drop])
    have hsplit := red_append hk' hd
    rw [List.take_append_drop, List.take_append_drop] at hsplit
    refine ⟨(red (u.take k) (v.take k)).length, ?_⟩
    have e : ((red (u.take k) (v.take k)).map fun T => T.1.length).sum = (u.take k).length := by
      conv_rhs => rw [← red_top hk'.length_eq]
      simp [List.length_flatten, Function.comp_def]
    rw [hsplit, List.take_left' rfl, e, List.length_take, min_eq_left hk]
  · rintro ⟨j, rfl⟩
    have hb : ∀ T ∈ (red u v).take j, Equiv1 T.1 T.2 :=
      fun T hT => (red_isBlock h T (List.mem_of_mem_take hT)).2.1
    have hlen : (((red u v).take j).map fun T => T.1.length).sum =
        (((red u v).take j).map fun T => T.2.length).sum :=
      congrArg List.sum (List.map_congr_left fun T hT => (hb T hT).length_eq)
    rw [take_red_top h.length_eq, hlen, take_red_bot h.length_eq]
    exact equiv1_join _ hb

/-! ### `lem:descendants` in the child graph, without finiteness -/

/-- `U` is a child of `T` (`def:bpa`): a block of `red (σ T.1) (σ T.2)`.  The
children of every state are formed, coincidence blocks included (`ChildNC` is
the manuscript's relation with terminal coincidence blocks). -/
def Child (s : α → List α) (T U : List α × List α) : Prop :=
  U ∈ red (subst s T.1) (subst s T.2)

/-- The ends of the directed paths of length `n` from `T` in the child graph,
in order and with multiplicity (a state's children are listed with
multiplicity).  No finite state set is assumed. -/
def descR (s : α → List α) : ℕ → List α × List α → List (List α × List α)
  | 0, T => [T]
  | n + 1, T => (red (subst s T.1) (subst s T.2)).flatMap (descR s n)

section DescR

variable (s : α → List α)

/-- A depth-`(n+1)` descendant of `T` is a depth-`n` descendant of a child. -/
theorem mem_descR_succ {n : ℕ} {T U : List α × List α} :
    U ∈ descR s (n + 1) T ↔ ∃ V, Child s T V ∧ U ∈ descR s n V := by
  simp only [descR, List.mem_flatMap, Child]

/-- `lem:descendants` for a balanced state at depth `n + 1 ≥ 1`. -/
theorem descR_succ (n : ℕ) : ∀ {T : List α × List α}, Equiv1 T.1 T.2 →
    descR s (n + 1) T = red ((subst s)^[n + 1] T.1) ((subst s)^[n + 1] T.2) := by
  induction n with
  | zero => intro T _; exact List.flatMap_singleton' _
  | succ n ih =>
    intro T h
    have hσ := equiv1_subst s h
    rw [Function.iterate_succ_apply _ (n + 1), Function.iterate_succ_apply _ (n + 1),
      red_iterate_subst s (n + 1) hσ]
    exact List.flatMap_congr fun V hV => ih (red_isBlock hσ V hV).2.1

/-- **(c)** **`lem:descendants`**, with no finiteness assumption: for a block `T`
and every `n ≥ 0`, the ends of the length-`n` paths from `T` in the child
graph, in order and with multiplicity, are the blocks of
`red (σⁿ T.1) (σⁿ T.2)`. -/
theorem descR_of_isBlock (n : ℕ) {T : List α × List α} (hT : IsBlock T) :
    descR s n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  cases n with
  | zero => exact (red_of_isBlock hT).symm
  | succ n => exact descR_succ s n hT.2.1

/-- **(c)** The boundary clause of `lem:descendants`, with no finiteness
assumption: for a block `T`, the boundaries between the depth-`n` descendants
are exactly the zero returns of `(σⁿ T.1, σⁿ T.2)`. -/
theorem descR_zero_return (n : ℕ) {T : List α × List α} (hT : IsBlock T) {k : ℕ}
    (hk : k ≤ ((subst s)^[n] T.1).length) :
    Equiv1 (((subst s)^[n] T.1).take k) (((subst s)^[n] T.2).take k) ↔
      ∃ j, (((descR s n T).take j).map fun U => U.1.length).sum = k := by
  rw [descR_of_isBlock s n hT]
  exact zero_return_iff (equiv1_iterate_subst s n hT.2.1) hk

/-- Reachability in the child graph is reachability at some finite depth. -/
theorem reflTransGen_iff_mem_descR {T U : List α × List α} :
    Relation.ReflTransGen (Child s) T U ↔ ∃ n, U ∈ descR s n T := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, List.mem_singleton_self _⟩
    | head hTV _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, (mem_descR_succ s).2 ⟨_, hTV, hn⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing T with
    | zero => rw [List.mem_singleton.1 hn]
    | succ n ih =>
      obtain ⟨V, hTV, hV⟩ := (mem_descR_succ s).1 hn
      exact .head hTV (ih hV)

/-- **(c)** **`lem:descendants`, reachability form**, with no finiteness
assumption: from a block `T`, `U` is reachable in the child graph iff it is a
block of `red (σⁿ T.1) (σⁿ T.2)` for some `n`. -/
theorem reflTransGen_child_iff {T U : List α × List α} (hT : IsBlock T) :
    Relation.ReflTransGen (Child s) T U ↔
      ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  rw [reflTransGen_iff_mem_descR]
  exact exists_congr fun n => by rw [descR_of_isBlock s n hT]

end DescR

/-! ### `lem:descendants` in the zero-return child system -/

section RedSystem

variable (s : α → List α) (hs : ∀ a, s a ≠ []) (C : Finset (List α × List α))
  (hC : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [])
  (hclosed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C)

/-- On `C`, the depth-`n` descendants of `Psc.Reduction.redSystem` are those of
the child graph. -/
theorem redSystem_desc_eq_descR (n : ℕ) :
    ∀ T ∈ C, (redSystem s hs C hC hclosed).desc n T = descR s n T := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro T hT
    show ((red (subst s T.1) (subst s T.2)).map _).flatten = _
    rw [descR, List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun V hV => ih V (hclosed T hT V hV))

/-- **(c)** `lem:descendants` for blocks of `C`, at every depth `n ≥ 0`. -/
theorem redSystem_desc_of_isBlock (n : ℕ) (T : List α × List α) (hT : T ∈ C) (hB : IsBlock T) :
    (redSystem s hs C hC hclosed).desc n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  (redSystem_desc_eq_descR s hs C hC hclosed n T hT).trans (descR_of_isBlock s n hB)

/-- **(c)** `lem:descendants`: for every state `T ∈ C` and `n ≥ 1`, the depth-`n`
descendants of `T`, in order and with multiplicity, are the blocks of
`red (σⁿ T.1) (σⁿ T.2)`. -/
theorem redSystem_desc (n : ℕ) (hn : 1 ≤ n) (T : List α × List α) (hT : T ∈ C) :
    (redSystem s hs C hC hclosed).desc n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact (redSystem_desc_eq_descR s hs C hC hclosed _ T hT).trans (descR_succ s m (hC T hT).1)

/-- **(c)** The boundary clause of `lem:descendants`: the boundaries between
the depth-`n` descendants of `T` are exactly the zero returns of
`(σⁿ T.1, σⁿ T.2)`. -/
theorem redSystem_desc_zero_return (n : ℕ) (hn : 1 ≤ n) (T : List α × List α) (hT : T ∈ C)
    {k : ℕ} (hk : k ≤ ((subst s)^[n] T.1).length) :
    Equiv1 (((subst s)^[n] T.1).take k) (((subst s)^[n] T.2).take k) ↔
      ∃ j, ((((redSystem s hs C hC hclosed).desc n T).take j).map fun U => U.1.length).sum
        = k := by
  rw [redSystem_desc s hs C hC hclosed n hn T hT]
  exact zero_return_iff (equiv1_iterate_subst s n (hC T hT).1) hk

end RedSystem

/-! ### Swap closure is without loss of generality for building a normalisation -/

/-- `D` contains every child of each of its states. -/
def ChildClosed (s : α → List α) (D : Set (List α × List α)) : Prop :=
  ∀ T ∈ D, ∀ U, Child s T U → U ∈ D

/-- `D` is closed under side swap. -/
def SwapClosed (D : Set (List α × List α)) : Prop := ∀ T ∈ D, T.swap ∈ D

/-- `D` contains no pair with equal sides (no coincidence block). -/
def CoincidenceFree (D : Set (List α × List α)) : Prop := ∀ T ∈ D, T.1 ≠ T.2

/-- Swapping a parent's sides swaps its children's sides (`red_swap`). -/
theorem child_swap {s : α → List α} {T U : List α × List α} (h : Child s T U) :
    Child s T.swap U.swap := by
  unfold Child at *
  rw [Prod.fst_swap, Prod.snd_swap, red_swap]
  exact List.mem_map.2 ⟨U, h, rfl⟩

omit [DecidableEq α] in
theorem mem_image_swap {D : Set (List α × List α)} {T : List α × List α} :
    T ∈ Prod.swap '' D ↔ T.swap ∈ D := by
  rw [Set.image_swap_eq_preimage_swap]; rfl

section SwapClosure

variable {s : α → List α} {D : Set (List α × List α)}

/-- **(d)** The swap closure of a child-closed set is child-closed. -/
theorem swapClosure_childClosed (h : ChildClosed s D) : ChildClosed s (D ∪ Prod.swap '' D) := by
  rintro T (hT | hT) U hU
  · exact Or.inl (h T hT U hU)
  · refine Or.inr (mem_image_swap.2 (h _ (mem_image_swap.1 hT) _ ?_))
    simpa using child_swap hU

omit [DecidableEq α] in
/-- **(d)** The swap closure is swap-closed. -/
theorem swapClosure_swapClosed : SwapClosed (D ∪ Prod.swap '' D) := by
  rintro T (hT | hT)
  · exact Or.inr (mem_image_swap.2 (by simpa using hT))
  · exact Or.inl (by simpa using mem_image_swap.1 hT)

omit [DecidableEq α] in
/-- **(d)** The swap closure of a coincidence-free set is coincidence-free. -/
theorem swapClosure_coincidenceFree (h : CoincidenceFree D) :
    CoincidenceFree (D ∪ Prod.swap '' D) := by
  rintro T (hT | hT)
  · exact h T hT
  · exact fun e => h _ (mem_image_swap.1 hT) e.symm

/-- **(d)** The swap closure of a set of balanced pairs with nonempty tracks is
again one. -/
theorem swapClosure_balanced (h : ∀ T ∈ D, Equiv1 T.1 T.2 ∧ T.1 ≠ []) :
    ∀ T ∈ D ∪ Prod.swap '' D, Equiv1 T.1 T.2 ∧ T.1 ≠ [] := by
  rintro T (hT | hT)
  · exact h T hT
  · obtain ⟨hE, hne⟩ := h _ (mem_image_swap.1 hT)
    simp only [Prod.fst_swap, Prod.snd_swap] at hE hne
    exact ⟨fun a => (hE a).symm,
      fun e => hne (List.length_eq_zero_iff.mp (hE.length_eq.trans (by simp [e])))⟩

omit [DecidableEq α] in
theorem subset_swapClosure : D ⊆ D ∪ Prod.swap '' D := Set.subset_union_left

omit [DecidableEq α] in
/-- The swap closure is the least swap-closed superset. -/
theorem swapClosure_subset {E : Set (List α × List α)} (hE : SwapClosed E) (hDE : D ⊆ E) :
    D ∪ Prod.swap '' D ⊆ E := by
  rintro T (hT | hT)
  · exact hDE hT
  · simpa using hE _ (hDE (mem_image_swap.1 hT))

end SwapClosure

section SwapClosureFinset

variable {s : α → List α} {D : Finset (List α × List α)}

theorem coe_swapClosureF (D : Finset (List α × List α)) :
    ((D ∪ D.image Prod.swap : Finset _) : Set (List α × List α)) =
      ↑D ∪ Prod.swap '' ↑D := by
  rw [Finset.coe_union, Finset.coe_image]

/-- **(d)**, `Finset` form: `D ∪ D.image Prod.swap` is child-closed when `D` is. -/
theorem swapClosureF_childClosed (h : ChildClosed s ↑D) :
    ChildClosed s ↑(D ∪ D.image Prod.swap) := by
  rw [coe_swapClosureF]; exact swapClosure_childClosed h

theorem swapClosureF_swapClosed :
    SwapClosed (↑(D ∪ D.image Prod.swap) : Set (List α × List α)) := by
  rw [coe_swapClosureF]; exact swapClosure_swapClosed

theorem swapClosureF_coincidenceFree (h : CoincidenceFree (↑D : Set (List α × List α))) :
    CoincidenceFree (↑(D ∪ D.image Prod.swap) : Set (List α × List α)) := by
  rw [coe_swapClosureF]; exact swapClosure_coincidenceFree h

theorem swapClosureF_balanced (h : ∀ T ∈ D, Equiv1 T.1 T.2 ∧ T.1 ≠ []) :
    ∀ T ∈ D ∪ D.image Prod.swap, Equiv1 T.1 T.2 ∧ T.1 ≠ [] := fun T hT =>
  swapClosure_balanced (D := ↑D) h T (by rw [← coe_swapClosureF]; exact hT)

end SwapClosureFinset

/-! ### Lexicographic normalized representatives -/

section Lex

variable [LinearOrder α] (s : α → List α) (hs : ∀ a, s a ≠ [])
  (C : Finset (List α × List α))
  (hC : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [])
  (hclosed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C)

/-- The manuscript's normalized representatives (`def:balanced`): for a
swap-closed, coincidence-free `C` over a linearly ordered alphabet, the states
whose first side is lexicographically smaller form a normalisation of
`redSystem`. -/
def lexNormalisation (hswap : ∀ T ∈ C, T.swap ∈ C) (hnc : ∀ T ∈ C, T.1 ≠ T.2) :
    Normalisation (redSystem s hs C hC hclosed) :=
  redNormalisation s hs C hC hclosed hswap (C.filter fun T => T.1 < T.2)
    (Finset.filter_subset _ _)
    (fun T hT => (lt_or_gt_of_ne (hnc T hT)).imp (fun h => Finset.mem_filter.2 ⟨hT, h⟩)
      (fun h => Finset.mem_filter.2 ⟨hswap T hT, h⟩))
    (fun _ hT hT' => lt_asymm (Finset.mem_filter.1 hT).2 (Finset.mem_filter.1 hT').2)

end Lex

/-! ### Reachability from the seeds (`def:bpa`) -/

/-- The states reachable from `S` by iterating the child relation. -/
def Reachable (s : α → List α) (S : Set (List α × List α)) : Set (List α × List α) :=
  {U | ∃ T ∈ S, Relation.ReflTransGen (Child s) T U}

section Reachable

variable {s : α → List α} {S : Set (List α × List α)}

theorem subset_reachable : S ⊆ Reachable s S := fun T hT => ⟨T, hT, .refl⟩

theorem reachable_childClosed : ChildClosed s (Reachable s S) :=
  fun _ ⟨T, hT, hTV⟩ _ hVU => ⟨T, hT, hTV.tail hVU⟩

/-- The reachable set is the least child-closed superset of `S`. -/
theorem reachable_subset {D : Set (List α × List α)} (hSD : S ⊆ D) (hD : ChildClosed s D) :
    Reachable s S ⊆ D := by
  rintro U ⟨T, hT, hTU⟩
  induction hTU with
  | refl => exact hSD hT
  | tail _ hVU ih => exact hD _ ih _ hVU

/-- **(e)** The states reachable from a swap-closed seed set are swap-closed. -/
theorem reachable_swapClosed (hS : SwapClosed S) : SwapClosed (Reachable s S) := by
  rintro U ⟨T, hT, hTU⟩
  exact ⟨T.swap, hS T hT, hTU.lift Prod.swap fun _ _ h => child_swap h⟩

/-- **(e)** The states reachable from balanced seeds are balanced. -/
theorem reachable_equiv1 (hS : ∀ T ∈ S, Equiv1 T.1 T.2) :
    ∀ U ∈ Reachable s S, Equiv1 U.1 U.2 := by
  rintro U ⟨T, hT, hTU⟩
  induction hTU with
  | refl => exact hS T hT
  | tail _ hVU ih => exact (red_isBlock (equiv1_subst s ih) _ hVU).2.1

/-- **(e)** The states reachable from blocks are blocks. -/
theorem reachable_isBlock (hS : ∀ T ∈ S, IsBlock T) : ∀ U ∈ Reachable s S, IsBlock U := by
  rintro U ⟨T, hT, hTU⟩
  rcases hTU.cases_tail with rfl | ⟨V, hTV, hVU⟩
  · exact hS _ hT
  · exact red_isBlock (equiv1_subst s (reachable_equiv1 (fun T hT => (hS T hT).2.1) V
      ⟨T, hT, hTV⟩)) U hVU

end Reachable

/-- The seeds `(ab, ba)`, `a ≠ b`, of `def:bpa`, as ordered pairs. -/
def seeds [Fintype α] : Finset (List α × List α) :=
  (Finset.univ.filter fun p : α × α => p.1 ≠ p.2).image fun p => ([p.1, p.2], [p.2, p.1])

theorem mem_seeds [Fintype α] {T : List α × List α} :
    T ∈ seeds ↔ ∃ a b, a ≠ b ∧ T = ([a, b], [b, a]) := by
  simp only [seeds, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor <;> rintro ⟨a, b, hab, rfl⟩ <;> exact ⟨a, b, hab, rfl⟩

theorem seed_isBlock {a b : α} (hab : a ≠ b) : IsBlock ([a, b], [b, a]) := by
  refine ⟨by simp, equiv1_iff_perm.2 (List.Perm.swap b a []), fun k hk hk' hE => ?_⟩
  obtain rfl : k = 1 := by simp at hk'; omega
  have := hE a
  simp [Ne.symm hab] at this

/-- **(e)** The seeds are swap-closed. -/
theorem seeds_swapClosed [Fintype α] :
    SwapClosed ((seeds : Finset (List α × List α)) : Set (List α × List α)) := by
  intro T hT
  obtain ⟨a, b, hab, rfl⟩ := mem_seeds.1 hT
  exact mem_seeds.2 ⟨b, a, hab.symm, rfl⟩

/-- **(e)** The seeds are blocks. -/
theorem seeds_isBlock [Fintype α] :
    ∀ T ∈ (seeds : Finset (List α × List α)), IsBlock T := by
  intro T hT
  obtain ⟨a, b, hab, rfl⟩ := mem_seeds.1 hT
  exact seed_isBlock hab

/-- The states reachable from the seeds in the full child graph `Child`, as
ordered pairs.  This is *not* the vertex set of `B_σ` (`bpaStatesNC`), whose
coincidence blocks are terminal: it also contains the coincidence blocks
reachable from coincidence blocks (`fib_bpaStates`).  The two agree on
noncoincident states (`mem_bpaStatesNC_iff`) and are finite together
(`finite_bpaStates_iff`). -/
def bpaStates [Fintype α] (s : α → List α) : Set (List α × List α) :=
  Reachable s ↑(seeds : Finset (List α × List α))

section Bpa

variable [Fintype α] (s : α → List α)

theorem seeds_subset_bpaStates : ↑(seeds : Finset (List α × List α)) ⊆ bpaStates s :=
  subset_reachable

theorem bpaStates_childClosed : ChildClosed s (bpaStates s) := reachable_childClosed

/-- **(e)** The reachable states are swap-closed. -/
theorem bpaStates_swapClosed : SwapClosed (bpaStates s) := reachable_swapClosed seeds_swapClosed

/-- **(e)** Every reachable state is an irreducible balanced pair. -/
theorem bpaStates_isBlock : ∀ T ∈ bpaStates s, IsBlock T := reachable_isBlock seeds_isBlock

/-- **(e)** Every reachable state is balanced. -/
theorem bpaStates_equiv1 : ∀ T ∈ bpaStates s, Equiv1 T.1 T.2 :=
  fun T hT => (bpaStates_isBlock s T hT).2.1

/-- **`lem:descendants` at the seeds**, with no finiteness assumption: the
reachable states are exactly the blocks of `red (σⁿ ab) (σⁿ ba)`, over the
seeds `(ab, ba)` and the depths `n`. -/
theorem mem_bpaStates_iff_red {U : List α × List α} :
    U ∈ bpaStates s ↔ ∃ T ∈ (seeds : Finset (List α × List α)), ∃ n,
      U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  exists_congr fun T => and_congr_right fun hT =>
    reflTransGen_child_iff s (seeds_isBlock T hT)

end Bpa

/-! ### The manuscript's `B_σ`: coincidence blocks are terminal -/

/-- The children of a coincidence block are coincidence blocks. -/
theorem child_coincident {s : α → List α} {T U : List α × List α} (hT : T.1 = T.2)
    (hU : Child s T U) : U.1 = U.2 := by
  unfold Child at hU
  rw [hT, red_self] at hU
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hU
  rfl

/-- The manuscript's child relation: coincidence blocks are terminal. -/
def ChildNC (s : α → List α) (T U : List α × List α) : Prop := T.1 ≠ T.2 ∧ Child s T U

/-- A noncoincident state reachable through `Child` is reachable through
`ChildNC`: forming the children of coincidence blocks adds only coincidence
blocks. -/
theorem reflTransGen_childNC {s : α → List α} {T U : List α × List α}
    (h : Relation.ReflTransGen (Child s) T U) (hU : U.1 ≠ U.2) :
    Relation.ReflTransGen (ChildNC s) T U := by
  induction h with
  | refl => exact .refl
  | tail _ hVU ih =>
    have hV := fun e => hU (child_coincident e hVU)
    exact (ih hV).tail ⟨hV, hVU⟩

/-- A coincidence block is a pair `([c], [c])` (`def:balanced`). -/
theorem eq_coincidence_of_isBlock {T : List α × List α} (hT : IsBlock T) (h : T.1 = T.2) :
    ∃ c, T = ([c], [c]) := by
  obtain ⟨u, v⟩ := T
  obtain rfl : u = v := h
  obtain ⟨hne, -, hirr⟩ := hT
  rcases u with _ | ⟨c, _ | ⟨b, w⟩⟩
  · exact absurd rfl hne
  · exact ⟨c, rfl⟩
  · exact absurd (fun _ => rfl) (hirr 1 Nat.one_pos (by simp))

/-- The vertex set of the balanced-pair automaton `B_σ` of `def:bpa`, as ordered
pairs: the states reachable from the seeds when coincidence blocks are
terminal. -/
def bpaStatesNC [Fintype α] (s : α → List α) : Set (List α × List α) :=
  {U | ∃ T ∈ (seeds : Finset (List α × List α)), Relation.ReflTransGen (ChildNC s) T U}

section BpaNC

variable [Fintype α] (s : α → List α)

theorem bpaStatesNC_subset_bpaStates : bpaStatesNC s ⊆ bpaStates s :=
  fun _ ⟨T, hT, h⟩ => ⟨T, hT, h.lift id fun _ _ h => h.2⟩

/-- `bpaStatesNC s` is the least superset of the seeds containing the children
of each of its noncoincident states. -/
theorem bpaStatesNC_subset {D : Set (List α × List α)}
    (hSD : ↑(seeds : Finset (List α × List α)) ⊆ D)
    (hD : ∀ T ∈ D, T.1 ≠ T.2 → ∀ U, Child s T U → U ∈ D) : bpaStatesNC s ⊆ D := by
  rintro U ⟨T, hT, hTU⟩
  induction hTU with
  | refl => exact hSD hT
  | tail _ hVU ih => exact hD _ ih hVU.1 _ hVU.2

/-- `B_σ` and the full child graph have the same noncoincident reachable
states. -/
theorem mem_bpaStatesNC_iff {U : List α × List α} (hU : U.1 ≠ U.2) :
    U ∈ bpaStatesNC s ↔ U ∈ bpaStates s :=
  ⟨fun h => bpaStatesNC_subset_bpaStates s h,
    fun ⟨T, hT, hTU⟩ => ⟨T, hT, reflTransGen_childNC hTU hU⟩⟩

/-- The full child graph adds to `B_σ` only coincidence blocks `(c, c)`. -/
theorem bpaStates_subset_union :
    bpaStates s ⊆ bpaStatesNC s ∪ Set.range fun c : α => ([c], [c]) := by
  intro U hU
  by_cases h : U.1 = U.2
  · obtain ⟨c, rfl⟩ := eq_coincidence_of_isBlock (bpaStates_isBlock s U hU) h
    exact Or.inr ⟨c, rfl⟩
  · exact Or.inl ((mem_bpaStatesNC_iff s h).2 hU)

/-- **The G1 bridge** (`hyp:G1`): over a finite alphabet, `B_σ` is finite iff
the set of states reachable in the full child graph is. -/
theorem finite_bpaStates_iff : (bpaStates s).Finite ↔ (bpaStatesNC s).Finite :=
  ⟨fun h => h.subset (bpaStatesNC_subset_bpaStates s),
    fun h => (h.union (Set.finite_range _)).subset (bpaStates_subset_union s)⟩

/-- The step of `thm:G1b1` that uses `lem:descendants`, with no finiteness
assumption: every vertex of `B_σ` is a block of `red (σⁿ ab) (σⁿ ba)` for some
seed `(ab, ba)` and some `n`. -/
theorem exists_red_of_mem_bpaStatesNC {U : List α × List α} (hU : U ∈ bpaStatesNC s) :
    ∃ T ∈ (seeds : Finset (List α × List α)), ∃ n,
      U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  (mem_bpaStates_iff_red s).1 (bpaStatesNC_subset_bpaStates s hU)

end BpaNC

/-! ### Under G1, the states reachable in the full child graph form a zero-return child system -/

section G1

variable [Fintype α] (s : α → List α) (hs : ∀ a, s a ≠ []) (hfin : (bpaStates s).Finite)

/-- Under G1 (`bpaStates s` finite, equivalently `bpaStatesNC s` finite by
`finite_bpaStates_iff`), the zero-return child system on the states reachable
from the seeds in the full child graph.  It agrees with `B_σ` on noncoincident
states. -/
noncomputable def bpaSystem : ChildSystem α :=
  redSystem s hs hfin.toFinset
    (fun T hT => ⟨(bpaStates_isBlock s T (hfin.mem_toFinset.1 hT)).2.1,
      (bpaStates_isBlock s T (hfin.mem_toFinset.1 hT)).1⟩)
    (fun T hT U hU => hfin.mem_toFinset.2 (bpaStates_childClosed s T (hfin.mem_toFinset.1 hT) U hU))

theorem bpaSystem_swap : ∀ T ∈ (bpaSystem s hs hfin).C, T.swap ∈ (bpaSystem s hs hfin).C :=
  fun T hT => hfin.mem_toFinset.2 (bpaStates_swapClosed s T (hfin.mem_toFinset.1 hT))

/-- Under G1, `lem:descendants` holds on `bpaSystem` at every depth `n ≥ 0`. -/
theorem bpaSystem_desc (n : ℕ) (T : List α × List α) (hT : T ∈ (bpaSystem s hs hfin).C) :
    (bpaSystem s hs hfin).desc n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  redSystem_desc_of_isBlock s hs _ _ _ n T hT (bpaStates_isBlock s T (hfin.mem_toFinset.1 hT))

/-- Under G1, the boundary clause of `lem:descendants` on `bpaSystem`, at every
depth `n ≥ 0`. -/
theorem bpaSystem_desc_zero_return (n : ℕ) (T : List α × List α)
    (hT : T ∈ (bpaSystem s hs hfin).C) {k : ℕ} (hk : k ≤ ((subst s)^[n] T.1).length) :
    Equiv1 (((subst s)^[n] T.1).take k) (((subst s)^[n] T.2).take k) ↔
      ∃ j, ((((bpaSystem s hs hfin).desc n T).take j).map fun U => U.1.length).sum = k := by
  rw [bpaSystem_desc s hs hfin n T hT]
  exact zero_return_iff
    (equiv1_iterate_subst s n (bpaStates_equiv1 s T (hfin.mem_toFinset.1 hT))) hk

end G1

/-! ### Calibrations and controls -/

/-- Two balanced pieces, the second a coincidence block. -/
def flatPieces : List (List (Fin 3) × List (Fin 3)) := [([0, 1, 1, 0], [1, 0, 0, 1]), ([2], [2])]

example : ∀ T ∈ flatPieces, Equiv1 T.1 T.2 := by decide

/-- Calibration of `red_flatten`: both sides, computed. -/
example : red (flatPieces.map Prod.fst).flatten (flatPieces.map Prod.snd).flatten =
    flatPieces.flatMap (fun T => red T.1 T.2) := by decide

example : red (flatPieces.map Prod.fst).flatten (flatPieces.map Prod.snd).flatten =
    [([0, 1], [1, 0]), ([1, 0], [0, 1]), ([2], [2])] := by decide

/-- Negative control: `red_flatten` needs balanced pieces.  The unbalanced
`(0, 1)`, `(1, 0)` concatenate to the single block `(01, 10)`. -/
example : red ([0, 1] : List (Fin 2)) [1, 0] ≠ red [0] [1] ++ red [1] [0] := by decide

/-- The Tribonacci substitution `0 ↦ 01`, `1 ↦ 02`, `2 ↦ 0`. -/
def tribSubst : Fin 3 → List (Fin 3) := fun a =>
  if a = 0 then [0, 1] else if a = 1 then [0, 2] else [0]

/-- Calibration of `red_subst`: `(σ 12, σ 21) = (020, 002)` is balanced, and
`red (σ² 12) (σ² 21) = red (01001) (01010)` is the concatenation of the
reductions of the inflated blocks `(0, 0)`, `(20, 02)`, including a newborn
zero return. -/
example : Equiv1 (subst tribSubst [1, 2]) (subst tribSubst [2, 1]) := by decide

example : red (subst tribSubst [1, 2]) (subst tribSubst [2, 1]) =
    [([0], [0]), ([2, 0], [0, 2])] := by
  decide

example : red ((subst tribSubst)^[2] [1, 2]) ((subst tribSubst)^[2] [2, 1]) =
    (red (subst tribSubst [1, 2]) (subst tribSubst [2, 1])).flatMap
      fun T => red (subst tribSubst T.1) (subst tribSubst T.2) := by decide

example : red ((subst tribSubst)^[2] [1, 2]) ((subst tribSubst)^[2] [2, 1]) =
    [([0], [0]), ([1], [1]), ([0], [0]), ([0, 1], [1, 0])] := by decide

/-- Calibration of `red_iterate_subst` at `n = 2` on the reducible pair
`(0110, 1001)`: both sides, computed. -/
example : red ((subst tribSubst)^[2] [0, 1, 1, 0]) ((subst tribSubst)^[2] [1, 0, 0, 1]) =
    (red [0, 1, 1, 0] [1, 0, 0, 1]).flatMap
      fun T => red ((subst tribSubst)^[2] T.1) ((subst tribSubst)^[2] T.2) := by decide

/-- Non-vacuity of `zero_return_iff`: `k = 2` is the zero return of
`(0110, 1001)`, the partial sum of the first block length. -/
example : Equiv1 (([0, 1, 1, 0] : List (Fin 2)).take 2) (([1, 0, 0, 1] : List (Fin 2)).take 2) :=
  (zero_return_iff (by decide) (by decide)).2 ⟨1, by decide⟩

/-- **(g)** `lem:descendants` at depth two on `tmRedSystem`, computed. -/
example : tmRedSystem.desc 2 tmPair =
    red ((subst thueMorseSubst)^[2] tmPair.1) ((subst thueMorseSubst)^[2] tmPair.2) := by decide

example : tmRedSystem.desc 2 tmPair = [tmPair, tmPair.swap, tmPair.swap, tmPair] := by decide

/-- A `redSystem` containing a reducible state: Thue–Morse with `(0110, 1001)`
adjoined. -/
def tmReducibleSystem : ChildSystem (Fin 2) :=
  redSystem thueMorseSubst (by decide)
    {([0, 1, 1, 0], [1, 0, 0, 1]), tmPair, tmPair.swap} (by decide) (by decide)

/-- `1 ≤ n` in `redSystem_desc` is sharp: at `n = 0` the reducible state
`(0110, 1001)` is its own depth-`0` descendant, not the two blocks of its
reduction. -/
example : tmReducibleSystem.desc 0 ([0, 1, 1, 0], [1, 0, 0, 1]) ≠
    red [0, 1, 1, 0] [1, 0, 0, 1] := by decide

example : tmReducibleSystem.desc 1 ([0, 1, 1, 0], [1, 0, 0, 1]) =
    red (subst thueMorseSubst [0, 1, 1, 0]) (subst thueMorseSubst [1, 0, 0, 1]) := by decide

example : tmReducibleSystem.desc 2 ([0, 1, 1, 0], [1, 0, 0, 1]) =
    red ((subst thueMorseSubst)^[2] [0, 1, 1, 0]) ((subst thueMorseSubst)^[2] [1, 0, 0, 1]) := by
  decide

/-- `0 ↦ 010`, `1 ↦ 101`: `σ(01, 10) = (010101, 101010)` splits into three
copies of `(01, 10)`. -/
def altSubst : Fin 2 → List (Fin 2) := fun a => if a = 0 then [0, 1, 0] else [1, 0, 1]

example : red (subst altSubst tmPair.1) (subst altSubst tmPair.2) = [tmPair, tmPair, tmPair] := by
  decide

/-- Non-vacuity of (d): `D = {(01, 10)}` is child-closed for `altSubst`,
coincidence-free, and not swap-closed; its swap closure is `{(01,10), (10,01)}`. -/
theorem alt_childClosed :
    ChildClosed altSubst ↑({tmPair} : Finset (List (Fin 2) × List (Fin 2))) :=
  fun T hT U hU => (by decide : ∀ T ∈ ({tmPair} : Finset _),
    ∀ U ∈ red (subst altSubst T.1) (subst altSubst T.2), U ∈ ({tmPair} : Finset _)) T hT U hU

example : CoincidenceFree
    (({tmPair} : Finset (List (Fin 2) × List (Fin 2))) : Set (List (Fin 2) × List (Fin 2))) := by
  intro T hT; rw [Finset.mem_coe, Finset.mem_singleton] at hT; subst hT; decide

example : ¬ SwapClosed
    (({tmPair} : Finset (List (Fin 2) × List (Fin 2))) : Set (List (Fin 2) × List (Fin 2))) :=
  fun h => absurd (h tmPair (Finset.mem_coe.2 (Finset.mem_singleton_self _))) (by decide)

example : ({tmPair} ∪ ({tmPair} : Finset (List (Fin 2) × List (Fin 2))).image Prod.swap) =
    {tmPair, tmPair.swap} := by decide

/-- The swap closure of `{(01, 10)}` for `altSubst`, as a `redSystem`, with its
lexicographic normalisation `R = {(01, 10)}`. -/
def altSwapSystem : ChildSystem (Fin 2) :=
  redSystem altSubst (by decide) ({tmPair} ∪ ({tmPair} : Finset _).image Prod.swap)
    (swapClosureF_balanced (by decide)) (swapClosureF_childClosed alt_childClosed)

def altLexNormalisation : Normalisation altSwapSystem :=
  lexNormalisation altSubst (by decide) _ _ _ (by decide) (by decide)

example : altLexNormalisation.R = {tmPair} := by decide

/-- `lexNormalisation` of `tmRedSystem` is the hand-written
`Psc.Reduction.tmRedNormalisation`'s `R = {(01, 10)}`. -/
example : (lexNormalisation thueMorseSubst (by decide) {tmPair, tmPair.swap} (by decide)
    (by decide) (by decide) (by decide)).R = tmRedNormalisation.R := by decide

/-- The seeds over two letters. -/
theorem tm_seeds : (seeds : Finset (List (Fin 2) × List (Fin 2))) = {tmPair, tmPair.swap} := by
  decide

example : (seeds : Finset (List (Fin 3) × List (Fin 3))).card = 6 := by decide

/-- The reachable states for Thue–Morse are exactly `(01, 10)`, `(10, 01)`. -/
theorem tm_bpaStates :
    bpaStates thueMorseSubst =
      ↑({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))) := by
  apply Set.Subset.antisymm
  · refine reachable_subset (fun T hT => ?_) (fun T hT U hU => ?_)
    · rw [Finset.mem_coe, tm_seeds] at hT; exact hT
    · exact (by decide : ∀ T ∈ ({tmPair, tmPair.swap} : Finset _),
        ∀ U ∈ red (subst thueMorseSubst T.1) (subst thueMorseSubst T.2),
          U ∈ ({tmPair, tmPair.swap} : Finset _)) T hT U hU
  · rw [← tm_seeds]; exact seeds_subset_bpaStates _

/-- G1 holds for Thue–Morse, and `bpaSystem` has the two states. -/
theorem tm_finite : (bpaStates thueMorseSubst).Finite := tm_bpaStates ▸ Finset.finite_toSet _

example : (bpaSystem thueMorseSubst (by decide) tm_finite).C = {tmPair, tmPair.swap} :=
  Finset.coe_injective (by
    rw [show (bpaSystem thueMorseSubst (by decide) tm_finite).C = tm_finite.toFinset from rfl,
      Set.Finite.coe_toFinset, tm_bpaStates])

/-- The Fibonacci substitution `0 ↦ 01`, `1 ↦ 0`.  The seed `(01, 10)` has the
coincidence child `(0, 0)`, whose children are `(0, 0)` and `(1, 1)`. -/
def fibSubst : Fin 2 → List (Fin 2) := fun a => if a = 0 then [0, 1] else [0]

/-- The full child graph of Fibonacci reaches four states, `(1, 1)` among them
(through the coincidence block `(0, 0)`). -/
theorem fib_bpaStates :
    bpaStates fibSubst =
      ↑({tmPair, tmPair.swap, ([0], [0]), ([1], [1])} : Finset (List (Fin 2) × List (Fin 2))) := by
  apply Set.Subset.antisymm
  · refine reachable_subset (fun T hT => ?_) (fun T hT U hU => ?_)
    · rw [Finset.mem_coe, tm_seeds] at hT
      exact (by decide : ({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))) ⊆
        {tmPair, tmPair.swap, ([0], [0]), ([1], [1])}) hT
    · exact (by decide : ∀ T ∈ ({tmPair, tmPair.swap, ([0], [0]), ([1], [1])} : Finset _),
        ∀ U ∈ red (subst fibSubst T.1) (subst fibSubst T.2),
          U ∈ ({tmPair, tmPair.swap, ([0], [0]), ([1], [1])} : Finset _)) T hT U hU
  · intro U hU
    rw [mem_bpaStates_iff_red, tm_seeds]
    rw [Finset.mem_coe] at hU
    exact (by decide : ∀ U ∈ ({tmPair, tmPair.swap, ([0], [0]), ([1], [1])} : Finset _),
      ∃ T ∈ ({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))), ∃ n ∈ Finset.range 3,
        U ∈ red ((subst fibSubst)^[n] T.1) ((subst fibSubst)^[n] T.2)) U hU
      |>.imp fun T ⟨hT, n, _, h⟩ => ⟨hT, n, h⟩

/-- The manuscript's `B_σ` for Fibonacci has three vertices: `(1, 1)` is a child
only of the terminal coincidence block `(0, 0)`. -/
theorem fib_bpaStatesNC :
    bpaStatesNC fibSubst =
      ↑({tmPair, tmPair.swap, ([0], [0])} : Finset (List (Fin 2) × List (Fin 2))) := by
  apply Set.Subset.antisymm
  · refine bpaStatesNC_subset _ (fun T hT => ?_) (fun T hT hne U hU => ?_)
    · rw [Finset.mem_coe, tm_seeds] at hT
      exact (by decide : ({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))) ⊆
        {tmPair, tmPair.swap, ([0], [0])}) hT
    · exact (by decide : ∀ T ∈ ({tmPair, tmPair.swap, ([0], [0])} : Finset _), T.1 ≠ T.2 →
        ∀ U ∈ red (subst fibSubst T.1) (subst fibSubst T.2),
          U ∈ ({tmPair, tmPair.swap, ([0], [0])} : Finset _)) T hT hne U hU
  · intro U hU
    rw [Finset.mem_coe] at hU
    have hs : tmPair ∈ (seeds : Finset (List (Fin 2) × List (Fin 2))) := by rw [tm_seeds]; decide
    have hs' : tmPair.swap ∈ (seeds : Finset (List (Fin 2) × List (Fin 2))) := by
      rw [tm_seeds]; decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl
    · exact ⟨_, hs, .refl⟩
    · exact ⟨_, hs', .refl⟩
    · exact ⟨_, hs, .single ⟨by decide, show _ ∈ _ by decide⟩⟩

theorem fib_one_not_mem_bpaStatesNC :
    (([1], [1]) : List (Fin 2) × List (Fin 2)) ∉ bpaStatesNC fibSubst := by
  rw [fib_bpaStatesNC, Finset.mem_coe]; decide

/-- `B_σ` is strictly smaller than `bpaStates`: `(1, 1)` is reachable only
through a coincidence block. -/
example : bpaStatesNC fibSubst ⊂ bpaStates fibSubst :=
  (Set.ssubset_iff_of_subset (bpaStatesNC_subset_bpaStates _)).2
    ⟨([1], [1]), by rw [fib_bpaStates, Finset.mem_coe]; decide, fib_one_not_mem_bpaStatesNC⟩

/-- Negative control for the reading of `lem:descendants`: the depth-`2`
descendants of the seed `(01, 10)` include `(1, 1)`, which is not a vertex of
`B_σ` with terminal coincidence blocks, so no length-`2` path of `B_σ` ends
there. -/
theorem fib_descR_two :
    descR fibSubst 2 tmPair = [([0], [0]), ([1], [1]), ([0], [0]), ([0, 1], [1, 0])] := by
  decide

example : ¬ Relation.ReflTransGen (ChildNC fibSubst) tmPair ([1], [1]) := fun h =>
  fib_one_not_mem_bpaStatesNC ⟨tmPair, by rw [tm_seeds]; decide, h⟩

end Psc.Descendants
