/-
# Binding the prefix-seeded `bpa-W` of Sirvent–Solomyak to `red`

`docs/c4-general-structure-2026-11-06.md` §3, Proposition B′ (its first two
sentences: "By Sirvent–Solomyak's identity, `[u, S^{t_n}u]` reduces into pairs
of `I(W)`, so it has cuts with gaps at most `ℓ`") and Corollary B(i);
`docs/c4-bprime-independent-proof-audit-2026-11-07.md`, proof step 1 (the
reduction/descendant identity, Sirvent–Solomyak (2002) §3, formula (3.1)) and
the first half of step 2 (the cut set of the infinite reduction), the
assumption inventory (recurrence of `u`, which the audit takes from
primitivity), acceptance matrix item 3 (P0: "bind Sirvent–Solomyak (3.1) to
the repository's exact `bpa-W` implementation ... include orientation,
coincidences, and index `I_{n+1}` versus `t_n`");
`docs/c4-bprime-machine-verification-priority-2026-11-07.md`, derivation item 1.

**Setting.** `u : ℕ → α` is an infinite word over an alphabet with decidable
equality, `s : α → List α` a substitution (`σ = subst s`), and `u` a one-sided
fixed point in the prefix sense `IsFixed s u`: the image of every prefix
`u[0, N)` is a prefix of `u`.  `W` is a prefix of `u` (`PrefixOf u W`); then
every `σⁿ(W)` is a prefix of `u` (`prefixOf_iterate`).  Windows are lists:
`win u t N = u[t, t + N)` (`List.ofFn`).  The *aligned pair at shift `t`* is
`(u, Sᵗu)`; its finite windows are `(win u 0 N, win u t N)`.  Orientation: the
first track is always `u` itself, the second the shifted word, as in
Sirvent–Solomyak's `[u, S^{|W|}u]`.  Primitivity is the form used throughout
the repository, `∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c` with
`inc = Psc.Incidence.inc`.

**Definitions.**
* `zeroReturn u t N`: the two length-`N` windows have equal Parikh vectors
  (`Equiv1`); `blocks u t N = red (win u 0 N) (win u t N)`;
* `levelSet u t`: the blocks of `blocks u t N` over all zero returns `N`,
  coincidence blocks `([c], [c])` retained;
* `tn s W n = |σⁿ(W)|`, `Ilevel s u W n = levelSet u (tn s W n)` (the level-`n`
  set `Iₙ(W)`, read as "the blocks of the reduction of `(u, S^{|σⁿ W|} u)`"),
  `IW s u W = ⋃ n, Ilevel s u W n` (the set `I(W)`; *termination* of `bpa-W`
  means that `IW` is finite, not termination with coincidence);
* `ssLevel s u W n`: Sirvent–Solomyak's recursion read literally,
  `ssLevel 0 = I₀(W)` and `ssLevel (n+1)` the red-children (`Psc.Descendants.Child`,
  coincidence blocks included) of the members of `ssLevel n`;
* `prefixParikh u k a = Σ_{i<k} [u i = a]` (the Parikh vector of `u[0, k)` in
  `ℤ`), the discrepancy `gapD u t k a = P k a - (P (t + k) a - P t a)` and
  **`BoundedGaps u t L`**: every `k` has a `k' ∈ [k, k + L]` with
  `gapD u t k' a = 0` for every letter `a`.  These three bodies are, symbol for
  symbol, those of `P`, `D` and the hypothesis `hgap` of
  `Psc.BPrimeCore.cut_bound`; `tn` is the body of `Psc.BPrimeCore.len`; so
  `BoundedGaps u (tn s W n) L` is *definitionally* the `n`-th instance of the
  `hgap` of `Psc.BPrimeCore.bprime_core`.  `D t 0 = 0` is a theorem
  (`gapD_zero`), not a conjunct, as in `BPrimeCore` (`D_zero`);
* `Unbounded u t`: the zero returns at shift `t` are unbounded, the recurrence
  input of Sirvent–Solomyak ("the initial reduction exists ... by uniform
  recurrence"); by `unbounded_iff_recurrent` it says that the Parikh class of
  `u[0, t)` recurs in `u`.

Proved here, in full:

* windows: `length_win`, `win_add` (`u[t, t+N+M) = u[t, t+N) ++ u[t+N, t+N+M)`),
  `take_win`, `win_congr`, `prefixOf_iff_getElem` (`PrefixOf u x` is the body
  of `Psc.BPrimeCore.IsPrefixOf x u`);
* **(a) independence of `N`**: `blocks_prefix` (for zero returns `N ≤ N'`, the
  reduction of the length-`N` windows is a list prefix of that of the
  length-`N'` windows, by `Psc.Descendants.red_append` at the zero return `N`),
  `blocks_subset`, `mem_levelSet_iff_ge` (with `Unbounded`, the zero returns
  `N ≥ K` alone define the same set, for every `K`); `levelSet_isBlock` (every
  member is an irreducible balanced block); `exists_win_of_mem_blocks` (every
  block is an aligned pair of windows `(u[k, k + m), u[t + k, t + k + m))` at a
  zero return `k`); `equiv1_win_succ_iff` (at shift one, `u[k, k + m)` and
  `u[k + 1, k + 1 + m)` are balanced iff `u (k + m) = u k`);
* the gap vocabulary: `prefixParikh_succ`, `prefixParikh_eq_count`, `gapD_zero`,
  `gapD_eq_count`, `zeroReturn_iff_gapD` (zero returns are the common zeros of
  `gapD u t ·`), `boundedGaps_iff_zeroReturn`; the shift/factor identity in
  `Equiv1` form, `zeroReturn_iff_factor` (`zeroReturn u t k ↔
  Equiv1 u[0, t) u[k, k + t)`, the content of `proof/bpa/BpaPrefixBridge.lean`),
  `unbounded_iff_recurrent`;
* the fixed-point window map: with `phi s u t = |σ(u[0, t))|`,
  `subst_win_zero` (`σ(u[0, N)) = u[0, φ N)`), **`subst_win`**
  (`σ(u[t, t+N)) = u[φ t, φ t + |σ(u[t, t+N))|)`, by cancelling the prefix
  `σ(u[0, t)) = u[0, φ t)` in `σ(u[0, t+N))`), `subst_win_of_zeroReturn`,
  `zeroReturn_phi` (inherited zero returns, `lem:inherited`), and
  **`blocks_phi`**: `blocks u (φ t) (φ N)` is the `flatMap` of the children
  `red (σ T.1) (σ T.2)` over `blocks u t N`, by `Psc.Descendants.red_subst`;
* recurrence: `occ_subst` (an occurrence of `x` at `m` gives one of `σ x` at
  `φ m`), `lt_phi` (`N < φ N` for `N > 0` when `|σ(u 0)| ≥ 2`),
  `unbounded_of_head_recurs` (if moreover `u k = u 0` for some `k > 0`, every
  prefix `u[0, t)` occurs at unbounded positions, so `Unbounded u t` holds for
  every `t`), and **from primitivity, for `σ` itself (no power)**:
  `head_recurs_of_primitive` (`Mᵏ > 0` gives `u m = u 0` for some `m > 0`:
  `σᵏ(u 0 u 1) = σᵏ[u 0] σᵏ[u 1]` is a prefix of `u`, and `u 0 ∈ σᵏ[u 1]`),
  `two_le_head_of_primitive` (`Mᵏ > 0` and `|α| ≥ 2` give `|σ(u 0)| ≥ 2`:
  otherwise `σⁿ[u 0] ⊆ {u 0}`, against the positive column of `u 0`),
  `unbounded_of_card_le_one`, and **`unbounded_of_primitive`** (a fixed point of
  a primitive `σ` has unbounded zero returns at every shift; nonerasing is
  `Psc.PrimitiveExpansion.nonerasing_of_primitive`);
* the prefix seed: `prefixOf_subst`, `prefixOf_iterate`, `win_tn`
  (`u[0, tₙ) = σⁿ(W)`), **`tn_succ`** (`t_{n+1} = φ(tₙ)`: the index of
  `I_{n+1}` is the image length of the index of `Iₙ`);
* **(b) Sirvent–Solomyak (3.1)**: `child_mem_levelSet_phi`,
  `child_mem_I_succ` (every red-child of a level-`n` block occurs at level
  `n + 1`; no recurrence needed), `exists_parent`, `exists_parent_I` (every
  level-`(n+1)` block is a red-child of a level-`n` block; uses `Unbounded` at
  level `n` and a nonerasing `s`), **`I_succ`** (the identity
  `I_{n+1}(W) = {T | ∃ U ∈ Iₙ(W), Child s U T}`), **`ssLevel_eq`** (the
  recursive definition equals the window definition at every level),
  `subst_win_tn` (`σ` maps the level-`n` windows of length `N` onto the
  level-`(n+1)` windows of length `φ N`), `unbounded_phi`, `unbounded_tn`
  (recurrence at level `0` propagates to every level), `IW_childClosed` (`I(W)`
  is child-closed, coincidences admitted), `IW_isBlock`, **`IW_eq_reachable`**
  (`I(W)` is the child closure of `I₀(W)` in the full child graph,
  `Psc.Descendants.Reachable`), and their hypothesis-exact forms
  **`I_succ_of_primitive`**, `ssLevel_eq_of_primitive`,
  `IW_eq_reachable_of_primitive` (fixed point, prefix seed, primitivity; no
  recurrence or nonerasing hypothesis) and **`IW_eq_iUnion_ssLevel`**
  (`⋃ₙ ssLevel s u W n = IW s u W`: `I(W)` read literally is the window set);
* **(c) termination**: `exists_bound_of_finite` (a finite `I(W)` has a bound
  `L` on its block lengths), **`boundedGaps_of_bound`** (a bound `L` on the
  block lengths of `levelSet u t` and unbounded zero returns give
  `BoundedGaps u t L`, through `Psc.FixedPointLimit.exists_cut` and
  `Psc.Descendants.zero_return_iff`), `boundedGaps_of_finite` (with
  `Unbounded`), and the hypothesis-exact **`boundedGaps_of_finite_primitive`**
  (fixed point, prefix seed, primitive `σ`, `I(W)` finite: one `L` gives
  `BoundedGaps u tₙ L` at every level `n`, i.e. the `hgap` of
  `Psc.BPrimeCore.bprime_core`);
* the bridge to `Psc.FixedPointLimit`: `isFixed_limit` and `prefixOf_limit`
  (the limit word of a chain `u₀ <+: σ u₀` with growth is a fixed point in the
  sense used here, with `u₀` as a prefix seed); `seedLimit`, `isFixed_seedLimit`,
  `prefixOf_seedLimit` (the same for a nonerasing `σ` and a seed `x <+: σ x` with
  `|x| < |σ x|`, growth supplied; every specimen's fixed point is built here);
* **(d) controls**, all by `decide` on finite data:
  - Fibonacci `0 ↦ 01`, `1 ↦ 0`, `W = 0`, on the genuine fixed point `fibU`
    (the `FixedPointLimit.limit` of `[0]`, matched to `σ⁶(0)` on `[0, 21)`):
    `t₀, t₁, t₂ = 1, 2, 3`; `fib_level0` (the level-0 blocks of the windows of
    length `10` at shift `1`), `fib_phi` (`φ 10 = 16`, `φ 1 = 2`),
    `fib_blocks_phi` (the level-1 blocks of the windows of length `16` at shift
    `2`, and the (3.1) relation between the two windows, computed);
    `fib_one_one_parents` (on these two windows, the level-1 block `(1, 1)` has
    only coincidence parents); `fib_primitive` (`M² > 0`), `fib_unbounded`
    (`unbounded_of_head_recurs`), `fib_I_succ` ((3.1) at every level, from
    `I_succ_of_primitive`) and `fib_ssLevel`;
  - positive control with an irreducible `χ_M` (`X² - X - 1`): **`fib_terminates`**
    (Fibonacci's `bpa-0` terminates: `I(0)` contains `(01, 10)` and is finite).
    `fib_subst_isChain` (no image `σ(w)` contains `11`), `fibU_not_one_one` (so
    neither does `fibU`), `fib_level0_subset` (`I₀(0) ⊆ {(0, 0), (01, 10)}` over
    all zero returns: a block at shift `1` is `0 1^{m-1}` against its shift, and
    `m ≤ 2`), `fib_one_one_parents_I0` (a parent in `I₀(0)` of `(1, 1)` is a
    coincidence block), `fib_IW_subset` (`I(0)` lies in the four states of
    `Psc.Descendants.fib_bpaStates`);
  - positive control `per_control` for the primitive `0 ↦ 01`, `1 ↦ 01` with
    fixed point `(01)^∞` and `W = 0`: `I₀(0) ⊆ {(01, 10)}` (`per_level0`, from
    `per_blocks`: the shift-1 reduction of `(01)^m` is `m` copies of
    `(01, 10)`), `{(01, 10), (0, 0), (1, 1)}` is child-closed, so `I(0)` is
    finite and contains `(01, 10)`, and `boundedGaps_of_finite_primitive`
    applies: its full hypothesis set is jointly satisfiable;
  - negative control `stairBoundedGaps` for the non-primitive `0 ↦ 01`,
    `1 ↦ 1` with fixed point `0 1^∞` (whose first letter never recurs): every
    hypothesis of `boundedGaps_of_finite` but `Unbounded` holds, `I(W)` is
    empty, hence finite, and `BoundedGaps` fails at every level for every `L`;
    with `stair_not_primitive` (a consequence of `unbounded_of_primitive`),
    neither recurrence nor primitivity can be dropped from (c).

Not proved here:

* that `I(W)` is finite for any specimen on three letters with an irreducible
  incidence polynomial (on two letters, `fib_terminates`; Tribonacci's `bpa-0` is
  not checked);
* that `I(W)` is finite for a seed `W` of Fibonacci other than `0`;
* the cut bound `|gapD u t k a| ≤ L` itself, `P(tₙ) = Mⁿ w`
  (`Psc.BPrimeCore.P_iterate`; `prefixParikh` is `BPrimeCore.P` by definition),
  the averaging, the cyclicity of `w` and the spectral conclusion of
  Proposition B′ (audit steps 2–6, sibling module `BPrimeCore`, which is not
  imported here; the composition of the two modules is `Psc.BPrime.bprime`, in
  `PscVerif/BPrime.lean`);
* any statement about non-termination (Corollary B (i) is
  `Psc.BPrime.corB_infinite`), about `bpa` seeds other than prefixes of a fixed
  point, or about periodic (not fixed) points;
* that `I(W)` contains a noncoincident pair (the remark after Corollary B; not
  needed by B′).
-/
import PscVerif.Descendants
import PscVerif.PrimitiveExpansion

namespace Psc.BPrimeBinding

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.FixedPointLimit Psc.Incidence

/-! ### Windows of an infinite word -/

section Windows

variable {α : Type*}

/-- The window `u[t, t + N)` of an infinite word, as a list. -/
def win (u : ℕ → α) (t N : ℕ) : List α := List.ofFn fun i : Fin N => u (t + i)

@[simp] theorem length_win (u : ℕ → α) (t N : ℕ) : (win u t N).length = N := by
  simp [win]

theorem getElem_win (u : ℕ → α) (t N i : ℕ) (h : i < (win u t N).length) :
    (win u t N)[i] = u (t + i) := by
  simp [win]

@[simp] theorem win_len_zero (u : ℕ → α) (t : ℕ) : win u t 0 = [] := by
  simp [win]

theorem win_zero_eq (u : ℕ → α) (N : ℕ) : win u 0 N = List.ofFn fun i : Fin N => u i := by
  simp [win]

/-- Windows concatenate: `u[t, t+N+M) = u[t, t+N) ++ u[t+N, t+N+M)`. -/
theorem win_add (u : ℕ → α) (t N M : ℕ) :
    win u t (N + M) = win u t N ++ win u (t + N) M := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [getElem_win, List.getElem_append]
    split_ifs with h
    · rw [getElem_win]
    · rw [getElem_win]
      simp only [length_win] at h ⊢
      congr 1
      omega

theorem take_win (u : ℕ → α) (t : ℕ) {k N : ℕ} (hk : k ≤ N) :
    (win u t N).take k = win u t k := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [win_add]
  exact List.take_left' (length_win u t k)

theorem win_congr {u v : ℕ → α} {t N : ℕ} (h : ∀ i < N, u (t + i) = v (t + i)) :
    win u t N = win v t N := by
  unfold win
  congr 1
  funext i
  exact h i i.2

/-- `x` is a prefix of the infinite word `u`. -/
def PrefixOf (u : ℕ → α) (x : List α) : Prop := win u 0 x.length = x

/-- `PrefixOf u x` in the per-index form, the body of `Psc.BPrimeCore.IsPrefixOf x u`. -/
theorem prefixOf_iff_getElem {u : ℕ → α} {x : List α} :
    PrefixOf u x ↔ ∀ i (h : i < x.length), x[i] = u i := by
  constructor
  · intro h i hi
    exact (List.getElem_of_eq h.symm hi).trans
      ((getElem_win u 0 _ i _).trans (by rw [Nat.zero_add]))
  · intro h
    refine List.ext_getElem (by simp) fun i _ h₂ => ?_
    rw [getElem_win, h i h₂, Nat.zero_add]

/-- `u` is a one-sided fixed point of `σ = subst s`: the image of every prefix
of `u` is a prefix of `u`. -/
def IsFixed (s : α → List α) (u : ℕ → α) : Prop := ∀ N, PrefixOf u (subst s (win u 0 N))

/-- The length map of `σ` on prefixes: `φ(t) = |σ(u[0, t))|`. -/
def phi (s : α → List α) (u : ℕ → α) (t : ℕ) : ℕ := (subst s (win u 0 t)).length

/-- `tₙ = |σⁿ(W)|`, the shift of level `n` (the body of `Psc.BPrimeCore.len`). -/
def tn (s : α → List α) (W : List α) (n : ℕ) : ℕ := ((subst s)^[n] W).length

theorem tn_zero (s : α → List α) (W : List α) : tn s W 0 = W.length := rfl

section Fixed

variable {s : α → List α} {u : ℕ → α}

/-- The image of the top window: `σ(u[0, N)) = u[0, φ N)`. -/
theorem subst_win_zero (hfix : IsFixed s u) (N : ℕ) :
    subst s (win u 0 N) = win u 0 (phi s u N) :=
  (hfix N).symm

/-- **The window map of a fixed point.**  `σ(u[t, t+N))` is the window of
`u` at shift `φ t` of its own length: cancel `σ(u[0, t)) = u[0, φ t)` in
`σ(u[0, t+N)) = u[0, |σ(u[0, t+N))|)`. -/
theorem subst_win (hfix : IsFixed s u) (t N : ℕ) :
    subst s (win u t N) = win u (phi s u t) (subst s (win u t N)).length := by
  have h1 := hfix (t + N)
  unfold PrefixOf at h1
  rw [win_add u 0 t N, Nat.zero_add, subst_append, List.length_append, win_add,
    Nat.zero_add] at h1
  exact (List.append_inj h1 (by simp)).2.symm

theorem prefixOf_subst (hfix : IsFixed s u) {x : List α} (hx : PrefixOf u x) :
    PrefixOf u (subst s x) := by
  have h := hfix x.length
  rwa [hx] at h

/-- Every `σⁿ(W)` is a prefix of `u`. -/
theorem prefixOf_iterate (hfix : IsFixed s u) {W : List α} (hW : PrefixOf u W) (n : ℕ) :
    PrefixOf u ((subst s)^[n] W) := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact prefixOf_subst hfix ih

/-- `u[0, tₙ) = σⁿ(W)`. -/
theorem win_tn (hfix : IsFixed s u) {W : List α} (hW : PrefixOf u W) (n : ℕ) :
    win u 0 (tn s W n) = (subst s)^[n] W :=
  prefixOf_iterate hfix hW n

/-- **The index of `I_{n+1}`**: `t_{n+1} = |σ(σⁿ W)| = φ(tₙ)`. -/
theorem tn_succ (hfix : IsFixed s u) {W : List α} (hW : PrefixOf u W) (n : ℕ) :
    tn s W (n + 1) = phi s u (tn s W n) := by
  unfold phi
  rw [win_tn hfix hW n, tn, Function.iterate_succ_apply']

end Fixed

end Windows

/-! ### Zero returns, prefix Parikh vectors and the gap predicate -/

variable {α : Type*} [DecidableEq α]

/-- The Parikh vector of `u[0, k)`, with integer entries (the body of
`Psc.BPrimeCore.P`). -/
def prefixParikh (u : ℕ → α) (k : ℕ) (a : α) : ℤ :=
  ∑ i ∈ Finset.range k, if u i = a then 1 else 0

/-- The discrepancy of the aligned pair at shift `t` after `k` letters,
`D t k = P k - (P (t + k) - P t)` (the body of `Psc.BPrimeCore.D`). -/
def gapD (u : ℕ → α) (t k : ℕ) (a : α) : ℤ :=
  prefixParikh u k a - (prefixParikh u (t + k) a - prefixParikh u t a)

/-- **The gap predicate consumed by the cut bound**: every `k` has a common
zero of `D t` in `[k, k + L]`.  This is, symbol for symbol, the hypothesis `hgap`
of `Psc.BPrimeCore.cut_bound`; `D t 0 = 0` is `gapD_zero`. -/
def BoundedGaps (u : ℕ → α) (t L : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' ≤ k + L ∧ ∀ a, gapD u t k' a = 0

/-- `P(k + 1) = P(k) + e_{u k}`: the prefix count advances by one unit vector. -/
theorem prefixParikh_succ (u : ℕ → α) (k : ℕ) (a : α) :
    prefixParikh u (k + 1) a = prefixParikh u k a + if u k = a then 1 else 0 := by
  unfold prefixParikh
  rw [Finset.sum_range_succ]

theorem prefixParikh_eq_count (u : ℕ → α) (k : ℕ) (a : α) :
    prefixParikh u k a = ((win u 0 k).count a : ℤ) := by
  induction k with
  | zero => simp [prefixParikh]
  | succ k ih =>
    rw [prefixParikh_succ, ih, win_add u 0 k 1, List.count_append]
    simp [win, List.count_singleton]

/-- `D t 0 = 0`. -/
@[simp] theorem gapD_zero (u : ℕ → α) (t : ℕ) (a : α) : gapD u t 0 a = 0 := by
  simp [gapD, prefixParikh]

theorem gapD_eq_count (u : ℕ → α) (t k : ℕ) (a : α) :
    gapD u t k a = ((win u 0 k).count a : ℤ) - (win u t k).count a := by
  simp only [gapD, prefixParikh_eq_count]
  rw [win_add u 0 t k, Nat.zero_add, List.count_append]
  push_cast
  ring

/-- `zeroReturn u t N`: the windows `u[0, N)` and `u[t, t + N)` of the aligned
pair at shift `t` have equal Parikh vectors. -/
def zeroReturn (u : ℕ → α) (t N : ℕ) : Prop := Equiv1 (win u 0 N) (win u t N)

instance (u : ℕ → α) (x : List α) : Decidable (PrefixOf u x) := by
  unfold PrefixOf; infer_instance

instance [Fintype α] (u : ℕ → α) (t N : ℕ) : Decidable (zeroReturn u t N) := by
  unfold zeroReturn; infer_instance

theorem zeroReturn_zero (u : ℕ → α) (t : ℕ) : zeroReturn u t 0 := by
  intro a; simp

/-- The zero returns are the common zeros of the discrepancy `D t = gapD u t`. -/
theorem zeroReturn_iff_gapD (u : ℕ → α) (t k : ℕ) :
    zeroReturn u t k ↔ ∀ a, gapD u t k a = 0 := by
  simp only [zeroReturn, Equiv1, gapD_eq_count, sub_eq_zero, Nat.cast_inj]

theorem boundedGaps_iff_zeroReturn (u : ℕ → α) (t L : ℕ) :
    BoundedGaps u t L ↔ ∀ k, ∃ k', k ≤ k' ∧ k' ≤ k + L ∧ zeroReturn u t k' := by
  simp only [BoundedGaps, zeroReturn_iff_gapD]

/-- **The shift/factor identity** (`proof/bpa/BpaPrefixBridge.lean`, in
`Equiv1` form): `k` is a zero return at shift `t` iff the factor `u[k, k + t)`
has the Parikh vector of the prefix `u[0, t)`. -/
theorem zeroReturn_iff_factor (u : ℕ → α) (t k : ℕ) :
    zeroReturn u t k ↔ Equiv1 (win u 0 t) (win u k t) := by
  have h := win_add u 0 t k
  have h' := win_add u 0 k t
  rw [Nat.zero_add] at h h'
  rw [Nat.add_comm t k, h'] at h
  refine forall_congr' fun a => ?_
  have := congrArg (List.count a) h
  simp only [List.count_append] at this
  omega

/-- The blocks of the reduction of the length-`N` windows of `(u, Sᵗu)`. -/
def blocks (u : ℕ → α) (t N : ℕ) : List (List α × List α) := red (win u 0 N) (win u t N)

/-- **(a) Prefix compatibility.**  For zero returns `N ≤ N'`, the reduction of
the length-`N` windows is a prefix of that of the length-`N'` windows
(`red_append` at the zero return `N`). -/
theorem blocks_prefix {u : ℕ → α} {t N N' : ℕ} (hN : zeroReturn u t N)
    (hN' : zeroReturn u t N') (hle : N ≤ N') : blocks u t N <+: blocks u t N' := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold zeroReturn at hN'
  rw [win_add u 0 N M, win_add u t N M] at hN'
  have hd := equiv1_cancel hN hN'
  refine ⟨red (win u (0 + N) M) (win u (t + N) M), ?_⟩
  unfold blocks
  rw [win_add u 0 N M, win_add u t N M, red_append hN hd]

theorem blocks_subset {u : ℕ → α} {t N N' : ℕ} (hN : zeroReturn u t N)
    (hN' : zeroReturn u t N') (hle : N ≤ N') {T : List α × List α}
    (hT : T ∈ blocks u t N) : T ∈ blocks u t N' :=
  (blocks_prefix hN hN' hle).subset hT

/-- The blocks of the infinite reduction of `(u, Sᵗu)`: the blocks of
`blocks u t N` over all zero returns `N`, coincidence blocks retained. -/
def levelSet (u : ℕ → α) (t : ℕ) : Set (List α × List α) :=
  {T | ∃ N, zeroReturn u t N ∧ T ∈ blocks u t N}

/-- The zero returns at shift `t` are unbounded. -/
def Unbounded (u : ℕ → α) (t : ℕ) : Prop := ∀ K, ∃ N, K ≤ N ∧ zeroReturn u t N

/-- Unbounded zero returns are recurrence of the Parikh class of `u[0, t)`. -/
theorem unbounded_iff_recurrent (u : ℕ → α) (t : ℕ) :
    Unbounded u t ↔ ∀ K, ∃ k, K ≤ k ∧ Equiv1 (win u 0 t) (win u k t) := by
  simp only [Unbounded, zeroReturn_iff_factor]

/-- **(a) Independence of the chosen zero return.**  With unbounded zero
returns, the zero returns `N ≥ K` define the same set, for every `K`. -/
theorem mem_levelSet_iff_ge {u : ℕ → α} {t : ℕ} (hunb : Unbounded u t) (K : ℕ)
    {T : List α × List α} :
    T ∈ levelSet u t ↔ ∃ N, K ≤ N ∧ zeroReturn u t N ∧ T ∈ blocks u t N := by
  constructor
  · rintro ⟨N, hN, hT⟩
    obtain ⟨N', hN'K, hN'⟩ := hunb (max K N)
    exact ⟨N', (le_max_left _ _).trans hN'K, hN',
      blocks_subset hN hN' ((le_max_right _ _).trans hN'K) hT⟩
  · rintro ⟨N, -, hN, hT⟩
    exact ⟨N, hN, hT⟩

/-- Every member of a level set is an irreducible balanced block. -/
theorem levelSet_isBlock {u : ℕ → α} {t : ℕ} : ∀ T ∈ levelSet u t, IsBlock T := by
  rintro T ⟨N, hN, hT⟩
  exact red_isBlock hN T hT

/-- **The blocks are aligned windows.**  A block of the reduction of the length-`N` windows
of `(u, Sᵗu)` is `(u[k, k + m), u[t + k, t + k + m))` for a zero return `k` with
`k + m ≤ N`: `k` is the partial sum of the lengths of the blocks before it
(`Psc.Descendants.take_red_top`, `take_red_bot`, `zero_return_iff`). -/
theorem exists_win_of_mem_blocks {u : ℕ → α} {t N : ℕ} (hN : zeroReturn u t N)
    {T : List α × List α} (hT : T ∈ blocks u t N) :
    ∃ k m, k + m ≤ N ∧ zeroReturn u t k ∧ T = (win u k m, win u (t + k) m) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT
  unfold blocks at hj ⊢
  set bs := red (win u 0 N) (win u t N) with hbs
  have hlen := (hN : Equiv1 (win u 0 N) (win u t N)).length_eq
  have hb : ∀ T ∈ bs, Equiv1 T.1 T.2 := fun T hT => (red_isBlock hN T hT).2.1
  set k := ((bs.take j).map fun T => T.1.length).sum with hk
  set m := bs[j].1.length with hm
  have hsum2 : ∀ i, ((bs.take i).map fun T => T.2.length).sum =
      ((bs.take i).map fun T => T.1.length).sum := fun i =>
    congrArg List.sum (List.map_congr_left fun T hT =>
      ((hb T (List.mem_of_mem_take hT)).length_eq).symm)
  have htake : bs.take (j + 1) = bs.take j ++ [bs[j]] := (List.take_concat_get' bs j hj).symm
  have hs1 : ((bs.take (j + 1)).map fun T => T.1.length).sum = k + m := by
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hs2 : ((bs.take (j + 1)).map fun T => T.2.length).sum = k + m := by
    rw [hsum2, hs1]
  have top1 := take_red_top hlen (j + 1)
  have top0 := take_red_top hlen j
  have bot1 := take_red_bot hlen (j + 1)
  have bot0 := take_red_bot hlen j
  rw [← hbs, hs1, htake, List.map_append, List.flatten_append] at top1
  rw [← hbs, ← hk] at top0
  rw [← hbs, hs2, htake, List.map_append, List.flatten_append] at bot1
  rw [← hbs, hsum2 j] at bot0
  rw [← top0] at top1
  rw [← bot0] at bot1
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at top1 bot1
  have hkmN : k + m ≤ N := by
    have := congrArg List.length top1
    simp only [List.length_take, length_win, List.length_append, ← hm] at this
    have hm0 : 0 < m := List.length_pos_of_ne_nil (red_isBlock hN _ (List.getElem_mem hj)).1
    omega
  have hkN : k ≤ N := by omega
  rw [take_win _ _ hkmN, take_win _ _ hkN, win_add u 0 k m, Nat.zero_add] at top1
  rw [take_win _ _ hkmN, take_win _ _ hkN, win_add u t k m] at bot1
  refine ⟨k, m, hkmN, ?_, Prod.ext (List.append_cancel_left top1).symm
    (List.append_cancel_left bot1).symm⟩
  have hz := (zero_return_iff hN (by rw [length_win]; exact hkN)).2 ⟨j, hk.symm⟩
  rwa [take_win _ _ hkN, take_win _ _ hkN] at hz

/-- **Balance at shift one is a return of the first letter**: `u[k, k + m)` and
`u[k + 1, k + 1 + m)` have equal Parikh vectors iff `u (k + m) = u k`
(`u[k, k + m + 1) = u[k, k + m) · u (k + m) = u k · u[k + 1, k + 1 + m)`). -/
theorem equiv1_win_succ_iff (u : ℕ → α) (k m : ℕ) :
    Equiv1 (win u k m) (win u (k + 1) m) ↔ u (k + m) = u k := by
  have h1 := win_add u k m 1
  have h2 := win_add u k 1 m
  rw [Nat.add_comm 1 m, h1] at h2
  have e1 : win u (k + m) 1 = [u (k + m)] := by simp [win]
  have e2 : win u k 1 = [u k] := by simp [win]
  rw [e1, e2] at h2
  constructor
  · intro h
    have := congrArg (List.count (u k)) h2
    simp only [List.count_append, List.count_singleton_self, h (u k)] at this
    by_contra hne
    simp [hne] at this
  · intro h a
    have := congrArg (List.count a) h2
    rw [List.count_append, List.count_append, h] at this
    simp only [List.count_cons] at this
    omega

/-! ### The window map and `red_subst` -/

section Subst

variable {s : α → List α} {u : ℕ → α}

/-- A nonerasing `σ` does not shorten prefixes: `N ≤ φ N`. -/
theorem le_phi (hs : ∀ a, s a ≠ []) (N : ℕ) : N ≤ phi s u N := by
  simpa [phi] using length_le_subst s hs (win u 0 N)

/-- At a zero return `N`, `σ(u[t, t+N)) = u[φ t, φ t + φ N)`. -/
theorem subst_win_of_zeroReturn (hfix : IsFixed s u) {t N : ℕ} (h : zeroReturn u t N) :
    subst s (win u t N) = win u (phi s u t) (phi s u N) := by
  rw [subst_win hfix t N]
  congr 1
  exact (equiv1_subst s h).length_eq.symm

/-- **`lem:inherited` for the aligned pair.**  A zero return `N` at shift `t`
gives the zero return `φ N` at shift `φ t`. -/
theorem zeroReturn_phi (hfix : IsFixed s u) {t N : ℕ} (h : zeroReturn u t N) :
    zeroReturn u (phi s u t) (phi s u N) := by
  have := equiv1_subst s h
  rwa [subst_win_zero hfix, subst_win_of_zeroReturn hfix h] at this

/-- **(3.1) on windows.**  The reduction of the windows of length `φ N` at
shift `φ t` lists the children `red (σ T.1) (σ T.2)` of the blocks of the
windows of length `N` at shift `t`, in order (`red_subst`). -/
theorem blocks_phi (hfix : IsFixed s u) {t N : ℕ} (h : zeroReturn u t N) :
    blocks u (phi s u t) (phi s u N) =
      (blocks u t N).flatMap fun T => red (subst s T.1) (subst s T.2) := by
  unfold blocks
  rw [← subst_win_zero hfix, ← subst_win_of_zeroReturn hfix h]
  exact red_subst s h

/-- Every red-child of a block at shift `t` is a block at shift `φ t`. -/
theorem child_mem_levelSet_phi (hfix : IsFixed s u) {t : ℕ} {U T : List α × List α}
    (hU : U ∈ levelSet u t) (hT : Child s U T) : T ∈ levelSet u (phi s u t) := by
  obtain ⟨N, hN, hUN⟩ := hU
  refine ⟨phi s u N, zeroReturn_phi hfix hN, ?_⟩
  rw [blocks_phi hfix hN]
  exact List.mem_flatMap.2 ⟨U, hUN, hT⟩

/-- Every block at shift `φ t` is a red-child of a block at shift `t`, when the
zero returns at shift `t` are unbounded and `σ` is nonerasing. -/
theorem exists_parent (hfix : IsFixed s u) (hs : ∀ a, s a ≠ []) {t : ℕ}
    (hunb : Unbounded u t) {T : List α × List α} (hT : T ∈ levelSet u (phi s u t)) :
    ∃ U ∈ levelSet u t, Child s U T := by
  obtain ⟨N', hN', hTN'⟩ := hT
  obtain ⟨N, hle, hN⟩ := hunb N'
  have hT' := blocks_subset hN' (zeroReturn_phi hfix hN) (hle.trans (le_phi hs N)) hTN'
  rw [blocks_phi hfix hN] at hT'
  obtain ⟨U, hU, hTU⟩ := List.mem_flatMap.1 hT'
  exact ⟨U, ⟨N, hN, hU⟩, hTU⟩

/-- Recurrence propagates along `φ`. -/
theorem unbounded_phi (hfix : IsFixed s u) (hs : ∀ a, s a ≠ []) {t : ℕ}
    (hunb : Unbounded u t) : Unbounded u (phi s u t) := by
  intro K
  obtain ⟨N, hle, hN⟩ := hunb K
  exact ⟨phi s u N, hle.trans (le_phi hs N), zeroReturn_phi hfix hN⟩

/-! ### Sufficient conditions for `Unbounded` -/

omit [DecidableEq α] in
/-- An occurrence of `x` at `m` gives an occurrence of `σ x` at `φ m`. -/
theorem occ_subst (hfix : IsFixed s u) {x : List α} {m : ℕ} (h : win u m x.length = x) :
    win u (phi s u m) (subst s x).length = subst s x := by
  have h' := subst_win hfix m x.length
  rw [h] at h'
  exact h'.symm

/-- If the image of the first letter has length at least two, `φ` is strictly
increasing on positive lengths: `N < φ N` for `0 < N`. -/
theorem lt_phi (hs : ∀ a, s a ≠ []) (h2 : 2 ≤ (s (u 0)).length) {N : ℕ} (hN : 0 < N) :
    N < phi s u N := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_lt hN
  unfold phi
  rw [show 0 + M + 1 = 1 + M by omega, win_add, subst_append, List.length_append]
  have e : (subst s (win u 0 1)).length = (s (u 0)).length := by simp [win, subst]
  have := length_le_subst s hs (win u (0 + 1) M)
  rw [length_win] at this
  omega

/-- **Every prefix recurs.**  For a fixed point whose first letter has an image
of length at least two and occurs again at some `k > 0`, every prefix `u[0, t)`
occurs at unbounded positions, so the zero returns at every shift `t` are
unbounded.  For a primitive `σ` itself (no power) both conditions hold
(`head_recurs_of_primitive`, `two_le_head_of_primitive`). -/
theorem unbounded_of_head_recurs (hfix : IsFixed s u) (hs : ∀ a, s a ≠ [])
    (h2 : 2 ≤ (s (u 0)).length) {k : ℕ} (hk : 0 < k) (hocc : u k = u 0) (t : ℕ) :
    Unbounded u t := by
  have hW : PrefixOf u [u 0] := by simp [PrefixOf, win]
  have hpos : ∀ n, win u ((phi s u)^[n] k) (tn s [u 0] n) = (subst s)^[n] [u 0] := by
    intro n
    induction n with
    | zero => simp [tn, win, hocc]
    | succ n ih =>
      rw [Function.iterate_succ_apply', tn, Function.iterate_succ_apply']
      exact occ_subst hfix ih
  have hlen : ∀ n, n + 1 ≤ tn s [u 0] n := by
    intro n
    induction n with
    | zero => simp [tn]
    | succ n ih =>
      rw [tn_succ hfix hW]
      have := lt_phi hs h2 (N := tn s [u 0] n) (by omega)
      omega
  have hmono : ∀ n, k + n ≤ (phi s u)^[n] k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have := lt_phi hs h2 (N := (phi s u)^[n] k) (by omega)
      omega
  intro K
  refine ⟨(phi s u)^[t + K] k, by have := hmono (t + K); omega, ?_⟩
  have ht : t ≤ tn s [u 0] (t + K) := by have := hlen (t + K); omega
  refine (zeroReturn_iff_factor u t _).2 ?_
  rw [← take_win u ((phi s u)^[t + K] k) ht, hpos, ← win_tn hfix hW, take_win u 0 ht]
  exact fun _ => rfl

section Primitive

variable [Fintype α]

/-- Under `Mᵏ > 0`, every letter occurs in `σᵏ [c]`. -/
theorem mem_iterate_of_pos {k : ℕ} (hpos : ∀ a c, 0 < (inc s ^ k) a c) (a c : α) :
    a ∈ (subst s)^[k] [c] := by
  rw [← List.count_pos_iff, count_iterate_subst]
  exact hpos a c

/-- **The first letter of a primitive fixed point recurs** (for `σ` itself):
`σᵏ(u 0 u 1) = σᵏ[u 0] σᵏ[u 1]` is a prefix of `u`, `σᵏ[u 0]` is nonempty and
`u 0 ∈ σᵏ[u 1]`. -/
theorem head_recurs_of_primitive (hfix : IsFixed s u) {k : ℕ}
    (hpos : ∀ a c, 0 < (inc s ^ k) a c) : ∃ m, 0 < m ∧ u m = u 0 := by
  have hW : PrefixOf u (win u 0 2) := by simp [PrefixOf]
  have h := win_tn hfix hW k
  have e2 : win u 0 2 = [u 0] ++ [u 1] := by simp [win]
  have hlen : tn s (win u 0 2) k =
      ((subst s)^[k] [u 0]).length + ((subst s)^[k] [u 1]).length := by
    rw [tn, e2, iterate_subst_append, List.length_append]
  rw [hlen, win_add, Nat.zero_add, e2, iterate_subst_append] at h
  set A := ((subst s)^[k] [u 0]).length
  set B := ((subst s)^[k] [u 1]).length
  have hB : win u A B = (subst s)^[k] [u 1] :=
    (List.append_inj h (by simp [A])).2
  have hA : 0 < A := List.length_pos_of_mem (mem_iterate_of_pos hpos (u 0) (u 0))
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem (mem_iterate_of_pos hpos (u 0) (u 1))
  refine ⟨A + i, by omega, ?_⟩
  have := getElem_win u A B i (by simpa [B] using hi)
  rw [← this]
  simp only [hB, hiu]

/-- **The first letter of a primitive fixed point has an image of length at
least two** (for `σ` itself, on two or more letters): otherwise `σ(u 0) = u 0`
(it is a prefix of `u`), so `σⁿ[u 0] ⊆ {u 0}`, against the positive column of
`u 0` in `Mᵏ`. -/
theorem two_le_head_of_primitive (hfix : IsFixed s u) (hcard : 2 ≤ Fintype.card α) {k : ℕ}
    (hpos : ∀ a c, 0 < (inc s ^ k) a c) : 2 ≤ (s (u 0)).length := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (u 0)
  have hpre := hfix 1
  have e : subst s (win u 0 1) = s (u 0) := by simp [win, subst]
  rw [e] at hpre
  have hsub : ∀ x ∈ s (u 0), x = u 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi0 : i = 0 := by omega
    subst hi0
    exact (List.getElem_of_eq hpre.symm hi).trans (getElem_win u 0 _ 0 _)
  have hall : ∀ n, ∀ x ∈ (subst s)^[n] [u 0], x = u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      simp only [subst, List.mem_flatten, List.mem_map] at hx
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx
      rw [ih y hy] at hxy
      exact hsub x hxy
  exact hb (hall k b (mem_iterate_of_pos hpos b (u 0)))

/-- On at most one letter, all windows of a given length have the same Parikh
vector. -/
theorem count_of_card_le_one (hcard : Fintype.card α ≤ 1) (x : List α) (a : α) :
    x.count a = x.length :=
  List.count_eq_length.2 fun _ _ => Fintype.card_le_one_iff.1 hcard _ _

/-- On at most one letter every length is a zero return. -/
theorem unbounded_of_card_le_one (hcard : Fintype.card α ≤ 1) (u : ℕ → α) (t : ℕ) :
    Unbounded u t := fun K =>
  ⟨K, le_rfl, fun a => by rw [count_of_card_le_one hcard, count_of_card_le_one hcard]; simp⟩

/-- **Recurrence from primitivity.**  A fixed point of a primitive `σ` has
unbounded zero returns at every shift: the recurrence input of Sirvent–Solomyak,
discharged from the hypothesis of the corrected theorem. -/
theorem unbounded_of_primitive (hfix : IsFixed s u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (t : ℕ) : Unbounded u t := by
  rcases le_or_gt (Fintype.card α) 1 with hcard | hcard
  · exact unbounded_of_card_le_one hcard u t
  have hs := Psc.PrimitiveExpansion.nonerasing_of_primitive s hprim
  obtain ⟨k, -, hk⟩ := hprim
  obtain ⟨m, hm0, hm⟩ := head_recurs_of_primitive hfix hk
  exact unbounded_of_head_recurs hfix hs (two_le_head_of_primitive hfix hcard hk) hm0 hm t

end Primitive

end Subst

/-! ### Sirvent–Solomyak (3.1) for the prefix-seeded levels -/

/-- The level-`n` set `Iₙ(W)`: the blocks of the reduction of
`(u, S^{|σⁿ W|} u)`, coincidence blocks retained. -/
def Ilevel (s : α → List α) (u : ℕ → α) (W : List α) (n : ℕ) : Set (List α × List α) :=
  levelSet u (tn s W n)

/-- `I(W) = ⋃ₙ Iₙ(W)`; `bpa-W` terminates iff this set is finite. -/
def IW (s : α → List α) (u : ℕ → α) (W : List α) : Set (List α × List α) :=
  ⋃ n, Ilevel s u W n

/-- Sirvent–Solomyak's recursion, read literally: `I₀(W)` is the reduction of
`(u, S^{|W|} u)`, and `I_{n+1}(W)` consists of the irreducible subpairs (the
red-children, coincidence blocks included) of the substituted members of
`Iₙ(W)`. -/
def ssLevel (s : α → List α) (u : ℕ → α) (W : List α) : ℕ → Set (List α × List α)
  | 0 => levelSet u W.length
  | n + 1 => {T | ∃ U ∈ ssLevel s u W n, Child s U T}

section SS

variable {s : α → List α} {u : ℕ → α} {W : List α}

theorem Ilevel_isBlock (n : ℕ) : ∀ T ∈ Ilevel s u W n, IsBlock T := levelSet_isBlock

/-- **The level window map.**  At a level-`n` zero return `N`, `σ` maps the
windows `(u[0, N), u[tₙ, tₙ + N))` onto the level-`(n+1)` windows of length
`φ N = |σ(u[0, N))|`. -/
theorem subst_win_tn (hfix : IsFixed s u) (hW : PrefixOf u W) {n N : ℕ}
    (h : zeroReturn u (tn s W n) N) :
    subst s (win u 0 N) = win u 0 (phi s u N) ∧
      subst s (win u (tn s W n) N) = win u (tn s W (n + 1)) (phi s u N) := by
  rw [tn_succ hfix hW]
  exact ⟨subst_win_zero hfix N, subst_win_of_zeroReturn hfix h⟩

/-- Recurrence at level `0` gives recurrence at every level. -/
theorem unbounded_tn (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) (n : ℕ) : Unbounded u (tn s W n) := by
  induction n with
  | zero => exact hunb
  | succ n ih => rw [tn_succ hfix hW]; exact unbounded_phi hfix hs ih

/-- **(3.1), first half.**  Every red-child of a level-`n` block occurs at
level `n + 1`. -/
theorem child_mem_I_succ (hfix : IsFixed s u) (hW : PrefixOf u W) {n : ℕ}
    {U T : List α × List α} (hU : U ∈ Ilevel s u W n) (hT : Child s U T) :
    T ∈ Ilevel s u W (n + 1) := by
  unfold Ilevel
  rw [tn_succ hfix hW]
  exact child_mem_levelSet_phi hfix hU hT

/-- **(3.1), second half.**  Every level-`(n+1)` block is a red-child of a
level-`n` block. -/
theorem exists_parent_I (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) {n : ℕ} {T : List α × List α}
    (hT : T ∈ Ilevel s u W (n + 1)) : ∃ U ∈ Ilevel s u W n, Child s U T := by
  unfold Ilevel at hT
  rw [tn_succ hfix hW] at hT
  exact exists_parent hfix hs (unbounded_tn hfix hW hs hunb n) hT

/-- **Sirvent–Solomyak (3.1).**  `I_{n+1}(W)` is the set of red-children of the
members of `Iₙ(W)`. -/
theorem I_succ (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) (n : ℕ) :
    Ilevel s u W (n + 1) = {T | ∃ U ∈ Ilevel s u W n, Child s U T} := by
  ext T
  exact ⟨exists_parent_I hfix hW hs hunb, fun ⟨_, hU, hT⟩ => child_mem_I_succ hfix hW hU hT⟩

/-- **The binding.**  The recursive `bpa-W` levels equal the window levels. -/
theorem ssLevel_eq (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) (n : ℕ) : ssLevel s u W n = Ilevel s u W n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [I_succ hfix hW hs hunb, ← ih]; rfl

/-- `I(W)` is child-closed in the full child graph (coincidences admitted). -/
theorem IW_childClosed (hfix : IsFixed s u) (hW : PrefixOf u W) :
    ChildClosed s (IW s u W) := by
  intro U hU T hT
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hU
  exact Set.mem_iUnion.2 ⟨n + 1, child_mem_I_succ hfix hW hn hT⟩

theorem IW_isBlock : ∀ T ∈ IW s u W, IsBlock T := by
  intro T hT
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hT
  exact Ilevel_isBlock n T hn

/-- **`I(W)` is the child closure of `I₀(W)`** in the full child graph. -/
theorem IW_eq_reachable (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) : IW s u W = Reachable s (Ilevel s u W 0) := by
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hT
    induction n generalizing T with
    | zero => exact subset_reachable hn
    | succ n ih =>
      obtain ⟨U, hU, hUT⟩ := exists_parent_I hfix hW hs hunb hn
      exact reachable_childClosed U (ih (Set.mem_iUnion.2 ⟨n, hU⟩) hU) T hUT
  · exact reachable_subset (fun T hT => Set.mem_iUnion.2 ⟨0, hT⟩) (IW_childClosed hfix hW)

section Primitive

variable [Fintype α]

/-- **Sirvent–Solomyak (3.1), hypothesis-exact**: fixed point, prefix seed and
primitivity. -/
theorem I_succ_of_primitive (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (n : ℕ) :
    Ilevel s u W (n + 1) = {T | ∃ U ∈ Ilevel s u W n, Child s U T} :=
  I_succ hfix hW (Psc.PrimitiveExpansion.nonerasing_of_primitive s hprim)
    (unbounded_of_primitive hfix hprim _) n

theorem ssLevel_eq_of_primitive (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (n : ℕ) :
    ssLevel s u W n = Ilevel s u W n :=
  ssLevel_eq hfix hW (Psc.PrimitiveExpansion.nonerasing_of_primitive s hprim)
    (unbounded_of_primitive hfix hprim _) n

theorem IW_eq_reachable_of_primitive (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    IW s u W = Reachable s (Ilevel s u W 0) :=
  IW_eq_reachable hfix hW (Psc.PrimitiveExpansion.nonerasing_of_primitive s hprim)
    (unbounded_of_primitive hfix hprim _)

/-- **`I(W)` read literally.**  The union of Sirvent–Solomyak's recursive levels (3.1) is
the window-defined `I(W)`, for a fixed point of a primitive `σ` with prefix seed `W`
(`ssLevel_eq_of_primitive` at every level). -/
theorem IW_eq_iUnion_ssLevel (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) : (⋃ n, ssLevel s u W n) = IW s u W :=
  Set.iUnion_congr fun n => ssLevel_eq_of_primitive hfix hW hprim n

end Primitive

end SS

/-! ### Termination gives bounded gaps -/

/-- A finite `I(W)` has a bound on the lengths of its blocks. -/
theorem exists_bound_of_finite {s : α → List α} {u : ℕ → α} {W : List α}
    (hfin : (IW s u W).Finite) : ∃ L, ∀ T ∈ IW s u W, T.1.length ≤ L := by
  obtain ⟨L, hL⟩ := (hfin.image fun T => T.1.length).bddAbove
  exact ⟨L, fun T hT => hL ⟨T, hT, rfl⟩⟩

/-- **Bounded blocks give bounded gaps.**  If the blocks at shift `t` have length
at most `L` and the zero returns are unbounded, then every `k` has a zero return
in `[k, k + L]`. -/
theorem boundedGaps_of_bound {u : ℕ → α} {t L : ℕ} (hunb : Unbounded u t)
    (hL : ∀ T ∈ levelSet u t, T.1.length ≤ L) : BoundedGaps u t L := by
  refine (boundedGaps_iff_zeroReturn u t L).2 fun k => ?_
  obtain ⟨N, hkN, hN⟩ := hunb k
  set bs := blocks u t N with hbs
  have htop : (bs.map Prod.fst).flatten = win u 0 N := red_top hN.length_eq
  obtain ⟨j, hj1, hj2⟩ := exists_cut L (bs.map Prod.fst)
    (by
      intro w hw
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hw
      exact hL T ⟨N, hN, hT⟩)
    k (by rw [htop, length_win]; exact hkN)
  set k' := ((bs.map Prod.fst).take j).flatten.length with hk'
  have hsum : ((bs.take j).map fun T => T.1.length).sum = k' := by
    rw [hk', List.length_flatten, ← List.map_take, List.map_map]
    rfl
  have hk'N : k' ≤ N := by
    have := (List.take_prefix j (bs.map Prod.fst)).flatten.length_le
    rwa [htop, length_win] at this
  have hz : Equiv1 ((win u 0 N).take k') ((win u t N).take k') :=
    (zero_return_iff hN (by rw [length_win]; exact hk'N)).2 ⟨j, hsum⟩
  rw [take_win u 0 hk'N, take_win u t hk'N] at hz
  exact ⟨k', hj1, hj2, hz⟩

/-- **(c) Termination, with the recurrence hypothesis.**  If `bpa-W` terminates
(`I(W)` finite) and the zero returns at level `0` are unbounded, one `L` bounds
the gaps between the zero returns of `(u, S^{tₙ}u)` at every level `n`. -/
theorem boundedGaps_of_finite {s : α → List α} {u : ℕ → α} {W : List α}
    (hfix : IsFixed s u) (hW : PrefixOf u W) (hs : ∀ a, s a ≠ [])
    (hunb : Unbounded u W.length) (hfin : (IW s u W).Finite) :
    ∃ L, ∀ n, BoundedGaps u (tn s W n) L := by
  obtain ⟨L, hL⟩ := exists_bound_of_finite hfin
  exact ⟨L, fun n => boundedGaps_of_bound (unbounded_tn hfix hW hs hunb n)
    fun T hT => hL T (Set.mem_iUnion.2 ⟨n, hT⟩)⟩

/-- **(c) Termination, hypothesis-exact.**  For a fixed point of a primitive `σ`
with prefix seed `W`, if `bpa-W` terminates (`I(W)` finite) then one `L` gives
`BoundedGaps u tₙ L` at every level `n`: the hypothesis `hgap` of
`Psc.BPrimeCore.bprime_core`, definitionally. -/
theorem boundedGaps_of_finite_primitive [Fintype α] {s : α → List α} {u : ℕ → α}
    {W : List α} (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (hfin : (IW s u W).Finite) :
    ∃ L, ∀ n, BoundedGaps u (tn s W n) L :=
  boundedGaps_of_finite hfix hW (Psc.PrimitiveExpansion.nonerasing_of_primitive s hprim)
    (unbounded_of_primitive hfix hprim _) hfin

/-! ### The limit words of `Psc.FixedPointLimit` are fixed points -/

section Limit

variable (s : α → List α) {u₀ : List α}

/-- The limit word of a chain `u₀ <+: σ u₀` with growth is a fixed point in the
sense of `IsFixed`. -/
theorem isFixed_limit (hu : u₀ <+: (subst s)^[1] u₀)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[1 * n] u₀).length) :
    IsFixed s (limit s u₀ 1 hgrow) := by
  intro N
  have h := limit_fixed_eq s hu hgrow N
  rw [Function.iterate_one] at h
  unfold PrefixOf
  rw [win_zero_eq, win_zero_eq]
  exact h

/-- `u₀` is a prefix seed of its limit word. -/
theorem prefixOf_limit (hu : u₀ <+: (subst s)^[1] u₀)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[1 * n] u₀).length) :
    PrefixOf (limit s u₀ 1 hgrow) u₀ := by
  unfold PrefixOf
  rw [win_zero_eq]
  exact ofFn_limit_of_prefix s hu hgrow (n := 0) (by simp)

/-- **The fixed point grown from a seed**: for a nonerasing `σ` and a seed `x <+: σ(x)` with
`|x| < |σ(x)|`, the limit word of `σⁿ(x)` (`Psc.FixedPointLimit.limit`, growth from
`grow_of_nonerasing`).  Every specimen of `PscVerif.BPrimeBinding` and `PscVerif.BPrime`
takes its fixed point from here. -/
noncomputable def seedLimit (x : List α) (hs : ∀ a, s a ≠ []) (hx : x <+: subst s x)
    (hlt : x.length < (subst s x).length) : ℕ → α :=
  limit s x 1 (grow_of_nonerasing s hs (p := 1) (by simpa using hx) (by simpa using hlt))

/-- The seeded limit word is a one-sided fixed point. -/
theorem isFixed_seedLimit (x : List α) (hs : ∀ a, s a ≠ []) (hx : x <+: subst s x)
    (hlt : x.length < (subst s x).length) : IsFixed s (seedLimit s x hs hx hlt) :=
  isFixed_limit s (by simpa using hx) _

/-- The seed is a prefix of its limit word. -/
theorem prefixOf_seedLimit (x : List α) (hs : ∀ a, s a ≠ []) (hx : x <+: subst s x)
    (hlt : x.length < (subst s x).length) : PrefixOf (seedLimit s x hs hx hlt) x :=
  prefixOf_limit s (by simpa using hx) _

end Limit

/-! ### Controls -/

section Controls

/-- The Fibonacci chain `[0] <+: σ [0] = [0, 1]`. -/
theorem fib_chain : ([0] : List (Fin 2)) <+: (subst fibSubst)^[1] [0] := by decide

/-- The Fibonacci fixed point `0100101001001…`, the limit of `σⁿ(0)` (`seedLimit`). -/
noncomputable def fibU : ℕ → Fin 2 := seedLimit fibSubst [0] (by decide) (by decide) (by decide)

/-- `fibU` is a one-sided fixed point. -/
theorem fibU_isFixed : IsFixed fibSubst fibU := isFixed_seedLimit _ _ _ _ _

/-- `0` is a prefix of `fibU`. -/
theorem fibU_prefix : PrefixOf fibU [0] := prefixOf_seedLimit _ _ _ _ _

/-- `σ⁶(0)`, of length `21`. -/
def fibWord : List (Fin 2) := (subst fibSubst)^[6] [0]

/-- A computable copy of `fibU` on `[0, 21)`. -/
def fibC (i : ℕ) : Fin 2 := fibWord.getD i 0

theorem fibU_eq (i : ℕ) (h : i < 21) : fibU i = fibC i := by
  have hlen : ((subst fibSubst)^[6] ([0] : List (Fin 2))).length = 21 := by decide
  have h' : i < ((subst fibSubst)^[6] ([0] : List (Fin 2))).length := hlen ▸ h
  rw [fibU, seedLimit, limit_spec fibSubst fib_chain _ 6 i h', fibC, fibWord,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']
  rfl

theorem fib_win (t N : ℕ) (h : t + N ≤ 21) : win fibU t N = win fibC t N :=
  win_congr fun i hi => fibU_eq _ (by omega)

/-- The shifts of levels `0, 1, 2` for `W = 0`: `1, 2, 3`. -/
example : tn fibSubst [0] 0 = 1 ∧ tn fibSubst [0] 1 = 2 ∧ tn fibSubst [0] 2 = 3 := by decide

/-- Level `0` on the window of length `10`: a zero return, and its blocks. -/
theorem fib_level0 :
    zeroReturn fibU 1 10 ∧
      blocks fibU 1 10 = [([0, 1], [1, 0]), ([0], [0]), ([0, 1], [1, 0]), ([0, 1], [1, 0]),
        ([0], [0]), ([0, 1], [1, 0])] := by
  unfold zeroReturn blocks
  rw [fib_win 0 10 (by norm_num), fib_win 1 10 (by norm_num)]
  decide

/-- `φ 10 = 16` and the shift of level `1` is `φ 1 = 2`. -/
theorem fib_phi : phi fibSubst fibU 10 = 16 ∧ phi fibSubst fibU 1 = 2 := by
  unfold phi
  rw [fib_win 0 10 (by norm_num), fib_win 0 1 (by norm_num)]
  decide

/-- Level `1` on the window of length `16`, and the (3.1) relation with the
level-`0` window of length `10`, both computed. -/
theorem fib_blocks_phi :
    blocks fibU 2 16 = [([0], [0]), ([1, 0], [0, 1]), ([0], [0]), ([1], [1]), ([0], [0]),
        ([1, 0], [0, 1]), ([0], [0]), ([1, 0], [0, 1]), ([0], [0]), ([1], [1]), ([0], [0]),
        ([1, 0], [0, 1])] ∧
      blocks fibU 2 16 =
        (blocks fibU 1 10).flatMap fun T => red (subst fibSubst T.1) (subst fibSubst T.2) := by
  unfold blocks
  rw [fib_win 0 16 (by norm_num), fib_win 2 16 (by norm_num), fib_win 0 10 (by norm_num),
    fib_win 1 10 (by norm_num)]
  decide

/-- The general `blocks_phi` gives the same relation. -/
example : blocks fibU (phi fibSubst fibU 1) (phi fibSubst fibU 10) =
    (blocks fibU 1 10).flatMap fun T => red (subst fibSubst T.1) (subst fibSubst T.2) :=
  blocks_phi fibU_isFixed fib_level0.1

/-- Coincidences are load-bearing on these windows: the level-`1` block `(1, 1)`
of the length-`16` window is a child only of the coincidence blocks `(0, 0)` of
the length-`10` level-`0` window.  (A statement about these two windows; over all
zero returns, `fib_one_one_parents_I0`.) -/
theorem fib_one_one_parents :
    (([1], [1]) : List (Fin 2) × List (Fin 2)) ∈ blocks fibU 2 16 ∧
      ∀ U ∈ blocks fibU 1 10, Child fibSubst U ([1], [1]) → U.1 = U.2 := by
  rw [fib_level0.2, fib_blocks_phi.1]
  unfold Child
  decide

/-- The level-`0` blocks on the window belong to `I₀(0)`, and the level-`1`
blocks to `I₁(0)`. -/
example : ∀ T ∈ blocks fibU 1 10, T ∈ Ilevel fibSubst fibU [0] 0 :=
  fun _ hT => ⟨10, fib_level0.1, hT⟩

example : ∀ T ∈ blocks fibU 2 16, T ∈ Ilevel fibSubst fibU [0] 1 := by
  intro T hT
  have h := zeroReturn_phi fibU_isFixed fib_level0.1
  rw [fib_phi.1, fib_phi.2] at h
  exact ⟨16, h, hT⟩

/-- Fibonacci is primitive: `M² > 0`. -/
theorem fib_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc fibSubst ^ k) a c :=
  ⟨2, by norm_num, fun a c => by fin_cases a <;> fin_cases c <;> decide +kernel⟩

/-- The first letter `0` has the image `01` and recurs at position `2`, so every
shift has unbounded zero returns (`unbounded_of_head_recurs`). -/
theorem fib_unbounded (t : ℕ) : Unbounded fibU t :=
  unbounded_of_head_recurs fibU_isFixed (by decide)
    (by rw [fibU_eq 0 (by norm_num)]; decide) (k := 2) (by norm_num)
    (by rw [fibU_eq 0 (by norm_num), fibU_eq 2 (by norm_num)]; decide) t

/-- (3.1) for the genuine Fibonacci fixed point with `W = 0`, at every level,
from the hypothesis-exact `I_succ_of_primitive`. -/
theorem fib_I_succ (n : ℕ) :
    Ilevel fibSubst fibU [0] (n + 1) =
      {T | ∃ U ∈ Ilevel fibSubst fibU [0] n, Child fibSubst U T} :=
  I_succ_of_primitive fibU_isFixed fibU_prefix fib_primitive n

/-- The recursive `bpa-W` of Fibonacci with `W = 0` is the window definition,
and `I(0)` is the child closure of `I₀(0)`. -/
theorem fib_ssLevel :
    (∀ n, ssLevel fibSubst fibU [0] n = Ilevel fibSubst fibU [0] n) ∧
      IW fibSubst fibU [0] = Reachable fibSubst (Ilevel fibSubst fibU [0] 0) :=
  ⟨ssLevel_eq fibU_isFixed fibU_prefix (by decide) (fib_unbounded _),
    IW_eq_reachable fibU_isFixed fibU_prefix (by decide) (fib_unbounded _)⟩

/-! #### Positive control: Fibonacci's `bpa-0` terminates (irreducible `χ_M`, two letters) -/

/-- No image `σ(w)` of Fibonacci contains the factor `11`: every `1` closes an image
`σ(0) = 01`, and every image begins with `0`. -/
theorem fib_subst_isChain (w : List (Fin 2)) :
    (subst fibSubst w).IsChain fun a b => ¬ (a = 1 ∧ b = 1) := by
  induction w with
  | nil => exact List.IsChain.nil
  | cons a w ih =>
    rw [subst_cons, List.isChain_append]
    refine ⟨by fin_cases a <;> decide, ih, fun x _ y hy => ?_⟩
    cases w with
    | nil => simp [subst] at hy
    | cons b w =>
      rw [subst_cons] at hy
      have : y = 0 := by
        revert hy
        fin_cases b <;> simp [fibSubst, eq_comm]
      simp [this]

/-- **`11` is not a factor of the Fibonacci fixed point**: `u[0, k + 2)` is a prefix of
`σ(u[0, k + 2))` (`fibU_isFixed`, `le_phi`), which has no factor `11`. -/
theorem fibU_not_one_one (k : ℕ) : ¬ (fibU k = 1 ∧ fibU (k + 1) = 1) := by
  have hle : k + 2 ≤ (subst fibSubst (win fibU 0 (k + 2))).length := le_phi (by decide) (k + 2)
  have hpre := prefixOf_iff_getElem.1 (fibU_isFixed (k + 2))
  have hc := List.isChain_iff_getElem.1 (fib_subst_isChain (win fibU 0 (k + 2))) k (by omega)
  rwa [hpre k (by omega), hpre (k + 1) (by omega)] at hc

/-- **`I₀(0)` of Fibonacci, over all zero returns**: `I₀(0) ⊆ {(0, 0), (01, 10)}`.  A block
of the shift-`1` reduction is `(u[k, k + m), u[k + 1, k + 1 + m))` at a zero return `k`
(`exists_win_of_mem_blocks`); balance and irreducibility at shift one say
`u k = u (k + m) = u 0 = 0` and `u (k + j) = 1` for `0 < j < m` (`equiv1_win_succ_iff`), and
`fibU_not_one_one` gives `m ≤ 2`. -/
theorem fib_level0_subset :
    Ilevel fibSubst fibU [0] 0 ⊆ {([0], [0]), ([0, 1], [1, 0])} := by
  rintro T ⟨N, hN, hT⟩
  change T ∈ blocks fibU 1 N at hT
  change zeroReturn fibU 1 N at hN
  have hB := red_isBlock hN T hT
  obtain ⟨k, m, -, hk, rfl⟩ := exists_win_of_mem_blocks hN hT
  obtain ⟨hne, hbal, hirr⟩ := hB
  have h0 : fibU 0 = 0 := by rw [fibU_eq 0 (by norm_num)]; decide
  have huk : fibU k = 0 := by
    have := (equiv1_win_succ_iff fibU 0 k).1 hk
    rwa [Nat.zero_add, h0] at this
  have hkm : fibU (k + m) = 0 := by
    have := (equiv1_win_succ_iff fibU k m).1 (by rwa [Nat.add_comm k 1])
    rwa [huk] at this
  have hstep : ∀ j, 0 < j → j < m → fibU (k + j) = 1 := by
    intro j hj0 hjm
    have h := hirr j hj0 (by simpa using hjm)
    simp only [take_win _ _ hjm.le, Nat.add_comm 1 k] at h
    rw [equiv1_win_succ_iff, huk] at h
    revert h
    generalize fibU (k + j) = x
    fin_cases x <;> simp
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 fun h => hne (by simp [h])
  have hm2 : m ≤ 2 := by
    by_contra h
    exact fibU_not_one_one (k + 1) ⟨hstep 1 one_pos (by omega), hstep 2 two_pos (by omega)⟩
  have hw : ∀ j, win fibU j 1 = [fibU j] := fun j => by simp [win]
  have hw2 : ∀ j, win fibU j 2 = [fibU j, fibU (j + 1)] := fun j => by
    simp [win, List.ofFn_succ]
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.add_comm 1 k]
  interval_cases m
  · left
    rw [hw, hw, huk, hkm]
  · right
    rw [hw2, hw2, huk, hstep 1 one_pos (by norm_num), hkm]

/-- **Coincidences are load-bearing in `I₁(0)`**: over all zero returns, a parent in
`I₀(0)` of the level-`1` block `(1, 1)` is a coincidence block (`fib_level0_subset`; the
children of `(01, 10)` are `(0, 0)` and `(10, 01)`). -/
theorem fib_one_one_parents_I0 :
    ∀ U ∈ Ilevel fibSubst fibU [0] 0, Child fibSubst U ([1], [1]) → U.1 = U.2 := by
  intro U hU
  rcases fib_level0_subset hU with rfl | rfl
  · exact fun _ => rfl
  · unfold Child; decide

/-- **`I(0)` of Fibonacci lies in the four states of its child graph**:
`I(0) = Reachable I₀(0)` (`IW_eq_reachable_of_primitive`) and `I₀(0) ⊆ bpaStates fibSubst`,
which is child-closed and equals `{(01, 10), (10, 01), (0, 0), (1, 1)}`
(`Psc.Descendants.fib_bpaStates`). -/
theorem fib_IW_subset : IW fibSubst fibU [0] ⊆ bpaStates fibSubst := by
  rw [IW_eq_reachable_of_primitive fibU_isFixed fibU_prefix fib_primitive]
  refine reachable_subset (fun T hT => ?_) (bpaStates_childClosed _)
  rw [fib_bpaStates, Finset.mem_coe]
  rcases fib_level0_subset hT with rfl | rfl <;> decide

/-- **Positive control with an irreducible `χ_M`: Fibonacci's `bpa-0` terminates.**  For
`0 ↦ 01`, `1 ↦ 0` (`χ_M = X² - X - 1`, irreducible over `ℚ`), its fixed point `fibU` and
`W = 0`: `I(0)` contains the noncoincident pair `(01, 10)` and is finite
(`fib_IW_subset`). -/
theorem fib_terminates :
    (([0, 1], [1, 0]) : List (Fin 2) × List (Fin 2)) ∈ IW fibSubst fibU [0] ∧
      (IW fibSubst fibU [0]).Finite :=
  ⟨Set.mem_iUnion.2 ⟨0, 10, fib_level0.1, show _ ∈ blocks fibU 1 10 by rw [fib_level0.2]; decide⟩,
    (Finset.finite_toSet _).subset (fib_bpaStates ▸ fib_IW_subset)⟩

/-! #### Positive control: a terminating `bpa-W` meeting every hypothesis of (c) -/

/-- The primitive `0 ↦ 01`, `1 ↦ 01` (incidence matrix with all entries `1`). -/
def perSubst : Fin 2 → List (Fin 2) := fun _ => [0, 1]

/-- Its fixed point `0101⋯`. -/
def perU (i : ℕ) : Fin 2 := if i % 2 = 0 then 0 else 1

theorem per_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc perSubst ^ k) a c :=
  ⟨1, le_rfl, by rw [pow_one]; show ∀ a c : Fin 2, 0 < (perSubst c).count a; decide⟩

theorem per_win_two (m : ℕ) : win perU (2 * m) 2 = [0, 1] ∧ win perU (2 * m + 1) 2 = [1, 0] := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1 + 1) % 2 = 0 := by omega
  simp [win, perU, List.ofFn_succ, h1, h2]

theorem per_win_even (m : ℕ) : win perU 0 (2 * m) = (List.replicate m [0, 1]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, win_add, ih, Nat.zero_add, (per_win_two m).1, List.replicate_succ',
      List.flatten_append]
    simp

theorem per_subst (w : List (Fin 2)) :
    subst perSubst w = (List.replicate w.length ([0, 1] : List (Fin 2))).flatten := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [subst_cons, ih, List.length_cons, List.replicate_succ, List.flatten_cons]
    rfl

theorem per_isFixed : IsFixed perSubst perU := by
  intro N
  unfold PrefixOf
  have hlen : ((List.replicate N ([0, 1] : List (Fin 2))).flatten).length = 2 * N := by
    simp [List.length_flatten, Nat.mul_comm]
  rw [per_subst, length_win, hlen, per_win_even]

/-- At shift `1` the zero returns are the even lengths. -/
theorem per_zeroReturn_one {N : ℕ} (h : zeroReturn perU 1 N) : N % 2 = 0 := by
  by_contra hN
  have := (zeroReturn_iff_factor perU 1 N).1 h 0
  simp [win, perU, hN] at this

/-- The shift-`1` reduction of `(01)^m` is `m` copies of `(01, 10)`. -/
theorem per_blocks (m : ℕ) : blocks perU 1 (2 * m) = List.replicate m ([0, 1], [1, 0]) := by
  induction m with
  | zero => simp [blocks, red, redAux]
  | succ m ih =>
    have hz : zeroReturn perU 1 (2 * m) := by
      refine (zeroReturn_iff_factor perU 1 _).2 ?_
      have e : win perU (2 * m) 1 = win perU 0 1 := by simp [win, perU]
      rw [e]
      exact fun _ => rfl
    have e0 : win perU 0 (2 * (m + 1)) = win perU 0 (2 * m) ++ [0, 1] := by
      rw [Nat.mul_succ, win_add, Nat.zero_add, (per_win_two m).1]
    have e1 : win perU 1 (2 * (m + 1)) = win perU 1 (2 * m) ++ [1, 0] := by
      rw [Nat.mul_succ, win_add, Nat.add_comm 1 (2 * m), (per_win_two m).2]
    have hb : Equiv1 ([0, 1] : List (Fin 2)) [1, 0] := by
      intro a; fin_cases a <;> rfl
    unfold blocks at ih ⊢
    rw [e0, e1, red_append hz hb, ih, List.replicate_succ']
    rfl

/-- `I₀(0) ⊆ {(01, 10)}`. -/
theorem per_level0 : Ilevel perSubst perU [0] 0 ⊆ {([0, 1], [1, 0])} := by
  rintro T ⟨N, hN, hT⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by have := per_zeroReturn_one hN; omega⟩
  change T ∈ blocks perU 1 (2 * m) at hT
  rw [per_blocks] at hT
  exact List.eq_of_mem_replicate hT

/-- The candidate state set `{(01, 10), (0, 0), (1, 1)}`. -/
def perStates : List (List (Fin 2) × List (Fin 2)) := [([0, 1], [1, 0]), ([0], [0]), ([1], [1])]

theorem per_childClosed : ChildClosed perSubst {T | T ∈ perStates} := by
  have h : ∀ U ∈ perStates, ∀ T ∈ red (subst perSubst U.1) (subst perSubst U.2),
      T ∈ perStates := by decide
  exact fun U hU T hT => h U hU T hT

/-- **Positive control for (c).**  For `0 ↦ 01`, `1 ↦ 01` with `W = 0`: the
fixed point, the prefix seed and primitivity hold, `I(0)` contains `(01, 10)`
and lies in `{(01, 10), (0, 0), (1, 1)}`, so `bpa-W` terminates, and
`boundedGaps_of_finite_primitive` gives one gap bound at every level. -/
theorem per_control :
    IsFixed perSubst perU ∧ PrefixOf perU [0] ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc perSubst ^ k) a c) ∧
      ([0, 1], [1, 0]) ∈ IW perSubst perU [0] ∧
      IW perSubst perU [0] ⊆ {T | T ∈ perStates} ∧ (IW perSubst perU [0]).Finite ∧
      ∃ L, ∀ n, BoundedGaps perU (tn perSubst [0] n) L := by
  have hW : PrefixOf perU [0] := by decide
  have hsub : IW perSubst perU [0] ⊆ {T | T ∈ perStates} := by
    rw [IW_eq_reachable_of_primitive per_isFixed hW per_primitive]
    refine reachable_subset (fun T hT => ?_) per_childClosed
    rw [Set.mem_singleton_iff.1 (per_level0 hT)]
    decide
  have hfin : (IW perSubst perU [0]).Finite := (List.finite_toSet perStates).subset hsub
  refine ⟨per_isFixed, hW, per_primitive, Set.mem_iUnion.2 ⟨0, 2, by decide, by decide⟩, hsub,
    hfin, boundedGaps_of_finite_primitive per_isFixed hW per_primitive hfin⟩

/-! #### Negative control: recurrence (and primitivity) cannot be dropped from (c) -/

/-- The non-primitive, nonerasing `0 ↦ 01`, `1 ↦ 1`. -/
def stairSubst : Fin 2 → List (Fin 2) := fun a => if a = 0 then [0, 1] else [1]

/-- Its fixed point `0 1 1 1 ⋯`. -/
def stairU (i : ℕ) : Fin 2 := if i = 0 then 0 else 1

theorem stair_win_pos (t N : ℕ) (ht : 0 < t) : win stairU t N = List.replicate N 1 := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [getElem_win, List.getElem_replicate]
    simp [stairU]
    omega

theorem stair_win_zero (N : ℕ) : win stairU 0 (N + 1) = 0 :: List.replicate N 1 := by
  rw [Nat.add_comm, win_add, stair_win_pos (0 + 1) N (by omega)]
  rfl

theorem stairU_isFixed : IsFixed stairSubst stairU := by
  intro N
  cases N with
  | zero => simp [PrefixOf, subst]
  | succ N =>
    have e : subst stairSubst (win stairU 0 (N + 1)) = 0 :: List.replicate (N + 1) 1 := by
      rw [stair_win_zero]
      simp only [subst, List.map_cons, List.map_replicate, List.flatten_cons]
      simp [stairSubst, List.flatten_replicate_singleton, List.replicate_succ]
    rw [PrefixOf, e, List.length_cons, List.length_replicate, stair_win_zero]

theorem stair_not_zeroReturn (t N : ℕ) (ht : 0 < t) (hN : 0 < N) : ¬ zeroReturn stairU t N := by
  intro h
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_lt hN
  have := h 0
  rw [stair_win_zero, stair_win_pos _ _ ht] at this
  simp [List.count_replicate] at this

/-- **Negative control.**  For `0 ↦ 01`, `1 ↦ 1` with `W = 0`, every hypothesis
of `boundedGaps_of_finite` except `Unbounded` holds and `I(W) = ∅` is finite,
but `BoundedGaps` fails at every level and for every `L`. -/
theorem stairBoundedGaps :
    IsFixed stairSubst stairU ∧ PrefixOf stairU [0] ∧ (∀ a, stairSubst a ≠ []) ∧
      IW stairSubst stairU [0] = ∅ ∧ ∀ n L, ¬ BoundedGaps stairU (tn stairSubst [0] n) L := by
  have htn : ∀ n, 0 < tn stairSubst [0] n := fun n =>
    List.length_pos_of_ne_nil (iterate_subst_ne_nil stairSubst (by decide) n (by simp))
  refine ⟨stairU_isFixed, by decide, by decide, ?_, fun n L h => ?_⟩
  · ext T
    simp only [IW, Ilevel, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro n ⟨N, hN, hT⟩
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp [blocks, red, redAux] at hT
    · exact stair_not_zeroReturn _ _ (htn n) hpos hN
  · obtain ⟨k', hk1, -, hk'⟩ := (boundedGaps_iff_zeroReturn _ _ _).1 h 1
    exact stair_not_zeroReturn _ _ (htn n) (by omega) hk'

/-- The staircase is not primitive: `unbounded_of_primitive` would give a
positive zero return at shift `1`. -/
theorem stair_not_primitive : ¬ ∃ k ≥ 1, ∀ a c, 0 < (inc stairSubst ^ k) a c := by
  intro hprim
  obtain ⟨N, hN, hz⟩ := unbounded_of_primitive stairU_isFixed hprim 1 1
  exact stair_not_zeroReturn 1 N (by norm_num) (by omega) hz

end Controls

end Psc.BPrimeBinding
