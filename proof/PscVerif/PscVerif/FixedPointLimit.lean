/-
# From the finite reduction lemma to one-sided fixed points

`docs/c4-concentration-attack-2026-11-06.md` §3 (and §8).  `PscVerif.Binomial`
proves the reduction lemma in finite form: a state `T₀ = (u₀, v₀)` of a finite
child-closed system with `u₀ <+: σᵖ u₀`, `v₀ <+: σᵖ v₀`, and for every `n` the
pair `(σ^{pn} u₀, σ^{pn} v₀)` a concatenation of states.  This module performs
the passage to the two one-sided `σᵖ`-invariant limit words.

Proved here, in full (depending only on the standard `propext`,
`Classical.choice`, `Quot.sound`):

* `chain_mono`: if `u <+: σᵖ u` then `n ≤ m → σ^{pn} u <+: σ^{pm} u`
  (the chain is increasing in the prefix order).  Hypothesis: only
  `hu : u <+: σᵖ u`.
* `limit`: under the growth hypothesis
  `hgrow : ∀ m, ∃ n, m < (σ^{pn} u).length` the limit word `x : ℕ → α`, defined
  by reading position `i` off any chain element long enough to contain it
  (chosen with `Classical.choose`).
* `limit_spec`: `x i = (σ^{pn} u).get ⟨i, h⟩` for every `n` and every in-range
  `i` — the definition does not depend on the chosen chain element.
* `limit_fixed` / `limit_fixed_eq`: for every `k`, with `P = x[0, k)`,
  `σᵖ P` is (equal to, hence) a prefix of `x[0, |σᵖ P|)`; i.e. `x` is
  `σᵖ`-invariant on prefixes.
* `fixed_points_equiv2_syndetic`: for a child system `S`, a state `T₀ ∈ S.C`
  with `T₀.1 <+: σᵖ T₀.1`, `T₀.2 <+: σᵖ T₀.2`, every state of `S.C`
  2-binomially equivalent on its tracks, growth of both chains, and a bound
  `B` on the top-track length of every state of `S.C`, the two limit words
  `x`, `y` satisfy: for every `m` there is `c` with `m ≤ c ≤ m + B` and
  `Equiv2 x[0, c) y[0, c)`.  The cuts are the block boundaries of
  `S.desc (p*n) T₀`; each block is balanced, so its two tracks have equal
  length, and consecutive cuts are at most `B` apart.

Hypotheses and their roles:

* `hu`, `hv` (`T₀.i <+: σᵖ T₀.i`): make the chains increasing, so the limit is
  well defined and every chain element is a prefix of it;
* `hgrow`, `hgrowy` (growth): make the limit a total function `ℕ → α`;
* `hK2` (all states 2-binomially equivalent): every block boundary is a
  2-binomial cut, and blocks are balanced (equal track lengths);
* `hT₀ : T₀ ∈ S.C`: lets `desc_top`, `desc_bot`, `desc_mem` apply;
* `hB` (`∀ U ∈ S.C, U.1.length ≤ B`): bounds the gaps between cuts.

Deviations from the original task text (both make the theorem stronger):

* the hypothesis `p ≥ 1` is not assumed: it is implied by growth
  (`pos_of_grow`, for `u` of any length), and is otherwise unused;
* the hypothesis "every state nonempty" (`0 < U.1.length`) is not assumed: the
  gap argument (smallest cut `≥ m`) needs only the upper bound `B`.

Also proved: `limit_zero` (the limit word starts with the first letter of
`u`); `grow_of_nonerasing` (growth follows from a nonerasing substitution and
one strict extension `|u| < |σᵖ u|`); and the assembled **`reduction_limit`**:
for a child system of a nonerasing substitution whose states are irreducible,
noncoincident, 2-binomially equivalent and strictly lengthened by `σ`, some
state and `p ≥ 1` give two `σᵖ`-invariant limit words with *different first
letters* that are 2-binomially equivalent on a syndetic set of prefix lengths,
with gap bound `S.C.sup (·.1.length)` derived from finiteness of `S.C`.

NOT formalized here: that a primitive substitution with Perron root `> 1` has a
power under which every state is strictly lengthened (the `hexp` hypothesis of
`reduction_limit`); the passage from one-sided fixed points to the two-sided or
tiling picture; any statement about the substitution being Pisot, irreducible,
or primitive.
-/
import PscVerif.Binomial
import Mathlib.Data.Finset.Lattice.Fold

namespace Psc.FixedPointLimit

open Psc.Binomial

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

/-! ### The increasing chain -/

theorem iterate_subst_prefix (s : α → List α) (k : ℕ) {x y : List α} (h : x <+: y) :
    (subst s)^[k] x <+: (subst s)^[k] y := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact subst_prefix s ih

theorem iterate_mul_succ (s : α → List α) (u : List α) (p n : ℕ) :
    (subst s)^[p * (n + 1)] u = (subst s)^[p] ((subst s)^[p * n] u) := by
  rw [← Function.iterate_add_apply]
  congr 1
  ring

theorem chain_succ (s : α → List α) {u : List α} {p : ℕ} (hu : u <+: (subst s)^[p] u)
    (n : ℕ) : (subst s)^[p * n] u <+: (subst s)^[p * (n + 1)] u := by
  have h := iterate_subst_prefix s (p * n) hu
  rw [← Function.iterate_add_apply] at h
  have e : p * n + p = p * (n + 1) := by ring
  rwa [e] at h

/-- **(1)** The chain `σ^{pn} u` is increasing in the prefix order. -/
theorem chain_mono (s : α → List α) {u : List α} {p : ℕ} (hu : u <+: (subst s)^[p] u) :
    ∀ n m, n ≤ m → (subst s)^[p * n] u <+: (subst s)^[p * m] u := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (chain_succ s hu m)

/-- Growth forces `p ≥ 1`: for `p = 0` the chain is constant. -/
theorem pos_of_grow (s : α → List α) (u : List α) (p : ℕ)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) : 1 ≤ p := by
  rcases Nat.eq_zero_or_pos p with h0 | hp
  · subst h0
    obtain ⟨n, hn⟩ := hgrow u.length
    simp at hn
  · exact hp

/-! ### The limit word -/

/-- **(2)** The limit of the increasing chain `σ^{pn} u`: position `i` is read
off a chain element long enough to contain it. -/
noncomputable def limit (s : α → List α) (u : List α) (p : ℕ)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) (i : ℕ) : α :=
  ((subst s)^[p * Classical.choose (hgrow i)] u).get ⟨i, Classical.choose_spec (hgrow i)⟩

/-- The limit word agrees with every chain element on its range. -/
theorem limit_spec (s : α → List α) {u : List α} {p : ℕ} (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) :
    ∀ n i (h : i < ((subst s)^[p * n] u).length),
      limit s u p hgrow i = ((subst s)^[p * n] u).get ⟨i, h⟩ := by
  intro n i h
  unfold limit
  have h0 := Classical.choose_spec (hgrow i)
  set n0 := Classical.choose (hgrow i)
  have ha := chain_mono s hu n0 (max n0 n) (le_max_left _ _)
  have hb := chain_mono s hu n (max n0 n) (le_max_right _ _)
  simp only [List.get_eq_getElem]
  rw [ha.getElem h0, hb.getElem h]

/-- Prefixes of the limit word are prefixes of chain elements. -/
theorem ofFn_limit_eq_take (s : α → List α) {u : List α} {p : ℕ}
    (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) {n c : ℕ}
    (hc : c ≤ ((subst s)^[p * n] u).length) :
    List.ofFn (fun i : Fin c => limit s u p hgrow i) = ((subst s)^[p * n] u).take c := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hc]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_take]
    have hi : i < ((subst s)^[p * n] u).length := by
      simp at h₁; omega
    rw [limit_spec s hu hgrow n i hi]
    rfl

/-- A prefix of a chain element is the prefix of the limit word of its length. -/
theorem ofFn_limit_of_prefix (s : α → List α) {u : List α} {p : ℕ}
    (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) {n : ℕ} {A : List α}
    (hA : A <+: (subst s)^[p * n] u) :
    List.ofFn (fun i : Fin A.length => limit s u p hgrow i) = A := by
  rw [ofFn_limit_eq_take s hu hgrow hA.length_le]
  exact (List.prefix_iff_eq_take.mp hA).symm

/-- `σᵖ`-invariance of the limit word on prefixes, as an equality: the image of
the length-`k` prefix is the prefix of the same length as that image. -/
theorem limit_fixed_eq (s : α → List α) {u : List α} {p : ℕ}
    (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) (k : ℕ) :
    List.ofFn (fun i : Fin ((subst s)^[p]
        (List.ofFn (fun i : Fin k => limit s u p hgrow i))).length => limit s u p hgrow i) =
      (subst s)^[p] (List.ofFn (fun i : Fin k => limit s u p hgrow i)) := by
  obtain ⟨n, hn⟩ := hgrow k
  have hP : List.ofFn (fun i : Fin k => limit s u p hgrow i) <+: (subst s)^[p * n] u := by
    rw [ofFn_limit_eq_take s hu hgrow hn.le]
    exact List.take_prefix _ _
  have hQ := iterate_subst_prefix s p hP
  rw [← iterate_mul_succ] at hQ
  exact ofFn_limit_of_prefix s hu hgrow hQ

/-- **(2)** `σᵖ`-invariance of the limit word on prefixes: `σᵖ` of the
length-`k` prefix is a prefix of the limit word (of the prefix of the length of
that image). -/
theorem limit_fixed (s : α → List α) {u : List α} {p : ℕ}
    (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) (k : ℕ) :
    (subst s)^[p] (List.ofFn (fun i : Fin k => limit s u p hgrow i)) <+:
      List.ofFn (fun i : Fin ((subst s)^[p]
        (List.ofFn (fun i : Fin k => limit s u p hgrow i))).length => limit s u p hgrow i) := by
  rw [limit_fixed_eq s hu hgrow k]

/-! ### Syndetic 2-binomial cuts of the two fixed points -/

/-- In a concatenation of blocks of length at most `B`, every `m` up to the total
length has a block boundary in `[m, m + B]`. -/
theorem exists_cut (B : ℕ) : ∀ (ws : List (List α)), (∀ w ∈ ws, w.length ≤ B) →
    ∀ m, m ≤ ws.flatten.length →
      ∃ k, m ≤ (ws.take k).flatten.length ∧ (ws.take k).flatten.length ≤ m + B := by
  intro ws
  induction ws with
  | nil =>
    intro _ m hm
    exact ⟨0, by simpa using hm, by simp⟩
  | cons w ws ih =>
    intro hB m hm
    have hw : w.length ≤ B := hB w (by simp)
    by_cases h0 : m = 0
    · exact ⟨0, by simp [h0], by simp⟩
    by_cases h1 : m ≤ w.length
    · exact ⟨1, by simpa using h1, by simp; omega⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (fun w' hw' => hB w' (by simp [hw'])) (m - w.length)
        (by simp only [List.flatten_cons, List.length_append] at hm; omega)
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [List.take_succ_cons, List.flatten_cons, List.length_append]; omega
      · simp only [List.take_succ_cons, List.flatten_cons, List.length_append]; omega

/-- **(3)** The two `σᵖ`-invariant limit words of a periodic state of a child
system all of whose states are 2-binomially equivalent agree in `N₁` and `N₂`
on a syndetic set of prefix lengths, with gaps bounded by the maximal state
length `B`. -/
theorem fixed_points_equiv2_syndetic (S : ChildSystem α) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ S.C) {p : ℕ}
    (hu : T₀.1 <+: (subst S.s)^[p] T₀.1) (hv : T₀.2 <+: (subst S.s)^[p] T₀.2)
    (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hgrow : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.1).length)
    (hgrowy : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.2).length)
    (B : ℕ) (hB : ∀ U ∈ S.C, U.1.length ≤ B) :
    ∀ m, ∃ c, m ≤ c ∧ c ≤ m + B ∧
      Equiv2 (List.ofFn (fun i : Fin c => limit S.s T₀.1 p hgrow i))
        (List.ofFn (fun i : Fin c => limit S.s T₀.2 p hgrowy i)) := by
  intro m
  obtain ⟨n, hn⟩ := hgrow m
  set bs := S.desc (p * n) T₀ with hbs
  have hmem : ∀ U ∈ bs, U ∈ S.C := S.desc_mem _ T₀ hT₀
  have htop : (bs.map Prod.fst).flatten = (subst S.s)^[p * n] T₀.1 := S.desc_top _ T₀ hT₀
  have hbot : (bs.map Prod.snd).flatten = (subst S.s)^[p * n] T₀.2 := S.desc_bot _ T₀ hT₀
  have hK : ∀ U ∈ bs, Equiv2 U.1 U.2 := fun U hU => hK2 U (hmem U hU)
  obtain ⟨k, hk1, hk2⟩ := exists_cut B (bs.map Prod.fst)
    (by
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨U, hU, rfl⟩ := hw
      exact hB U (hmem U hU))
    m (by rw [htop]; exact hn.le)
  rw [← List.map_take] at hk1 hk2
  set A := ((bs.take k).map Prod.fst).flatten with hA
  set A' := ((bs.take k).map Prod.snd).flatten with hA'
  have hE : Equiv2 A A' := equiv2_at_cuts bs hK k
  have hlen : A.length = A'.length := Equiv1.length_eq hE.1
  have hApre : A <+: (subst S.s)^[p * n] T₀.1 := by
    rw [← htop, hA]
    conv_rhs => rw [← List.take_append_drop k bs]
    rw [List.map_append, List.flatten_append]
    exact List.prefix_append _ _
  have hA'pre : A' <+: (subst S.s)^[p * n] T₀.2 := by
    rw [← hbot, hA']
    conv_rhs => rw [← List.take_append_drop k bs]
    rw [List.map_append, List.flatten_append]
    exact List.prefix_append _ _
  refine ⟨A.length, hk1, hk2, ?_⟩
  have e1 := ofFn_limit_of_prefix S.s hu hgrow hApre
  have e2 := ofFn_limit_of_prefix S.s hv hgrowy hA'pre
  rw [← hlen] at e2
  rw [e1, e2]
  exact hE

/-! ### Growth, first letters, and the assembled reduction lemma -/

theorem subst_ne_nil (s : α → List α) (hs : ∀ a, s a ≠ []) {w : List α} (hw : w ≠ []) :
    subst s w ≠ [] := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [subst, hs a]

theorem iterate_subst_ne_nil (s : α → List α) (hs : ∀ a, s a ≠ []) (k : ℕ) {w : List α}
    (hw : w ≠ []) : (subst s)^[k] w ≠ [] := by
  induction k with
  | zero => exact hw
  | succ k ih => rw [Function.iterate_succ_apply']; exact subst_ne_nil s hs ih

/-- A nonerasing substitution does not shorten words. -/
theorem length_le_subst (s : α → List α) (hs : ∀ a, s a ≠ []) (w : List α) :
    w.length ≤ (subst s w).length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have h1 : 1 ≤ (s a).length := List.length_pos_of_ne_nil (hs a)
    simp only [subst, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem length_le_iterate_subst (s : α → List α) (hs : ∀ a, s a ≠ []) (k : ℕ) (w : List α) :
    w.length ≤ ((subst s)^[k] w).length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']; exact ih.trans (length_le_subst s hs _)

/-- **Growth** of the chain from a nonerasing substitution and one strict
extension `|u| < |σᵖ u|` (in the application: a primitive substitution, after
passing to a power whose images all have length at least two). -/
theorem grow_of_nonerasing (s : α → List α) (hs : ∀ a, s a ≠ []) {u : List α} {p : ℕ}
    (hu : u <+: (subst s)^[p] u) (hlt : u.length < ((subst s)^[p] u).length) :
    ∀ m, ∃ n, m < ((subst s)^[p * n] u).length := by
  obtain ⟨r, hr⟩ := hu
  have hr0 : r ≠ [] := by
    rintro rfl
    rw [List.append_nil] at hr
    rw [← hr] at hlt
    exact lt_irrefl _ hlt
  have key : ∀ n, n ≤ ((subst s)^[p * n] u).length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h1 : (subst s)^[p * (n + 1)] u = (subst s)^[p * n] u ++ (subst s)^[p * n] r := by
        rw [show p * (n + 1) = p * n + p by ring, Function.iterate_add_apply, ← hr,
          iterate_subst_append]
      have h2 := List.length_pos_of_ne_nil (iterate_subst_ne_nil s hs (p * n) hr0)
      rw [h1, List.length_append]
      omega
  exact fun m => ⟨m + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (key (m + 1))⟩

/-- The limit word starts with the first letter of `u`. -/
theorem limit_zero (s : α → List α) {u : List α} {p : ℕ} (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) (hne : u ≠ []) :
    limit s u p hgrow 0 = u.head hne := by
  have h0 : 0 < ((subst s)^[p * 0] u).length := by
    simpa using List.length_pos_of_ne_nil hne
  rw [limit_spec s hu hgrow 0 0 h0]
  cases u with
  | nil => exact absurd rfl hne
  | cons a t => simp

/-- **Reduction lemma, limit form.**  Let `S` be a child system of a
nonerasing substitution all of whose states are irreducible, noncoincident
(`U.1 ≠ U.2`) and 2-binomially equivalent, and strictly lengthened by one
application of `σ` on both tracks.  Then some state `T₀` and `p ≥ 1` give two
`σᵖ`-invariant limit words with **different first letters** that are
2-binomially equivalent on a syndetic set of prefix lengths, with gaps at most
the maximal state length `S.C.sup (·.1.length)`. -/
theorem reduction_limit (S : ChildSystem α) (hs : ∀ a, S.s a ≠ [])
    (T : List α × List α) (hT : T ∈ S.C) (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2)
    (hstrict : ∀ U ∈ S.C, Irreducible U.1 U.2 ∧ U.1 ≠ U.2)
    (hexp : ∀ U ∈ S.C,
      U.1.length < (subst S.s U.1).length ∧ U.2.length < (subst S.s U.2).length) :
    ∃ T₀ ∈ S.C, ∃ p ≥ 1, ∃ (_ : T₀.1 <+: (subst S.s)^[p] T₀.1)
      (_ : T₀.2 <+: (subst S.s)^[p] T₀.2)
      (hg : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.1).length)
      (hg' : ∀ m, ∃ n, m < ((subst S.s)^[p * n] T₀.2).length),
      limit S.s T₀.1 p hg 0 ≠ limit S.s T₀.2 p hg' 0 ∧
      ∀ m, ∃ c, m ≤ c ∧ c ≤ m + S.C.sup (fun U => U.1.length) ∧
        Equiv2 (List.ofFn (fun i : Fin c => limit S.s T₀.1 p hg i))
          (List.ofFn (fun i : Fin c => limit S.s T₀.2 p hg' i)) := by
  obtain ⟨T₀, h₀, p, hp, hper⟩ := S.exists_periodic T hT
  obtain ⟨h1, h2⟩ := S.iterate_first_prefix p T₀ h₀
  rw [hper] at h1 h2
  -- one strict extension along each track, for `p ≥ 1`
  have hstep : ∀ w : List α, w.length < (subst S.s w).length →
      w.length < ((subst S.s)^[p] w).length := by
    intro w hw
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    exact hw.trans_le (length_le_iterate_subst S.s hs k _)
  have hg := grow_of_nonerasing S.s hs h1 (hstep _ (hexp T₀ h₀).1)
  have hg' := grow_of_nonerasing S.s hs h2 (hstep _ (hexp T₀ h₀).2)
  refine ⟨T₀, h₀, p, hp, h1, h2, hg, hg', ?_, ?_⟩
  · -- distinct first letters
    have hne1 : T₀.1 ≠ [] := by
      intro h; have := (hexp T₀ h₀).1; rw [h] at this; simp [subst] at this
    have hne2 : T₀.2 ≠ [] := by
      intro h; have := (hexp T₀ h₀).2; rw [h] at this; simp [subst] at this
    rw [limit_zero S.s h1 hg hne1, limit_zero S.s h2 hg' hne2]
    obtain ⟨hirr, hnc⟩ := hstrict T₀ h₀
    have hbal := (hK2 T₀ h₀).1
    revert hne1 hne2 hirr hnc hbal
    rcases T₀ with ⟨_ | ⟨a, u⟩, _ | ⟨b, v⟩⟩ <;> intro hne1 hne2 hirr hnc hbal
    · exact absurd rfl hne1
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact heads_ne hbal hirr hnc
  · exact fixed_points_equiv2_syndetic S h₀ h1 h2 hK2 hg hg' _
      (fun U hU => Finset.le_sup (f := fun U => U.1.length) hU)

end Psc.FixedPointLimit
