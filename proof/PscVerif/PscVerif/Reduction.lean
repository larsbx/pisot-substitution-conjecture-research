/-
# Zero-return reduction of balanced pairs

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `def:balanced` (the
reduction `red(u, v)`) and `def:bpa` (the children of a state are the blocks of
`red(σ u, σ v)`); `docs/c4-concentration-attack-2026-11-06.md` §8.

`red u v` cuts the pair `(u, v)` at every zero return, i.e. at every position
`k ≥ 1` where the prefixes `u[k]`, `v[k]` have equal letter counts, into
consecutive blocks.  It is computed by `redAux`, a structural recursion that
reads both words letter by letter and carries the current (not yet closed)
block as an accumulator; a block is closed as soon as its two tracks are
permutations of each other (`List.Perm`, which is `Equiv1` by
`equiv1_iff_perm`).  If the words have equal length but are not balanced, the
trailing unclosed part is emitted as a last (unbalanced) block, so no letter is
lost (`red_top`, `red_bot`); for unequal lengths the excess of the longer word
is dropped.  Only the balanced, equal-length case is used below.

Proved here, in full (no finiteness of the alphabet is used except in the
`decide` controls):

* `red_top`, `red_bot`: for `|u| = |v|`, the first (resp. second) tracks of
  `red u v` concatenate to `u` (resp. `v`); `red_ne_nil`: `red u v ≠ []` for
  `u ≠ []`;
* `red_isBlock`: for balanced `u, v` (`Equiv1`), every block of `red u v` is an
  `IsBlock`: nonempty, balanced and `IrreduciblePair`;
* **`red_unique`**: any list of `IsBlock` blocks whose tracks concatenate to
  `u` and `v` equals `red u v` (the zero-return factorization is unique), and
  `red_eq_iff` packages (a), (b), (c) for balanced pairs;
* `red_swap`: `red v u = (red u v).map Prod.swap`, for all `u, v`;
* `equiv1_subst`: a substitution preserves `Equiv1` (via `List.Perm`, over any
  alphabet);
* `redSystem`: for a nonerasing substitution `s` and a finite set `C` of
  balanced pairs with nonempty tracks closed under taking the blocks of
  `red (σ u) (σ v)`, the `Psc.Binomial.ChildSystem` with
  `children T = red (σ T.1) (σ T.2)` (`top`, `bot`, `nonempty` are derived);
  `redSystem_isBlock`: its children are irreducible balanced pairs;
* `redSystem_states_isBlock`: if every state of `C` occurs as a child of a
  state of `C` (e.g. `C` strongly connected), every state is an `IsBlock`;
* `redSystem_children_swap` and `redNormalisation`: the children of `T.swap`
  are the swaps of the children of `T`, so for a swap-closed `C` every choice
  of representatives `R ⊆ C` with the `cover` / `not_both` properties gives a
  `Psc.SignedCocycle.Normalisation` of `redSystem` — the hypotheses
  `swap_mem` (given) and `children_swap` (derived) of that structure are thus
  discharged for the zero-return children of the manuscript.  Such an `R`
  exists only for a coincidence-free `C`
  (`Psc.SignedCocycle.Normalisation.noncoincident`): coincidence blocks such as
  `(2, 2)` must already be excluded from `C`, as they are from a strict
  component;
* controls (`decide`): `red (0110) (1001) = [(01,10), (10,01)]`, a coincidence
  block, an unbalanced leftover; `tmRedSystem`, the Thue–Morse system built by
  `redSystem`, has the same children as `Psc.Binomial.thueMorse` on its states,
  and `tmRedNormalisation` is a normalisation of it with `R = {(01, 10)}`.

Not proved here: `lem:descendants` (that the blocks of `red (σⁿ u) (σⁿ v)` are
the depth-`n` descendants, i.e. that `red` commutes with inflation of the
block boundaries; `ChildSystem.desc` is not compared with `red` at depth
`n > 1`), the inherited/newborn distinction of `lem:inherited`, reachability
from the seeds, coincidence blocks being terminal, and the finiteness
hypothesis G1 (here `C` is an arbitrary given finite set).  `lem:descendants`,
reachability from the seeds and coincidence blocks being terminal are treated in
`Psc.Descendants`.
-/
import PscVerif.SignedCocycle
import PscVerif.FixedPointLimit

namespace Psc.Reduction

open Psc.Binomial Psc.Incidence Psc.SignedCocycle

variable {α : Type*} [DecidableEq α]

/-- `Equiv1` is the permutation relation. -/
theorem equiv1_iff_perm {x y : List α} : Equiv1 x y ↔ x.Perm y :=
  List.perm_iff_count.symm

/-- The reduction with an accumulator: `redAux pu pv u v` reads `u` and `v`
letter by letter, `(pu, pv)` being the current unclosed block. -/
def redAux : List α → List α → List α → List α → List (List α × List α)
  | pu, pv, a :: u, b :: v =>
    if (pu ++ [a]).Perm (pv ++ [b]) then (pu ++ [a], pv ++ [b]) :: redAux [] [] u v
    else redAux (pu ++ [a]) (pv ++ [b]) u v
  | pu, pv, _, _ => if pu = [] ∧ pv = [] then [] else [(pu, pv)]

/-- The zero-return reduction `red(u, v)` of `def:balanced`. -/
def red (u v : List α) : List (List α × List α) := redAux [] [] u v

/-- A block of a reduction: nonempty, balanced, irreducible. -/
def IsBlock (T : List α × List α) : Prop :=
  T.1 ≠ [] ∧ Equiv1 T.1 T.2 ∧ IrreduciblePair T.1 T.2

theorem redAux_cons_cons (pu pv : List α) (a b : α) (u v : List α) :
    redAux pu pv (a :: u) (b :: v) =
      if (pu ++ [a]).Perm (pv ++ [b]) then (pu ++ [a], pv ++ [b]) :: redAux [] [] u v
      else redAux (pu ++ [a]) (pv ++ [b]) u v := rfl

theorem redAux_of_nil (pu pv : List α) {u v : List α} (h : u = [] ∨ v = []) :
    redAux pu pv u v = if pu = [] ∧ pv = [] then [] else [(pu, pv)] := by
  rcases h with rfl | rfl
  · cases v <;> rfl
  · cases u <;> rfl

/-! ### Side swap -/

theorem redAux_swap (pu pv u v : List α) :
    redAux pv pu v u = (redAux pu pv u v).map Prod.swap := by
  induction u generalizing pu pv v with
  | nil =>
    rw [redAux_of_nil _ _ (Or.inr rfl), redAux_of_nil _ _ (Or.inl rfl)]
    by_cases h : pu = [] ∧ pv = []
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]; rfl
  | cons a u ih =>
    cases v with
    | nil =>
      rw [redAux_of_nil _ _ (Or.inl rfl), redAux_of_nil _ _ (Or.inr rfl)]
      by_cases h : pu = [] ∧ pv = []
      · simp [h]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]; rfl
    | cons b v =>
      rw [redAux_cons_cons, redAux_cons_cons]
      by_cases h : (pu ++ [a]).Perm (pv ++ [b])
      · rw [ite_eq_left h, ite_eq_left h.symm, ih]; rfl
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm), ih]

/-- (d) Swapping the two words swaps every block. -/
theorem red_swap (u v : List α) : red v u = (red u v).map Prod.swap :=
  redAux_swap [] [] u v

/-! ### The tracks concatenate to the two words -/

theorem redAux_top (pu pv u v : List α) (h : u.length = v.length) :
    ((redAux pu pv u v).map Prod.fst).flatten = pu ++ u := by
  induction u generalizing pu pv v with
  | nil =>
    rw [redAux_of_nil _ _ (Or.inl rfl)]
    by_cases hp : pu = [] ∧ pv = []
    · simp [hp]
    · simp [hp]
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      have h' : u.length = v.length := by simpa using h
      rw [redAux_cons_cons]
      split_ifs <;> simp [ih _ _ _ h']

/-- (a) The first tracks of `red u v` concatenate to `u`. -/
theorem red_top {u v : List α} (h : u.length = v.length) :
    ((red u v).map Prod.fst).flatten = u := by
  simpa [red] using redAux_top [] [] u v h

/-- (a) The second tracks of `red u v` concatenate to `v`. -/
theorem red_bot {u v : List α} (h : u.length = v.length) :
    ((red u v).map Prod.snd).flatten = v := by
  have := red_top (u := v) (v := u) h.symm
  rw [red_swap, List.map_map] at this
  simpa [Function.comp_def] using this

theorem red_ne_nil {u v : List α} (hu : u ≠ []) (h : u.length = v.length) :
    red u v ≠ [] := by
  intro h0
  have := red_top h
  rw [h0] at this
  exact hu this.symm

/-! ### Blocks are irreducible balanced pairs -/

theorem equiv1_cancel {x y u v : List α} (h : Equiv1 x y) (h' : Equiv1 (x ++ u) (y ++ v)) :
    Equiv1 u v := by
  intro c
  have := h' c
  simp only [List.count_append, h c] at this
  omega

theorem redAux_isBlock (pu pv u v : List α) (hp : pu.length = pv.length)
    (huv : u.length = v.length)
    (hz : ∀ k, 0 < k → k ≤ pu.length → ¬ Equiv1 (pu.take k) (pv.take k))
    (hbal : Equiv1 (pu ++ u) (pv ++ v)) : ∀ T ∈ redAux pu pv u v, IsBlock T := by
  induction u generalizing pu pv v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp (by simp at huv; omega)
    subst hv
    have hpu : pu = [] := by
      by_contra hne
      apply hz pu.length (List.length_pos_iff.mpr hne) le_rfl
      rw [List.take_length, hp, List.take_length]
      simpa using hbal
    have hpv : pv = [] := List.length_eq_zero_iff.mp (by rw [← hp, hpu]; rfl)
    subst hpu hpv
    simp [redAux_of_nil]
  | cons a u ih =>
    cases v with
    | nil => simp at huv
    | cons b v =>
      have huv' : u.length = v.length := by simpa using huv
      rw [redAux_cons_cons]
      by_cases hP : (pu ++ [a]).Perm (pv ++ [b])
      · rw [ite_eq_left hP]
        have hE : Equiv1 (pu ++ [a]) (pv ++ [b]) := equiv1_iff_perm.2 hP
        intro T hT
        rcases List.mem_cons.1 hT with rfl | hT
        · refine ⟨by simp, hE, fun k hk hkl => ?_⟩
          have hk' : k ≤ pu.length := by simp at hkl; omega
          rw [List.take_append_of_le_length hk', List.take_append_of_le_length (hp ▸ hk')]
          exact hz k hk hk'
        · refine ih [] [] v rfl huv' (fun k hk hk' => by simp at hk'; omega) ?_ T hT
          exact equiv1_cancel hE (by simpa using hbal)
      · rw [ite_eq_right hP]
        refine ih _ _ v (by simp [hp]) huv' (fun k hk hk' => ?_) (by simpa using hbal)
        rcases Nat.lt_or_ge k (pu.length + 1) with hlt | hge
        · have hk' : k ≤ pu.length := by omega
          rw [List.take_append_of_le_length hk', List.take_append_of_le_length (hp ▸ hk')]
          exact hz k hk hk'
        · have h1 : k = (pu ++ [a]).length := by simp at hk' ⊢; omega
          have h2 : k = (pv ++ [b]).length := by simp [← hp] at hk' ⊢; omega
          have e1 : (pu ++ [a]).take k = pu ++ [a] := by rw [h1, List.take_length]
          have e2 : (pv ++ [b]).take k = pv ++ [b] := by rw [h2, List.take_length]
          rw [e1, e2]
          exact fun hE => hP (equiv1_iff_perm.1 hE)

/-- (b) For a balanced pair, every block of `red u v` is nonempty, balanced and
irreducible. -/
theorem red_isBlock {u v : List α} (h : Equiv1 u v) : ∀ T ∈ red u v, IsBlock T :=
  redAux_isBlock [] [] u v rfl h.length_eq (fun k hk hk' => by simp at hk'; omega) (by simpa)

/-! ### Uniqueness of the factorization -/

theorem redAux_unique (u : List α) :
    ∀ (v pu pv x y : List α) (rest : List (List α × List α)),
    pu.length = pv.length → x ≠ [] → IsBlock (pu ++ x, pv ++ y) →
    (∀ T ∈ rest, IsBlock T) → u = x ++ (rest.map Prod.fst).flatten →
    v = y ++ (rest.map Prod.snd).flatten →
    redAux pu pv u v = (pu ++ x, pv ++ y) :: rest := by
  induction u with
  | nil =>
    intro v pu pv x y rest _ hx _ _ hu _
    exact absurd (List.append_eq_nil_iff.mp hu.symm).1 hx
  | cons a u ih =>
    intro v pu pv x y rest hp hx hB hrest hu hv
    obtain ⟨a', x', rfl⟩ := List.exists_cons_of_ne_nil hx
    simp only [List.cons_append, List.cons.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    have hlen : (pu ++ a :: x').length = (pv ++ y).length := hB.2.1.length_eq
    obtain ⟨b, y', rfl⟩ : ∃ b y', y = b :: y' :=
      List.exists_cons_of_ne_nil (fun hy => by subst hy; simp at hlen; omega)
    have hxy : x'.length = y'.length := by simp at hlen; omega
    subst hv
    rw [List.cons_append, redAux_cons_cons]
    by_cases hx' : x' = []
    · have hy' : y' = [] := List.length_eq_zero_iff.mp (by rw [← hxy, hx']; rfl)
      subst hx' hy'
      rw [ite_eq_left (equiv1_iff_perm.1 hB.2.1)]
      simp only [List.nil_append, List.cons.injEq, true_and]
      cases rest with
      | nil => rfl
      | cons r rest =>
        have hr := hrest r (by simp)
        simpa using ih _ [] [] r.1 r.2 rest rfl hr.1 (by simpa using hr)
          (fun T hT => hrest T (by simp [hT])) (by simp) rfl
    · have hk : pu.length + 1 < (pu ++ a :: x').length := by
        have := List.length_pos_iff.mpr hx'; simp; omega
      have hirr := hB.2.2 (pu.length + 1) (by omega) hk
      rw [List.take_length_add_append, hp, List.take_length_add_append] at hirr
      rw [ite_eq_right (fun hP => hirr (by simpa using equiv1_iff_perm.2 hP))]
      simpa using ih _ (pu ++ [a]) (pv ++ [b]) x' y' rest (by simp [hp]) hx'
        (by simpa using hB) hrest rfl rfl

/-- (c) The zero-return factorization is unique: a list of nonempty, balanced,
irreducible blocks whose tracks concatenate to `u` and `v` is `red u v`. -/
theorem red_unique {u v : List α} (bs : List (List α × List α)) (hbs : ∀ T ∈ bs, IsBlock T)
    (hu : (bs.map Prod.fst).flatten = u) (hv : (bs.map Prod.snd).flatten = v) :
    bs = red u v := by
  subst hu hv
  cases bs with
  | nil => rfl
  | cons r rest =>
    have hr := hbs r (by simp)
    symm
    simpa [red] using redAux_unique _ _ [] [] r.1 r.2 rest rfl hr.1 (by simpa using hr)
      (fun T hT => hbs T (by simp [hT])) (by simp) (by simp)

/-- For a balanced pair, `red u v` is characterized as the unique factorization
into irreducible balanced blocks. -/
theorem red_eq_iff {u v : List α} (h : Equiv1 u v) (bs : List (List α × List α)) :
    bs = red u v ↔ (∀ T ∈ bs, IsBlock T) ∧ (bs.map Prod.fst).flatten = u ∧
      (bs.map Prod.snd).flatten = v := by
  constructor
  · rintro rfl
    exact ⟨red_isBlock h, red_top h.length_eq, red_bot h.length_eq⟩
  · rintro ⟨hb, hu, hv⟩
    exact red_unique bs hb hu hv

/-! ### The zero-return child system -/

/-- A substitution preserves balance. -/
theorem equiv1_subst (s : α → List α) {x y : List α} (h : Equiv1 x y) :
    Equiv1 (subst s x) (subst s y) :=
  equiv1_iff_perm.2 ((equiv1_iff_perm.1 h).map s).flatten

/-- The child system of `def:bpa`: the children of a state `T` are the blocks
of `red (σ T.1) (σ T.2)`. -/
def redSystem (s : α → List α) (hs : ∀ a, s a ≠ []) (C : Finset (List α × List α))
    (hC : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [])
    (hclosed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C) :
    ChildSystem α where
  s := s
  C := C
  children T := red (subst s T.1) (subst s T.2)
  top T hT := red_top (equiv1_subst s (hC T hT).1).length_eq
  bot T hT := red_bot (equiv1_subst s (hC T hT).1).length_eq
  closed := hclosed
  nonempty T hT :=
    red_ne_nil (Psc.FixedPointLimit.subst_ne_nil s hs (hC T hT).2)
      (equiv1_subst s (hC T hT).1).length_eq

section RedSystem

variable (s : α → List α) (hs : ∀ a, s a ≠ []) (C : Finset (List α × List α))
  (hC : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [])
  (hclosed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C)

/-- The children in `redSystem` are irreducible balanced pairs. -/
theorem redSystem_isBlock :
    ∀ T ∈ (redSystem s hs C hC hclosed).C,
      ∀ U ∈ (redSystem s hs C hC hclosed).children T, IsBlock U :=
  fun T hT => red_isBlock (equiv1_subst s (hC T hT).1)

/-- If every state occurs as a child of a state, every state is a block. -/
theorem redSystem_states_isBlock
    (hocc : ∀ T ∈ C, ∃ U ∈ C, T ∈ red (subst s U.1) (subst s U.2)) :
    ∀ T ∈ (redSystem s hs C hC hclosed).C, IsBlock T := fun T hT => by
  obtain ⟨U, hU, hTU⟩ := hocc T hT
  exact redSystem_isBlock s hs C hC hclosed U hU T hTU

/-- (f) Swapping a parent's sides swaps all its children's sides, in order. -/
theorem redSystem_children_swap (T : List α × List α) :
    (redSystem s hs C hC hclosed).children T.swap =
      ((redSystem s hs C hC hclosed).children T).map Prod.swap :=
  red_swap _ _

/-- (f) For a swap-closed `C`, any representative set `R ⊆ C` meeting every
state or its swap exactly once is a normalisation of `redSystem`;
`children_swap` is derived from `red_swap`.  `hnot` forces `C` to be
coincidence-free (`Normalisation.noncoincident`). -/
def redNormalisation (hswap : ∀ T ∈ C, T.swap ∈ C) (R : Finset (List α × List α))
    (hsub : R ⊆ C) (hcover : ∀ T ∈ C, T ∈ R ∨ T.swap ∈ R)
    (hnot : ∀ T ∈ R, T.swap ∉ R) :
    Normalisation (redSystem s hs C hC hclosed) where
  R := R
  swap_mem := hswap
  children_swap T _ := redSystem_children_swap s hs C hC hclosed T
  sub := hsub
  cover := hcover
  not_both := hnot

end RedSystem

/-! ### Controls -/

/-- `(0110, 1001)` = `σ_TM (01, 10)` splits into `(01, 10), (10, 01)`. -/
example : red ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] =
    [([0, 1], [1, 0]), ([1, 0], [0, 1])] := by
  decide

/-- A coincidence block `(2, 2)` after a noncoincident one. -/
example : red ([0, 1, 2] : List (Fin 3)) [1, 0, 2] = [([0, 1], [1, 0]), ([2], [2])] := by
  decide

/-- An unbalanced pair: the unclosed rest is emitted as a last block. -/
example : red ([0, 1, 0] : List (Fin 2)) [1, 0, 1] = [([0, 1], [1, 0]), ([0], [1])] := by
  decide

/-- The Thue–Morse child system, with children computed by zero-return
reduction. -/
def tmRedSystem : ChildSystem (Fin 2) :=
  redSystem thueMorseSubst (by decide) {tmPair, tmPair.swap} (by decide) (by decide)

/-- `tmRedSystem` agrees with the hand-written `Psc.Binomial.thueMorse`. -/
theorem tmRedSystem_eq : tmRedSystem.C = thueMorse.C ∧
    ∀ T ∈ tmRedSystem.C, tmRedSystem.children T = thueMorse.children T := by
  decide

/-- A normalisation of `tmRedSystem` with `R = {(01, 10)}`. -/
def tmRedNormalisation : Normalisation tmRedSystem :=
  redNormalisation thueMorseSubst (by decide) {tmPair, tmPair.swap} (by decide) (by decide)
    (by decide) {tmPair} (by decide) (by decide) (by decide)

end Psc.Reduction
