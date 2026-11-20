/-
# Strict-system definitions and the literal strong-coincidence exclusion

Canonical extraction from `StrictSystem.lean`: its original declarations
and proof bodies are unchanged. Importing the full `StrictSystem` module
still exposes these names alongside its component and sector theorems.
The lightweight core depends only on the literal descendant calculus and
supports consumers that do not need the later spectral machinery.
-/
import PscVerif.Descendants
import Mathlib.Tactic.FinCases

set_option linter.dupNamespace false

namespace Psc.StrictSystem

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants Psc.SignedCocycle

variable {α : Type*} [DecidableEq α]

/-! ### Strict systems -/

/-- A **strict system** for `s` (cut-pair note §2): a finite nonempty set `C` of
ordered pairs, each an irreducible balanced block (`IsBlock`) and
noncoincident, closed under taking the blocks of `red (σ T.1) (σ T.2)`. -/
structure StrictSystem (s : α → List α) (C : Finset (List α × List α)) : Prop where
  nonempty : C.Nonempty
  isBlock : ∀ T ∈ C, IsBlock T
  noncoincident : ∀ T ∈ C, T.1 ≠ T.2
  closed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C

/-- Over a finite alphabet `IsBlock` is decidable (for the `decide` controls). -/
instance [Fintype α] (T : List α × List α) : Decidable (IsBlock T) := by
  unfold IsBlock; infer_instance

/-- A block with its sides swapped is a block. -/
theorem isBlock_swap {T : List α × List α} (h : IsBlock T) : IsBlock T.swap := by
  obtain ⟨hne, hbal, hirr⟩ := h
  refine ⟨?_, fun a => (hbal a).symm, fun k hk hkl hE => hirr k hk ?_ fun a => (hE a).symm⟩
  · intro h0
    apply hne
    apply List.length_eq_zero_iff.mp
    rw [hbal.length_eq]
    simpa using congrArg List.length h0
  · simpa [hbal.length_eq] using hkl

/-- The swap closure `C ∪ swap C` (the `Finset` form of `Psc.Descendants`). -/
abbrev swapClosureF (C : Finset (List α × List α)) : Finset (List α × List α) :=
  C ∪ C.image Prod.swap

theorem mem_swapClosureF {C : Finset (List α × List α)} {T : List α × List α} :
    T ∈ swapClosureF C ↔ T ∈ C ∨ T.swap ∈ C := by
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨U, hU, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hU)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨T.swap, h, Prod.swap_swap T⟩

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)}

theorem equiv1 (h : StrictSystem s C) : ∀ T ∈ C, Equiv1 T.1 T.2 :=
  fun T hT => (h.isBlock T hT).2.1

/-- The hypothesis `hC` of `Psc.Reduction.redSystem`. -/
theorem balanced (h : StrictSystem s C) : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [] :=
  fun T hT => ⟨(h.isBlock T hT).2.1, (h.isBlock T hT).1⟩

theorem childClosed (h : StrictSystem s C) : ChildClosed s ↑C :=
  fun T hT U hU => h.closed T hT U hU

/-- Every block of `red (σⁿ T.1) (σⁿ T.2)`, `T ∈ C`, lies in `C`: the factor
closure used in the proof of Theorem A(2). -/
theorem mem_of_red_iterate (h : StrictSystem s C) (n : ℕ) :
    ∀ T ∈ C, ∀ U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2), U ∈ C := by
  induction n with
  | zero =>
    intro T hT U hU
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
      red_of_isBlock (h.isBlock T hT)] at hU
    rw [List.mem_singleton.1 hU]; exact hT
  | succ n ih =>
    intro T hT U hU
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      red_iterate_subst s n (equiv1_subst s (h.equiv1 T hT))] at hU
    obtain ⟨V, hV, hUV⟩ := List.mem_flatMap.1 hU
    exact ih V (h.closed T hT V hV) U hUV

/-- States reachable from a state of `C` in the full child graph lie in `C`. -/
theorem reflTransGen_mem (h : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.ReflTransGen (Child s) T U) : U ∈ C := by
  induction hTU with
  | refl => exact hT
  | tail _ hVU ih => exact h.closed _ ih _ hVU

theorem transGen_mem (h : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.TransGen (Child s) T U) : U ∈ C :=
  h.reflTransGen_mem hT hTU.to_reflTransGen

/-- **The swap closure of a strict system is strict.** -/
theorem swapClosure (h : StrictSystem s C) : StrictSystem s (swapClosureF C) where
  nonempty := h.nonempty.mono Finset.subset_union_left
  isBlock T hT := by
    rcases mem_swapClosureF.1 hT with hT | hT
    · exact h.isBlock T hT
    · simpa using isBlock_swap (h.isBlock _ hT)
  noncoincident T hT := swapClosureF_coincidenceFree (D := C) h.noncoincident T hT
  closed T hT U hU := swapClosureF_childClosed (D := C) h.childClosed T hT U hU

theorem swapClosure_swap_mem : ∀ T ∈ swapClosureF C, T.swap ∈ swapClosureF C :=
  fun T hT => swapClosureF_swapClosed (D := C) T hT

/-! ### The zero-return child system and its normalisations -/

/-- For nonerasing `s`, the zero-return child system (`Psc.Reduction.redSystem`)
of a strict system: states `C`, children `red (σ T.1) (σ T.2)`. -/
def toChildSystem (h : StrictSystem s C) (hs : ∀ a, s a ≠ []) : ChildSystem α :=
  redSystem s hs C h.balanced h.closed

variable (h : StrictSystem s C) (hs : ∀ a, s a ≠ [])

@[simp] theorem toChildSystem_C : (h.toChildSystem hs).C = C := rfl

@[simp] theorem toChildSystem_s : (h.toChildSystem hs).s = s := rfl

theorem toChildSystem_children (T : List α × List α) :
    (h.toChildSystem hs).children T = red (subst s T.1) (subst s T.2) := rfl

/-- The balance hypothesis `hbal` of the sector theorems (`Psc.ParikhRank`,
`Psc.Degree2Sector`, `Psc.KernelCofactor`, ...). -/
theorem toChildSystem_equiv1 : ∀ T ∈ (h.toChildSystem hs).C, Equiv1 T.1 T.2 := h.equiv1

/-- The hypothesis `hC : S.C.Nonempty` of the sector theorems. -/
theorem toChildSystem_nonempty : (h.toChildSystem hs).C.Nonempty := h.nonempty

theorem toChildSystem_isBlock : ∀ T ∈ (h.toChildSystem hs).C, IsBlock T := h.isBlock

theorem toChildSystem_top_ne_nil : ∀ T ∈ (h.toChildSystem hs).C, T.1 ≠ [] :=
  fun T hT => (h.isBlock T hT).1

theorem toChildSystem_noncoincident : ∀ T ∈ (h.toChildSystem hs).C, T.1 ≠ T.2 :=
  h.noncoincident

/-- `lem:descendants` in the child system of a strict system, at every depth. -/
theorem toChildSystem_desc (n : ℕ) (T : List α × List α) (hT : T ∈ C) :
    (h.toChildSystem hs).desc n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  redSystem_desc_of_isBlock s hs C h.balanced h.closed n T hT (h.isBlock T hT)

/-- The lexicographic normalisation (`Psc.Descendants.lexNormalisation`) of a
swap-closed strict system. -/
def lexNormOf [LinearOrder α] (hswap : ∀ T ∈ C, T.swap ∈ C) :
    Normalisation (h.toChildSystem hs) :=
  lexNormalisation s hs C h.balanced h.closed hswap h.noncoincident

/-- The lexicographic normalisation of the swap closure of a strict system
(swap closure first, `swapClosure`). -/
def lexNorm [LinearOrder α] : Normalisation (h.swapClosure.toChildSystem hs) :=
  h.swapClosure.lexNormOf hs swapClosure_swap_mem

theorem lexNorm_R [LinearOrder α] :
    (h.lexNorm hs).R = (swapClosureF C).filter fun T => T.1 < T.2 := rfl

end StrictSystem

/-! ### Theorem A of the cut-pair note -/

/-- The **cut-pair set** `A(C)`, as ordered letter pairs: `(c, c')` is a cut pair
if some state of `C` has first letters `c` (top) and `c'` (bottom).  The note's
unordered `{c, c'} ∈ A(C)` is `CutPair C c c' ∨ CutPair C c' c`. -/
def CutPair (C : Finset (List α × List α)) (c c' : α) : Prop :=
  ∃ T ∈ C, T.1.head? = some c ∧ T.2.head? = some c'

/-- A *left strong-coincidence witness* for the letters `c, c'`:
`σⁿ(c) = P x Q`, `σⁿ(c') = P' x Q'` with `p(P) = p(P')` (`Equiv1`). -/
def StrongCoincidenceWitness (s : α → List α) (c c' : α) : Prop :=
  ∃ (n : ℕ) (P Q P' Q' : List α) (x : α), (subst s)^[n] [c] = P ++ x :: Q ∧
    (subst s)^[n] [c'] = P' ++ x :: Q' ∧ Equiv1 P P'

theorem strongCoincidenceWitness_comm {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ StrongCoincidenceWitness s c' c := by
  constructor <;>
  · rintro ⟨n, P, Q, P', Q', x, h1, h2, hP⟩
    exact ⟨n, P', Q', P, Q, x, h2, h1, fun a => (hP a).symm⟩

/-- The first block of `red (c :: q) (c' :: q')` begins with `c` on top and `c'`
on the bottom. -/
theorem exists_first_block {c c' : α} {q q' : List α} (h : Equiv1 (c :: q) (c' :: q')) :
    ∃ U ∈ red (c :: q) (c' :: q'), U.1.head? = some c ∧ U.2.head? = some c' := by
  obtain ⟨U, rest, hr⟩ := List.exists_cons_of_ne_nil
    (red_ne_nil (u := c :: q) (v := c' :: q') (by simp) h.length_eq)
  have hmem : U ∈ red (c :: q) (c' :: q') := by rw [hr]; exact List.mem_cons_self
  have hU := red_isBlock h U hmem
  have htop := red_top h.length_eq
  have hbot := red_bot h.length_eq
  rw [hr] at htop hbot
  simp only [List.map_cons, List.flatten_cons] at htop hbot
  have h2 : U.2 ≠ [] := fun h0 =>
    hU.1 (List.length_eq_zero_iff.mp (by rw [hU.2.1.length_eq, h0]; rfl))
  refine ⟨U, hmem, ?_, ?_⟩
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hU.1
    rw [hx] at htop ⊢
    simp only [List.cons_append, List.cons.injEq] at htop
    rw [htop.1]; rfl
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil h2
    rw [hx] at hbot ⊢
    simp only [List.cons_append, List.cons.injEq] at hbot
    rw [hbot.1]; rfl

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)} (h : StrictSystem s C)
include h

/-- **Theorem A(1).**  Every state has distinct first letters. -/
theorem first_letters_ne {T : List α × List α} (hT : T ∈ C) :
    ∃ (c c' : α) (u v : List α), T = (c :: u, c' :: v) ∧ c ≠ c' := by
  obtain ⟨hne, hbal, hirr⟩ := h.isBlock T hT
  have hnc := h.noncoincident T hT
  obtain ⟨u0, v0⟩ := T
  obtain ⟨c, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c', v, rfl⟩ := List.exists_cons_of_ne_nil (l := v0) fun h0 => by
    simp [h0] at hbal
    exact absurd hbal.length_eq (by simp)
  exact ⟨c, c', u, v, rfl, Psc.Binomial.heads_ne hbal hirr hnc⟩

/-- **Theorem A(1)**, cut-pair form: `A(C)` consists of off-diagonal pairs. -/
theorem cutPair_ne {c c' : α} (hcp : CutPair C c c') : c ≠ c' := by
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨d, d', u, v, rfl, hdd⟩ := h.first_letters_ne hT
  simp only [List.head?_cons, Option.some.injEq] at h1 h2
  exact h1 ▸ h2 ▸ hdd

/-- **Theorem A(1)**: `A(C)` is nonempty. -/
theorem exists_cutPair : ∃ c c', CutPair C c c' := by
  obtain ⟨T, hT⟩ := h.nonempty
  obtain ⟨c, c', u, v, rfl, -⟩ := h.first_letters_ne hT
  exact ⟨c, c', _, hT, rfl, rfl⟩

/-- **Theorem A(2)**, split form.  If `σⁿ(S) = (p c q, p' c' q')` for a state
`S ∈ C` with `p(p) = p(p')` (a proper balanced cut, the cut at index `0`
included), then `(c, c')` is a cut pair of `C`. -/
theorem cut_follow {T : List α × List α} (hT : T ∈ C) (n : ℕ) {p q p' q' : List α} {c c' : α}
    (hu : (subst s)^[n] T.1 = p ++ c :: q) (hv : (subst s)^[n] T.2 = p' ++ c' :: q')
    (hp : Equiv1 p p') : CutPair C c c' := by
  have hbal := equiv1_iterate_subst s n (h.equiv1 T hT)
  rw [hu, hv] at hbal
  have hrest : Equiv1 (c :: q) (c' :: q') := equiv1_cancel hp hbal
  obtain ⟨U, hU, h1, h2⟩ := exists_first_block hrest
  refine ⟨U, h.mem_of_red_iterate n T hT U ?_, h1, h2⟩
  rw [hu, hv, red_append hp hrest]
  exact List.mem_append_right _ hU

/-- **Theorem A(2)**, index form: a balanced cut at `k < |σⁿ(S.1)|` is followed by
the two letters of a cut pair. -/
theorem cut_follow_index {T : List α × List α} (hT : T ∈ C) (n : ℕ) {k : ℕ}
    (hk : k < ((subst s)^[n] T.1).length)
    (hcut : Equiv1 (((subst s)^[n] T.1).take k) (((subst s)^[n] T.2).take k)) :
    ∃ c c', ((subst s)^[n] T.1)[k]? = some c ∧ ((subst s)^[n] T.2)[k]? = some c' ∧
      CutPair C c c' := by
  have hlen := (equiv1_iterate_subst s n (h.equiv1 T hT)).length_eq
  have hk' : k < ((subst s)^[n] T.2).length := hlen ▸ hk
  refine ⟨_, _, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', ?_⟩
  refine h.cut_follow hT n (p := ((subst s)^[n] T.1).take k) (p' := ((subst s)^[n] T.2).take k)
    (q := ((subst s)^[n] T.1).drop (k + 1)) (q' := ((subst s)^[n] T.2).drop (k + 1)) ?_ ?_ hcut
  · rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  · rw [← List.drop_eq_getElem_cons hk', List.take_append_drop]

/-- **Theorem A(3)**: the first-letter map preserves the cut-pair set (and, by
`cutPair_ne`, separates it). -/
theorem cutPair_subst {c c' d d' : α} (hcp : CutPair C c c') (hd : (s c).head? = some d)
    (hd' : (s c').head? = some d') : CutPair C d d' := by
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨u, hu⟩ := List.head?_eq_some_iff.1 h1
  obtain ⟨v, hv⟩ := List.head?_eq_some_iff.1 h2
  obtain ⟨x, hx⟩ := List.head?_eq_some_iff.1 hd
  obtain ⟨y, hy⟩ := List.head?_eq_some_iff.1 hd'
  refine h.cut_follow hT 1 (p := []) (p' := []) (q := x ++ subst s u) (q' := y ++ subst s v)
    ?_ ?_ (fun _ => rfl)
  · rw [Function.iterate_one, hu, subst_cons, hx]; rfl
  · rw [Function.iterate_one, hv, subst_cons, hy]; rfl

/-- **Theorem A(3)** for nonerasing `s`, with `g(a)` the first letter of `σ(a)`:
`(g × g)(A(C)) ⊆ A(C)` and `g(c) ≠ g(c')` on `A(C)`. -/
theorem cutPair_first (hs : ∀ a, s a ≠ []) {c c' : α} (hcp : CutPair C c c') :
    CutPair C ((s c).head (hs c)) ((s c').head (hs c')) ∧ (s c).head (hs c) ≠ (s c').head (hs c') :=
  have hg := h.cutPair_subst hcp (List.head?_eq_some_head (hs c)) (List.head?_eq_some_head (hs c'))
  ⟨hg, h.cutPair_ne hg⟩

/-- **Theorem A(4)**: no cut pair has a left strong-coincidence witness. -/
theorem not_witness {c c' : α} (hcp : CutPair C c c') : ¬ StrongCoincidenceWitness s c c' := by
  rintro ⟨n, P, Q, P', Q', x, hc, hc', hP⟩
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨u, hu⟩ := List.head?_eq_some_iff.1 h1
  obtain ⟨v, hv⟩ := List.head?_eq_some_iff.1 h2
  have e1 : (subst s)^[n] T.1 = P ++ x :: (Q ++ (subst s)^[n] u) := by
    rw [hu, show c :: u = [c] ++ u from rfl, iterate_subst_append, hc]; simp
  have e2 : (subst s)^[n] T.2 = P' ++ x :: (Q' ++ (subst s)^[n] v) := by
    rw [hv, show c' :: v = [c'] ++ v from rfl, iterate_subst_append, hc']; simp
  exact h.cutPair_ne (h.cut_follow hT n e1 e2 hP) rfl

/-- **Theorem A(4)**, unordered form. -/
theorem not_witness_of_cutPair_swap {c c' : α} (hcp : CutPair C c' c) :
    ¬ StrongCoincidenceWitness s c c' :=
  fun hw => h.not_witness hcp (strongCoincidenceWitness_comm.1 hw)

end StrictSystem

/-- **Corollary (C4FromStrongCoincidence).**  If every pair of distinct letters
has a left strong-coincidence witness, no strict system exists. -/
theorem no_strictSystem_of_strongCoincidence {s : α → List α}
    (hw : ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') (C : Finset (List α × List α)) :
    ¬ StrictSystem s C := fun h => by
  obtain ⟨c, c', hcp⟩ := h.exists_cutPair
  exact h.not_witness hcp (hw c c' (h.cutPair_ne hcp))

/-! ### (c) Decide-checked strong-coincidence witnesses -/

/-- The index form of a witness, decidable over a finite alphabet: position `i`
of `σⁿ(c)` and position `j` of `σⁿ(c')` carry the same letter and have prefixes
with equal letter counts. -/
def IndexWitness (s : α → List α) (c c' : α) (n i j : ℕ) : Prop :=
  i < ((subst s)^[n] [c]).length ∧ ((subst s)^[n] [c])[i]? = ((subst s)^[n] [c'])[j]? ∧
    Equiv1 (((subst s)^[n] [c]).take i) (((subst s)^[n] [c']).take j)

instance [Fintype α] (s : α → List α) (c c' : α) (n i j : ℕ) :
    Decidable (IndexWitness s c c' n i j) := by
  unfold IndexWitness; infer_instance

/-- A witness at level `n`: `σⁿ(c) = P x Q`, `σⁿ(c') = P' x Q'`, `p(P) = p(P')`. -/
def WitnessAt (s : α → List α) (c c' : α) (n : ℕ) : Prop :=
  ∃ (P Q P' Q' : List α) (x : α), (subst s)^[n] [c] = P ++ x :: Q ∧
    (subst s)^[n] [c'] = P' ++ x :: Q' ∧ Equiv1 P P'

theorem strongCoincidenceWitness_iff_exists_witnessAt {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ ∃ n, WitnessAt s c c' n :=
  ⟨fun ⟨n, P, Q, P', Q', x, h⟩ => ⟨n, P, Q, P', Q', x, h⟩,
    fun ⟨n, P, Q, P', Q', x, h⟩ => ⟨n, P, Q, P', Q', x, h⟩⟩

/-- A witness at level `n` in index form, and conversely. -/
theorem witnessAt_iff_index {s : α → List α} {c c' : α} {n : ℕ} :
    WitnessAt s c c' n ↔ ∃ i j, IndexWitness s c c' n i j := by
  constructor
  · rintro ⟨P, Q, P', Q', x, h1, h2, hP⟩
    refine ⟨P.length, P'.length, ?_, ?_, ?_⟩
    · rw [h1]; simp
    · rw [h1, h2, List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
      simp
    · rw [h1, h2, List.take_left' rfl, List.take_left' rfl]; exact hP
  · rintro ⟨i, j, hi, hx, hP⟩
    set u := (subst s)^[n] [c]
    set v := (subst s)^[n] [c']
    have hv : v[j]? = some u[i] := by rw [← hx]; exact List.getElem?_eq_getElem hi
    obtain ⟨hj, hvj⟩ := List.getElem?_eq_some_iff.1 hv
    refine ⟨u.take i, u.drop (i + 1), v.take j, v.drop (j + 1), u[i], ?_, ?_, hP⟩
    · rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    · rw [← hvj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

/-- A witness in index form is a left strong-coincidence witness, and conversely. -/
theorem strongCoincidenceWitness_iff_index {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ ∃ n i j, IndexWitness s c c' n i j := by
  simp only [strongCoincidenceWitness_iff_exists_witnessAt, witnessAt_iff_index]

theorem witness_of_index {s : α → List α} {c c' : α} (n i j : ℕ)
    (h : IndexWitness s c c' n i j) : StrongCoincidenceWitness s c c' :=
  strongCoincidenceWitness_iff_index.2 ⟨n, i, j, h⟩

/-- An index witness is aligned: `p(P) = p(P')` forces `|P| = |P'|`. -/
theorem IndexWitness.aligned {s : α → List α} {c c' : α} {n i j : ℕ}
    (h : IndexWitness s c c' n i j) : i = j := by
  obtain ⟨hi, hx, hP⟩ := h
  have hj : j < ((subst s)^[n] [c']).length := by
    by_contra hj
    have hnone : ((subst s)^[n] [c'])[j]? = none := List.getElem?_eq_none (by omega)
    rw [hnone, List.getElem?_eq_getElem hi] at hx
    exact Option.some_ne_none _ hx
  have := hP.length_eq
  rw [List.length_take, List.length_take] at this
  omega

/-- **Least witness level `m`**, decidable over a finite alphabet: an aligned
witness at level `m`, and none at any level `n < m`. -/
def LeastWitnessLevel (s : α → List α) (c c' : α) (m : ℕ) : Prop :=
  (∃ i < ((subst s)^[m] [c]).length, IndexWitness s c c' m i i) ∧
    ∀ n < m, ∀ i < ((subst s)^[n] [c]).length, ¬ IndexWitness s c c' n i i

instance [Fintype α] (s : α → List α) (c c' : α) (m : ℕ) :
    Decidable (LeastWitnessLevel s c c' m) := by
  unfold LeastWitnessLevel; infer_instance

/-- `LeastWitnessLevel s c c' m` says what it says: `m` is the least level of a
left strong-coincidence witness for `(c, c')`. -/
theorem leastWitnessLevel_spec {s : α → List α} {c c' : α} {m : ℕ}
    (h : LeastWitnessLevel s c c' m) :
    WitnessAt s c c' m ∧ ∀ n < m, ¬ WitnessAt s c c' n := by
  refine ⟨witnessAt_iff_index.2 (let ⟨i, _, hi⟩ := h.1; ⟨i, i, hi⟩), fun n hn hw => ?_⟩
  obtain ⟨i, j, hij⟩ := witnessAt_iff_index.1 hw
  obtain rfl := hij.aligned
  exact h.2 n hn i hij.1 hij

/-- Over three letters, witnesses for the pairs `01`, `02`, `12` give one for
every pair of distinct letters. -/
theorem fin3_all_pairs {s : Fin 3 → List (Fin 3)} (h01 : StrongCoincidenceWitness s 0 1)
    (h02 : StrongCoincidenceWitness s 0 2) (h12 : StrongCoincidenceWitness s 1 2) :
    ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c' := by
  intro c c' hne
  fin_cases c <;> fin_cases c' <;> simp at hne
  · exact h01
  · exact h02
  · exact strongCoincidenceWitness_comm.1 h01
  · exact h12
  · exact strongCoincidenceWitness_comm.1 h02
  · exact strongCoincidenceWitness_comm.1 h12

end Psc.StrictSystem
