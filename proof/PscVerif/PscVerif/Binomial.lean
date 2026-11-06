/-
# Two-binomial calculus and the Concentration reduction lemma

`docs/c4-concentration-attack-2026-11-06.md` §3.  Words are lists over an
arbitrary alphabet `α` with decidable equality.  `n2 w a b` counts the scattered
occurrences of `a b` in `w` (an `a` strictly before a `b`).  Two words are
*2-binomially equivalent* (`Equiv2`) if they have the same letter counts and the
same `n2` counts; `K₂(u,v) = 0` for a balanced pair is exactly `Equiv2 u v`.

Proved here, in full:

* `n2_append`: `n2 (x ++ y) = n2 x + n2 y + |x|_a * |y|_b`;
* `Equiv2.append`, `equiv2_join`: concatenations of pairwise 2-binomially
  equivalent blocks are 2-binomially equivalent (block additivity of `K₂`);
* the **reduction lemma** in finite form, `reduction_lemma`: in a finite
  child-closed system of 2-binomially equivalent pairs whose children
  concatenate to the images, some state `T₀` returns to itself as the first
  child after `p ≥ 1` steps, its two words are prefixes of their own
  `σᵖ`-images, and for every `n` the pair `(σ^{pn} u₀, σ^{pn} v₀)` is a
  concatenation of states of the system — so the two words are 2-binomially
  equivalent at every block boundary;
* `heads_ne`: an irreducible noncoincident balanced pair has distinct first
  letters.

The passage from the finite statement to the two one-sided fixed points is the
standard limit of an increasing sequence of prefixes and is not formalized.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Ring

namespace Psc.Binomial

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

/-- Scattered occurrences of the length-two word `a b` in `w`. -/
def n2 : List α → α → α → ℕ
  | [], _, _ => 0
  | c :: w, a, b => (if c = a then w.count b else 0) + n2 w a b

theorem n2_append (x y : List α) (a b : α) :
    n2 (x ++ y) a b = n2 x a b + n2 y a b + x.count a * y.count b := by
  induction x with
  | nil => simp [n2]
  | cons c x ih =>
    simp only [List.cons_append, n2, ih, List.count_append, List.count_cons]
    by_cases h : c = a
    · subst h; simp only [ite_true, beq_self_eq_true]; ring
    · have h' : (c == a) = false := by simpa using h
      simp [h, h']

/-- Same letter counts (`K₁ = 0`). -/
def Equiv1 (x y : List α) : Prop := ∀ a, x.count a = y.count a

/-- Two-binomial equivalence (`K₁ = K₂ = 0`). -/
def Equiv2 (x y : List α) : Prop := Equiv1 x y ∧ ∀ a b, n2 x a b = n2 y a b

theorem Equiv1.append {x x' y y' : List α} (hx : Equiv1 x x') (hy : Equiv1 y y') :
    Equiv1 (x ++ y) (x' ++ y') := fun a => by simp [List.count_append, hx a, hy a]

theorem Equiv2.append {x x' y y' : List α} (hx : Equiv2 x x') (hy : Equiv2 y y') :
    Equiv2 (x ++ y) (x' ++ y') :=
  ⟨hx.1.append hy.1, fun a b => by rw [n2_append, n2_append, hx.2, hy.2, hx.1 a, hy.1 b]⟩

theorem Equiv2.refl (x : List α) : Equiv2 x x := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- A list of pairs, all 2-binomially equivalent, concatenates to a 2-binomially
equivalent pair. -/
theorem equiv2_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv2 T.1 T.2) :
    Equiv2 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => exact Equiv2.refl []
  | cons T bs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (h T (by simp)).append (ih fun T' hT' => h T' (by simp [hT']))

/-- Every block boundary of such a concatenation is a 2-binomial cut. -/
theorem equiv2_at_cuts (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv2 T.1 T.2)
    (k : ℕ) : Equiv2 ((bs.take k).map Prod.fst).flatten ((bs.take k).map Prod.snd).flatten :=
  equiv2_join _ fun T hT => h T (List.mem_of_mem_take hT)

/-! ### Substitutions and child-closed systems -/

/-- The image of a word under a substitution `s : α → List α`. -/
def subst (s : α → List α) (w : List α) : List α := (w.map s).flatten

theorem subst_append (s : α → List α) (x y : List α) :
    subst s (x ++ y) = subst s x ++ subst s y := by simp [subst]

theorem subst_prefix (s : α → List α) {x y : List α} (h : x <+: y) :
    subst s x <+: subst s y := by
  obtain ⟨t, rfl⟩ := h; exact ⟨subst s t, (subst_append s x t).symm⟩

theorem iterate_subst_append (s : α → List α) (n : ℕ) (x y : List α) :
    (subst s)^[n] (x ++ y) = (subst s)^[n] x ++ (subst s)^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, subst_append]

theorem iterate_subst_nil (s : α → List α) (n : ℕ) : (subst s)^[n] [] = [] :=
  Function.iterate_fixed (by simp [subst]) n

theorem iterate_subst_flatten (s : α → List α) (n : ℕ) (ws : List (List α)) :
    (subst s)^[n] ws.flatten = (ws.map (subst s)^[n]).flatten := by
  induction ws with
  | nil => simp [iterate_subst_nil]
  | cons w ws ih => simp [iterate_subst_append, ih]

/-- A finite system of ordered pairs with a children map whose blocks
concatenate, on each track, to the image of the parent; closed under children;
every child list nonempty. -/
structure ChildSystem (α : Type*) [DecidableEq α] where
  s : α → List α
  C : Finset (List α × List α)
  children : List α × List α → List (List α × List α)
  top : ∀ T ∈ C, ((children T).map Prod.fst).flatten = subst s T.1
  bot : ∀ T ∈ C, ((children T).map Prod.snd).flatten = subst s T.2
  closed : ∀ T ∈ C, ∀ U ∈ children T, U ∈ C
  nonempty : ∀ T ∈ C, children T ≠ []

namespace ChildSystem

variable (S : ChildSystem α)

/-- Depth-`n` descendant blocks of a state. -/
def desc (S : ChildSystem α) : ℕ → List α × List α → List (List α × List α)
  | 0, T => [T]
  | n + 1, T => ((S.children T).map (desc S n)).flatten

theorem desc_mem (n : ℕ) : ∀ T ∈ S.C, ∀ U ∈ S.desc n T, U ∈ S.C := by
  induction n with
  | zero => intro T hT U hU; simp [desc] at hU; exact hU ▸ hT
  | succ n ih =>
    intro T hT U hU
    simp only [desc, List.mem_flatten, List.mem_map] at hU
    obtain ⟨_, ⟨V, hV, rfl⟩, hU⟩ := hU
    exact ih V (S.closed T hT V hV) U hU

/-- `σⁿ` of each track is the concatenation of the depth-`n` descendants
(`lem:descendants`). -/
theorem desc_top (n : ℕ) : ∀ T ∈ S.C,
    ((S.desc n T).map Prod.fst).flatten = (subst S.s)^[n] T.1 := by
  induction n with
  | zero => intro T _; simp [desc]
  | succ n ih =>
    intro T hT
    rw [Function.iterate_succ_apply, ← S.top T hT, iterate_subst_flatten]
    simp only [desc, List.map_flatten, List.flatten_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun V hV => ?_
    simpa [Function.comp] using ih V (S.closed T hT V hV)

theorem desc_bot (n : ℕ) : ∀ T ∈ S.C,
    ((S.desc n T).map Prod.snd).flatten = (subst S.s)^[n] T.2 := by
  induction n with
  | zero => intro T _; simp [desc]
  | succ n ih =>
    intro T hT
    rw [Function.iterate_succ_apply, ← S.bot T hT, iterate_subst_flatten]
    simp only [desc, List.map_flatten, List.flatten_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun V hV => ?_
    simpa [Function.comp] using ih V (S.closed T hT V hV)

/-- The first-child map. -/
def first (T : List α × List α) : List α × List α := ((S.children T).head?).getD T

theorem first_mem : ∀ T ∈ S.C, S.first T ∈ S.C := by
  intro T hT
  unfold first
  cases h : S.children T with
  | nil => exact absurd h (S.nonempty T hT)
  | cons U _ => exact S.closed T hT U (by simp [h])

theorem first_prefix_top : ∀ T ∈ S.C, (S.first T).1 <+: subst S.s T.1 := by
  intro T hT
  rw [← S.top T hT]
  unfold first
  cases h : S.children T with
  | nil => exact absurd h (S.nonempty T hT)
  | cons U us => exact ⟨(us.map Prod.fst).flatten, by simp⟩

theorem first_prefix_bot : ∀ T ∈ S.C, (S.first T).2 <+: subst S.s T.2 := by
  intro T hT
  rw [← S.bot T hT]
  unfold first
  cases h : S.children T with
  | nil => exact absurd h (S.nonempty T hT)
  | cons U us => exact ⟨(us.map Prod.snd).flatten, by simp⟩

theorem iterate_first_mem (n : ℕ) : ∀ T ∈ S.C, S.first^[n] T ∈ S.C := by
  induction n with
  | zero => intro T hT; exact hT
  | succ n ih => intro T hT; rw [Function.iterate_succ_apply']; exact S.first_mem _ (ih T hT)

theorem iterate_first_prefix (n : ℕ) : ∀ T ∈ S.C,
    (S.first^[n] T).1 <+: (subst S.s)^[n] T.1 ∧ (S.first^[n] T).2 <+: (subst S.s)^[n] T.2 := by
  induction n with
  | zero => intro T _; exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ n ih =>
    intro T hT
    obtain ⟨h1, h2⟩ := ih T hT
    have hm := S.iterate_first_mem n T hT
    simp only [Function.iterate_succ_apply']
    exact ⟨(S.first_prefix_top _ hm).trans (subst_prefix S.s h1),
      (S.first_prefix_bot _ hm).trans (subst_prefix S.s h2)⟩

/-- Pigeonhole: the first-child map has a periodic state. -/
theorem exists_periodic (T : List α × List α) (hT : T ∈ S.C) :
    ∃ T₀ ∈ S.C, ∃ p ≥ 1, S.first^[p] T₀ = T₀ := by
  classical
  let g : Fin (S.C.card + 1) → S.C := fun i => ⟨S.first^[i] T, S.iterate_first_mem i T hT⟩
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have hv : S.first^[(i : ℕ)] T = S.first^[(j : ℕ)] T := congrArg Subtype.val hg
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · refine ⟨S.first^[i] T, S.iterate_first_mem i T hT, j - i, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, hv]
  · refine ⟨S.first^[j] T, S.iterate_first_mem j T hT, i - j, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, hv]

/-- **Reduction lemma (finite form).**  If every state of a nonempty child
system is 2-binomially equivalent on its two tracks, some state `T₀` has
`p ≥ 1` with: `T₀`'s words are prefixes of their own `σᵖ`-images, and for every
`n`, `(σ^{pn} u₀, σ^{pn} v₀)` is the concatenation of states of the system, so
the two tracks agree in `N₁` and `N₂` at every block boundary. -/
theorem reduction_lemma (T : List α × List α) (hT : T ∈ S.C)
    (hK2 : ∀ U ∈ S.C, Equiv2 U.1 U.2) :
    ∃ T₀ ∈ S.C, ∃ p ≥ 1,
      T₀.1 <+: (subst S.s)^[p] T₀.1 ∧ T₀.2 <+: (subst S.s)^[p] T₀.2 ∧
      ∀ n, ∃ bs : List (List α × List α), (∀ U ∈ bs, U ∈ S.C) ∧
        (bs.map Prod.fst).flatten = (subst S.s)^[p * n] T₀.1 ∧
        (bs.map Prod.snd).flatten = (subst S.s)^[p * n] T₀.2 ∧
        ∀ k, Equiv2 ((bs.take k).map Prod.fst).flatten ((bs.take k).map Prod.snd).flatten := by
  obtain ⟨T₀, h₀, p, hp, hper⟩ := S.exists_periodic T hT
  obtain ⟨h1, h2⟩ := S.iterate_first_prefix p T₀ h₀
  rw [hper] at h1 h2
  refine ⟨T₀, h₀, p, hp, h1, h2, fun n => ⟨S.desc (p * n) T₀, S.desc_mem _ T₀ h₀,
    S.desc_top _ T₀ h₀, S.desc_bot _ T₀ h₀, fun k => equiv2_at_cuts _ ?_ k⟩⟩
  intro U hU; exact hK2 U (S.desc_mem _ T₀ h₀ U hU)

end ChildSystem

/-! ### Irreducible noncoincident pairs have distinct first letters -/

/-- `(u, v)` is irreducible: no proper nonempty prefixes with equal letter counts. -/
def Irreducible (u v : List α) : Prop :=
  ∀ k, 0 < k → k < u.length → ¬ Equiv1 (u.take k) (v.take k)

theorem heads_ne {a b : α} {u v : List α} (hbal : Equiv1 (a :: u) (b :: v))
    (hirr : Irreducible (a :: u) (b :: v)) (hnc : a :: u ≠ b :: v) : a ≠ b := by
  rintro rfl
  have hlen : u.length = v.length := by
    simpa using (List.perm_iff_count.mpr hbal).length_eq
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · apply hnc
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    rw [List.length_eq_zero_iff.mp h0, hv]
  · exact hirr 1 Nat.one_pos (by simp; omega) (fun c => by simp)

end Psc.Binomial
