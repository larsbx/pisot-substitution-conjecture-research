/-
# Two-binomial calculus and the Concentration reduction lemma

`docs/c4-concentration-attack-2026-11-06.md` §3.  Words are lists over an
arbitrary alphabet `α` with decidable equality.  `n2 w a b` counts the scattered
occurrences of `a b` in `w` (an `a` strictly before a `b`).  Two words are
*2-binomially equivalent* (`Equiv2`) if they have the same letter counts and the
same `n2` counts; `K₂(u,v) = 0` for a balanced pair is exactly `Equiv2 u v`.

Proved here, in full:

* `n2_append`: `n2 (x ++ y) = n2 x + n2 y + |x|_a * |y|_b`;
* `n2_add_n2_swap`: for `a ≠ b`, `n2 w a b + n2 w b a = |w|_a · |w|_b`;
  `n2_self`: `n2 w a a = (|w|_a).choose 2`;
* `Equiv1.append`, `equiv1_join`, `Equiv2.append`, `equiv2_join`:
  concatenations of pairwise balanced (resp. 2-binomially equivalent) blocks
  are balanced (resp. 2-binomially equivalent; block additivity of `K₂`);
* the **reduction lemma** in finite form, `reduction_lemma`: in a finite
  child-closed system of 2-binomially equivalent pairs whose children
  concatenate to the images, some state `T₀` returns to itself as the first
  child after `p ≥ 1` steps, its two words are prefixes of their own
  `σᵖ`-images, and for every `n` the pair `(σ^{pn} u₀, σ^{pn} v₀)` is a
  concatenation of states of the system — so the two words are 2-binomially
  equivalent at every block boundary;
* `power`, `subst_power`: the power substitution `a ↦ σᵏ [a]` acts on words
  as `σᵏ`; `ChildSystem.desc_ne_nil` and `ChildSystem.pow`: the depth-`k`
  descendants of a child system form a child system of the power substitution
  on the same states;
* `heads_ne`: an irreducible (`IrreduciblePair`) noncoincident balanced pair
  has distinct first letters;
* over a finite alphabet, `Equiv1`, `Equiv2` and `IrreduciblePair` are
  decidable (instances used by the `decide` controls);
* `thueMorse`: the Thue–Morse child system (`0 ↦ 01`, `1 ↦ 10`, states
  `(01, 10)` and `(10, 01)`, children `T, T.swap`), a concrete instance used as
  a control in `PscVerif.PrimitiveExpansion` and `PscVerif.SignedCocycle`.

The passage from the finite statement to the two one-sided fixed points is the
standard limit of an increasing sequence of prefixes and is not formalized.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Psc.Binomial

variable {α : Type*} [DecidableEq α]

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

/-- Words with the same letter counts have the same length. -/
theorem Equiv1.length_eq {x y : List α} (h : Equiv1 x y) : x.length = y.length :=
  (List.perm_iff_count.mpr h).length_eq

/-- A list of balanced pairs concatenates to a balanced pair. -/
theorem equiv1_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv1 T.1 T.2) :
    Equiv1 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => intro a; rfl
  | cons T bs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (h T (by simp)).append (ih fun T' hT' => h T' (by simp [hT']))

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

omit [DecidableEq α] in
theorem subst_append (s : α → List α) (x y : List α) :
    subst s (x ++ y) = subst s x ++ subst s y := by simp [subst]

omit [DecidableEq α] in
theorem subst_prefix (s : α → List α) {x y : List α} (h : x <+: y) :
    subst s x <+: subst s y := by
  obtain ⟨t, rfl⟩ := h; exact ⟨subst s t, (subst_append s x t).symm⟩

omit [DecidableEq α] in
theorem iterate_subst_append (s : α → List α) (n : ℕ) (x y : List α) :
    (subst s)^[n] (x ++ y) = (subst s)^[n] x ++ (subst s)^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, subst_append]

omit [DecidableEq α] in
theorem iterate_subst_nil (s : α → List α) (n : ℕ) : (subst s)^[n] [] = [] :=
  Function.iterate_fixed (by simp [subst]) n

omit [DecidableEq α] in
theorem iterate_subst_flatten (s : α → List α) (n : ℕ) (ws : List (List α)) :
    (subst s)^[n] ws.flatten = (ws.map (subst s)^[n]).flatten := by
  induction ws with
  | nil => simp [iterate_subst_nil]
  | cons w ws ih => simp [iterate_subst_append, ih]

/-- The `k`-th power substitution `a ↦ σᵏ [a]`. -/
def power (s : α → List α) (k : ℕ) : α → List α := fun a => (subst s)^[k] [a]

omit [DecidableEq α] in
/-- `subst (power s k) = σᵏ`: the power substitution acts on words as the
`k`-th iterate. -/
theorem subst_power (s : α → List α) (k : ℕ) : subst (power s k) = (subst s)^[k] := by
  funext w
  induction w with
  | nil => simp [subst, iterate_subst_nil]
  | cons a t ih =>
    have e1 : subst (power s k) (a :: t) = power s k a ++ subst (power s k) t := by
      simp [subst]
    rw [e1, ih, show a :: t = [a] ++ t from rfl, iterate_subst_append]
    rfl

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
  | zero => intro T hT U hU; simp only [desc, List.mem_singleton] at hU; exact hU ▸ hT
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

/-- Every state has a nonempty list of depth-`n` descendants. -/
theorem desc_ne_nil (n : ℕ) : ∀ T ∈ S.C, S.desc n T ≠ [] := by
  induction n with
  | zero => intro T _; simp [desc]
  | succ n ih =>
    intro T hT
    obtain ⟨V, hV⟩ := List.exists_mem_of_ne_nil _ (S.nonempty T hT)
    simp only [desc, ne_eq, List.flatten_eq_nil_iff, List.mem_map, not_forall]
    exact ⟨_, ⟨V, hV, rfl⟩, ih V (S.closed T hT V hV)⟩

/-- The `k`-step child system: the same states, depth-`k` descendants as
children, and the power substitution `a ↦ σᵏ [a]` (`power`). -/
def pow (S : ChildSystem α) (k : ℕ) : ChildSystem α where
  s := power S.s k
  C := S.C
  children := S.desc k
  top := fun T hT => by rw [subst_power]; exact S.desc_top k T hT
  bot := fun T hT => by rw [subst_power]; exact S.desc_bot k T hT
  closed := fun T hT U hU => S.desc_mem k T hT U hU
  nonempty := fun T hT => S.desc_ne_nil k T hT

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

/-- The pair `(u, v)` is irreducible (as a balanced pair): no proper nonempty
prefixes with equal letter counts.  Named `IrreduciblePair` so that it does not
shadow Mathlib's `Irreducible` under `open Psc.Binomial`. -/
def IrreduciblePair (u v : List α) : Prop :=
  ∀ k, 0 < k → k < u.length → ¬ Equiv1 (u.take k) (v.take k)

/-- Over a finite alphabet the three pair predicates are decidable (used by the
`decide` controls; `IrreduciblePair` quantifies over the bounded range
`k < |u|`). -/
instance [Fintype α] (x y : List α) : Decidable (Equiv1 x y) := by
  unfold Equiv1; infer_instance

instance [Fintype α] (x y : List α) : Decidable (Equiv2 x y) := by
  unfold Equiv2; infer_instance

instance [Fintype α] (u v : List α) : Decidable (IrreduciblePair u v) := by
  unfold IrreduciblePair
  exact decidable_of_iff (∀ k ∈ List.range u.length, 0 < k → ¬ Equiv1 (u.take k) (v.take k))
    ⟨fun h k hk hl => h k (List.mem_range.2 hl) hk,
      fun h k hm hk => h k hk (List.mem_range.1 hm)⟩

theorem heads_ne {a b : α} {u v : List α} (hbal : Equiv1 (a :: u) (b :: v))
    (hirr : IrreduciblePair (a :: u) (b :: v)) (hnc : a :: u ≠ b :: v) : a ≠ b := by
  rintro rfl
  have hlen : u.length = v.length := by simpa using hbal.length_eq
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · apply hnc
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    rw [List.length_eq_zero_iff.mp h0, hv]
  · exact hirr 1 Nat.one_pos (by simp; omega) (fun c => by simp)

/-! ### A concrete child system: Thue–Morse -/

/-- The Thue–Morse substitution `0 ↦ 01`, `1 ↦ 10`. -/
def thueMorseSubst : Fin 2 → List (Fin 2) := fun a => if a = 0 then [0, 1] else [1, 0]

/-- The balanced pair `(01, 10)`. -/
def tmPair : List (Fin 2) × List (Fin 2) := ([0, 1], [1, 0])

/-- The Thue–Morse child system on the two states `(01, 10)` and `(10, 01)`:
`σ(01, 10) = (01·10, 10·01)` and `σ(10, 01) = (10·01, 01·10)`, so the children
of a state `T` are `T, T.swap`. -/
def thueMorse : ChildSystem (Fin 2) where
  s := thueMorseSubst
  C := {tmPair, tmPair.swap}
  children := fun T => [T, T.swap]
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

end Psc.Binomial
