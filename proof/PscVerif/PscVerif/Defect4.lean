/-
# The degree-four defect `K₄`: concatenation, shuffles and the word intertwiner

`docs/c4-concentration-attack-2026-11-06.md` §8;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `lem:conc-subst` (i),
(ii), (iii) at `r = 4` and `thm:defect-intertwiner` at `r = 4` (the word-level
identity, and its column and matrix forms on normalised representatives).

Words are lists over an alphabet `α` with decidable equality; a substitution is
any map `s : α → List α` (no primitivity, unimodularity, Pisot or
irreducibility hypothesis is used).  `n2` is `Psc.Binomial.n2`, `n3` is
`Psc.Incidence.n3` and `M = Psc.Incidence.inc s`, `M a c = |s c|_a`.  Here
`n4 w a b c d` is the scattered count of `a b c d`, defined like `n3` by
`n4 (x :: t) a b c d = (if x = a then n3 t b c d else 0) + n4 t a b c d`;
`Equiv3 u v` is `Equiv2 u v` together with `n3 u = n3 v`, i.e.
`K₁ = K₂ = K₃ = 0` (`equiv3_iff`); and
`K4 u v a b c d = n4 u a b c d - n4 v a b c d` in `ℤ`.

## Proved here, in full

* `n4_append` (`lem:conc-subst` (i), `r = 4`):
  `n4 (x ++ y) a b c d = n4 x a b c d + n3 x a b c · |y|_d + n2 x a b · n2 y c d
  + |x|_a · n3 y b c d + n4 y a b c d`; `Equiv3.append`, `equiv3_join`:
  concatenations of 3-binomially equivalent blocks are 3-binomially equivalent.
* `k4_swap`: `K4 v u = - K4 u v`.
* **Shuffle identities on words** (`lem:conc-subst` (iii) at `r = 4`, in its
  corrected form; any alphabet, in `ℕ`).  As printed, (iii) is the
  shuffle-character identity `N_{x ⧢ y}(w) = N_x(w) N_y(w)`, which is false on
  repeated letters: for `w = a`, `N_a(w) N_a(w) = 1` but
  `N_{a ⧢ a}(w) = 2 N_{aa}(w) = 0`.  Products of scattered counts are
  infiltration products (a position may be shared by the two factors when the
  letters agree), which gives the bracketed corrections below.  They have
  degree `< 4`, so they cancel under `Equiv3`, and the relations of `K₄` used
  by `thm:defect-intertwiner` survive (the degree-three instance is discrepancy
  D2 of `docs/verification-architecture.md`).
  - `count_mul_n3` (`a ⧢ bcd`): `|w|_a · n3 w b c d = n4 abcd + n4 bacd +
    n4 bcad + n4 bcda + [a = b] n3 w a c d + [a = c] n3 w b a d +
    [a = d] n3 w b c a`;
  - `n3_mul_count` (`abc ⧢ d`): `n3 w a b c · |w|_d = n4 abcd + n4 abdc +
    n4 adbc + n4 dabc + ([a = d] + [b = d] + [c = d]) n3 w a b c`;
  - `n2_mul_n2` (`ab ⧢ cd`): `n2 w a b · n2 w c d` is the sum of `n4` over the
    six shuffles `abcd, acbd, acdb, cabd, cadb, cdab`, plus
    `[a = c] (n3 w a b d + n3 w a d b + [b = d] n2 w a b) + [a = d] n3 w c a b
    + [b = c] n3 w a b d + [b = d] (n3 w a c b + n3 w c a b)`.
* **The proper shuffle relations of `K₄`**: if `Equiv3 u v`, then
  - `k4_shuffle_left` (`a ⧢ bcd`):
    `K4 abcd + K4 bacd + K4 bcad + K4 bcda = 0`;
  - `k4_shuffle_two` (`ab ⧢ cd`):
    `K4 abcd + K4 acbd + K4 acdb + K4 cabd + K4 cadb + K4 cdab = 0`;
  - `k4_shuffle_right` (`abc ⧢ d`): `k4_shuffle_left` re-indexed at
    `(d, a, b, c)`.
  These are the relations `⟨K₄, x ⧢ y⟩ = 0` for all words `x, y` with
  `|x|, |y| ≥ 1`, `|x| + |y| = 4`.  Over `Fin 3` the first two are, verbatim,
  the families `R1`, `R2` of `Psc.LieWeights.ShuffleAnnih4`.
* **Block additivity**: `k4_additive`: if `Equiv3 x x'` and `Equiv3 y y'` then
  `K4 (x ++ y) (x' ++ y') = K4 x x' + K4 y y'`; `k4_join`, its iterate over a
  list of `Equiv3` blocks; `k4_children`, its `ChildSystem` form over the raw
  ordered children of a state.
* Over a finite alphabet:
  - `n4_subst` (`lem:conc-subst` (ii), `r = 4`, with the correction `Λ₄`
    explicit):
    ```
    n4 (σ w) a b e f = Σ_{x,y,z,t} M a x · M b y · M e z · M f t · n4 w x y z t
                     + Σ_{x,z,t} n2 (s x) a b · M e z · M f t · n3 w x z t
                     + Σ_{x,y,t} M a x · n2 (s y) b e · M f t · n3 w x y t
                     + Σ_{x,y,z} M a x · M b y · n2 (s z) e f · n3 w x y z
                     + Σ_{x,z} n3 (s x) a b e · M f z · n2 w x z
                     + Σ_{x,z} n2 (s x) a b · n2 (s z) e f · n2 w x z
                     + Σ_{x,z} M a x · n3 (s z) b e f · n2 w x z
                     + Σ_x |w|_x · n4 (s x) a b e f,
    ```
    the corrections being linear in `N₃(w)`, `N₂(w)`, `N₁(w)` with
    coefficients depending only on `s`;
  - `equiv3_subst`, `equiv3_iterate_subst`: `Equiv3` is preserved by `σ` and
    by every `σⁿ`;
  - `k4_subst` (`thm:defect-intertwiner` at `r = 4` on words): if `Equiv3 u v`
    then `K4 (σ u) (σ v) a b e f = Σ_{x,y,z,t} M a x · M b y · M e z · M f t ·
    K4 u v x y z t`;
  - `k4_image_children`, `k4_rep`: for a child system whose states are all
    `Equiv3`, `M^{⊗4} K₄(T) = Σ_{U ∈ children T} K₄(U)`, and on a
    `Psc.SignedCocycle.Normalisation`
    `M^{⊗4} K₄(j) = Σ_i S i j · K₄(i)` (via
    `Psc.SignedIntertwiner.sum_children_signed`); matrix form `q4_mul_ssign`:
    `Q₄ S = (M ⊗ₖ (M ⊗ₖ (M ⊗ₖ M))) Q₄`, with `Q4` the `(α × α × α × α) × R`
    column matrix of `K₄` (81 rows over `Fin 3`), i.e. `Q₄ S = Φ₄ Q₄` with
    `Φ₄ = M^{⊗4}` on the full tensor power.
* Controls (`decide`).
  - Non-vacuity: `equiv3_tm3`, `k4_tm3`: the Thue–Morse blocks
    `t₃ = σ³(0) = 01101001` and `t̄₃ = σ³(1) = 10010110` (`tm3_eq`) are
    3-binomially equivalent with `K₄_{0101} = 8`; `k4_ternary`: over `Fin 3`,
    `012100201` and `102001210` are 3-binomially equivalent with
    `K₄_{0102} = 4`; `w4` (the identity substitution,
    `C = {(011220100112, 120010112201), swap}`, built by
    `Psc.Reduction.redSystem` and normalised by
    `Psc.Reduction.redNormalisation`): the pair is distinct and irreducible
    (`w4_irreducible`) and 3-binomially equivalent (`w4_equiv3`), `S = (1)`
    (`w4_ssign`), and `w4_k4`: `M^{⊗4} K₄ = K₄` with `K₄_{0101} = 8`
    (`w4_k4_ne`).  A zero-return system meeting the hypotheses of
    `k4_children`, `k4_image_children`, `k4_rep` and `q4_mul_ssign` with
    `K₄ ≠ 0`, but with `M = 1` and `S = (1)`.
  - `exT` (`Psc.SignedIntertwiner.exBSubst`: `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`;
    `C = {(t₃, t̄₃), (t̄₃, t₃)}` over `Fin 3`, the only child of `(t₃, t̄₃)`
    declared to be its swap): an **algebra-only** control, like
    `Psc.SignedIntertwiner.exB`.  Its state is reducible (`exT_reducible`) and
    its declared children are not those of `red` (`exT_not_red`); it exercises
    the sign `-1` and a non-identity `M`: `S = (-1)` (`exT_ssign`), `exT_k4`:
    `M^{⊗4} K₄(t₃, t̄₃) = - K₄(t₃, t̄₃)`, with `K₄_{0101} = 8` (`exT_k4_ne`).
  - Negative (the hypothesis `Equiv3` cannot be weakened to `Equiv2`; each
    pair below is `Equiv2` and not `Equiv3`):
    `k4_subst_needs_equiv3`: the pair `(0110, 1001)` is mapped by Thue–Morse
    to `(t₃, t̄₃)`, with `K₄_{0101} = 8`, while
    `(M^{⊗4} K₄(0110, 1001))_{0101} = 0`; `k4_shuffle_left_needs_equiv3`: on
    the same pair the `a ⧢ bcd` sum at `(0, 1, 0, 1)` is `-2`;
    `k4_shuffle_two_needs_equiv3`: on `Psc.SignedIntertwiner.wTPair =
    (0112201, 1200112)` the `ab ⧢ cd` sum at `(0, 1, 0, 2)` is `-2` (a binary
    control cannot serve here: `(0110, 1001)` satisfies every `ab ⧢ cd`
    relation, `k4_shuffle_two_binary`); `k4_additive_needs_equiv3`: with
    `x = 0110`, `x' = 1001` and `y = y' = 0`, `K₄(x y, x' y')_{0010} = -1` while
    `K₄(x, x')_{0010} + K₄(y, y')_{0010} = 0`.

## What is not proved here

* `K₄ ∈ Lie₄` (the first assertion of `thm:defect-intertwiner` at `r = 4`) and
  the restriction `Φ₄ = M^{⊗4}|_{Lie₄}`.  Both halves exist: Ree's theorem at
  degree four on three letters is `Psc.LieWeights`
  (`shuffleAnnih4_iff_mem_span`: `ShuffleAnnih4` cuts out the span of the 18
  Lyndon brackets; `finrank_shuffleAnnih4Space`: dimension `18`;
  `phi4_mem_span`: `M^{⊗4}`-invariance), and `k4_shuffle_left`,
  `k4_shuffle_two` are its `R1`, `R2` for the vector `(K4 u v a b c d)_{abcd}`
  over `Fin 3`.  The composition is `Psc.Defect4Lie`
  (`k4Vec_mem_span_lyndon4`, `q4_col_mem_lie4`, `phi4Lie_k4Lie`); this module
  does not import `PscVerif.LieWeights`.
* Any spectral consequence for `Q₄` (`ρ(Φ₄|_{im Q₄}) ≤ β`, `thm:sieve` at
  `r = 4`, the `(2,1,1)` and `(2,2,0)` sectors).  The weights of `Φ₄` on `Lie₄`
  are `Psc.LieWeights.charpoly_phi4Lie`, which is not used here.
* The first-defect selection: the hypotheses are `Equiv3` on every state, not
  that `4` is the least degree with a nonzero defect.  Nothing about general
  degree `r`.
* No statement about infinite words, fixed points or the balanced-pair
  algorithm.  None of the controls is a PIP specimen: `w4` uses the identity
  substitution, `exT` a letter permutation with an inert letter, and
  Thue–Morse is not irreducible Pisot.
-/
import PscVerif.Lie3
import PscVerif.Intertwiner3
import PscVerif.SignedIntertwiner

namespace Psc.Defect4

open Psc.Binomial Psc.Incidence Psc.Intertwiner3 Psc.Lie3 Psc.SignedCocycle
open Psc.SignedIntertwiner

section General

variable {α : Type*} [DecidableEq α]

/-! ### The scattered count of a length-four word -/

/-- Scattered occurrences of the length-four word `a b c d` in `w`. -/
def n4 : List α → α → α → α → α → ℕ
  | [], _, _, _, _ => 0
  | x :: t, a, b, c, d => (if x = a then n3 t b c d else 0) + n4 t a b c d

@[simp] theorem n4_nil (a b c d : α) : n4 ([] : List α) a b c d = 0 := rfl

theorem n4_cons (x : α) (t : List α) (a b c d : α) :
    n4 (x :: t) a b c d = (if x = a then n3 t b c d else 0) + n4 t a b c d := rfl

/-- **`lem:conc-subst` (i) at `r = 4`**:
`N₄(xy) = N₄(x) + N₃(x) ⊗ N₁(y) + N₂(x) ⊗ N₂(y) + N₁(x) ⊗ N₃(y) + N₄(y)`. -/
theorem n4_append (x y : List α) (a b c d : α) :
    n4 (x ++ y) a b c d =
      n4 x a b c d + n3 x a b c * y.count d + n2 x a b * n2 y c d
        + x.count a * n3 y b c d + n4 y a b c d := by
  induction x with
  | nil => simp [n2]
  | cons p x ih =>
    simp only [List.cons_append, n4, ih, n3_append, n3, n2, List.count_cons]
    by_cases h : p = a
    · subst h; simp only [ite_true, beq_self_eq_true]; ring
    · have h' : (p == a) = false := by simpa using h
      simp [h, h']

/-! ### Three-binomial equivalence and the degree-four defect -/

/-- Three-binomial equivalence (`K₁ = K₂ = K₃ = 0`). -/
def Equiv3 (x y : List α) : Prop := Equiv2 x y ∧ ∀ a b c, n3 x a b c = n3 y a b c

theorem Equiv3.refl (x : List α) : Equiv3 x x := ⟨Equiv2.refl x, fun _ _ _ => rfl⟩

/-- `Equiv3` is `Equiv2` together with the vanishing of `K₃`. -/
theorem equiv3_iff (u v : List α) :
    Equiv3 u v ↔ Equiv2 u v ∧ ∀ a b c, K3 u v a b c = 0 := by
  simp only [Equiv3, K3, sub_eq_zero, Nat.cast_inj]

theorem Equiv3.append {x x' y y' : List α} (hx : Equiv3 x x') (hy : Equiv3 y y') :
    Equiv3 (x ++ y) (x' ++ y') :=
  ⟨hx.1.append hy.1, fun a b c => by
    rw [n3_append, n3_append, hx.2, hy.2, hx.1.1 a, hy.1.2 b c, hx.1.2 a b, hy.1.1 c]⟩

/-- A list of pairs, all 3-binomially equivalent, concatenates to a
3-binomially equivalent pair. -/
theorem equiv3_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv3 T.1 T.2) :
    Equiv3 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => exact Equiv3.refl []
  | cons T bs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (h T (by simp)).append (ih fun T' hT' => h T' (by simp [hT']))

/-- Over a finite alphabet `Equiv3` is decidable (used by the `decide` controls). -/
instance [Fintype α] (x y : List α) : Decidable (Equiv3 x y) := by
  unfold Equiv3; infer_instance

/-- The degree-four defect of a pair of words, in `ℤ`. -/
def K4 (u v : List α) (a b c d : α) : ℤ := (n4 u a b c d : ℤ) - n4 v a b c d

/-- `K4` is antisymmetric in the two words. -/
theorem k4_swap (u v : List α) (a b c d : α) : K4 v u a b c d = - K4 u v a b c d := by
  unfold K4; ring

/-! ### Shuffle identities with their coincidence corrections -/

/-- **`a ⧢ bcd`** on words, with the coincidence corrections. -/
theorem count_mul_n3 (w : List α) (a b c d : α) :
    w.count a * n3 w b c d =
      n4 w a b c d + n4 w b a c d + n4 w b c a d + n4 w b c d a
        + (if a = b then n3 w a c d else 0) + (if a = c then n3 w b a d else 0)
        + (if a = d then n3 w b c a else 0) := by
  induction w with
  | nil => simp
  | cons x t ih =>
    have key := count_mul_n2 t a c d
    simp only [n4_cons, n3_cons, List.count_cons, beq_iff_eq]
    split_ifs at * <;> subst_vars <;>
      first | contradiction | linear_combination ih | linear_combination ih + key

/-- **`abc ⧢ d`** on words, with the coincidence corrections: `count_mul_n3` at
`(d, a, b, c)`. -/
theorem n3_mul_count (w : List α) (a b c d : α) :
    n3 w a b c * w.count d =
      n4 w a b c d + n4 w a b d c + n4 w a d b c + n4 w d a b c
        + (if a = d then n3 w a b c else 0) + (if b = d then n3 w a b c else 0)
        + (if c = d then n3 w a b c else 0) := by
  rw [mul_comm, count_mul_n3 w d a b c]
  split_ifs <;> subst_vars <;> first | contradiction | ring1

/-- **`ab ⧢ cd`** on words, with the coincidence corrections. -/
theorem n2_mul_n2 (w : List α) (a b c d : α) :
    n2 w a b * n2 w c d =
      n4 w a b c d + n4 w a c b d + n4 w a c d b + n4 w c a b d + n4 w c a d b + n4 w c d a b
        + (if a = c then n3 w a b d + n3 w a d b + (if b = d then n2 w a b else 0) else 0)
        + (if a = d then n3 w c a b else 0) + (if b = c then n3 w a b d else 0)
        + (if b = d then n3 w a c b + n3 w c a b else 0) := by
  induction w with
  | nil => simp [n2]
  | cons x t ih =>
    have k1 := count_mul_count t b d
    have k2 := count_mul_n2 t b c d
    have k3 := n2_mul_count t a b d
    simp only [n4_cons, n3_cons, n2]
    split_ifs at * <;> subst_vars <;>
      first
        | contradiction
        | linear_combination ih
        | linear_combination ih + k2
        | linear_combination ih + k3
        | linear_combination ih + k1 + k2 + k3

/-! ### The shuffle relations of `K₄` -/

/-- **First shuffle relation of `K₄`** (`a ⧢ bcd`): on a 3-binomially
equivalent pair, `K₄(abcd) + K₄(bacd) + K₄(bcad) + K₄(bcda) = 0`. -/
theorem k4_shuffle_left {u v : List α} (h : Equiv3 u v) (a b c d : α) :
    K4 u v a b c d + K4 u v b a c d + K4 u v b c a d + K4 u v b c d a = 0 := by
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  have hu := count_mul_n3 u a b c d
  rw [h1 a] at hu
  simp only [h3] at hu
  have := congrArg (fun n : ℕ => (n : ℤ)) (hu.symm.trans (count_mul_n3 v a b c d))
  push_cast at this
  unfold K4
  linear_combination this

/-- The re-indexed form (`abc ⧢ d`): `k4_shuffle_left` at `(d, a, b, c)`. -/
theorem k4_shuffle_right {u v : List α} (h : Equiv3 u v) (a b c d : α) :
    K4 u v a b c d + K4 u v a b d c + K4 u v a d b c + K4 u v d a b c = 0 := by
  linear_combination k4_shuffle_left h d a b c

/-- **Second shuffle relation of `K₄`** (`ab ⧢ cd`): on a 3-binomially
equivalent pair, the six shuffles of `ab` and `cd` sum to zero. -/
theorem k4_shuffle_two {u v : List α} (h : Equiv3 u v) (a b c d : α) :
    K4 u v a b c d + K4 u v a c b d + K4 u v a c d b + K4 u v c a b d + K4 u v c a d b
      + K4 u v c d a b = 0 := by
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  have hu := n2_mul_n2 u a b c d
  simp only [h2, h3] at hu
  have := congrArg (fun n : ℕ => (n : ℤ)) (hu.symm.trans (n2_mul_n2 v a b c d))
  push_cast at this
  unfold K4
  linear_combination this

/-! ### Block additivity -/

/-- **Block additivity of `K₄`** (`lem:conc-subst` (i) on a pair with
`K₁ = K₂ = K₃ = 0` on both blocks). -/
theorem k4_additive {x x' y y' : List α} (hx : Equiv3 x x') (hy : Equiv3 y y')
    (a b c d : α) :
    K4 (x ++ y) (x' ++ y') a b c d = K4 x x' a b c d + K4 y y' a b c d := by
  unfold K4
  rw [n4_append, n4_append, hx.2 a b c, hy.1.1 d, hx.1.2 a b, hy.1.2 c d, hx.1.1 a,
    hy.2 b c d]
  push_cast
  ring

/-- Block additivity of `K₄` over a list of 3-binomially equivalent blocks. -/
theorem k4_join (bs : List (List α × List α)) (h : ∀ T ∈ bs, Equiv3 T.1 T.2)
    (a b c d : α) :
    K4 (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten a b c d =
      (bs.map fun T => K4 T.1 T.2 a b c d).sum := by
  induction bs with
  | nil => simp [K4]
  | cons T bs ih =>
    have hbs : ∀ T' ∈ bs, Equiv3 T'.1 T'.2 := fun T' hT' => h T' (by simp [hT'])
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [k4_additive (h T (by simp)) (equiv3_join bs hbs), ih hbs]

/-- **Block additivity of `K₄` over the children of a state** (raw ordered
children, as `Psc.Intertwiner3.k3_children`): if every child of `T ∈ C` is
3-binomially equivalent, then `K₄(σ T.1, σ T.2) = Σ_{U ∈ children T} K₄(U)`. -/
theorem k4_children (S : ChildSystem α) {T : List α × List α} (hT : T ∈ S.C)
    (hch : ∀ U ∈ S.children T, Equiv3 U.1 U.2) (a b c d : α) :
    K4 (subst S.s T.1) (subst S.s T.2) a b c d =
      ((S.children T).map fun U => K4 U.1 U.2 a b c d).sum := by
  rw [← S.top T hT, ← S.bot T hT]
  exact k4_join _ hch a b c d

/-! ### The substitution formula and the word intertwiner -/

variable [Fintype α]

/-- **`lem:conc-subst` (ii) at `r = 4`**, with the correction term explicit
(`M = inc s`): the main term `M^{⊗4} N₄(w)`, three terms linear in `N₃(w)` (two
of the four letters read inside one image `s x`), three linear in `N₂(w)`, and
one linear in `N₁(w)`. -/
theorem n4_subst (s : α → List α) (w : List α) (a b e f : α) :
    n4 (subst s w) a b e f =
      (∑ x, ∑ y, ∑ z, ∑ t, inc s a x * inc s b y * inc s e z * inc s f t * n4 w x y z t)
      + (∑ x, ∑ z, ∑ t, n2 (s x) a b * inc s e z * inc s f t * n3 w x z t)
      + (∑ x, ∑ y, ∑ t, inc s a x * n2 (s y) b e * inc s f t * n3 w x y t)
      + (∑ x, ∑ y, ∑ z, inc s a x * inc s b y * n2 (s z) e f * n3 w x y z)
      + (∑ x, ∑ z, n3 (s x) a b e * inc s f z * n2 w x z)
      + (∑ x, ∑ z, n2 (s x) a b * n2 (s z) e f * n2 w x z)
      + (∑ x, ∑ z, inc s a x * n3 (s z) b e f * n2 w x z)
      + ∑ x, w.count x * n4 (s x) a b e f := by
  induction w with
  | nil => simp [subst, n2]
  | cons p w ih =>
    rw [subst_cons, n4_append, ih, n3_subst, n2_subst, count_subst]
    simp only [n4, n3, n2, List.count_cons, mul_add, add_mul, Finset.sum_add_distrib]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, one_mul, beq_iff_eq,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum, inc_apply]
    simp only [mul_comm, mul_assoc, mul_left_comm]
    ring

/-- `Equiv3` is preserved by a substitution. -/
theorem equiv3_subst (s : α → List α) {u v : List α} (h : Equiv3 u v) :
    Equiv3 (subst s u) (subst s v) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨equiv2_subst s ⟨h1, h2⟩, fun a b e => ?_⟩
  rw [n3_subst, n3_subst]
  simp only [show ∀ x, u.count x = v.count x from h1, h2, h3]

/-- `Equiv3` is preserved by every iterate of a substitution, so `k4_subst`
applies at every level of `σⁿ`. -/
theorem equiv3_iterate_subst (s : α → List α) {u v : List α} (h : Equiv3 u v) (n : ℕ) :
    Equiv3 ((subst s)^[n] u) ((subst s)^[n] v) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact equiv3_subst s ih

/-- **Degree-four defect intertwiner on words** (`lem:conc-subst` (ii) on a
pair; `thm:defect-intertwiner` at `r = 4`): if `K₁(u,v) = K₂(u,v) = K₃(u,v) = 0`
then `K₄(σu, σv) = M^{⊗4} K₄(u,v)`. -/
theorem k4_subst (s : α → List α) {u v : List α} (h : Equiv3 u v) (a b e f : α) :
    K4 (subst s u) (subst s v) a b e f =
      ∑ x, ∑ y, ∑ z, ∑ t,
        (inc s a x : ℤ) * inc s b y * inc s e z * inc s f t * K4 u v x y z t := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold K4
  rw [n4_subst, n4_subst]
  simp only [show ∀ x, u.count x = v.count x from h1, h2, h3]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end General

/-! ### The column identity on representatives -/

section Signed

open scoped Kronecker

variable {α : Type*} [Fintype α] [DecidableEq α] {S : ChildSystem α}
  (P : Normalisation S)

/-- For 3-binomially equivalent states, `M^{⊗4} K₄(T)` is the sum of the `K₄`
of the raw ordered children of `T ∈ C` (`k4_subst` with `k4_children`). -/
theorem k4_image_children (hbal : ∀ T ∈ S.C, Equiv3 T.1 T.2) {T : List α × List α}
    (hT : T ∈ S.C) (a b e f : α) :
    ∑ x, ∑ y, ∑ z, ∑ t, (inc S.s a x : ℤ) * inc S.s b y * inc S.s e z * inc S.s f t *
      K4 T.1 T.2 x y z t = ((S.children T).map fun U => K4 U.1 U.2 a b e f).sum := by
  rw [← k4_subst S.s (hbal T hT)]
  exact k4_children S hT (fun U hU => hbal U (S.closed T hT U hU)) a b e f

/-- **Signed degree-four intertwiner** (`thm:defect-intertwiner`, `r = 4`,
column form of `Q₄ S = M^{⊗4} Q₄`): for 3-binomially equivalent states,
`M^{⊗4} K₄(j) = Σ_i S i j · K₄(i)` on the representatives. -/
theorem k4_rep (hbal : ∀ T ∈ S.C, Equiv3 T.1 T.2) (j : P.Rep) (a b e f : α) :
    ∑ x, ∑ y, ∑ z, ∑ t, (inc S.s a x : ℤ) * inc S.s b y * inc S.s e z * inc S.s f t *
      K4 j.1.1 j.1.2 x y z t = ∑ i : P.Rep, P.Ssign i j * K4 i.1.1 i.1.2 a b e f := by
  rw [k4_image_children hbal (P.sub j.2)]
  exact sum_children_signed P (fun U => K4 U.1 U.2 a b e f) (fun i => k4_swap _ _ a b e f) j

/-- The column matrix `Q₄` of `K₄` on the representatives, rows `α × α × α × α`. -/
def Q4 : Matrix (α × α × α × α) P.Rep ℤ :=
  Matrix.of fun t j => K4 j.1.1 j.1.2 t.1 t.2.1 t.2.2.1 t.2.2.2

open Matrix in
/-- **`Q₄ S = M^{⊗4} Q₄`** (`Φ₄ = M ⊗ (M ⊗ (M ⊗ M))` on the full tensor power),
for 3-binomially equivalent states: `k4_rep` column by column. -/
theorem q4_mul_ssign (hbal : ∀ T ∈ S.C, Equiv3 T.1 T.2) :
    Q4 P * P.Ssign =
      ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ
        ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ (inc S.s).map (Nat.cast : ℕ → ℤ)))) *
        Q4 P := by
  ext ⟨a, b, e, f⟩ j
  simp only [mul_apply, Q4, of_apply, kroneckerMap_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans ?_
  rw [← k4_rep P hbal j a b e f]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  ring

end Signed

/-! ### Controls -/

/-- The Thue–Morse blocks `t₃ = σ³(0) = 01101001` and `t̄₃ = σ³(1) = 10010110`. -/
def tm3 : List (Fin 2) := [0, 1, 1, 0, 1, 0, 0, 1]

/-- The complementary block `t̄₃`. -/
def tm3bar : List (Fin 2) := [1, 0, 0, 1, 0, 1, 1, 0]

theorem tm3_eq :
    (subst thueMorseSubst)^[3] [0] = tm3 ∧ (subst thueMorseSubst)^[3] [1] = tm3bar := by
  decide

/-- `t₃` and `t̄₃` are 3-binomially equivalent ... -/
theorem equiv3_tm3 : Equiv3 tm3 tm3bar := by decide

/-- ... with `K₄(t₃, t̄₃)_{0101} = 8`, so the hypothesis of `k4_subst`,
`k4_additive` and the shuffle relations does not force `K₄ = 0`. -/
theorem k4_tm3 : K4 tm3 tm3bar 0 1 0 1 = 8 := by decide

/-- A ternary control: `012100201` and `102001210` are 3-binomially
equivalent with `K₄_{0102} = 4`. -/
theorem k4_ternary :
    Equiv3 ([0, 1, 2, 1, 0, 0, 2, 0, 1] : List (Fin 3)) [1, 0, 2, 0, 0, 1, 2, 1, 0] ∧
      K4 ([0, 1, 2, 1, 0, 0, 2, 0, 1] : List (Fin 3)) [1, 0, 2, 0, 0, 1, 2, 1, 0] 0 1 0 2 = 4 := by
  decide

/-- **Negative control: `Equiv2` does not suffice for `k4_subst`.**  The
2-binomially equivalent pair `(0110, 1001)` is mapped by Thue–Morse to
`(t₃, t̄₃)`, whose `K₄_{0101}` is `8`, while `M^{⊗4} K₄(0110, 1001)` vanishes
there (the Thue–Morse incidence matrix has rank one). -/
theorem k4_subst_needs_equiv3 :
    Equiv2 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧
      ¬ Equiv3 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧
      K4 (subst thueMorseSubst [0, 1, 1, 0]) (subst thueMorseSubst [1, 0, 0, 1]) 0 1 0 1 ≠
        ∑ x, ∑ y, ∑ z, ∑ t, (inc thueMorseSubst 0 x : ℤ) * inc thueMorseSubst 1 y *
          inc thueMorseSubst 0 z * inc thueMorseSubst 1 t *
            K4 [0, 1, 1, 0] [1, 0, 0, 1] x y z t := by
  refine ⟨equiv2_example, by decide, ?_⟩
  simp only [Fin.sum_univ_two, inc_apply]
  decide

/-- **Negative control: `Equiv2` does not suffice for `k4_shuffle_left`.**  On
`(0110, 1001)`, `K₄(0101) + K₄(1001) + K₄(1001) + K₄(1010) = -2`. -/
theorem k4_shuffle_left_needs_equiv3 :
    Equiv2 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧
      ¬ Equiv3 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧
      K4 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] 0 1 0 1 + K4 [0, 1, 1, 0] [1, 0, 0, 1] 1 0 0 1
        + K4 [0, 1, 1, 0] [1, 0, 0, 1] 1 0 0 1 + K4 [0, 1, 1, 0] [1, 0, 0, 1] 1 0 1 0 = -2 :=
  ⟨equiv2_example, by decide, by decide⟩

/-- **Negative control: `Equiv2` does not suffice for `k4_shuffle_two`.**  On
`wTPair = (0112201, 1200112)` the six shuffles of `01` and `02` give
`K₄(0102) + K₄(0012) + K₄(0021) + K₄(0012) + K₄(0021) + K₄(0201) = -2`.  (The
binary pair `(0110, 1001)` satisfies every `ab ⧢ cd` relation,
`k4_shuffle_two_binary`, so this control is ternary.) -/
theorem k4_shuffle_two_needs_equiv3 :
    Equiv2 wTPair.1 wTPair.2 ∧ ¬ Equiv3 wTPair.1 wTPair.2 ∧
      K4 wTPair.1 wTPair.2 0 1 0 2 + K4 wTPair.1 wTPair.2 0 0 1 2 + K4 wTPair.1 wTPair.2 0 0 2 1
        + K4 wTPair.1 wTPair.2 0 0 1 2 + K4 wTPair.1 wTPair.2 0 0 2 1
        + K4 wTPair.1 wTPair.2 0 2 0 1 = -2 := by
  decide

/-- The binary `Equiv2` pair `(0110, 1001)`, which violates `a ⧢ bcd`
(`k4_shuffle_left_needs_equiv3`), satisfies every `ab ⧢ cd` relation. -/
theorem k4_shuffle_two_binary (a b c d : Fin 2) :
    K4 [0, 1, 1, 0] [1, 0, 0, 1] a b c d + K4 [0, 1, 1, 0] [1, 0, 0, 1] a c b d
      + K4 [0, 1, 1, 0] [1, 0, 0, 1] a c d b + K4 [0, 1, 1, 0] [1, 0, 0, 1] c a b d
      + K4 [0, 1, 1, 0] [1, 0, 0, 1] c a d b + K4 [0, 1, 1, 0] [1, 0, 0, 1] c d a b = 0 := by
  revert a b c d; decide

/-- **Negative control: `Equiv2` does not suffice for `k4_additive`.**  With
`x = 0110`, `x' = 1001` (`Equiv2`, not `Equiv3`) and `y = y' = 0`,
`K₄(x y, x' y')_{0010} = -1` while `K₄(x, x')_{0010} + K₄(y, y')_{0010} = 0`. -/
theorem k4_additive_needs_equiv3 :
    Equiv2 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧
      ¬ Equiv3 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] ∧ Equiv3 ([0] : List (Fin 2)) [0] ∧
      K4 ([0, 1, 1, 0] ++ [0] : List (Fin 2)) ([1, 0, 0, 1] ++ [0]) 0 0 1 0 = -1 ∧
      K4 ([0, 1, 1, 0] : List (Fin 2)) [1, 0, 0, 1] 0 0 1 0 + K4 ([0] : List (Fin 2)) [0] 0 0 1 0
        = 0 :=
  ⟨equiv2_example, by decide, Equiv3.refl _, by decide, by decide⟩

/-- The distinct irreducible 3-binomially equivalent pair
`(011220100112, 120010112201)`. -/
def w4Pair : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 2, 2, 0, 1, 0, 0, 1, 1, 2], [1, 2, 0, 0, 1, 0, 1, 1, 2, 2, 0, 1])

/-- The zero-return system of `w4Pair` under the identity: each state is its
own only child. -/
def w4 : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem idSubst (by decide) {w4Pair, w4Pair.swap} (by decide) (by decide)

/-- `w4` normalised by `R = {w4Pair}`, via `Psc.Reduction.redNormalisation`. -/
def w4Norm : Normalisation w4 :=
  Psc.Reduction.redNormalisation idSubst (by decide) {w4Pair, w4Pair.swap} (by decide)
    (by decide) (by decide) {w4Pair} (by decide) (by decide) (by decide)

theorem w4_equiv3 : ∀ T ∈ w4.C, Equiv3 T.1 T.2 := by decide

theorem w4_irreducible : w4Pair.1 ≠ w4Pair.2 ∧ IrreduciblePair w4Pair.1 w4Pair.2 := by
  decide

def w4Rep : w4Norm.Rep := ⟨w4Pair, Finset.mem_singleton_self _⟩

theorem w4Norm_rep (i : w4Norm.Rep) : i = w4Rep :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `S = (1)`. -/
theorem w4_ssign (i j : w4Norm.Rep) : w4Norm.Ssign i j = 1 := by
  obtain rfl := w4Norm_rep i
  obtain rfl := w4Norm_rep j
  decide

theorem w4_k4_ne : K4 w4Pair.1 w4Pair.2 0 1 0 1 = 8 := by decide

/-- `k4_rep` on `w4`: `M^{⊗4} K₄ = K₄`. -/
theorem w4_k4 (a b e f : Fin 3) :
    ∑ x, ∑ y, ∑ z, ∑ t, (inc w4.s a x : ℤ) * inc w4.s b y * inc w4.s e z * inc w4.s f t *
      K4 w4Pair.1 w4Pair.2 x y z t = K4 w4Pair.1 w4Pair.2 a b e f := by
  have : Subsingleton w4Norm.Rep :=
    ⟨fun i j => (w4Norm_rep i).trans (w4Norm_rep j).symm⟩
  have h := k4_rep w4Norm w4_equiv3 w4Rep a b e f
  rwa [Fintype.sum_subsingleton _ w4Rep, w4_ssign, one_mul] at h

/-- The Thue–Morse blocks `(t₃, t̄₃)` over `Fin 3` (the letter `2` unused). -/
def exTPair : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1, 1, 0])

/-- `exBSubst` (`0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`) maps `t₃ ↦ t̄₃ ↦ t₃`; the only child
of a state is declared to be its swap.  An algebra-only control: see
`exT_reducible`, `exT_not_red`. -/
def exT : ChildSystem (Fin 3) where
  s := exBSubst
  C := {exTPair, exTPair.swap}
  children := fun T => [T.swap]
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

/-- `exT` normalised by `R = {(t₃, t̄₃)}`. -/
def exTNorm : Normalisation exT where
  R := {exTPair}
  swap_mem := by decide
  children_swap := by decide
  sub := by decide
  cover := by decide
  not_both := by decide

theorem exT_equiv3 : ∀ T ∈ exT.C, Equiv3 T.1 T.2 := by decide

/-- The state of `exT` is reducible (zero return after `01 / 10`). -/
theorem exT_reducible : ¬ IrreduciblePair exTPair.1 exTPair.2 := by decide

/-- The declared children of `exT` are not the zero-return blocks. -/
theorem exT_not_red :
    exT.children exTPair ≠ Psc.Reduction.red (subst exT.s exTPair.1) (subst exT.s exTPair.2) := by
  decide

def exTRep : exTNorm.Rep := ⟨exTPair, Finset.mem_singleton_self _⟩

theorem exTNorm_rep (i : exTNorm.Rep) : i = exTRep :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `S = (-1)`: the only child carries the sign `-1`. -/
theorem exT_ssign (i j : exTNorm.Rep) : exTNorm.Ssign i j = -1 := by
  obtain rfl := exTNorm_rep i
  obtain rfl := exTNorm_rep j
  decide

theorem exT_k4_ne : K4 exTPair.1 exTPair.2 0 1 0 1 = 8 := by decide

/-- `k4_rep` on `exT`: `M^{⊗4} K₄(t₃, t̄₃) = - K₄(t₃, t̄₃)`. -/
theorem exT_k4 (a b e f : Fin 3) :
    ∑ x, ∑ y, ∑ z, ∑ t, (inc exT.s a x : ℤ) * inc exT.s b y * inc exT.s e z *
      inc exT.s f t * K4 exTPair.1 exTPair.2 x y z t = -K4 exTPair.1 exTPair.2 a b e f := by
  have : Subsingleton exTNorm.Rep :=
    ⟨fun i j => (exTNorm_rep i).trans (exTNorm_rep j).symm⟩
  have h := k4_rep exTNorm exT_equiv3 exTRep a b e f
  rwa [Fintype.sum_subsingleton _ exTRep, exT_ssign, neg_one_mul] at h

end Psc.Defect4
