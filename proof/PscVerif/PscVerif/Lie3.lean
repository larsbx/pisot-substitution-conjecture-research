/-
# `K₃` lies in the free Lie component at degree three

`docs/c4-concentration-attack-2026-11-06.md` §8;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `lem:conc-subst` (iii) at
`r = 3` (the shuffle annihilation of the first nonzero defect) and the
identification of the shuffle annihilator with `Lie₃` used in
`thm:defect-intertwiner`.

Words are lists over an alphabet `α` with decidable equality; `n2` is
`Psc.Binomial.n2`, `n3` is `Psc.Incidence.n3`, and
`K3 u v a b c = n3 u a b c - n3 v a b c` is `Psc.Intertwiner3.K3`.

## What is proved, in full

* **Shuffle identities on words** (any alphabet, in `ℕ`).  The naive shuffle
  products need coincidence corrections, since a position can be shared by the
  two factors when letters agree (cf. `Psc.N_mul_N₂` in `PscVerif.Shuffle`):
  - `count_mul_count`: `|w|_a · |w|_c = n2 w a c + n2 w c a + [a = c] |w|_a`;
  - `count_mul_n2` (`a ⧢ bc`): `|w|_a · n2 w b c = n3 w a b c + n3 w b a c +
    n3 w b c a + [a = b] n2 w a c + [a = c] n2 w b a`;
  - `n2_mul_count` (`ab ⧢ c`): `n2 w a b · |w|_c = n3 w a b c + n3 w a c b +
    n3 w c a b + [b = c] n2 w a b + [a = c] n2 w a b`, which is `count_mul_n2`
    at `(c, a, b)` (`ab ⧢ c = c ⧢ ab`).
* **The proper shuffle relations of `K₃`** (any alphabet): if `Equiv2 u v`
  (`K₁ = K₂ = 0`) then `k3_shuffle_left`:
  `K3 a b c + K3 b a c + K3 b c a = 0`.  This is one family of relations;
  `k3_shuffle_right`, `K3 a b c + K3 a c b + K3 c a b = 0`, is the same family
  re-indexed at `(c, a, b)`.  `BalancedPair.K₃_shuffle_right` is the re-indexed
  form for `Psc.BalancedPair` (via `PscVerif.CountBridge`); the first is
  `Psc.BalancedPair.K₃_shuffle_zero`.
* **Ree's theorem at degree three on three letters, as an exact finite
  statement.**  `Vec3 = Fin 3 → Fin 3 → Fin 3 → ℚ` (coordinates of
  `(ℚ³)^{⊗3}` in the word basis), `ShuffleAnnih f` (the shuffle relations in
  both index orders for all `a b c`; `shuffleAnnih_iff_left`: the first order
  alone is equivalent, so `shuffleAnnihSpace` is the sector
  `W₃ = ker S` of `Psc.BalancedPair.K₃_shuffle_zero` in coordinate form),
  `br x y z` (the word-basis coordinates of
  `[[x,y],z] = xyz - yxz - zxy + zyx`) and `lyndon : Fin 8 → Vec3`, the
  standard bracketings of the Lyndon words `001, 002, 011, 012, 021, 022, 112,
  122` (`[0,[0,1]] = -br 0 1 0`, `[0,[0,2]] = -br 0 2 0`, `[[0,1],1]`,
  `[0,[1,2]] = -br 1 2 0`, `[[0,2],1]`, `[[0,2],2]`, `[1,[1,2]] = -br 1 2 1`,
  `[[1,2],2]`):
  - `shuffleAnnih_br`: every `br x y z` satisfies `ShuffleAnnih` (a kernel
    `decide` over all `3⁶` index choices);
  - `eq_sum_lyndon`: if `ShuffleAnnih f` then `f = Σ_i lyndonCoeff f i • lyndon i`
    with the explicit coefficients `f₀₀₁, f₀₀₂, f₀₁₁, f₀₁₂, f₀₁₂ + f₀₂₁, f₀₂₂,
    f₁₁₂, f₁₂₂` (coordinatewise `linear_combination` over the 27 coordinates);
    `lyndonCoeff_sum`: these coefficients recover any combination exactly;
  - `shuffleAnnih_iff_mem_span`, `shuffleAnnihSpace_eq_span`: the shuffle
    annihilator is exactly the `ℚ`-span of the eight Lyndon brackets;
  - `linearIndependent_lyndon` and `finrank_shuffleAnnihSpace`: the eight are
    linearly independent, so the shuffle annihilator has dimension
    `8 = dim Lie₃(ℚ³) = (3³ - 3)/3`.
* **Invariance** `shuffleAnnih_phi3`, `phi3_mem_span`: `M^{⊗3}` (`phi3 M`, any
  rational `3 × 3` matrix `M`) maps `Lie₃` into itself.
* **Conclusion** `k3Vec_mem_span_lyndon`: for every 2-binomially equivalent pair
  of words over `Fin 3`, the vector `(K3 u v a b c : ℚ)` lies in the span of the
  eight Lyndon brackets (`K₃ ∈ Lie₃`), with the explicit expansion
  `k3Vec_eq_sum_lyndon`; `k3Vec_example` (non-vacuity): `(0110, 1001)` over
  `Fin 3` is 2-binomially equivalent with `k3Vec ≠ 0`.

## What is not proved here

* Ree's theorem in general (other degrees, other alphabet sizes; degree four
  on three letters is `Psc.LieWeights`), and the
  identification of the span of the brackets with the free Lie algebra as an
  abstract object: `Lie₃` here *means* the span of the eight explicit
  bracket vectors in `(ℚ³)^{⊗3}`.
* Nothing about the spectrum of `M^{⊗3}` on `Lie₃`, the cocycle, the operator
  `Q₃` (see `PscVerif.SignedIntertwiner`), or any spectral consequence.
* No statement about infinite words, fixed points or the balanced-pair
  algorithm.
-/
import PscVerif.CountBridge

namespace Psc.Lie3

open Psc.Binomial Psc.Incidence Psc.Intertwiner3

/-! ### Shuffle identities for the scattered counts -/

section Words

variable {α : Type*} [DecidableEq α]

/-- Degree-two shuffle with its coincidence correction. -/
theorem count_mul_count (w : List α) (a c : α) :
    w.count a * w.count c = n2 w a c + n2 w c a + if a = c then w.count a else 0 := by
  induction w with
  | nil => simp [n2]
  | cons x t ih =>
    simp only [n2, List.count_cons, beq_iff_eq]
    split_ifs at * <;> subst_vars <;> first | contradiction | linear_combination ih

/-- **`a ⧢ bc`** on words, with the coincidence corrections. -/
theorem count_mul_n2 (w : List α) (a b c : α) :
    w.count a * n2 w b c =
      n3 w a b c + n3 w b a c + n3 w b c a
        + (if a = b then n2 w a c else 0) + (if a = c then n2 w b a else 0) := by
  induction w with
  | nil => simp [n2]
  | cons x t ih =>
    have key := count_mul_count t a c
    simp only [n3_cons, n2, List.count_cons, beq_iff_eq]
    split_ifs at * <;> subst_vars <;>
      first | contradiction | linear_combination ih | linear_combination ih + key

/-- **`ab ⧢ c`** on words, with the coincidence corrections: `count_mul_n2` at
`(c, a, b)`. -/
theorem n2_mul_count (w : List α) (a b c : α) :
    n2 w a b * w.count c =
      n3 w a b c + n3 w a c b + n3 w c a b
        + (if b = c then n2 w a b else 0) + (if a = c then n2 w a b else 0) := by
  rw [mul_comm, count_mul_n2 w c a b]
  split_ifs <;> subst_vars <;> first | contradiction | ring1

/-- **First shuffle relation of `K₃`** (`a ⧢ bc`): on a 2-binomially
equivalent pair, `K₃(abc) + K₃(bac) + K₃(bca) = 0`. -/
theorem k3_shuffle_left {u v : List α} (h : Equiv2 u v) (a b c : α) :
    K3 u v a b c + K3 u v b a c + K3 u v b c a = 0 := by
  have hu := count_mul_n2 u a b c
  have hv := count_mul_n2 v a b c
  rw [h.1 a, h.2 b c, h.2 a c, h.2 b a] at hu
  unfold K3
  have := congrArg (fun n : ℕ => (n : ℤ)) (hu.symm.trans hv)
  push_cast at this
  linear_combination this

/-- The shuffle relation re-indexed (`ab ⧢ c`): `k3_shuffle_left` at
`(c, a, b)`. -/
theorem k3_shuffle_right {u v : List α} (h : Equiv2 u v) (a b c : α) :
    K3 u v a b c + K3 u v a c b + K3 u v c a b = 0 := by
  linear_combination k3_shuffle_left h c a b

end Words

/-- A balanced pair with `K₂ = 0` is 2-binomially equivalent. -/
theorem equiv2_of_balancedPair (s : BalancedPair) (h₂ : ∀ i j, s.K₂ i j = 0) :
    Equiv2 s.u s.v := by
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have := s.parikh a
    rw [CountBridge.N_eq_count, CountBridge.N_eq_count] at this
    exact_mod_cast this
  · have := h₂ a b
    rw [CountBridge.K₂_eq_K2, Psc.Intertwiner2.K2, sub_eq_zero] at this
    exact_mod_cast this

/-- The second shuffle relation for `Psc.BalancedPair` (the first is
`Psc.BalancedPair.K₃_shuffle_zero`). -/
theorem BalancedPair.K₃_shuffle_right (s : BalancedPair) (h₂ : ∀ i j, s.K₂ i j = 0)
    (a b c : Letter) : s.K₃ a b c + s.K₃ a c b + s.K₃ c a b = 0 := by
  simp only [CountBridge.K₃_eq_K3]
  exact k3_shuffle_right (equiv2_of_balancedPair s h₂) a b c

/-! ### Ree's theorem at degree three on three letters -/

/-- Coordinates of a tensor in `(ℚ³)^{⊗3}` in the word basis. -/
abbrev Vec3 := Fin 3 → Fin 3 → Fin 3 → ℚ

/-- The shuffle relations (`a ⧢ bc` and its re-indexing `ab ⧢ c`) at every
index. -/
def ShuffleAnnih (f : Vec3) : Prop :=
  ∀ a b c, f a b c + f b a c + f b c a = 0 ∧ f a b c + f a c b + f c a b = 0

/-- The re-indexed relation is redundant: `ShuffleAnnih` is `W₃ = ker S` of
`Psc.BalancedPair.K₃_shuffle_zero`, in coordinate form. -/
theorem shuffleAnnih_iff_left (f : Vec3) :
    ShuffleAnnih f ↔ ∀ a b c, f a b c + f b a c + f b c a = 0 :=
  ⟨fun h a b c => (h a b c).1, fun h a b c => ⟨h a b c, by linear_combination h c a b⟩⟩

/-- The shuffle annihilator as a subspace. -/
def shuffleAnnihSpace : Submodule ℚ Vec3 where
  carrier := {f | ShuffleAnnih f}
  add_mem' {f g} hf hg a b c := by
    obtain ⟨hf1, hf2⟩ := hf a b c
    obtain ⟨hg1, hg2⟩ := hg a b c
    simp only [Pi.add_apply]
    constructor <;> linarith
  zero_mem' _ _ _ := by simp
  smul_mem' r f hf a b c := by
    obtain ⟨h1, h2⟩ := hf a b c
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨by linear_combination r * h1, by linear_combination r * h2⟩

/-- The word-basis vector of `xyz`. -/
def word (x y z : Fin 3) : Vec3 := fun a b c => if a = x ∧ b = y ∧ c = z then 1 else 0

/-- The word-basis coordinates of `[[x,y],z] = xyz - yxz - zxy + zyx`. -/
def br (x y z : Fin 3) : Vec3 := word x y z - word y x z - word z x y + word z y x

/-- Every left-normed bracket `[[x,y],z]` satisfies both shuffle relations. -/
theorem shuffleAnnih_br (x y z : Fin 3) : ShuffleAnnih (br x y z) := by
  revert x y z
  unfold ShuffleAnnih br word
  decide +kernel

/-- The standard bracketings of the eight Lyndon words of length three on
`0 < 1 < 2`: `001, 002, 011, 012, 021, 022, 112, 122`. -/
def lyndon : Fin 8 → Vec3 :=
  ![-br 0 1 0, -br 0 2 0, br 0 1 1, -br 1 2 0, br 0 2 1, br 0 2 2, -br 1 2 1, br 1 2 2]

/-- The coefficients of a shuffle-annihilated vector on the Lyndon brackets. -/
def lyndonCoeff (f : Vec3) : Fin 8 → ℚ :=
  ![f 0 0 1, f 0 0 2, f 0 1 1, f 0 1 2, f 0 1 2 + f 0 2 1, f 0 2 2, f 1 1 2, f 1 2 2]

theorem lyndon_mem (i : Fin 8) : lyndon i ∈ shuffleAnnihSpace := by
  have h : ∀ x y z, -br x y z ∈ shuffleAnnihSpace := fun x y z =>
    neg_mem (shuffleAnnih_br x y z)
  fin_cases i
  exacts [h 0 1 0, h 0 2 0, shuffleAnnih_br 0 1 1, h 1 2 0, shuffleAnnih_br 0 2 1,
    shuffleAnnih_br 0 2 2, h 1 2 1, shuffleAnnih_br 1 2 2]

/-- **Ree at degree three, spanning half**: a shuffle-annihilated vector is the
explicit combination of the eight Lyndon brackets. -/
theorem eq_sum_lyndon {f : Vec3} (h : ShuffleAnnih f) :
    f = ∑ i, lyndonCoeff f i • lyndon i := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [lyndonCoeff, lyndon, br, word, Fin.sum_univ_eight]
  · linear_combination (1/3 : ℚ) * (h 0 0 0).1
  · linear_combination (h 0 0 1).1
  · linear_combination (h 0 0 2).1
  · linear_combination (-1 : ℚ) * (h 0 0 1).1 + (h 0 0 1).2
  · linear_combination (h 0 1 1).2
  · linear_combination (h 0 2 1).2
  · linear_combination (h 0 1 1).1 + (-1 : ℚ) * (h 0 1 1).2
  · linear_combination (1/3 : ℚ) * (h 1 1 1).1
  · linear_combination (h 0 1 2).1 + (-1 : ℚ) * (h 0 2 1).2
  · linear_combination (h 1 1 2).1
  · linear_combination (-1 : ℚ) * (h 0 0 2).1 + (h 0 0 2).2
  · linear_combination (h 0 1 2).2
  · linear_combination (h 0 2 2).2
  · linear_combination (-1 : ℚ) * (h 0 1 2).1 + (h 1 0 2).2
  · linear_combination (-1 : ℚ) * (h 1 1 2).1 + (h 1 1 2).2
  · linear_combination (h 1 2 2).2
  · linear_combination (h 0 2 2).1 + (-1 : ℚ) * (h 0 2 2).2
  · linear_combination (h 1 2 2).1 + (-1 : ℚ) * (h 1 2 2).2
  · linear_combination (1/3 : ℚ) * (h 2 2 2).1

/-- The coefficients `lyndonCoeff` recover every combination of the Lyndon
brackets exactly. -/
theorem lyndonCoeff_sum (g : Fin 8 → ℚ) : lyndonCoeff (∑ i, g i • lyndon i) = g := by
  funext i
  fin_cases i <;> simp [lyndonCoeff, lyndon, br, word, Fin.sum_univ_eight]

/-- **The eight Lyndon brackets are linearly independent.** -/
theorem linearIndependent_lyndon : LinearIndependent ℚ lyndon := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrFun (lyndonCoeff_sum g) i
  rw [hg] at this
  rw [← this]
  fin_cases i <;> simp [lyndonCoeff]

/-- **Ree at degree three on three letters**: a vector satisfies both shuffle
relations iff it lies in the `ℚ`-span of the eight Lyndon brackets. -/
theorem shuffleAnnih_iff_mem_span (f : Vec3) :
    ShuffleAnnih f ↔ f ∈ Submodule.span ℚ (Set.range lyndon) := by
  constructor
  · intro h
    rw [eq_sum_lyndon h]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    have hle : Submodule.span ℚ (Set.range lyndon) ≤ shuffleAnnihSpace :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr lyndon_mem)
    exact hle h

theorem shuffleAnnihSpace_eq_span :
    shuffleAnnihSpace = Submodule.span ℚ (Set.range lyndon) :=
  Submodule.ext shuffleAnnih_iff_mem_span

/-- The shuffle annihilator in `(ℚ³)^{⊗3}` has dimension `8 = dim Lie₃(ℚ³)`. -/
theorem finrank_shuffleAnnihSpace : Module.finrank ℚ shuffleAnnihSpace = 8 := by
  rw [shuffleAnnihSpace_eq_span, finrank_span_eq_card linearIndependent_lyndon]
  simp

/-! ### `M^{⊗3}` preserves `Lie₃` -/

/-- `M^{⊗3}` in word-basis coordinates. -/
def phi3 (M : Matrix (Fin 3) (Fin 3) ℚ) (f : Vec3) : Vec3 :=
  fun a b c => ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * f x y z

/-- The shuffle relations are natural: `M^{⊗3}` maps the shuffle annihilator
into itself (the 27 relations at `(x, y, z)`, weighted by `M a x · M b y · M c z`). -/
theorem shuffleAnnih_phi3 (M : Matrix (Fin 3) (Fin 3) ℚ) {f : Vec3} (hf : ShuffleAnnih f) :
    ShuffleAnnih (phi3 M f) := by
  rw [shuffleAnnih_iff_left] at hf ⊢
  intro a b c
  have h := hf
  simp only [phi3, Fin.sum_univ_three]
  linear_combination
    M a 0 * M b 0 * M c 0 * h 0 0 0 + M a 0 * M b 0 * M c 1 * h 0 0 1
    + M a 0 * M b 0 * M c 2 * h 0 0 2 + M a 0 * M b 1 * M c 0 * h 0 1 0
    + M a 0 * M b 1 * M c 1 * h 0 1 1 + M a 0 * M b 1 * M c 2 * h 0 1 2
    + M a 0 * M b 2 * M c 0 * h 0 2 0 + M a 0 * M b 2 * M c 1 * h 0 2 1
    + M a 0 * M b 2 * M c 2 * h 0 2 2 + M a 1 * M b 0 * M c 0 * h 1 0 0
    + M a 1 * M b 0 * M c 1 * h 1 0 1 + M a 1 * M b 0 * M c 2 * h 1 0 2
    + M a 1 * M b 1 * M c 0 * h 1 1 0 + M a 1 * M b 1 * M c 1 * h 1 1 1
    + M a 1 * M b 1 * M c 2 * h 1 1 2 + M a 1 * M b 2 * M c 0 * h 1 2 0
    + M a 1 * M b 2 * M c 1 * h 1 2 1 + M a 1 * M b 2 * M c 2 * h 1 2 2
    + M a 2 * M b 0 * M c 0 * h 2 0 0 + M a 2 * M b 0 * M c 1 * h 2 0 1
    + M a 2 * M b 0 * M c 2 * h 2 0 2 + M a 2 * M b 1 * M c 0 * h 2 1 0
    + M a 2 * M b 1 * M c 1 * h 2 1 1 + M a 2 * M b 1 * M c 2 * h 2 1 2
    + M a 2 * M b 2 * M c 0 * h 2 2 0 + M a 2 * M b 2 * M c 1 * h 2 2 1
    + M a 2 * M b 2 * M c 2 * h 2 2 2

/-- **`Lie₃` is `M^{⊗3}`-invariant**, so `Φ₃ = M^{⊗3}` restricts to it. -/
theorem phi3_mem_span (M : Matrix (Fin 3) (Fin 3) ℚ) {f : Vec3}
    (hf : f ∈ Submodule.span ℚ (Set.range lyndon)) :
    phi3 M f ∈ Submodule.span ℚ (Set.range lyndon) :=
  (shuffleAnnih_iff_mem_span _).mp (shuffleAnnih_phi3 M ((shuffleAnnih_iff_mem_span f).mpr hf))

/-! ### `K₃ ∈ Lie₃` -/

/-- The degree-three defect of a pair of words over `Fin 3`, as a vector of
`(ℚ³)^{⊗3}`. -/
def k3Vec (u v : List (Fin 3)) : Vec3 := fun a b c => (K3 u v a b c : ℚ)

theorem shuffleAnnih_k3Vec {u v : List (Fin 3)} (h : Equiv2 u v) :
    ShuffleAnnih (k3Vec u v) := fun a b c => by
  refine ⟨?_, ?_⟩
  · have := k3_shuffle_left h a b c
    simp only [k3Vec]
    exact_mod_cast this
  · have := k3_shuffle_right h a b c
    simp only [k3Vec]
    exact_mod_cast this

/-- The explicit expansion of `K₃` on the Lyndon brackets. -/
theorem k3Vec_eq_sum_lyndon {u v : List (Fin 3)} (h : Equiv2 u v) :
    k3Vec u v = ∑ i, lyndonCoeff (k3Vec u v) i • lyndon i :=
  eq_sum_lyndon (shuffleAnnih_k3Vec h)

/-- **`K₃ ∈ Lie₃`**: for every 2-binomially equivalent pair of words over
`Fin 3`, the degree-three defect lies in the span of the eight Lyndon
brackets. -/
theorem k3Vec_mem_span_lyndon {u v : List (Fin 3)} (h : Equiv2 u v) :
    k3Vec u v ∈ Submodule.span ℚ (Set.range lyndon) :=
  (shuffleAnnih_iff_mem_span _).mp (shuffleAnnih_k3Vec h)

/-- Non-vacuity: the pair `(0110, 1001)` of `Psc.Intertwiner3.k3_example`,
read over `Fin 3`, is 2-binomially equivalent with a nonzero `K₃` vector. -/
theorem k3Vec_example :
    Equiv2 ([0, 1, 1, 0] : List (Fin 3)) [1, 0, 0, 1] ∧
      k3Vec [0, 1, 1, 0] [1, 0, 0, 1] ≠ 0 := by
  refine ⟨by unfold Equiv2 Equiv1; decide, fun h => ?_⟩
  have := congrFun (congrFun (congrFun h 0) 1) 0
  have h2 : K3 ([0, 1, 1, 0] : List (Fin 3)) [1, 0, 0, 1] 0 1 0 = 2 := by decide
  simp [k3Vec, h2] at this

end Psc.Lie3
