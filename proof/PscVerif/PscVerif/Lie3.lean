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

## Proved here, in full

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
  statement.**  `Vec3 R = Fin 3 → Fin 3 → Fin 3 → R` (coordinates of
  `(R³)^{⊗3}` in the word basis), `ShuffleAnnih f` (the shuffle relations in
  both index orders for all `a b c`; `shuffleAnnih_iff_left`: the first order
  alone is equivalent, so `shuffleAnnihSpace` is the sector
  `W₃ = ker S` of `Psc.BalancedPair.K₃_shuffle_zero` in coordinate form),
  `br x y z` (the word-basis coordinates of
  `[[x,y],z] = xyz - yxz - zxy + zyx`) and `lyndon : Fin 8 → Vec3 R`, the
  standard bracketings of the Lyndon words `001, 002, 011, 012, 021, 022, 112,
  122` (`[0,[0,1]] = -br 0 1 0`, `[0,[0,2]] = -br 0 2 0`, `[[0,1],1]`,
  `[0,[1,2]] = -br 1 2 0`, `[[0,2],1]`, `[[0,2],2]`, `[1,[1,2]] = -br 1 2 1`,
  `[[1,2],2]`).  Over **any commutative ring `R`**:
  - `shuffleAnnih_br`: every `br x y z` satisfies `ShuffleAnnih` (a kernel
    `decide` over all `3⁶` index choices over `ℤ`, `shuffleAnnih_br_int`,
    transported along `Int.castRingHom` by `ShuffleAnnih.map` and `map3_br`);
  - `lyndonCoeff_sum`: the explicit coefficients
    `lyndonCoeff f = (f₀₀₁, f₀₀₂, f₀₁₁, f₀₁₂, f₀₁₂ + f₀₂₁, f₀₂₂, f₁₁₂, f₁₂₂)`
    recover any combination of the brackets exactly, hence
    `linearIndependent_lyndon`;
  - naturality under ring homomorphisms: `map3`, `ShuffleAnnih.map`,
    `map3_lyndon`, `lyndonCoeff_map3`, `phi3_map`.
  Over **a field `F` of characteristic zero** (the certificate divides by `3`):
  - `eq_sum_lyndon`: if `ShuffleAnnih f` then `f = Σ_i lyndonCoeff f i • lyndon i`
    (coordinatewise `linear_combination` over the 27 coordinates);
  - `shuffleAnnih_iff_mem_span`, `shuffleAnnihSpace_eq_span`: the shuffle
    annihilator is exactly the `F`-span of the eight Lyndon brackets;
  - `finrank_shuffleAnnihSpace`: it has dimension
    `8 = dim Lie₃(F³) = (3³ - 3)/3`.
  The rational statements are the instances `R = ℚ`, `F = ℚ`.
  Negative control for the characteristic hypothesis:
  `zmod3_shuffleAnnih_not_mem_span`: over `ZMod 3` the word vector `000` is
  shuffle-annihilated but not in the span of the brackets (they all vanish at
  `000`), so the spanning half fails in characteristic three.
* **Invariance** `shuffleAnnih_phi3` (any commutative ring), `phi3_mem_span`
  (a field of characteristic zero): `M^{⊗3}` (`phi3 M`, any `3 × 3` matrix `M`)
  maps the shuffle annihilator, i.e. `Lie₃`, into itself (the relations at
  `(x, y, z)`, weighted by `M a x · M b y · M c z`).
* **Conclusion** (over `ℚ`) `k3Vec_mem_span_lyndon`: for every 2-binomially
  equivalent pair of words over `Fin 3`, the vector `(K3 u v a b c : ℚ)` lies in
  the span of the eight Lyndon brackets (`K₃ ∈ Lie₃`), with the explicit
  expansion `k3Vec_eq_sum_lyndon`; `k3Vec_example` (non-vacuity): `(0110, 1001)`
  over `Fin 3` is 2-binomially equivalent with `k3Vec ≠ 0`.

## Not proved here

* Ree's theorem in general (other degrees, other alphabet sizes; degree four
  on three letters is `Psc.LieWeights`), and the
  identification of the span of the brackets with the free Lie algebra as an
  abstract object: `Lie₃` here *means* the span of the eight explicit
  bracket vectors in `(F³)^{⊗3}`.  Fields of positive characteristic are not
  treated for the spanning half: its certificate `eq_sum_lyndon` divides only by
  `3`, but the weaker hypothesis `(3 : F) ≠ 0` is not stated; in characteristic
  three the spanning half fails (`zmod3_shuffleAnnih_not_mem_span`).
* Nothing about the spectrum of `M^{⊗3}` on `Lie₃` (the weights and content
  components are `Psc.LieWeights`), the cocycle, the operator `Q₃` (see
  `PscVerif.SignedIntertwiner`), or any spectral consequence.
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

/-- Coordinates of a tensor in `(R³)^{⊗3}` in the word basis. -/
abbrev Vec3 (R : Type*) := Fin 3 → Fin 3 → Fin 3 → R

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The shuffle relations (`a ⧢ bc` and its re-indexing `ab ⧢ c`) at every
index. -/
def ShuffleAnnih (f : Vec3 R) : Prop :=
  ∀ a b c, f a b c + f b a c + f b c a = 0 ∧ f a b c + f a c b + f c a b = 0

/-- The re-indexed relation is redundant: `ShuffleAnnih` is `W₃ = ker S` of
`Psc.BalancedPair.K₃_shuffle_zero`, in coordinate form. -/
theorem shuffleAnnih_iff_left (f : Vec3 R) :
    ShuffleAnnih f ↔ ∀ a b c, f a b c + f b a c + f b c a = 0 :=
  ⟨fun h a b c => (h a b c).1, fun h a b c => ⟨h a b c, by linear_combination h c a b⟩⟩

/-- The shuffle annihilator as a submodule. -/
def shuffleAnnihSpace : Submodule R (Vec3 R) where
  carrier := {f | ShuffleAnnih f}
  add_mem' {f g} hf hg a b c := by
    obtain ⟨hf1, hf2⟩ := hf a b c
    obtain ⟨hg1, hg2⟩ := hg a b c
    simp only [Pi.add_apply]
    exact ⟨by linear_combination hf1 + hg1, by linear_combination hf2 + hg2⟩
  zero_mem' _ _ _ := by simp
  smul_mem' r f hf a b c := by
    obtain ⟨h1, h2⟩ := hf a b c
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨by linear_combination r * h1, by linear_combination r * h2⟩

/-- The word-basis vector of `xyz`. -/
def word (x y z : Fin 3) : Vec3 R := fun a b c => if a = x ∧ b = y ∧ c = z then 1 else 0

/-- The word-basis coordinates of `[[x,y],z] = xyz - yxz - zxy + zyx`. -/
def br (x y z : Fin 3) : Vec3 R := word x y z - word y x z - word z x y + word z y x

/-- Coordinatewise image under a ring homomorphism. -/
def map3 (φ : R →+* S) (f : Vec3 R) : Vec3 S := fun a b c => φ (f a b c)

/-- The shuffle relations are preserved by every ring homomorphism. -/
theorem ShuffleAnnih.map (φ : R →+* S) {f : Vec3 R} (h : ShuffleAnnih f) :
    ShuffleAnnih (map3 φ f) := fun a b c => by
  obtain ⟨h1, h2⟩ := h a b c
  exact ⟨by simpa [map3] using congrArg φ h1, by simpa [map3] using congrArg φ h2⟩

@[simp] theorem map3_add (φ : R →+* S) (f g : Vec3 R) :
    map3 φ (f + g) = map3 φ f + map3 φ g := by
  funext a b c; simp [map3]

@[simp] theorem map3_sub (φ : R →+* S) (f g : Vec3 R) :
    map3 φ (f - g) = map3 φ f - map3 φ g := by
  funext a b c; simp [map3]

@[simp] theorem map3_neg (φ : R →+* S) (f : Vec3 R) : map3 φ (-f) = -map3 φ f := by
  funext a b c; simp [map3]

@[simp] theorem map3_word (φ : R →+* S) (x y z : Fin 3) : map3 φ (word x y z) = word x y z := by
  funext a b c; simp only [map3, word]; split_ifs <;> simp

@[simp] theorem map3_br (φ : R →+* S) (x y z : Fin 3) : map3 φ (br x y z) = br x y z := by
  simp [br]

/-- The brackets over `ℤ`: a kernel `decide` over all `3⁶` index choices. -/
theorem shuffleAnnih_br_int (x y z : Fin 3) : ShuffleAnnih (br (R := ℤ) x y z) := by
  revert x y z
  unfold ShuffleAnnih br word
  decide +kernel

/-- Every left-normed bracket `[[x,y],z]` satisfies both shuffle relations, over
every commutative ring (`shuffleAnnih_br_int`, transported along
`Int.castRingHom`). -/
theorem shuffleAnnih_br (x y z : Fin 3) : ShuffleAnnih (br (R := R) x y z) := by
  rw [← map3_br (Int.castRingHom R)]
  exact (shuffleAnnih_br_int x y z).map _

/-- The standard bracketings of the eight Lyndon words of length three on
`0 < 1 < 2`: `001, 002, 011, 012, 021, 022, 112, 122`. -/
def lyndon : Fin 8 → Vec3 R :=
  ![-br 0 1 0, -br 0 2 0, br 0 1 1, -br 1 2 0, br 0 2 1, br 0 2 2, -br 1 2 1, br 1 2 2]

/-- The coefficients of a shuffle-annihilated vector on the Lyndon brackets. -/
def lyndonCoeff (f : Vec3 R) : Fin 8 → R :=
  ![f 0 0 1, f 0 0 2, f 0 1 1, f 0 1 2, f 0 1 2 + f 0 2 1, f 0 2 2, f 1 1 2, f 1 2 2]

theorem lyndon_mem (i : Fin 8) : lyndon (R := R) i ∈ shuffleAnnihSpace := by
  have h : ∀ x y z, -br x y z ∈ shuffleAnnihSpace (R := R) := fun x y z =>
    neg_mem (shuffleAnnih_br x y z)
  fin_cases i
  exacts [h 0 1 0, h 0 2 0, shuffleAnnih_br 0 1 1, h 1 2 0, shuffleAnnih_br 0 2 1,
    shuffleAnnih_br 0 2 2, h 1 2 1, shuffleAnnih_br 1 2 2]

theorem lyndonCoeff_zero : lyndonCoeff (0 : Vec3 R) = 0 := by
  funext i; fin_cases i <;> simp [lyndonCoeff]

/-- The coefficients `lyndonCoeff` recover every combination of the Lyndon
brackets exactly. -/
theorem lyndonCoeff_sum (g : Fin 8 → R) : lyndonCoeff (∑ i, g i • lyndon i) = g := by
  funext i
  fin_cases i <;> simp [lyndonCoeff, lyndon, br, word, Fin.sum_univ_eight]

/-- **The eight Lyndon brackets are linearly independent** (over every commutative
ring). -/
theorem linearIndependent_lyndon : LinearIndependent R (lyndon (R := R)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [← congrFun (lyndonCoeff_sum g) i, hg, lyndonCoeff_zero, Pi.zero_apply]

theorem map3_lyndon (φ : R →+* S) (i : Fin 8) : map3 φ (lyndon i) = lyndon i := by
  fin_cases i <;> simp [lyndon]

theorem lyndonCoeff_map3 (φ : R →+* S) (f : Vec3 R) (i : Fin 8) :
    lyndonCoeff (map3 φ f) i = φ (lyndonCoeff f i) := by
  fin_cases i <;> simp [lyndonCoeff, map3]

/-! ### `M^{⊗3}` preserves the shuffle annihilator -/

/-- `M^{⊗3}` in word-basis coordinates. -/
def phi3 (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3 R) : Vec3 R :=
  fun a b c => ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * f x y z

/-- The shuffle relations are natural: `M^{⊗3}` maps the shuffle annihilator
into itself (the relations at `(x, y, z)` weighted by `M a x · M b y · M c z`). -/
theorem shuffleAnnih_phi3 (M : Matrix (Fin 3) (Fin 3) R) {f : Vec3 R} (hf : ShuffleAnnih f) :
    ShuffleAnnih (phi3 M f) := by
  intro a b c
  have k₁ : ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * (f x y z + f y x z + f y z x) = 0 := by
    simp [(hf _ _ _).1]
  have k₂ : ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * (f x y z + f x z y + f z x y) = 0 := by
    simp [(hf _ _ _).2]
  simp only [phi3, Fin.sum_univ_three] at k₁ k₂ ⊢
  exact ⟨by linear_combination k₁, by linear_combination k₂⟩

/-- `M^{⊗3}` commutes with every ring homomorphism. -/
theorem phi3_map (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3 R) :
    phi3 (M.map φ) (map3 φ f) = map3 φ (phi3 M f) := by
  funext a b c
  simp [phi3, map3, map_sum, map_mul, Matrix.map_apply]

end Ring

/-! ### Ree at degree three over a field of characteristic zero -/

section Field

variable {F : Type*} [Field F] [CharZero F]

/-- **Ree at degree three, spanning half**: a shuffle-annihilated vector is the
explicit combination of the eight Lyndon brackets. -/
theorem eq_sum_lyndon {f : Vec3 F} (h : ShuffleAnnih f) :
    f = ∑ i, lyndonCoeff f i • lyndon i := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [lyndonCoeff, lyndon, br, word, Fin.sum_univ_eight]
  · linear_combination (1/3 : F) * (h 0 0 0).1
  · linear_combination (h 0 0 1).1
  · linear_combination (h 0 0 2).1
  · linear_combination (-1 : F) * (h 0 0 1).1 + (h 0 0 1).2
  · linear_combination (h 0 1 1).2
  · linear_combination (h 0 2 1).2
  · linear_combination (h 0 1 1).1 + (-1 : F) * (h 0 1 1).2
  · linear_combination (1/3 : F) * (h 1 1 1).1
  · linear_combination (h 0 1 2).1 + (-1 : F) * (h 0 2 1).2
  · linear_combination (h 1 1 2).1
  · linear_combination (-1 : F) * (h 0 0 2).1 + (h 0 0 2).2
  · linear_combination (h 0 1 2).2
  · linear_combination (h 0 2 2).2
  · linear_combination (-1 : F) * (h 0 1 2).1 + (h 1 0 2).2
  · linear_combination (-1 : F) * (h 1 1 2).1 + (h 1 1 2).2
  · linear_combination (h 1 2 2).2
  · linear_combination (h 0 2 2).1 + (-1 : F) * (h 0 2 2).2
  · linear_combination (h 1 2 2).1 + (-1 : F) * (h 1 2 2).2
  · linear_combination (1/3 : F) * (h 2 2 2).1

/-- **Ree at degree three on three letters**: a vector satisfies both shuffle
relations iff it lies in the `F`-span of the eight Lyndon brackets. -/
theorem shuffleAnnih_iff_mem_span (f : Vec3 F) :
    ShuffleAnnih f ↔ f ∈ Submodule.span F (Set.range lyndon) := by
  constructor
  · intro h
    rw [eq_sum_lyndon h]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    have hle : Submodule.span F (Set.range lyndon) ≤ shuffleAnnihSpace :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr lyndon_mem)
    exact hle h

theorem shuffleAnnihSpace_eq_span :
    shuffleAnnihSpace = Submodule.span F (Set.range (lyndon (R := F))) :=
  Submodule.ext shuffleAnnih_iff_mem_span

/-- The shuffle annihilator in `(F³)^{⊗3}` has dimension `8 = dim Lie₃(F³)`. -/
theorem finrank_shuffleAnnihSpace : Module.finrank F (shuffleAnnihSpace (R := F)) = 8 := by
  rw [shuffleAnnihSpace_eq_span, finrank_span_eq_card linearIndependent_lyndon]
  simp

/-- **`Lie₃` is `M^{⊗3}`-invariant**, so `Φ₃ = M^{⊗3}` restricts to it. -/
theorem phi3_mem_span (M : Matrix (Fin 3) (Fin 3) F) {f : Vec3 F}
    (hf : f ∈ Submodule.span F (Set.range lyndon)) :
    phi3 M f ∈ Submodule.span F (Set.range lyndon) :=
  (shuffleAnnih_iff_mem_span _).mp (shuffleAnnih_phi3 M ((shuffleAnnih_iff_mem_span f).mpr hf))

end Field

/-! ### Negative control: characteristic three -/

/-- **The characteristic-zero hypothesis of `shuffleAnnihSpace_eq_span` cannot
be dropped.**  Over `ZMod 3` the word vector `000` is shuffle-annihilated (both
relations at `(0, 0, 0)` read `3 f₀₀₀ = 0`, and every other relation has no
term at `000`), but it is not in the span of the eight Lyndon brackets, all of
which vanish at `000`.  So neither `eq_sum_lyndon` nor
`shuffleAnnih_iff_mem_span` holds over `ZMod 3`. -/
theorem zmod3_shuffleAnnih_not_mem_span :
    ShuffleAnnih (word (R := ZMod 3) 0 0 0) ∧
      word (R := ZMod 3) 0 0 0 ∉ Submodule.span (ZMod 3) (Set.range (lyndon (R := ZMod 3))) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold ShuffleAnnih word
    decide +kernel
  · have key : ∀ g ∈ Submodule.span (ZMod 3) (Set.range (lyndon (R := ZMod 3))), g 0 0 0 = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i <;> simp [lyndon, br, word]
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul r x _ hx => simp [hx]
    exact absurd (key _ h) (by simp [word])

/-! ### `K₃ ∈ Lie₃` -/

/-- The degree-three defect of a pair of words over `Fin 3`, as a vector of
`(ℚ³)^{⊗3}`. -/
def k3Vec (u v : List (Fin 3)) : Vec3 ℚ := fun a b c => (K3 u v a b c : ℚ)

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
    k3Vec u v ∈ Submodule.span ℚ (Set.range (lyndon (R := ℚ))) :=
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
