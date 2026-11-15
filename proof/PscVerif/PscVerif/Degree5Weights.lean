/- Degree-five weights after a change of basis over a splitting field. -/
import PscVerif.Lie5
import PscVerif.LieWeights

namespace Psc.Degree5Weights

open Psc.Lie5 Psc.LieWeights Matrix
open scoped BigOperators Kronecker

def letters : Word5 → List (Fin 3)
  | ⟨a,b,c,d,e⟩ => [a,b,c,d,e]

def content (w : Word5) : Fin 3 → ℕ := wordContent (letters w)

def pure (i : Fin 3) : Word5 := ⟨i,i,i,i,i⟩

abbrev Mixed (κ : Fin 3 → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), κ = ![4,1,0] ∘ σ ∨ κ = ![3,2,0] ∘ σ ∨
    κ = ![3,1,1] ∘ σ ∨ κ = ![2,2,1] ∘ σ

theorem content_cases : ∀ w : Word5, (∃ i, w = pure i) ∨ Mixed (content w) := by
  decide +kernel

def power5 {K : Type*} [Mul K] (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix Word5 Word5 K := M ⊗ₖ (M ⊗ₖ (M ⊗ₖ (M ⊗ₖ M)))

theorem power5_mul {K : Type*} [CommSemiring K] (A B : Matrix (Fin 3) (Fin 3) K) :
    power5 (A * B) = power5 A * power5 B := by
  simp only [power5, mul_kronecker_mul]

theorem power5_one {K : Type*} [CommSemiring K] :
    power5 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp only [power5, one_kronecker_one]

theorem power5_diagonal {K : Type*} [CommSemiring K] (x : Fin 3 → K) :
    power5 (diagonal x) = diagonal (fun w => mono x (content w)) := by
  simp only [power5, diagonal_kronecker_diagonal]
  congr 1
  funext ⟨a,b,c,d,e⟩
  simp only [content, letters, mono_wordContent, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

theorem coeff_cons (t : Word5 × ℤ) (row : Sparse) (w : Word5) :
    coeff (t :: row) w = (if t.1 = w then t.2 else 0) + coeff row w := by
  by_cases h : t.1 = w <;> simp [coeff, h]

/-- Evaluate a weighted coefficient sum directly on the sparse expansion. -/
theorem weighted_coeff {K : Type*} [CommRing K] (g : Word5 → K) (row : Sparse) :
    (∑ v, g v * (coeff row v : K)) = (row.map fun t => g t.1 * (t.2 : K)).sum := by
  induction row with
  | nil => simp [coeff]
  | cons t row ih =>
    simp only [coeff_cons, Int.cast_add, mul_add, Finset.sum_add_distrib, ih,
      List.map_cons, List.sum_cons]
    simp [apply_ite]

def bracketContent (i : Fin 48) : Fin 3 → ℕ :=
  content ((bracket5 i).headD (pure 0, 0)).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Every checked expansion is homogeneous and its signed coefficients
sum to zero. The certificate runs on sparse bracket rows. -/
theorem bracket_content_sums (i : Fin 48) :
    (bracket5 i).all (fun t => content t.1 == bracketContent i) = true ∧
      ((bracket5 i).map Prod.snd).sum = 0 := by
  fin_cases i <;> decide +kernel

theorem pure_bracket {K : Type*} [Field K] (Q : Matrix (Fin 3) (Fin 3) K)
    (j : Fin 48) (i : Fin 3) :
    (power5 Q *ᵥ (fun v => (coeff (bracket5 j) v : K))) (pure i) = 0 := by
  change (∑ v, power5 Q (pure i) v * (coeff (bracket5 j) v : K)) = 0
  have entry (v : Word5) : power5 Q (pure i) v = mono (Q i) (content v) := by
    rcases v with ⟨a,b,c,d,e⟩
    simp only [power5, pure, kroneckerMap_apply, content, letters, mono_wordContent,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [weighted_coeff]
  have h := (bracket_content_sums j).1
  simp only [List.all_eq_true, beq_iff_eq] at h
  have hm : ((bracket5 j).map fun t => power5 Q (pure i) t.1 * (t.2 : K)) =
      ((bracket5 j).map fun t => mono (Q i) (bracketContent j) * (t.2 : K)) :=
    List.map_congr_left fun t ht => by rw [entry, h t ht]
  rw [hm, List.sum_map_mul_left]
  have hz : ((bracket5 j).map fun t => (t.2 : K)).sum = 0 := by
    have hc := congrArg (fun z : ℤ => (z : K)) (bracket_content_sums j).2
    simpa only [Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_zero] using hc
  rw [hz, mul_zero]

/-- A diagonal eigenvector with pure coordinates zero has a mixed weight.
This formulation works when different contents have the same weight. -/
theorem mixed_of_diagonal_eigen {K : Type*} [Field K] (x : Fin 3 → K)
    {f : Word5 → K} {z : K} (hne : f ≠ 0)
    (hzero : ∀ i, f (pure i) = 0) (heig : power5 (diagonal x) *ᵥ f = z • f) :
    ∃ κ, Mixed κ ∧ z = mono x κ := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rcases content_cases w with ⟨i,rfl⟩ | hm
  · exact False.elim (hw (hzero i))
  refine ⟨content w, hm, ?_⟩
  have he := congrFun heig w
  rw [power5_diagonal, mulVec_diagonal] at he
  exact (mul_right_cancel₀ hw he).symm

/-- The verified rational shuffle criterion supplies bracket coefficients
over any characteristic-zero extension field. -/
theorem cast_bracket_combination {K : Type*} [Field K] [CharZero K]
    {f : Vec5} (h : ShuffleAnnih5 f) :
    ∃ c : Fin 48 → K, (fun v => (f v : K)) =
      ∑ j, c j • (fun v => (coeff (bracket5 j) v : K)) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 48 → ℚ, f = ∑ j, c j • lyndon5 j :=
    ⟨_, eq_sum_lyndon5 h⟩
  refine ⟨fun j => (c j : K), ?_⟩
  funext v
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, lyndon5]
  push_cast; rfl

/-- A degree-five Lie eigenvector has one of the four mixed shapes after
an invertible change of basis. The argument uses a nonzero word coordinate
and so makes no simple-spectrum assumption on the tensor action. -/
theorem mixed_of_lie_eigen {K : Type*} [Field K]
    (M Q L : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K)
    (hQ : Q * M = diagonal x * Q) (hL : L * Q = 1)
    {f : Word5 → K} {z : K} (hne : f ≠ 0)
    (hLie : ∃ c : Fin 48 → K,
      f = ∑ j, c j • (fun v => (coeff (bracket5 j) v : K)))
    (heig : power5 M *ᵥ f = z • f) :
    ∃ κ, Mixed κ ∧ z = mono x κ := by
  classical
  have hnon : power5 Q *ᵥ f ≠ 0 := by
    intro h
    apply hne
    have hh := congrArg (fun v => power5 L *ᵥ v) h
    rwa [mulVec_mulVec, ← power5_mul, hL, power5_one, one_mulVec, mulVec_zero] at hh
  have hpure (i : Fin 3) : (power5 Q *ᵥ f) (pure i) = 0 := by
    obtain ⟨c, rfl⟩ := hLie
    simp [mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, pure_bracket]
  have he : power5 (diagonal x) *ᵥ (power5 Q *ᵥ f) = z • (power5 Q *ᵥ f) := by
    rw [mulVec_mulVec, ← power5_mul, ← hQ, power5_mul, ← mulVec_mulVec, heig, mulVec_smul]
  exact mixed_of_diagonal_eigen x hnon hpure he

/-- The three placements of (2,2,1) are a common nonzero multiple of the
reciprocal roots, so distinct incidence roots give distinct sector weights. -/
theorem reciprocal_221 {K : Type*} [Field K] {a b c : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a*b*c)^2 / a = a*b^2*c^2 ∧
    (a*b*c)^2 / b = a^2*b*c^2 ∧
    (a*b*c)^2 / c = a^2*b^2*c := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- The reciprocal sector polynomial in the elementary symmetric data
of the incidence roots. -/
theorem reciprocal_221_polynomial {K : Type*} [CommRing K] (a b c t : K) :
    (t - a*b^2*c^2) * (t - a^2*b*c^2) * (t - a^2*b^2*c) =
      t^3 - (a*b*c)*(a*b + a*c + b*c)*t^2 +
        (a*b*c)^3*(a + b + c)*t - (a*b*c)^5 := by
  ring

/-- Even distinct incidence eigenvalues can give a collision between
different mixed contents. This diagonal control has no Pisot hypothesis. -/
theorem mixed_weight_collision :
    (2 : ℚ) * 4^4 = 2^2 * 4^2 * 8 := by norm_num

end Psc.Degree5Weights
