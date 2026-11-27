/-
# Pisot spectral contraction core

This module exposes the properness and contraction construction independently of the
strict-system equivalence and example applications in `GeometricFPisot`. The existing
contraction declarations are extracted unchanged and retain their public names.
-/
import PscVerif.GeometricFLength
import PscVerif.ConcentrationAlgebra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Psc.GeometricFPisot

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.BPrimeBinding Psc.GeometricF

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### Complex functionals on integer vectors -/

/-- The additive functional `v ↦ w·v` on integer vectors, for a complex row `w`. -/
def dotHom (w : α → ℂ) : (α → ℤ) →+ ℂ where
  toFun v := ∑ a, w a * (v a : ℂ)
  map_zero' := by simp
  map_add' v v' := by simp [mul_add, Finset.sum_add_distrib]

omit [DecidableEq α] in
theorem dotHom_apply (w : α → ℂ) (v : α → ℤ) : dotHom w v = ∑ a, w a * (v a : ℂ) := rfl

/-- A left eigen-row `w M = z w` of the complex incidence matrix is an eigenfunctional of the
integer incidence action: `w·(M v) = z (w·v)`. -/
theorem dotHom_mulVec {s : α → List α} {w : α → ℂ} {z : ℂ}
    (h : w ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = z • w) (v : α → ℤ) :
    dotHom w (incZ s *ᵥ v) = z * dotHom w v := by
  have hc : ∀ c, ∑ a, w a * ((inc s a c : ℕ) : ℂ) = z * w c := fun c => by
    have := congrFun h c
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [dotHom_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, ← hc c, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- A real left eigen-row, read over `ℂ`. -/
theorem ofReal_left_eigen {s : α → List α} {ℓ : α → ℝ} {β : ℝ}
    (h : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    (fun a => (ℓ a : ℂ)) ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = (β : ℂ) • fun a => (ℓ a : ℂ) := by
  funext c
  have := congrFun h c
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  exact_mod_cast this

omit [DecidableEq α] in
/-- The complexified length functional is the length functional. -/
theorem dotHom_ofReal (ℓ : α → ℝ) (v : α → ℤ) :
    dotHom (fun a => (ℓ a : ℂ)) v = ((lenHom ℓ v : ℝ) : ℂ) := by
  simp [dotHom_apply, lenHom_apply]

/-! ### Properness: Lemma 1 (2) -/

/-- **Properness from a spanning family of functionals.**  If the rows `W k` span `ℂ^α`, then
only finitely many integer vectors have all the coordinates `W k · v` bounded by `B`: each
`v_a` is a fixed linear combination of the `W k · v`. -/
theorem finite_of_span_eq_top {κ : Type*} [Fintype κ] (W : κ → α → ℂ)
    (hW : Submodule.span ℂ (Set.range W) = ⊤) (B : ℝ) :
    {v : α → ℤ | ∀ k, ‖dotHom (W k) v‖ ≤ B}.Finite := by
  have hc : ∀ a : α, ∃ c : κ → ℂ, ∑ k, c k • W k = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (by rw [hW]; exact Submodule.mem_top)
  choose c hc using hc
  refine (Set.Finite.pi fun a : α =>
    Set.finite_Icc (-⌈(∑ k, ‖c a k‖) * B⌉) ⌈(∑ k, ‖c a k‖) * B⌉).subset ?_
  intro v hv a _
  have e : ((v a : ℤ) : ℂ) = ∑ k, c a k * dotHom (W k) v := by
    have h1 : ((v a : ℤ) : ℂ) = ∑ b, (Pi.single a (1 : ℂ) : α → ℂ) b * (v b : ℂ) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [h1, ← hc a]
    simp only [dotHom_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  have hn : |((v a : ℤ) : ℝ)| ≤ (∑ k, ‖c a k‖) * B := by
    have h2 : ‖((v a : ℤ) : ℂ)‖ ≤ (∑ k, ‖c a k‖) * B := by
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hv k) (norm_nonneg _)
    rwa [Complex.norm_intCast] at h2
  rw [abs_le] at hn
  have hceil := Int.le_ceil ((∑ k, ‖c a k‖) * B)
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · have : ((-⌈(∑ k, ‖c a k‖) * B⌉ : ℤ) : ℝ) ≤ ((v a : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((v a : ℤ) : ℝ) ≤ ((⌈(∑ k, ‖c a k‖) * B⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

omit [DecidableEq α] in
/-- **Left eigen-rows for pairwise distinct eigenvalues, as many as letters, span `ℂ^α`**
(eigenvectors for distinct eigenvalues are linearly independent). -/
theorem span_eq_top_of_left_eigen {κ : Type*} [Fintype κ] (A : Matrix α α ℂ) (μ : κ → ℂ)
    (hμ : Function.Injective μ) (W : κ → α → ℂ) (hW0 : ∀ k, W k ≠ 0)
    (hW : ∀ k, W k ᵥ* A = μ k • W k) (hcard : Fintype.card κ = Fintype.card α) :
    Submodule.span ℂ (Set.range W) = ⊤ := by
  have hli : LinearIndependent ℂ W :=
    Module.End.eigenvectors_linearIndependent' A.vecMulLinear μ hμ W fun k =>
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.vecMulLinear_apply]; exact hW k), hW0 k⟩
  exact hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, Module.finrank_fintype_fun_eq_card])

/-- A separable characteristic polynomial over `ℂ` has as many distinct roots as letters. -/
theorem card_roots_toFinset (A : Matrix α α ℂ) (hsep : A.charpoly.Separable) :
    A.charpoly.roots.toFinset.card = Fintype.card α := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    charpoly_natDegree_eq_dim]

/-- An irreducible `χ_M` over `ℚ` is separable over `ℂ`. -/
theorem charpoly_separable_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) :
    ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable := by
  have e : ((inc s).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  rw [← e, Matrix.charpoly_map]
  exact hirr.separable.map

/-- An irreducible `χ_M` forces a nonempty alphabet (`χ = 1` on the empty one). -/
theorem nonempty_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  rw [Matrix.charpoly_isEmpty] at hirr
  exact not_irreducible_one hirr

/-! ### (A) Contraction data from the spectral hypotheses -/

/-- **Properness of the eigen-coordinates** (Lemma 1 (2) of the note).  If the rows `W k`
span `ℂ^α` and `W k₀` is the real row `ℓ`, then for all real `a, b` only finitely many integer
vectors `v` have `|ℓ·v| ≤ a` and `∑_{k ≠ k₀} |W k · v| ≤ b`. -/
theorem proper_of_span {κ : Type*} [Fintype κ] (W : κ → α → ℂ)
    (hW : Submodule.span ℂ (Set.range W) = ⊤) {ℓ : α → ℝ} (k₀ : κ)
    (hk₀ : W k₀ = fun a => (ℓ a : ℂ)) [Fintype {k : κ // k ≠ k₀}] (a b : ℝ) :
    {v : α → ℤ | |lenHom ℓ v| ≤ a ∧
      ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖ ≤ b}.Finite := by
  refine (finite_of_span_eq_top W hW (|a| + |b|)).subset ?_
  rintro v ⟨hv1, hv2⟩ k
  by_cases h : k = k₀
  · rw [h, hk₀, dotHom_ofReal, Complex.norm_real, Real.norm_eq_abs]
    linarith [le_abs_self a, abs_nonneg b]
  · have h1 : ‖dotHom (W k) v‖ ≤ ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖ :=
      Finset.single_le_sum (f := fun i : {k : κ // k ≠ k₀} => ‖dotHom (W i.1) v‖)
        (a := ⟨k, h⟩) (fun i _ => norm_nonneg _) (Finset.mem_univ _)
    linarith [le_abs_self b, abs_nonneg a]

/-- **(A), eigen-row form.**  Let `W k` (`k : κ`, `|κ| = |α|`) be nonzero left eigen-rows of
the complex incidence matrix for pairwise distinct eigenvalues `μ k`, let `W k₀` be a real row
`ℓ`, and let `‖μ k‖ ≤ ρ < 1` for every `k ≠ k₀`.  Then `ν v = ∑_{k ≠ k₀} |W k · v|` and `ρ`
are contraction data for the length functional `v ↦ ℓ·v`.  On three letters this is the
statement for eigenvalues `β, λ₂, λ₃` with `|λ₂|, |λ₃| < 1`; the eigen-rows are a basis of
`ℂ^α` because the eigenvalues are pairwise distinct (`span_eq_top_of_left_eigen`). -/
theorem contractionData_of_eigenrows {κ : Type*} [Fintype κ] (s : α → List α) (μ : κ → ℂ)
    (hμ : Function.Injective μ) (W : κ → α → ℂ) (hW0 : ∀ k, W k ≠ 0)
    (hWA : ∀ k, W k ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = μ k • W k)
    (hcard : Fintype.card κ = Fintype.card α) {ℓ : α → ℝ} (k₀ : κ)
    (hk₀ : W k₀ = fun a => (ℓ a : ℂ)) [Fintype {k : κ // k ≠ k₀}] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hlam : ∀ k, k ≠ k₀ → ‖μ k‖ ≤ ρ) :
    ContractionData s (lenHom ℓ) (fun v => ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖) ρ :=
  contractionData_of_eigenfunctionals (fun i : {k : κ // k ≠ k₀} => dotHom (W i.1))
    (fun i => μ i.1) (fun i v => dotHom_mulVec (hWA i.1) v) hρ0 hρ1 (fun i => hlam i.1 i.2)
    (proper_of_span W (span_eq_top_of_left_eigen _ μ hμ W hW0 hWA hcard) k₀ hk₀)

/-- A finite family of reals `< 1` is bounded by one `ρ` with `0 ≤ ρ < 1`. -/
theorem exists_bound_lt_one {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, f i < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, f i ≤ ρ := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨0, le_rfl, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨max (f i₀) 0, le_max_right _ _, max_lt (hf i₀) one_pos,
      fun i => (hi₀ i).trans (le_max_left _ _)⟩

/-- **(A), the core: contracted eigenfunctionals and contraction data from the spectrum.**
Let the complex characteristic polynomial of the incidence matrix be separable (pairwise
distinct eigenvalues), let `ℓ ≠ 0` be a real left eigen-row for `β`, and let every other
complex root of `χ_M` lie in the open unit disc.  Then there are finitely many additive
functionals `η i` on integer vectors with `η i (M v) = lam i * η i v`, each `lam i` a root of
`χ_M` other than `β`, all of modulus at most some `ρ < 1`, such that
`ν v = ∑ i, ‖η i v‖` and `ρ` are contraction data for the length functional `v ↦ ℓ·v`.

Properness (Lemma 1 (2) of the note) is where distinctness enters: `ℓ` and one left eigen-row
for each other root are `|α|` eigen-rows for pairwise distinct eigenvalues, hence a basis of
`ℂ^α`, and `finite_of_span_eq_top` applies. -/
theorem exists_eigenfunctionals_of_separable (s : α → List α)
    (hsep : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ι : Type) (_ : Fintype ι) (η : ι → (α → ℤ) →+ ℂ) (lam : ι → ℂ) (ρ : ℝ),
      (∀ i v, η i (incZ s *ᵥ v) = lam i * η i v) ∧
      (∀ i, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval (lam i) = 0 ∧ lam i ≠ β) ∧
      (∀ i, ‖lam i‖ ≤ ρ) ∧
      ContractionData s (lenHom ℓ) (fun v => ∑ i, ‖η i v‖) ρ := by
  classical
  have hp0 : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  -- the set of roots: as many as letters
  obtain ⟨R, hmem, hcard⟩ : ∃ R : Finset ℂ,
      (∀ z : ℂ, z ∈ R ↔ ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) ∧
        R.card = Fintype.card α :=
    ⟨_, fun z => by rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def],
      card_roots_toFinset _ hsep⟩
  -- the Perron row over `ℂ`
  have hℓc0 : (fun a => (ℓ a : ℂ)) ≠ 0 := fun h => hℓ0 (funext fun a => by
    have := congrFun h a
    simpa using this)
  have hℓcA := ofReal_left_eigen hℓM
  have hβroot : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval (β : ℂ) = 0 :=
    Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ _ _ hℓc0 hℓcA
  -- a left eigen-row for every root
  have hq : ∀ z : R, ∃ q : α → ℂ, q ≠ 0 ∧
      q ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = (z : ℂ) • q := fun z => by
    obtain ⟨q, hq0, hq⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
      ((inc s).map (Nat.cast : ℕ → ℂ))ᵀ (z : ℂ)
      (by rw [Matrix.charpoly_transpose]; exact (hmem z).1 z.2)
    exact ⟨q, hq0, by rw [← Matrix.mulVec_transpose]; exact hq⟩
  choose q hq0 hqA using hq
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : R, (k₀ : ℂ) = β := ⟨⟨β, (hmem _).2 hβroot⟩, rfl⟩
  have hW0 : ∀ k, Function.update q k₀ (fun a => (ℓ a : ℂ)) k ≠ 0 := fun k => by
    by_cases h : k = k₀
    · rw [h, Function.update_self]
      exact hℓc0
    · rw [Function.update_of_ne h]
      exact hq0 k
  have hWA : ∀ k : R, Function.update q k₀ (fun a => (ℓ a : ℂ)) k ᵥ*
      (inc s).map (Nat.cast : ℕ → ℂ) = (k : ℂ) • Function.update q k₀ (fun a => (ℓ a : ℂ)) k :=
    fun k => by
      by_cases h : k = k₀
      · rw [h, Function.update_self, hk₀]
        exact hℓcA
      · rw [Function.update_of_ne h]
        exact hqA k
  have hne : ∀ i : {k : R // k ≠ k₀}, ((i.1 : ℂ)) ≠ β := fun i h =>
    i.2 (Subtype.ext (h.trans hk₀.symm))
  obtain ⟨ρ, hρ0, hρ1, hlam⟩ := exists_bound_lt_one (fun i : {k : R // k ≠ k₀} => ‖(i.1 : ℂ)‖)
    fun i => hpisot _ ((hmem _).1 i.1.2) (hne i)
  exact ⟨{k : R // k ≠ k₀}, inferInstance,
    fun i => dotHom (Function.update q k₀ (fun a => (ℓ a : ℂ)) i.1),
    fun i => (i.1 : ℂ), ρ, fun i v => dotHom_mulVec (hWA i.1) v,
    fun i => ⟨(hmem _).1 i.1.2, hne i⟩, hlam,
    contractionData_of_eigenrows s (fun k : R => (k : ℂ)) Subtype.val_injective _ hW0 hWA
      (by rw [Fintype.card_coe]; exact hcard) k₀ (Function.update_self ..)
      hρ0 hρ1 fun k hk => hlam ⟨k, hk⟩⟩

/-- **(A), separable form**: contraction data exist. -/
theorem exists_contractionData_of_separable (s : α → List α)
    (hsep : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  obtain ⟨ι, _, η, lam, ρ, -, -, -, hc⟩ :=
    exists_eigenfunctionals_of_separable s hsep hℓ0 hℓM hpisot
  exact ⟨_, ρ, hc⟩

/-- **(A) on the standing class.**  Let `χ_M` be irreducible over `ℚ`, let `ℓ > 0` be a left
eigen-row of the incidence matrix for `β` (the Perron row), and let every complex root of
`χ_M` other than `β` lie in the open unit disc (the Pisot hypothesis, in the form of the
conclusion of `Psc.BPrime.bprime_cubic`).  Then `ContractionData s (lenHom ℓ) ν ρ` holds for
some `ν`, `ρ`.  Primitivity is not used. -/
theorem exists_contractionData_of_pisot (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  have := nonempty_of_irreducible s hirr
  exact exists_contractionData_of_separable s (charpoly_separable_of_irreducible s hirr)
    (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) hℓM hpisot

/-- Evaluating the rational incidence characteristic polynomial over a field is
ordinary evaluation of the incidence characteristic polynomial cast to that field. -/
theorem aeval_charpoly {K : Type*} [Field K] [Algebra ℚ K] (s : α → List α) (x : K) :
    aeval x ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly =
      ((inc s).map (Nat.cast : ℕ → K)).charpoly.eval x := by
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map]
  congr 2
  ext a c
  simp

end Psc.GeometricFPisot
