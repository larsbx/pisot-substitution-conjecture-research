import PscVerif.GeometricFStrict
import PscVerif.BPrime

namespace Psc.GeometricFPisot

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.BPrimeBinding Psc.GeometricF
open Psc.StrictSystem (StrictSystem StrongCoincidenceWitness)

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

/-! ### The Pisot hypothesis in the repository's other two forms -/

/-- **From `Psc.BPrime.IsPisot`.**  With `χ_M` irreducible, the Perron root `β` of a positive
left eigen-row is a root of `χ_M`, `χ_M` is its minimal polynomial
(`Psc.BPrime.minpoly_eq_charpoly`), and `IsPisot β` puts every other complex root of `χ_M`
in the open unit disc. -/
theorem pisot_roots_of_isPisot (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hP : Psc.BPrime.IsPisot β) :
    ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ < 1 := by
  have := nonempty_of_irreducible s hirr
  have hroot := Psc.BPrime.isRoot_of_pos_left_eigen s hℓ hℓM
  intro z hz hzβ
  refine hP.2.2 z ?_ hzβ
  rw [Psc.BPrime.minpoly_eq_charpoly s hirr hroot, Psc.BPrime.aeval_charpoly]
  exact hz

/-- **The Perron root is the Pisot root**, on any alphabet (three letters:
`Psc.Degree4Floor.perron_eq_pisot`).  If `β` is a complex root of `χ_M` with `1 < ‖β‖` and
every other complex root has modulus `< 1` (the hypotheses `hβ`, `hβ1`, `hpisot` of
`Psc.Degree4Floor.sieve4_pisot` and `Psc.Degree5Completion`), and `ℓ > 0` is a left eigen-row
for the real `r`, then `r = β` and `1 < r`.  No primitivity: `‖β‖ ≤ r` is
`Psc.PerronExistence.norm_le_of_pos_left_eigen`. -/
theorem perron_eq_pisot_root (s : α → List α) {r : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) : (r : ℂ) = β ∧ 1 < r := by
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Matrix.charpoly_isEmpty] at hβ
    simp at hβ
  have hc : ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  have hN : ∀ a c, 0 ≤ (inc s).map (Nat.cast : ℕ → ℝ) a c := fun a c => Nat.cast_nonneg _
  have hle : ‖β‖ ≤ r :=
    Psc.PerronExistence.norm_le_of_pos_left_eigen _ hN ℓ hℓ r hℓM β
      (by rw [hc, ← Psc.BPrime.aeval_charpoly]; exact hβ)
  have hr : aeval (r : ℂ) ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 := by
    rw [Psc.BPrime.aeval_charpoly, ← hc]
    exact Psc.PerronExistence.isRoot_ofReal_of_left_eigen _ ℓ
      (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) r hℓM
  refine ⟨?_, lt_of_lt_of_le hβ1 hle⟩
  by_contra hne'
  have h1 := hpisot _ hr hne'
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [le_abs_self r]

/-- **From the sieve form to the root form.**  Under the hypotheses of
`perron_eq_pisot_root`, the eigenvalue `r` of a positive left eigen-row satisfies `1 < r` and
every complex root of `χ_M` other than `r` has modulus `< 1`. -/
theorem pisot_roots_of_pisot_root (s : α → List α) {r : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) :
    1 < r ∧ ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ r →
      ‖z‖ < 1 := by
  obtain ⟨hr, hr1⟩ := perron_eq_pisot_root s hℓ hℓM hβ hβ1 hpisot
  refine ⟨hr1, fun z hz hzr => ?_⟩
  rw [hr] at hzr
  exact hpisot z (by rw [Psc.BPrime.aeval_charpoly]; exact hz) hzr

/-! ### (B) and (C): Theorem FC1 on the standing class -/

section Instance

variable {s : α → List α} {β : ℝ} {ℓ : α → ℝ}

/-- **(A) and (B): the abstract hypotheses of Theorem FC1 hold on the standing class.**  For
a primitive substitution on at least two letters with `χ_M` irreducible over `ℚ`, Perron row
`ℓ > 0`, `ℓ M = β ℓ`, and every other complex root of `χ_M` in the open unit disc:
`LengthData`, `1 < β` (`Psc.BPrimeCore.one_lt_perron`) and `ContractionData` all hold for the
length functional `v ↦ ℓ·v`. -/
theorem fc1_hypotheses_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    LengthData s (lenHom ℓ) β ∧ 1 < β ∧
      ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  have hβ := Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM
  exact ⟨lengthData_of_left_eigen (by linarith) hℓ hℓM, hβ,
    exists_contractionData_of_pisot s hirr hℓ hℓM hpisot⟩

/-- **(A) and (B) in the hypothesis form of the sieve theorems, with the Perron row
produced.**  Let `σ` be primitive with `χ_M` irreducible over `ℚ`, and let `β` be a complex
root of `χ_M` with `1 < ‖β‖` and every other complex root of modulus `< 1` (the standing
hypotheses of `Psc.Degree4Floor.sieve4_pisot`).  Then there are a real `r` with `r = β`, a
left eigen-row `ℓ > 0` for `r`, and `ν`, `ρ` such that `LengthData s (lenHom ℓ) r`, `1 < r` and
`ContractionData s (lenHom ℓ) ν ρ` hold: every abstract hypothesis of
`Psc.GeometricF.fc1_equivalence_of_contraction` except `PropertyF`. -/
theorem exists_fc1_data_of_primitive_pisot
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (r : ℝ) (ℓ : α → ℝ) (ν : (α → ℤ) → ℝ) (ρ : ℝ), (r : ℂ) = β ∧ (∀ a, 0 < ℓ a) ∧
      ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ ∧
      LengthData s (lenHom ℓ) r ∧ 1 < r ∧ ContractionData s (lenHom ℓ) ν ρ := by
  obtain ⟨r, hr0, ℓ, hℓ, hℓM⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc s hprim
  obtain ⟨hr1, hroots⟩ := pisot_roots_of_pisot_root s hℓ hℓM hβ hβ1 hpisot
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hroots
  exact ⟨r, ℓ, ν, ρ, (perron_eq_pisot_root s hℓ hℓM hβ hβ1 hpisot).1, hℓ, hℓM,
    lengthData_of_left_eigen hr0 hℓ hℓM, hr1, hc⟩

/-- **Theorem FC1 (the equivalences) for an irreducible Pisot incidence matrix.**  Let `χ_M`
be irreducible over `ℚ`, `ℓ > 0` a left eigen-row for `β > 1`, every other complex root of
`χ_M` of modulus `< 1`, and let property (F) hold for the tile lengths `ℓ`.  Then `σ` has a
strict system iff some pair of distinct `g`-periodic letters has no left strong-coincidence
witness iff left strong coincidence fails for some pair of distinct letters. -/
theorem fc1_equivalence_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  exact fc1_equivalence_of_contraction (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ hc hF

/-- **Theorem FC1 (the equivalences) on the standing class**, in the hypothesis form of
`Psc.BPrime`: `σ` primitive on at least two letters, `χ_M` irreducible over `ℚ`, `ℓ > 0` with
`ℓ M = β ℓ`, every complex root of `χ_M` other than `β` in the open unit disc, and
property (F) for the tile lengths `ℓ`.  No abstract hypothesis is left: `β > 1` is
`Psc.BPrimeCore.one_lt_perron` and the contraction data are
`exists_contractionData_of_pisot`. -/
theorem fc1_equivalence_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_pisot hirr hℓ hℓM (Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM) hpisot hF

/-- **Theorem FC1 (the equivalences) with `Psc.BPrime.IsPisot`**: `χ_M` irreducible over
`ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, `β` a Pisot number, and property (F).  Irreducibility cannot
be dropped in this form: `IsPisot β` constrains only the conjugates of `β`. -/
theorem fc1_equivalence_of_isPisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hP : Psc.BPrime.IsPisot β) (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_pisot hirr hℓ hℓM hP.1 (pisot_roots_of_isPisot s hirr hℓ hℓM hP) hF

/-- **Theorem FC1 (the equivalences) in the hypothesis form of the sieve theorems**
(`Psc.Degree4Floor.sieve4_pisot`, `Psc.Degree5Completion`): `χ_M` irreducible over `ℚ`, a
complex root `β` with `1 < ‖β‖`, every other complex root of modulus `< 1`; then for every
positive left eigen-row `ℓ` (eigenvalue `r`, which is `β`: `perron_eq_pisot_root`) with
property (F) the equivalences hold. -/
theorem fc1_equivalence_of_pisot_root
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1)
    {r : ℝ} (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') := by
  obtain ⟨hr1, hroots⟩ := pisot_roots_of_pisot_root s hℓ hℓM hβ hβ1 hpisot
  exact fc1_equivalence_of_pisot hirr hℓ hℓM hr1 hroots hF

/-- **Theorem FC1, items (1) and (2), for an irreducible Pisot incidence matrix**: `χ_M`
irreducible over `ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, `β > 0`, every other complex root of `χ_M` of
modulus `< 1`, and property (F).  For any two `σ^m`-fixed words, `m ≥ 1`, there is `N` with
`M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}`, and every window `(t, t + β^{mN} ℓ_max]`, `t ≥ 0`,
holds the position of a common vertex (`ℓ_max ≥ max_a ℓ_a`).  `β > 1` is not needed here. -/
theorem fc1_inclusion_gap_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 0 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, ℓ a ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X',
          t < lenHom ℓ z ∧ lenHom ℓ z ≤ t + β ^ (m * N) * ℓmax := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  obtain ⟨N, h1, h2⟩ := fc1_inclusion_gap_of_contraction (lengthData_of_left_eigen hβ hℓ hℓM)
    hc hF hm hX hX'
  exact ⟨N, h1, fun ℓmax hmax t ht =>
    h2 ℓmax (fun a => by rw [lenHom_single]; exact hmax a) t ht⟩

/-- **Theorem FC1, item (3), for an irreducible Pisot incidence matrix**: under the
hypotheses of `fc1_equivalence_of_pisot`, if the first letters of two `σ^m`-fixed words have
no left strong-coincidence witness, the blocks of `(X, X')` between consecutive common
vertices form a strict system for `σ^m`, and `σ` has a strict system. -/
theorem fc1_strictSystem_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    (hnw : ¬ StrongCoincidenceWitness s (X 0) (X' 0)) :
    (∃ C : Finset (List α × List α), (↑C : Set (List α × List α)) = cutBlocks X X' ∧
      StrictSystem (power s m) C) ∧ ∃ C : Finset (List α × List α), StrictSystem s C := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  have hL := lengthData_of_left_eigen (lt_trans one_pos hβ) hℓ hℓM
  exact fc1_strictSystem hL hβ hm hX hX' (relStates_finite_of_contraction hL hc hm hX hX')
    (fun _ hx => reaches_vertex_of_propertyF hL hc hF (relStates_isState hx)) hnw

/-- **Theorem FC1, items (1) and (2), on the standing class** (primitive, at least two
letters, `χ_M` irreducible, every root other than the Perron root in the open unit disc,
property (F)). -/
theorem fc1_inclusion_gap_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, ℓ a ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X',
          t < lenHom ℓ z ∧ lenHom ℓ z ≤ t + β ^ (m * N) * ℓmax :=
  fc1_inclusion_gap_of_pisot hirr hℓ hℓM
    (lt_trans one_pos (Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM)) hpisot hF hm hX hX'

end Instance

/-- **Theorem FC1 on PIP3** (three letters): `σ` primitive, `χ_M` irreducible over `ℚ`,
Perron row `ℓ > 0` with `ℓ M = β ℓ`, every complex root of `χ_M` other than `β` in the open
unit disc, and property (F) for the tile lengths `ℓ`.  Then `σ` has a strict system iff some
pair of distinct `g`-periodic letters has no left strong-coincidence witness iff left strong
coincidence fails for some pair of distinct letters. -/
theorem fc1_pip3 {s : Fin 3 → List (Fin 3)} {β : ℝ} {ℓ : Fin 3 → ℝ}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_primitive_pisot hprim hirr hℓ hℓM hpisot hF

/-! ### Non-vacuity on a PIP3 specimen, and the strict control -/

section Controls

open Psc.Descendants (tribSubst)

/-- **Non-vacuity of (A) and (B) on PIP3.**  For Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0` every
spectral hypothesis of this module holds (`Psc.BPrime.trib_prim`, `trib_irreducible`,
`trib_isPisot`), so its Perron row `ℓ` has `LengthData`, `β > 1` and `ContractionData`: every
hypothesis of `Psc.GeometricF.fc1_equivalence_of_contraction` except `PropertyF`. -/
theorem trib_fc1_hypotheses : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ) (ν : (Fin 3 → ℤ) → ℝ) (ρ : ℝ),
    (∀ a, 0 < ℓ a) ∧ ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧
      Psc.BPrime.IsPisot β ∧
      (∀ z : ℂ, ((inc tribSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
        ‖z‖ < 1) ∧
      LengthData tribSubst (lenHom ℓ) β ∧ 1 < β ∧ ContractionData tribSubst (lenHom ℓ) ν ρ := by
  obtain ⟨β, hβ0, ℓ, hℓ, hℓM⟩ :=
    Psc.PerronExistence.exists_pos_left_eigen_inc tribSubst Psc.BPrime.trib_prim
  have hP := Psc.BPrime.trib_isPisot hℓ hℓM
  have hroots := pisot_roots_of_isPisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM hP
  obtain ⟨ν, ρ, hc⟩ :=
    exists_contractionData_of_pisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM hroots
  exact ⟨β, ℓ, ν, ρ, hℓ, hℓM, hP, hroots, lengthData_of_left_eigen hβ0 hℓ hℓM, hP.1, hc⟩

/-- **Theorem FC1 for Tribonacci, with property (F) as the only hypothesis left**: for every
positive left eigen-row `ℓ` of its incidence matrix. -/
theorem trib_fc1_of_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hF : PropertyF tribSubst (lenHom ℓ)) :
    ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c') :=
  fc1_equivalence_of_isPisot Psc.BPrime.trib_irreducible hℓ hℓM (Psc.BPrime.trib_isPisot hℓ hℓM)
    hF

/-- **The conclusion of `trib_fc1_of_propertyF` is true unconditionally**: on Tribonacci
every pair of distinct letters has a left strong-coincidence witness
(`Psc.StrictSystem.trib_least`), so all three statements of the equivalence are false
(`Psc.StrictSystem.trib_no_strictSystem`).  This is proved without Theorem FC1 and without
`PropertyF`; it shows that the instance does not assert anything false on this specimen. -/
theorem trib_fc1_statements :
    (¬ ∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ∧
      (¬ ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      ¬ ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c' := by
  have hall : ∀ c c' : Fin 3, c ≠ c' → StrongCoincidenceWitness tribSubst c c' :=
    Psc.StrictSystem.fin3_all_pairs
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.1)
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.2.1)
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.2.2)
  exact ⟨fun ⟨C, hC⟩ => Psc.StrictSystem.trib_no_strictSystem C hC,
    fun ⟨c, c', hne, _, _, hnw⟩ => hnw (hall c c' hne), fun h => h hall⟩

/-- **Negative control for (A).**  On the reducible strict control `10/102/211`
(`Psc.StrictSystem.carrierSubst`, primitive, `χ_M = (X − 1)(X² − 2X − 2)`) the hypotheses of
`exists_contractionData_of_separable` fail for every positive left eigen-row, as they must
(`Psc.GeometricF.carrier_not_contractionData`): `χ_M` is not both separable over `ℂ` and
Pisot in the root form.  In particular the standing hypotheses (irreducible, root form) fail
there. -/
theorem carrier_not_pisot_roots {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ¬ (((inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℂ)).charpoly.Separable ∧
      ∀ z : ℂ, ((inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 →
        z ≠ β → ‖z‖ < 1) := by
  rintro ⟨hsep, hp⟩
  have hβ := Psc.BPrimeCore.one_lt_perron _ Psc.StrictSystem.carrier_primitive hℓ hℓM
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_separable _ hsep
    (fun h => (hℓ 0).ne' (congrFun h 0)) hℓM hp
  exact carrier_not_contractionData (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ hc

end Controls

/-! ### Bridges for the local copies of `PscVerif.GeometricFInclusion` -/

omit [Fintype α] in
/-- `Psc.GeometricF.pvec` is `Psc.BPrimeCore.parikhCast` at `ℤ`. -/
theorem pvec_eq_parikhCast (w : List α) :
    pvec w = (Psc.BPrimeCore.parikhCast w : α → ℤ) := rfl

/-- `Psc.GeometricF.incZ` is `Psc.Degree2Sector.incZ` on the substitution of a child
system. -/
theorem incZ_eq_degree2Sector (S : Psc.Binomial.ChildSystem (Fin 3)) :
    incZ S.s = Psc.Degree2Sector.incZ S := rfl

end Psc.GeometricFPisot
