/-
# Linear-algebra steps of the Concentration attack

`docs/c4-concentration-attack-2026-11-06.md` §§2–3.

* `eigenrow_eq_zero` (**Galois lemma**, eigen-functional form): let `W` be a
  `3 × 3` matrix over a field `F` such that every nonzero `w` is a cyclic vector
  (`w, Ww, W²w` independent; for `W = Λ²M` this is irreducibility of
  `χ_{Λ²M}`).  If a left eigen-row `y` of `W`, over any extension `K`, vanishes
  on a nonzero `F`-rational vector, then `y = 0`.  Applied to the three
  eigen-rows of `Λ²M`, this is: one eigencoordinate of a rational `K₂` vanishes
  iff all do iff `K₂ = 0`.
* `exists_factor_through` (**Theorem A(iv)**, factorization step): if `P` is onto
  and intertwines `N` with `M`, `Q` intertwines `N` with `R`, `f(R) = 0`, and
  `f(N)` maps `ker P` onto itself, then `Q = L ∘ P` for a linear `L`.  The
  hypothesis on `ker P` is what Perron simplicity of `β` supplies when
  `f = χ_M`: then `χ_{N | ker P} = χ_N / χ_M` is coprime to `χ_M`.  That
  deduction is not formalized here.
* `injective_of_irreducible` (**Theorem A(iv)**, injectivity): an intertwiner
  `L ≠ 0` out of a module with no proper nonzero invariant subspace is injective.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace Psc.ConcentrationAlgebra

open Matrix Polynomial

/-! ### The eigen-functional (Galois) lemma -/

section Galois

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem eigenrow_eq_zero (W : Matrix (Fin 3) (Fin 3) F)
    (hcyc : ∀ w : Fin 3 → F, w ≠ 0 →
      LinearIndependent F ![w, W *ᵥ w, W *ᵥ (W *ᵥ w)])
    (y : Fin 3 → K) (μ : K) (hy : y ᵥ* W.map (algebraMap F K) = μ • y)
    (w : Fin 3 → F) (hw0 : w ≠ 0) (hw : y ⬝ᵥ (algebraMap F K ∘ w) = 0) : y = 0 := by
  set f := algebraMap F K
  let vs : Fin 3 → Fin 3 → F := ![w, W *ᵥ w, W *ᵥ (W *ᵥ w)]
  -- columns of `B` are the three vectors
  let B : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => vs j i
  have hB : IsUnit B := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hcyc w hw0 using 1
    funext j i
    rfl
  have hBK : IsUnit (B.map f) := by
    have hd : (B.map f).det = f B.det := (RingHom.map_det f B).symm
    have : IsUnit (B.map f).det := by
      rw [hd]; exact ((Matrix.isUnit_iff_isUnit_det B).mp hB).map f
    exact (Matrix.isUnit_iff_isUnit_det _).mpr this
  -- `y ⬝ (W v) = μ (y ⬝ v)` on mapped vectors
  have step : ∀ v : Fin 3 → F, y ⬝ᵥ (f ∘ (W *ᵥ v)) = μ * (y ⬝ᵥ (f ∘ v)) := by
    intro v
    have : f ∘ (W *ᵥ v) = W.map f *ᵥ (f ∘ v) := by
      ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Function.comp]
    rw [this, Matrix.dotProduct_mulVec, hy, smul_dotProduct, smul_eq_mul]
  have h0 : ∀ j, y ⬝ᵥ (f ∘ vs j) = 0 := by
    intro j
    fin_cases j
    · show y ⬝ᵥ (f ∘ w) = 0; exact hw
    · show y ⬝ᵥ (f ∘ (W *ᵥ w)) = 0; rw [step, hw, mul_zero]
    · show y ⬝ᵥ (f ∘ (W *ᵥ (W *ᵥ w))) = 0; rw [step, step, hw, mul_zero, mul_zero]
  have hyB : y ᵥ* B.map f = 0 := by
    ext j
    have := h0 j
    simpa [Matrix.vecMul, dotProduct, B, Function.comp] using this
  obtain ⟨u, hu⟩ := hBK
  have := congrArg (· ᵥ* (↑u⁻¹ : Matrix (Fin 3) (Fin 3) K)) hyB
  simpa [Matrix.vecMul_vecMul, ← hu] using this

end Galois

/-! ### Factorization through the Parikh map -/

section Factor

variable {F V X Y : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup X]
  [Module F X] [AddCommGroup Y] [Module F Y]

theorem comp_pow_of_intertwine (Q : V →ₗ[F] Y) (N : V →ₗ[F] V) (R : Y →ₗ[F] Y)
    (hQ : ∀ v, Q (N v) = R (Q v)) (n : ℕ) (v : V) : Q ((N ^ n) v) = (R ^ n) (Q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hQ, ih]

theorem comp_aeval_of_intertwine (Q : V →ₗ[F] Y) (N : V →ₗ[F] V) (R : Y →ₗ[F] Y)
    (hQ : ∀ v, Q (N v) = R (Q v)) (f : F[X]) (v : V) :
    Q (aeval N f v) = aeval R f (Q v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      comp_pow_of_intertwine Q N R hQ]

theorem exists_factor_through (P : V →ₗ[F] X) (Q : V →ₗ[F] Y) (N : V →ₗ[F] V)
    (R : Y →ₗ[F] Y) (hP : Function.Surjective P) (hQ : Q ∘ₗ N = R ∘ₗ Q)
    (f : F[X]) (hf : aeval R f = 0)
    (hsplit : ∀ x ∈ LinearMap.ker P, ∃ z ∈ LinearMap.ker P, x = aeval N f z) :
    ∃ L : X →ₗ[F] Y, Q = L ∘ₗ P := by
  have hker : LinearMap.ker P ≤ LinearMap.ker Q := by
    intro x hx
    obtain ⟨z, -, rfl⟩ := hsplit x hx
    have hQ' : ∀ v, Q (N v) = R (Q v) := fun v => by
      simpa using congrArg (fun T : V →ₗ[F] Y => T v) hQ
    simp [LinearMap.mem_ker, comp_aeval_of_intertwine Q N R hQ' f z, hf]
  refine ⟨(LinearMap.ker P).liftQ Q hker ∘ₗ
    (P.quotKerEquivOfSurjective hP).symm.toLinearMap, ?_⟩
  ext v
  have : (P.quotKerEquivOfSurjective hP).symm (P v) = Submodule.Quotient.mk v :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  simp [this]

/-- An intertwiner `L ∘ M = R ∘ L`, nonzero, out of a module with no proper
nonzero `M`-invariant subspace, is injective. -/
theorem injective_of_irreducible (L : X →ₗ[F] Y) (M : X →ₗ[F] X) (R : Y →ₗ[F] Y)
    (hL : L ∘ₗ M = R ∘ₗ L) (hL0 : L ≠ 0)
    (hirr : ∀ p : Submodule F X, (∀ x ∈ p, M x ∈ p) → p = ⊥ ∨ p = ⊤) :
    Function.Injective L := by
  rw [← LinearMap.ker_eq_bot]
  rcases hirr (LinearMap.ker L) (fun x hx => by
    have := congrArg (fun T : X →ₗ[F] Y => T x) hL
    simp only [LinearMap.comp_apply] at this
    simp [LinearMap.mem_ker, this, (LinearMap.mem_ker).mp hx]) with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.mp h) hL0

end Factor

end Psc.ConcentrationAlgebra
