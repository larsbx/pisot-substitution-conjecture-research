import Mathlib
import Lean.Util.CollectAxioms

/-!
# R1F — complete *conditional* integer divisibility criterion

This module formalizes the precise gap left by finite-field-only cycle
refutations: a verified integer diagonalization with inverse integer
coordinate changes gives an if-and-only-if integrality certificate.

No Smith-form algorithm, incidence matrix diagonalization, occurrence
enumerator or PSC-level completeness theorem is claimed here.
-/

namespace PscRoutes.R1Smith

/-- Scalar integer membership is *exactly* divisibility, including
the singular coefficient zero. Mod-prime solvability is not enough. -/
theorem scalar_solvability_iff_dvd (a b : ℤ) :
    (∃ x : ℤ, a * x = b) ↔ a ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩

/-- Independent coordinates of a purported integer Smith diagonal
are solvable exactly when all diagonal entries divide the transformed
right-hand side. Zero diagonals require a zero right-hand coordinate. -/
theorem diagonal_solvability_iff_dvd {d : ℕ}
    (diagonal rhs : Fin d → ℤ) :
    (∃ x : Fin d → ℤ,
       ∀ i : Fin d, diagonal i * x i = rhs i) ↔
    (∀ i : Fin d, diagonal i ∣ rhs i) := by
  constructor
  · rintro ⟨x, hx⟩ i
    exact ⟨x i, (hx i).symm⟩
  · intro h
    classical
    refine ⟨fun i => Classical.choose (h i), ?_⟩
    intro i
    exact (Classical.choose_spec (h i)).symm

/-- Soundness AND completeness of a *verified* integer diagonal
certificate. Uinv and Vinv are explicit integer inverse operators:
they need not be linear at this abstract interface, but their laws and
the diagonal identity are mandatory. For a real Smith certificate
these laws must be derived from exact integer matrix products.

An accepted proof of this theorem does NOT produce U,V, or an SNF. -/
theorem diagonal_certificate_complete
    {d : ℕ} (A U V Uinv Vinv : (Fin d → ℤ) → (Fin d → ℤ))
    (diagonal rhs : Fin d → ℤ)
    (hU : ∀ z, Uinv (U z) = z)
    (hV : ∀ z, V (Vinv z) = z)
    (hdiag : ∀ (y : Fin d → ℤ) (i : Fin d),
      U (A (V y)) i = diagonal i * y i) :
    (∃ x : Fin d → ℤ, A x = rhs) ↔
       (∀ i : Fin d, diagonal i ∣ U rhs i) := by
  constructor
  · rintro ⟨x, hx⟩
    intro i
    let y := Vinv x
    have hy : V y = x := hV x
    have hresult : U (A (V y)) = U rhs := by rw [hy, hx]
    refine ⟨y i, ?_⟩
    have hi := congrFun hresult i
    rw [hdiag y i] at hi
    exact hi.symm
  · intro hd
    obtain ⟨y, hy⟩ :=
      (diagonal_solvability_iff_dvd diagonal (U rhs)).2 hd
    refine ⟨V y, ?_⟩
    apply (show Function.Injective U from by
      intro z z' h
      have h' := congrArg Uinv h
      simpa [hU] using h')
    funext i
    rw [hdiag y i]
    exact hy i

/-- An explicit complete scalar negative certificate cannot
mistake modular solvability for an integral witness. -/
theorem four_x_eq_two_smith_refuses :
    ¬ ∃ x : ℤ, 4 * x = 2 := by
  rw [scalar_solvability_iff_dvd]
  omega

/-- A zero Smith invariant forces a zero corresponding rhs entry. -/
theorem zero_diagonal_requires_zero (b : ℤ) :
    (∃ x : ℤ, (0 : ℤ) * x = b) ↔ b = 0 := by
  simp

end PscRoutes.R1Smith

#print axioms PscRoutes.R1Smith.scalar_solvability_iff_dvd
#print axioms PscRoutes.R1Smith.diagonal_solvability_iff_dvd
#print axioms PscRoutes.R1Smith.diagonal_certificate_complete
#print axioms PscRoutes.R1Smith.four_x_eq_two_smith_refuses
#print axioms PscRoutes.R1Smith.zero_diagonal_requires_zero

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Smith.scalar_solvability_iff_dvd,
    `PscRoutes.R1Smith.diagonal_solvability_iff_dvd,
    `PscRoutes.R1Smith.diagonal_certificate_complete,
    `PscRoutes.R1Smith.four_x_eq_two_smith_refuses,
    `PscRoutes.R1Smith.zero_diagonal_requires_zero] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1SMITH_AXIOMS_OK\t{name}"
