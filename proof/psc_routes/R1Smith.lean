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
  simp [eq_comm]


/-- **Concrete matrix certificate form:** integer matrices U, V,
Uinv, Vinv and the exact integer identities

  Uinv * U = I,    V * Vinv = I,    U * A * V = diag(d)

suffice to decide whether Ax=b has an integral solution, by checking
only dᵢ ∣ (U*b)ᵢ. All conditions are statements about finite **exact
integer matrices**, so a future certificate producer may emit them for
independent kernel replay. This theorem does not compute such matrices,
or identify A with the actual ancestry-cycle operator. -/
theorem matrix_smith_certificate_complete
    {d : ℕ}
    (A U Uinv V Vinv : Matrix (Fin d) (Fin d) ℤ)
    (diagonal rhs : Fin d → ℤ)
    (hU : Uinv * U = 1)
    (hV : V * Vinv = 1)
    (hdiag : U * A * V = Matrix.diagonal diagonal) :
    (∃ x : Fin d → ℤ, A.mulVec x = rhs) ↔
      (∀ i : Fin d, diagonal i ∣ (U.mulVec rhs) i) := by
  have hUinv : ∀ z : Fin d → ℤ,
      Uinv.mulVec (U.mulVec z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hVinv : ∀ z : Fin d → ℤ,
      V.mulVec (Vinv.mulVec z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  have hd : ∀ (y : Fin d → ℤ) (i : Fin d),
      U.mulVec (A.mulVec (V.mulVec y)) i =
        diagonal i * y i := by
    intro y i
    calc
      U.mulVec (A.mulVec (V.mulVec y)) i =
        (U * A * V).mulVec y i := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (Matrix.diagonal diagonal).mulVec y i := by rw [hdiag]
      _ = diagonal i * y i := Matrix.mulVec_diagonal diagonal y i
  exact diagonal_certificate_complete
    (fun z => A.mulVec z)
    (fun z => U.mulVec z)
    (fun z => V.mulVec z)
    (fun z => Uinv.mulVec z)
    (fun z => Vinv.mulVec z)
    diagonal rhs hUinv hVinv hd


/-- Finite-word integral ancestry applies an additive matrix action
and then the correction *at that step*. This is the canonical
recurrence for the integer Parikh defect; individual digits still
need to be bound to actual proper substituted-source prefixes. -/
def ancestryOrbit {V : Type*} [AddCommGroup V]
    (M : V →+ V) (correction : ℕ → V) (start : V) : ℕ → V
  | 0 => start
  | n + 1 => M (ancestryOrbit M correction start n) + correction n

/-- The homogeneous part and the accumulated forced digits use the
same recurrence, with and without the correction. -/
def ancestryHomogeneous {V : Type*} [AddCommGroup V]
    (M : V →+ V) (start : V) : ℕ → V
  | 0 => start
  | n + 1 => M (ancestryHomogeneous M start n)

def ancestryForcedDigits {V : Type*} [AddCommGroup V]
    (M : V →+ V) (correction : ℕ → V) : ℕ → V
  | 0 => 0
  | n + 1 => M (ancestryForcedDigits M correction n) + correction n

/-- Exact affine unrolling over **any** additive group with a
homomorphism M; no real/Pisot assumption or finite-word cap is used. -/
theorem ancestryOrbit_unroll {V : Type*} [AddCommGroup V]
    (M : V →+ V) (correction : ℕ → V) (start : V) (n : ℕ) :
    ancestryOrbit M correction start n =
      ancestryHomogeneous M start n +
      ancestryForcedDigits M correction n := by
  induction n with
  | zero => simp [ancestryOrbit, ancestryHomogeneous, ancestryForcedDigits]
  | succ n ih =>
      simp only [ancestryOrbit, ancestryHomogeneous, ancestryForcedDigits,
        ih, map_add]
      abel

/-- An ancestry cycle closes **if and only if** the integer
matrix-cycle equation holds. This is exact, including signed forcing.
It is the missing algebraic interface between literal digit provenance
and a complete integral diagonal/Smith certificate. -/
theorem ancestryOrbit_closed_iff_cycle_equation
    {V : Type*} [AddCommGroup V]
    (M : V →+ V) (correction : ℕ → V) (start : V) (n : ℕ) :
    ancestryOrbit M correction start n = start ↔
      start - ancestryHomogeneous M start n =
        ancestryForcedDigits M correction n := by
  rw [ancestryOrbit_unroll]
  constructor
  · intro h
    calc
      start - ancestryHomogeneous M start n =
        (ancestryHomogeneous M start n +
         ancestryForcedDigits M correction n) -
        ancestryHomogeneous M start n := by rw [h]
      _ = ancestryForcedDigits M correction n := by abel
  · intro h
    calc
      ancestryHomogeneous M start n +
          ancestryForcedDigits M correction n =
        ancestryHomogeneous M start n +
          (start - ancestryHomogeneous M start n) := by rw [h]
      _ = start := by abel


/-- A **conditional but complete** integral-cycle criterion.

The two independent, machine-checkable boundaries are explicit:
  1. A.mulVec agrees for *every integral address* with
     x ↦ x − (homogeneous n-step ancestry of x).
  2. U,V and their integer inverses satisfy the exact diagonal
     matrix certificate.

The iff then decides the existence of a *periodic integral defect*
for one exact correction word. It does not assert that the word came
from a real pair of substitution tracks, or that eliminating such
defects eliminates every strictly nonsynchronizing occurrence cycle. -/
theorem ancestry_smith_cycle_criterion
    {d : ℕ} (M : (Fin d → ℤ) →+ (Fin d → ℤ))
    (correction : ℕ → Fin d → ℤ) (n : ℕ)
    (A U Uinv V Vinv : Matrix (Fin d) (Fin d) ℤ)
    (diagonal : Fin d → ℤ)
    (hA : ∀ x : Fin d → ℤ,
      A.mulVec x = x - ancestryHomogeneous M x n)
    (hU : Uinv * U = 1)
    (hV : V * Vinv = 1)
    (hdiag : U * A * V = Matrix.diagonal diagonal) :
    (∃ x : Fin d → ℤ, ancestryOrbit M correction x n = x) ↔
      (∀ i : Fin d, diagonal i ∣
        (U.mulVec (ancestryForcedDigits M correction n)) i) := by
  calc
    (∃ x : Fin d → ℤ, ancestryOrbit M correction x n = x) ↔
        (∃ x : Fin d → ℤ,
          A.mulVec x = ancestryForcedDigits M correction n) := by
          constructor
          · rintro ⟨x, hx⟩
            refine ⟨x, ?_⟩
            rw [hA x]
            exact (ancestryOrbit_closed_iff_cycle_equation M correction x n).mp hx
          · rintro ⟨x, hx⟩
            refine ⟨x, ?_⟩
            apply (ancestryOrbit_closed_iff_cycle_equation M correction x n).mpr
            rw [hA x] at hx
            exact hx
    _ ↔ (∀ i : Fin d, diagonal i ∣
        (U.mulVec (ancestryForcedDigits M correction n)) i) :=
      matrix_smith_certificate_complete A U Uinv V Vinv diagonal
        (ancestryForcedDigits M correction n) hU hV hdiag


/-! ### Fully specified integral Smith certificate for the Tribonacci
    period-one ancestry operator `I-M`.

The following six literal matrices can be checked by ring arithmetic
over Z. Their existence supplies a **concrete** diagonal certificate
without trusting a numerical eigensolver or prime-field oracle. -/

def tribonacciCycleA : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -1, -1; -1, 1, 0; 0, -1, 1]

def tribonacciSmithU : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -1, 0; -1, 0, 0; -1, 0, 1]

def tribonacciSmithUinv : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -1, 0; -1, 0, 0; 0, -1, 1]

def tribonacciSmithV : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, -1; 0, 1, -1; 0, 0, 1]

def tribonacciSmithVinv : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; 0, 1, 1; 0, 0, 1]

def tribonacciSmithDiagonal : Fin 3 → ℤ := ![1, 1, 2]

/-- Integer left inverse; no rational denominators. -/
theorem tribonacci_smith_U_left_inverse :
    tribonacciSmithUinv * tribonacciSmithU = 1 := by
  first
  | decide
  | (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tribonacciSmithUinv, tribonacciSmithU, Matrix.mul_apply])

/-- Integer right inverse; no rational denominators. -/
theorem tribonacci_smith_V_right_inverse :
    tribonacciSmithV * tribonacciSmithVinv = 1 := by
  first
  | decide
  | (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tribonacciSmithV, tribonacciSmithVinv, Matrix.mul_apply])

/-- Exact Smith diagonal U*(I−M)*V = diag(1,1,2). -/
theorem tribonacci_smith_matrix_certificate :
    tribonacciSmithU * tribonacciCycleA * tribonacciSmithV =
      Matrix.diagonal tribonacciSmithDiagonal := by
  first
  | decide
  | (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tribonacciSmithU, tribonacciCycleA,
        tribonacciSmithV, tribonacciSmithDiagonal, Matrix.mul_apply,
        Matrix.diagonal])

/-- A fully concrete, kernel-checkable integer divisibility criterion
for *every* possible right-hand-side of the Tribonacci period-one
matrix equation. **Still not** a theorem on occurrence-compatible
ancestry: this is the algebraic part only. -/
theorem tribonacci_smith_membership (rhs : Fin 3 → ℤ) :
    (∃ x : Fin 3 → ℤ, tribonacciCycleA.mulVec x = rhs) ↔
      (∀ i : Fin 3, tribonacciSmithDiagonal i ∣
         (tribonacciSmithU.mulVec rhs) i) := by
  exact matrix_smith_certificate_complete
    tribonacciCycleA tribonacciSmithU tribonacciSmithUinv
    tribonacciSmithV tribonacciSmithVinv
    tribonacciSmithDiagonal rhs
    tribonacci_smith_U_left_inverse
    tribonacci_smith_V_right_inverse
    tribonacci_smith_matrix_certificate


/-- Literal incidence matrix of 0↦01, 1↦02, 2↦0,
the same columns independently checked against words by R1Modular. -/
def tribonacciIncidenceMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1; 1, 0, 0; 0, 1, 0]

/-- The concrete Smith operator is exactly I−M, not an unrelated
3×3 matrix chosen to give a convenient diagonal parity conclusion. -/
theorem tribonacci_cycle_A_is_identity_minus_incidence :
    tribonacciCycleA = 1 - tribonacciIncidenceMatrix := by
  first
  | decide
  | (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tribonacciCycleA, tribonacciIncidenceMatrix])

end PscRoutes.R1Smith

#print axioms PscRoutes.R1Smith.scalar_solvability_iff_dvd
#print axioms PscRoutes.R1Smith.diagonal_solvability_iff_dvd
#print axioms PscRoutes.R1Smith.diagonal_certificate_complete
#print axioms PscRoutes.R1Smith.four_x_eq_two_smith_refuses
#print axioms PscRoutes.R1Smith.zero_diagonal_requires_zero
#print axioms PscRoutes.R1Smith.matrix_smith_certificate_complete
#print axioms PscRoutes.R1Smith.ancestryOrbit_unroll
#print axioms PscRoutes.R1Smith.ancestryOrbit_closed_iff_cycle_equation
#print axioms PscRoutes.R1Smith.ancestry_smith_cycle_criterion
#print axioms PscRoutes.R1Smith.tribonacci_smith_U_left_inverse
#print axioms PscRoutes.R1Smith.tribonacci_smith_V_right_inverse
#print axioms PscRoutes.R1Smith.tribonacci_smith_matrix_certificate
#print axioms PscRoutes.R1Smith.tribonacci_smith_membership
#print axioms PscRoutes.R1Smith.tribonacci_cycle_A_is_identity_minus_incidence

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Smith.scalar_solvability_iff_dvd,
    `PscRoutes.R1Smith.diagonal_solvability_iff_dvd,
    `PscRoutes.R1Smith.diagonal_certificate_complete,
    `PscRoutes.R1Smith.four_x_eq_two_smith_refuses,
    `PscRoutes.R1Smith.zero_diagonal_requires_zero,
    `PscRoutes.R1Smith.matrix_smith_certificate_complete,
    `PscRoutes.R1Smith.ancestryOrbit_unroll,
    `PscRoutes.R1Smith.ancestryOrbit_closed_iff_cycle_equation,
    `PscRoutes.R1Smith.ancestry_smith_cycle_criterion,
    `PscRoutes.R1Smith.tribonacci_smith_U_left_inverse,
    `PscRoutes.R1Smith.tribonacci_smith_V_right_inverse,
    `PscRoutes.R1Smith.tribonacci_smith_matrix_certificate,
    `PscRoutes.R1Smith.tribonacci_smith_membership,
    `PscRoutes.R1Smith.tribonacci_cycle_A_is_identity_minus_incidence] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1SMITH_AXIOMS_OK\t{name}"
