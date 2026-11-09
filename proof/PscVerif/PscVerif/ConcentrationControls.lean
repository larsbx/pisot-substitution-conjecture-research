/-
# Negative controls for Open Problem Concentration

`docs/c4-concentration-attack-2026-11-06.md` §5, checked by kernel reduction
(`decide +kernel`; no `native_decide`).

* `t13_irreducible`, `t13_equiv2`: the pair `(1222200110120, 2201121220001)` is
  irreducible (`Psc.Binomial.IrreduciblePair`) and 2-binomially equivalent
  (`K₁ = K₂ = 0`);
* `t13_k3_ne_zero`, `t13_det_sector`: its `K₃` (`k3`, built from the scattered
  count `Psc.Incidence.n3`) is nonzero and satisfies
  `M0^{⊗3} K₃ = det(M0)·K₃` for `M0 = [[5,21,1],[6,26,1],[6,24,1]]`,
  `det M0 = -2`, so it lies in the determinant sector of `M0`;
* `m0_positive`, `m0_det`, `m0_charpoly_values`: `M0` is entrywise positive,
  and `χ(x) = x³ - 32x² + 5x + 2` has no root among `±1, ±2` and changes sign on
  `(-1,0)`, `(0,1)`, `(1,32)`.  By the rational root theorem and the
  intermediate value theorem these give an irreducible Pisot cubic; those two
  standard inferences are not formalized here;
* `factors_equiv2`, `factors_occur`: `0112201` and `1200112` are distinct,
  2-binomially equivalent, and both occur in `σ⁶(0)` for `σ = 011/2/120`.
-/
import PscVerif.Incidence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

namespace Psc.ConcentrationControls

open Psc.Binomial Psc.Incidence

abbrev L := Fin 3

def u13 : List L := ([1,2,2,2,2,0,0,1,1,0,1,2,0] : List L)
def v13 : List L := ([2,2,0,1,1,2,1,2,2,0,0,0,1] : List L)

theorem t13_irreducible : IrreduciblePair u13 v13 := by decide +kernel
theorem t13_equiv2 : Equiv2 u13 v13 := by decide +kernel

/-- The degree-three defect of `(u13, v13)`, from the scattered count
`Psc.Incidence.n3`. -/
def k3 (a b c : L) : ℤ := (n3 u13 a b c : ℤ) - n3 v13 a b c

def m0 : L → L → ℤ := ![![5, 21, 1], ![6, 26, 1], ![6, 24, 1]]

def sum3 (f : L → ℤ) : ℤ := f 0 + f 1 + f 2

def det3 (m : L → L → ℤ) : ℤ :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0)
    + m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

theorem m0_det : det3 m0 = -2 := by decide +kernel
theorem m0_positive : ∀ i j, 0 < m0 i j := by decide +kernel

theorem t13_k3_ne_zero : ∃ a b c, k3 a b c ≠ 0 := ⟨0, 2, 1, by decide +kernel⟩

/-- `M0^{⊗3} K₃ = det(M0)·K₃`. -/
theorem t13_det_sector : ∀ a b c,
    sum3 (fun x => sum3 fun y => sum3 fun z => m0 a x * m0 b y * m0 c z * k3 x y z)
      = det3 m0 * k3 a b c := by decide +kernel

def chi (x : ℤ) : ℤ := x ^ 3 - 32 * x ^ 2 + 5 * x + 2

theorem chi_is_charpoly (x : ℤ) :
    chi x = det3 (fun i j => (if i = j then x else 0) - m0 i j) := by
  simp only [chi, det3, m0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  norm_num
  ring

theorem m0_charpoly_values :
    chi 1 ≠ 0 ∧ chi (-1) ≠ 0 ∧ chi 2 ≠ 0 ∧ chi (-2) ≠ 0 ∧
    chi (-1) < 0 ∧ 0 < chi 0 ∧ chi 1 < 0 ∧ 0 < chi 32 := by decide +kernel

/-! ### `011/2/120` has distinct 2-binomially equivalent factors -/

def sigma : L → List L := ![([0,1,1] : List L), ([2] : List L), ([1,2,0] : List L)]

def x7 : List L := ([0,1,1,2,2,0,1] : List L)
def y7 : List L := ([1,2,0,0,1,1,2] : List L)

theorem factors_equiv2 : Equiv2 x7 y7 ∧ x7 ≠ y7 := by decide +kernel

theorem factors_occur :
    x7 <:+: (subst sigma)^[6] ([0] : List L) ∧ y7 <:+: (subst sigma)^[6] ([0] : List L) := by
  decide +kernel

end Psc.ConcentrationControls
