/- The finite-word obstruction for a substitution power with even image counts. -/
module

import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

public section

namespace Psc.PeriodicPartnerLiteralDefect

private abbrev WordAlgebra (α : Type*) := MonoidAlgebra (ZMod 2) (FreeMonoid α)

private noncomputable abbrev basis {α : Type*} : FreeMonoid α →* WordAlgebra α :=
  MonoidAlgebra.of (ZMod 2) (FreeMonoid α)

/-- Multiply the factors `1 + X_a` in word order. -/
private noncomputable def expansion {α : Type*} : FreeMonoid α →* WordAlgebra α :=
  FreeMonoid.lift fun a => 1 + basis (FreeMonoid.of a)

private theorem expansion_of {α : Type*} (a : α) :
    expansion (FreeMonoid.of a) = 1 + basis (FreeMonoid.of a) := rfl

private theorem expansion_constant {α : Type*} (w : FreeMonoid α) :
    (expansion w).coeff 1 = 1 := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    have hz : (basis (FreeMonoid.of a) * expansion w).coeff 1 = 0 :=
      MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 _ fun x hx => by
        have h := congrArg FreeMonoid.length hx
        simp at h
    rw [map_mul, expansion_of, add_mul, one_mul, MonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih, hz, add_zero]

private theorem letter_mul_coeff {α : Type*} [DecidableEq α]
    (a b : α) (x : WordAlgebra α) :
    (basis (FreeMonoid.of a) * x).coeff (FreeMonoid.of b) =
      if a = b then x.coeff 1 else 0 := by
  change (MonoidAlgebra.single (FreeMonoid.of a) 1 * x).coeff _ = _
  by_cases h : a = b
  · subst b
    rw [ite_eq_left rfl]
    simpa using (MonoidAlgebra.coeff_single_mul_eq_mul_coeff (x := x) (r := 1)
      (m := FreeMonoid.of a) (m₁ := FreeMonoid.of a) 1 (by simp))
  · rw [ite_eq_right h]
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro d hd
    have hw := congrArg FreeMonoid.toList hd
    simp only [FreeMonoid.toList_of_mul, FreeMonoid.toList_of, List.cons.injEq] at hw
    exact h hw.1

private theorem expansion_linear {α : Type*} [DecidableEq α] (w : FreeMonoid α) (b : α) :
    (expansion w).coeff (FreeMonoid.of b) = (w.toList.count b : ZMod 2) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [MonoidAlgebra.one_def]
  | of_mul a w ih =>
    rw [map_mul, expansion_of, add_mul, one_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      letter_mul_coeff, expansion_constant, ih, FreeMonoid.toList_of_mul, List.count_cons]
    by_cases h : a = b <;> simp [h, add_comm]

private noncomputable def evaluate {α : Type*} (f : α → WordAlgebra α) :
    WordAlgebra α →ₐ[ZMod 2] WordAlgebra α :=
  MonoidAlgebra.lift (ZMod 2) (WordAlgebra α) (FreeMonoid α) (FreeMonoid.lift f)

private theorem evaluate_basis {α : Type*} (f : α → WordAlgebra α) (w : FreeMonoid α) :
    evaluate f (basis w) = FreeMonoid.lift f w := MonoidAlgebra.lift_of ..

private theorem expansion_injective {α : Type*} :
    Function.Injective (expansion : FreeMonoid α →* WordAlgebra α) := by
  let cancelShift := evaluate fun a : α => basis (FreeMonoid.of a) - 1
  have h (w : FreeMonoid α) : cancelShift (expansion w) = basis w := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp only [map_one]
    | of_mul a w ih =>
      rw [map_mul, map_mul, map_mul, ih, expansion_of, map_add, map_one]
      dsimp only [cancelShift]
      rw [evaluate_basis, FreeMonoid.lift_eval_of]
      have he : 1 + (basis (FreeMonoid.of a) - 1) = basis (FreeMonoid.of a) := by abel
      rw [he]
  intro u v huv
  apply MonoidAlgebra.of_injective (R := ZMod 2)
  exact (h u).symm.trans ((congrArg cancelShift huv).trans (h v))

private def VanishesBelow {α : Type*} (degree : ℕ) (f : WordAlgebra α) : Prop :=
  ∀ w, w.length < degree → f.coeff w = 0

private theorem VanishesBelow.mono {α : Type*} {d e : ℕ} {f : WordAlgebra α}
    (h : VanishesBelow e f) (hle : d ≤ e) : VanishesBelow d f :=
  fun w hw => h w (hw.trans_le hle)

private theorem VanishesBelow.add {α : Type*} {d : ℕ} {f g : WordAlgebra α}
    (hf : VanishesBelow d f) (hg : VanishesBelow d g) : VanishesBelow d (f + g) := by
  intro w hw
  simp [MonoidAlgebra.coeff_add, hf w hw, hg w hw]

private theorem VanishesBelow.sub {α : Type*} {d : ℕ} {f g : WordAlgebra α}
    (hf : VanishesBelow d f) (hg : VanishesBelow d g) : VanishesBelow d (f - g) := by
  intro w hw
  simp [MonoidAlgebra.coeff_sub, hf w hw, hg w hw]

private theorem VanishesBelow.mul {α : Type*} {d e : ℕ} {f g : WordAlgebra α}
    (hf : VanishesBelow d f) (hg : VanishesBelow e g) : VanishesBelow (d + e) (f * g) := by
  classical
  intro w hw
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  have hlu : d ≤ u.length := Nat.le_of_not_lt fun h => Finsupp.mem_support_iff.mp hu (hf u h)
  have hlv : e ≤ v.length := Nat.le_of_not_lt fun h => Finsupp.mem_support_iff.mp hv (hg v h)
  have huv : u * v ≠ w := by
    intro he
    have hlen := congrArg FreeMonoid.length he
    rw [FreeMonoid.length_mul] at hlen
    omega
  simp [huv]

private theorem expansion_sub_one {α : Type*} (w : FreeMonoid α) :
    VanishesBelow 1 (expansion w - 1) := by
  intro v hv
  have hv₁ : v = 1 := FreeMonoid.length_eq_zero.mp (by omega)
  subst v
  simp [MonoidAlgebra.coeff_sub, expansion_constant]

private theorem expansion_even_image {α : Type*} [DecidableEq α] (w : FreeMonoid α)
    (h : ∀ b, Even (w.toList.count b)) : VanishesBelow 2 (expansion w - 1) := by
  intro v hv
  by_cases hzero : v.length = 0
  · exact expansion_sub_one w v (by omega)
  · obtain ⟨b, rfl⟩ := FreeMonoid.length_eq_one.mp (by omega : v.length = 1)
    simp [MonoidAlgebra.coeff_sub, expansion_linear, MonoidAlgebra.one_def, (h b).natCast_zmod_two]

private theorem evaluate_length {α : Type*} {f : α → WordAlgebra α}
    (h : ∀ a, VanishesBelow 2 (f a)) (w : FreeMonoid α) :
    VanishesBelow (2 * w.length) (evaluate f (basis w)) := by
  rw [evaluate_basis]
  induction w using FreeMonoid.inductionOn' with
  | one => simp [VanishesBelow]
  | of_mul a w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, FreeMonoid.length_mul, FreeMonoid.length_of,
      Nat.mul_add, Nat.mul_one]
    exact (h a).mul ih

private theorem evaluate_raises_degree {α : Type*} {f : α → WordAlgebra α}
    (h : ∀ a, VanishesBelow 2 (f a)) {d : ℕ} {x : WordAlgebra α} (hx : VanishesBelow d x) :
    VanishesBelow (2 * d) (evaluate f x) := by
  classical
  intro v hv
  rw [MonoidAlgebra.lift_unique (evaluate f) x, Finsupp.sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hlen : d ≤ w.length := Nat.le_of_not_lt fun hn => Finsupp.mem_support_iff.mp hw (hx w hn)
  have hvan := (evaluate_length h w).mono (Nat.mul_le_mul_left 2 hlen)
  change x.coeff w • (evaluate f (basis w)).coeff v = 0
  rw [hvan v hv, smul_zero]

private theorem padding_difference {α : Type*} (l r : FreeMonoid α) {d : ℕ} {x : WordAlgebra α}
    (hx : VanishesBelow d x) :
    VanishesBelow (d + 1) (expansion l * x * expansion r - x) := by
  have hzero : VanishesBelow 0 (expansion r) := by simp [VanishesBelow]
  have h₁ := ((expansion_sub_one l).mul hx).mul hzero
  have h₂ := hx.mul (expansion_sub_one r)
  have he : expansion l * x * expansion r - x =
      (expansion l - 1) * x * expansion r + x * (expansion r - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel
  rw [he]
  exact (by simpa only [Nat.add_zero, Nat.add_comm 1 d] using h₁ : VanishesBelow (d + 1) _).add h₂

private theorem evaluate_expansion {α : Type*} (s : FreeMonoid α →* FreeMonoid α)
    (w : FreeMonoid α) :
    evaluate (fun a => expansion (s (FreeMonoid.of a)) - 1) (expansion w) = expansion (s w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih, expansion_of, map_add, map_one, evaluate_basis,
      FreeMonoid.lift_eval_of]
    abel_nf

private theorem freeMonoid_eq_of_common_padding {α : Type*} [DecidableEq α]
    (s : FreeMonoid α →* FreeMonoid α) (h : ∀ a b, Even ((s (FreeMonoid.of a)).toList.count b))
    {u v l r : FreeMonoid α} (hu : s u = l * u * r) (hv : s v = l * v * r) : u = v := by
  let f (a : α) := expansion (s (FreeMonoid.of a)) - 1
  let x := expansion u - expansion v
  have he : evaluate f x = expansion l * x * expansion r := by
    change evaluate f (expansion u - expansion v) = _
    rw [map_sub, evaluate_expansion, evaluate_expansion, hu, hv]
    simp only [x, map_mul, mul_sub, sub_mul]
  have hbase : VanishesBelow 1 x := by
    intro w hw
    have heq : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
    subst w
    simp [x, MonoidAlgebra.coeff_sub, expansion_constant]
  have hdegrees (k : ℕ) : VanishesBelow (k + 1) x := by
    induction k with
    | zero => exact hbase
    | succ k ih =>
      have hhigh := (evaluate_raises_degree
        (f := f) (fun a => expansion_even_image _ (h a)) ih).mono
        (show k + 1 + 1 ≤ 2 * (k + 1) by omega)
      have hpad := padding_difference l r ih
      rw [← he] at hpad
      simpa only [sub_sub_cancel] using hhigh.sub hpad
  apply expansion_injective
  apply sub_eq_zero.mp
  apply MonoidAlgebra.ext
  exact Finsupp.ext fun w => hdegrees w.length w (Nat.lt_succ_self w.length)

private theorem lift_ofList_flatMap {α : Type*} (s : α → List α) (w : List α) :
    FreeMonoid.lift (fun a => FreeMonoid.ofList (s a)) (FreeMonoid.ofList w) =
      FreeMonoid.ofList (w.flatMap s) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [List.flatMap_cons, FreeMonoid.ofList_cons, FreeMonoid.ofList_append, ih]

/-- A power with even counts in every image cannot reproduce distinct
finite words between common prefix and suffix words. -/
theorem eq_of_common_padding {α : Type*} [DecidableEq α] (s : α → List α)
    (h : ∀ a b, Even ((s a).count b)) {u v l r : List α}
    (hu : u.flatMap s = l ++ u ++ r) (hv : v.flatMap s = l ++ v ++ r) : u = v := by
  apply FreeMonoid.ofList.injective
  refine freeMonoid_eq_of_common_padding (FreeMonoid.lift fun a => FreeMonoid.ofList (s a))
    (by simpa only [FreeMonoid.lift_eval_of, FreeMonoid.toList_ofList] using h)
    (l := FreeMonoid.ofList l) (r := FreeMonoid.ofList r) ?_ ?_
  · simp only [lift_ofList_flatMap, hu, FreeMonoid.ofList_append, mul_assoc]
  · simp only [lift_ofList_flatMap, hv, FreeMonoid.ofList_append, mul_assoc]

/-- Period doubling has a common-prefix difference, and its second power
fails the even-count hypothesis. -/
theorem period_doubling_padding_control :
    let δ : Bool → List Bool := fun a => [false, !a]
    let s : Bool → List Bool := fun a => (δ a).flatMap δ
    let l := [false, true, false]
    s false = l ++ [false] ∧ s true = l ++ [true] ∧ ¬ Even ((s false).count false) := by
  decide

end Psc.PeriodicPartnerLiteralDefect
