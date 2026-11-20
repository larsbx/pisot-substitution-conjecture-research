/- Finite-word obstructions from incidence modulo two. -/
module

import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Function.Iterate
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

private theorem evaluate_length {α : Type*} {f : α → WordAlgebra α} {k : ℕ}
    (h : ∀ a, VanishesBelow k (f a)) (w : FreeMonoid α) :
    VanishesBelow (k * w.length) (evaluate f (basis w)) := by
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

private theorem evaluate_sub_basis {α : Type*} {f g : α → WordAlgebra α}
    (hf : ∀ a, VanishesBelow 1 (f a)) (hg : ∀ a, VanishesBelow 1 (g a))
    (hfg : ∀ a, VanishesBelow 2 (f a - g a)) (w : FreeMonoid α) :
    VanishesBelow (w.length + 1) (evaluate f (basis w) - evaluate g (basis w)) := by
  simp only [evaluate_basis]
  induction w using FreeMonoid.inductionOn' with
  | one => simp [VanishesBelow]
  | of_mul a w ih =>
    rw [map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of,
      FreeMonoid.length_mul, FreeMonoid.length_of]
    have htail : VanishesBelow w.length (FreeMonoid.lift f w) := by
      simpa only [one_mul, evaluate_basis] using evaluate_length hf w
    have he : f a * FreeMonoid.lift f w - g a * FreeMonoid.lift g w =
        (f a - g a) * FreeMonoid.lift f w +
          g a * (FreeMonoid.lift f w - FreeMonoid.lift g w) := by
      simp only [sub_mul, mul_sub]
      abel
    rw [he]
    have hlen : 2 + w.length = 1 + w.length + 1 := by omega
    exact (hlen ▸ (hfg a).mul htail).add (by simpa only [Nat.add_assoc] using (hg a).mul ih)

private theorem evaluate_sub_raises_degree {α : Type*} {f g : α → WordAlgebra α}
    (hf : ∀ a, VanishesBelow 1 (f a)) (hg : ∀ a, VanishesBelow 1 (g a))
    (hfg : ∀ a, VanishesBelow 2 (f a - g a)) {d : ℕ} {x : WordAlgebra α}
    (hx : VanishesBelow d x) : VanishesBelow (d + 1) (evaluate f x - evaluate g x) := by
  classical
  intro v hv
  rw [MonoidAlgebra.lift_unique (evaluate f) x, MonoidAlgebra.lift_unique (evaluate g) x]
  simp only [Finsupp.sum, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_sum,
    Finsupp.sub_apply, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hlen : d ≤ w.length := Nat.le_of_not_lt fun hn => Finsupp.mem_support_iff.mp hw (hx w hn)
  have hvan := evaluate_sub_basis hf hg hfg w v (by omega)
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hvan
  rw [← smul_sub]
  change x.coeff w • ((evaluate f (basis w)).coeff v - (evaluate g (basis w)).coeff v) = 0
  rw [hvan, smul_zero]

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

private theorem evaluate_padded_difference {α : Type*} (s : FreeMonoid α →* FreeMonoid α)
    {u v l r : FreeMonoid α} (hu : s u = l * u * r) (hv : s v = l * v * r) :
    evaluate (fun a => expansion (s (FreeMonoid.of a)) - 1) (expansion u - expansion v) =
      expansion l * (expansion u - expansion v) * expansion r := by
  rw [map_sub, evaluate_expansion, evaluate_expansion, hu, hv]
  simp only [map_mul, mul_sub, sub_mul]

private theorem eq_of_padded_degree_increase {α : Type*} (s : FreeMonoid α →* FreeMonoid α)
    {u v l r : FreeMonoid α} (hu : s u = l * u * r) (hv : s v = l * v * r)
    (hraise : ∀ d, 1 ≤ d → VanishesBelow d (expansion u - expansion v) →
      VanishesBelow (d + 1) (evaluate (fun a => expansion (s (FreeMonoid.of a)) - 1)
        (expansion u - expansion v))) : u = v := by
  have hdegrees (k : ℕ) : VanishesBelow (k + 1) (expansion u - expansion v) := by
    induction k with
    | zero =>
      intro w hw
      have heq : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
      subst w
      simp [MonoidAlgebra.coeff_sub, expansion_constant]
    | succ k ih =>
      have hhigh := hraise (k + 1) (by omega) ih
      have hpad := padding_difference l r ih
      rw [← evaluate_padded_difference s hu hv] at hpad
      simpa only [sub_sub_cancel] using hhigh.sub hpad
  apply expansion_injective
  apply sub_eq_zero.mp
  apply MonoidAlgebra.ext
  exact Finsupp.ext fun w => hdegrees w.length w (Nat.lt_succ_self w.length)

private theorem freeMonoid_eq_of_common_padding {α : Type*} [DecidableEq α]
    (s : FreeMonoid α →* FreeMonoid α) (h : ∀ a b, Even ((s (FreeMonoid.of a)).toList.count b))
    {u v l r : FreeMonoid α} (hu : s u = l * u * r) (hv : s v = l * v * r) : u = v := by
  apply eq_of_padded_degree_increase s hu hv
  intro d hd hx
  exact (evaluate_raises_degree (fun a => expansion_even_image _ (h a)) hx).mono (by omega)

private theorem evaluate_marked_expansion {α : Type*} (mark : α → Bool) (t : WordAlgebra α)
    (w : FreeMonoid α) :
    evaluate (fun a => if mark a then t else 0) (expansion w) =
      (1 + t) ^ (w.toList.countP mark) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [map_mul, map_mul, ih, expansion_of, map_add, map_one, evaluate_basis,
      FreeMonoid.lift_eval_of, FreeMonoid.toList_of_mul]
    cases h : mark a <;> simp [h, pow_succ']

private theorem freeMonoid_eq_of_common_padding_of_marked_count {α : Type*} [DecidableEq α]
    (s : FreeMonoid α →* FreeMonoid α) (mark : α → Bool) (reference : α)
    (hcolumns : ∀ a b, ((s (FreeMonoid.of a)).toList.count b : ZMod 2) =
      if mark a then ((s (FreeMonoid.of reference)).toList.count b : ZMod 2) else 0)
    {u v l r : FreeMonoid α} (hu : s u = l * u * r) (hv : s v = l * v * r)
    (hcount : u.toList.countP mark = v.toList.countP mark) : u = v := by
  let f (a : α) := expansion (s (FreeMonoid.of a)) - 1
  let g (a : α) := if mark a then f reference else 0
  have hf (a : α) : VanishesBelow 1 (f a) := expansion_sub_one _
  have hg (a : α) : VanishesBelow 1 (g a) := by
    by_cases hm : mark a
    · simpa only [g, ite_eq_left hm] using hf reference
    · simp [g, hm, VanishesBelow]
  have hfg (a : α) : VanishesBelow 2 (f a - g a) := by
    intro w hw
    by_cases hzero : w.length = 0
    · exact (hf a).sub (hg a) w (by omega)
    · obtain ⟨b, rfl⟩ := FreeMonoid.length_eq_one.mp (by omega : w.length = 1)
      have h := hcolumns a b
      by_cases hm : mark a <;>
        simp [f, g, hm, MonoidAlgebra.coeff_sub, expansion_linear, MonoidAlgebra.one_def] at h ⊢ <;>
        simp [h]
  have hsurrogate : evaluate g (expansion u - expansion v) = 0 := by
    rw [map_sub]
    change evaluate (fun a => if mark a then f reference else 0) (expansion u) -
      evaluate (fun a => if mark a then f reference else 0) (expansion v) = 0
    rw [evaluate_marked_expansion, evaluate_marked_expansion, hcount, sub_self]
  apply eq_of_padded_degree_increase s hu hv
  intro _ _ hx
  have hlow := evaluate_sub_raises_degree hf hg hfg hx
  rwa [hsurrogate, sub_zero] at hlow

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

/-- When the image-count columns modulo two are zero or the same column,
the number of marked letters determines a word reproduced between fixed pads. -/
theorem eq_of_common_padding_of_marked_count {α : Type*} [DecidableEq α]
    (s : α → List α) (mark : α → Bool) (reference : α)
    (hcolumns : ∀ a b, ((s a).count b : ZMod 2) =
      if mark a then ((s reference).count b : ZMod 2) else 0)
    {u v l r : List α} (hu : u.flatMap s = l ++ u ++ r) (hv : v.flatMap s = l ++ v ++ r)
    (hcount : u.countP mark = v.countP mark) : u = v := by
  apply FreeMonoid.ofList.injective
  refine freeMonoid_eq_of_common_padding_of_marked_count
    (FreeMonoid.lift fun a => FreeMonoid.ofList (s a)) mark reference
    (by simpa only [FreeMonoid.lift_eval_of, FreeMonoid.toList_ofList] using hcolumns)
    (l := FreeMonoid.ofList l) (r := FreeMonoid.ofList r) ?_ ?_
    (by simpa only [FreeMonoid.toList_ofList] using hcount)
  · simp only [lift_ofList_flatMap, hu, FreeMonoid.ofList_append, mul_assoc]
  · simp only [lift_ofList_flatMap, hv, FreeMonoid.ofList_append, mul_assoc]

private theorem count_flatMap_of_marked_columns {α : Type*} [DecidableEq α]
    (s : α → List α) (mark : α → Bool) (b : α) (column : ZMod 2)
    (h : ∀ a, ((s a).count b : ZMod 2) = if mark a then column else 0) (w : List α) :
    ((w.flatMap s).count b : ZMod 2) = (w.countP mark : ZMod 2) * column := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.flatMap_cons, List.count_append, Nat.cast_add, h a, ih]
    cases ha : mark a <;> simp [ha, add_mul, add_comm]

/-- For a common-padding pair, the marked-count difference modulo two
determines every coordinate of the letter-count difference modulo two. -/
theorem count_difference_mod_two_of_common_padding {α : Type*} [DecidableEq α]
    (s : α → List α) (mark : α → Bool) (reference : α)
    (hcolumns : ∀ a b, ((s a).count b : ZMod 2) =
      if mark a then ((s reference).count b : ZMod 2) else 0)
    {u v l r : List α} (hu : u.flatMap s = l ++ u ++ r) (hv : v.flatMap s = l ++ v ++ r)
    (b : α) : (u.count b : ZMod 2) - (v.count b : ZMod 2) =
      ((u.countP mark : ZMod 2) - (v.countP mark : ZMod 2)) * (s reference).count b := by
  calc
    _ = ((u.flatMap s).count b : ZMod 2) - ((v.flatMap s).count b : ZMod 2) := by
      rw [hu, hv]
      simp only [List.count_append, Nat.cast_add]
      abel
    _ = _ := by
      rw [count_flatMap_of_marked_columns s mark b _ (fun a => hcolumns a b),
        count_flatMap_of_marked_columns s mark b _ (fun a => hcolumns a b), sub_mul]

/-- An invariant mod-two quotient row kills the contribution of any
intertwining transfer from a nilpotent source. Only the boundary term survives. -/
theorem winding_eq_boundary_of_nilpotent_transfer {U V : Type*}
    [AddCommMonoid U] [Module (ZMod 2) U] [AddCommMonoid V] [Module (ZMod 2) V]
    (A : U →ₗ[ZMod 2] U) (B : V →ₗ[ZMod 2] V) (transfer : U →ₗ[ZMod 2] V)
    (mark : V →ₗ[ZMod 2] ZMod 2) {n : ℕ}
    (hnil : ∀ u, ((A : U → U)^[n]) u = 0)
    (htransfer : ∀ u, B (transfer u) = transfer (A u))
    (hfixed : ∀ v, mark (B v) = mark v) (u : U) (boundary : V) :
    mark (transfer u + boundary) = mark boundary := by
  have hstep (x : U) : mark (transfer (A x)) = mark (transfer x) := by
    rw [← htransfer, hfixed]
  have hiterate (k : ℕ) (x : U) : mark (transfer (((A : U → U)^[k]) x)) = mark (transfer x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, ih, hstep]
  have hu := (hiterate n u).symm
  rw [hnil u, map_zero, map_zero] at hu
  rw [map_add, hu, zero_add]

/-- Period doubling has a common-prefix difference, and its second power
fails the even-count hypothesis. -/
theorem period_doubling_padding_control :
    let δ : Bool → List Bool := fun a => [false, !a]
    let s : Bool → List Bool := fun a => (δ a).flatMap δ
    let l := [false, true, false]
    s false = l ++ [false] ∧ s true = l ++ [true] ∧ ¬ Even ((s false).count false) := by
  decide

/-- The same period-doubling power has the required columns, but its two
one-letter padded words have different marked counts. -/
theorem period_doubling_marked_count_control :
    let δ : Bool → List Bool := fun a => [false, !a]
    let s : Bool → List Bool := fun a => (δ a).flatMap δ
    (∀ a b : Bool, ((s a).count b : ZMod 2) = if !a then ((s false).count b : ZMod 2) else 0) ∧
      ([false] : List Bool).countP (!·) = 1 ∧ ([true] : List Bool).countP (!·) = 0 := by
  decide

end Psc.PeriodicPartnerLiteralDefect
