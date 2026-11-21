/- Finite algebra for the nonunit stack subdivision argument. -/
import PscVerif.PeriodicPartnerEvenTails
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Abel

namespace Psc.PeriodicPartnerStackWordRigidity

section Correction

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

/-- The degree correction on an oriented edge-chain space. -/
def sylvester (A : Module.End K U) (B : Module.End K V) :
    (U →ₗ[K] V) →ₗ[K] (U →ₗ[K] V) where
  toFun C := B.comp C - C.comp A
  map_add' C D := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
    abel
  map_smul' r C := by
    ext x
    simp [smul_sub]

private theorem aeval_comp_of_intertwines
    (A : Module.End K U) (B : Module.End K V) (C : U →ₗ[K] V)
    (h : B.comp C = C.comp A) (p : Polynomial K) :
    (Polynomial.aeval B p).comp C = C.comp (Polynomial.aeval A p) := by
  have hp (n : ℕ) : (B ^ n).comp C = C.comp (A ^ n) := by
    induction n with
    | zero =>
      ext x
      rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, ← Algebra.smul_def, LinearMap.smul_comp,
      LinearMap.comp_smul, hp]

/-- An annihilator of the edge operator which acts injectively on the target
forces the homogeneous degree correction to vanish. -/
theorem sylvester_injective_of_annihilator
    (A : Module.End K U) (B : Module.End K V) (p : Polynomial K)
    (hA : Polynomial.aeval A p = 0) (hB : Function.Injective (Polynomial.aeval B p)) :
    Function.Injective (sylvester A B) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro C hC
  have h : B.comp C = C.comp A := sub_eq_zero.mp hC
  have hz := aeval_comp_of_intertwines A B C h p
  rw [hA, LinearMap.comp_zero] at hz
  ext x
  have hx := DFunLike.congr_fun hz x
  exact hB (by simpa using hx)

/-- A unique degree correction exists for every specified residual. -/
theorem sylvester_exists_unique [FiniteDimensional K U] [FiniteDimensional K V]
    (A : Module.End K U) (B : Module.End K V) (p : Polynomial K)
    (hA : Polynomial.aeval A p = 0) (hB : Function.Injective (Polynomial.aeval B p))
    (E : U →ₗ[K] V) : ∃! C, B.comp C - C.comp A = E := by
  have hinj := sylvester_injective_of_annihilator A B p hA hB
  obtain ⟨C, hC⟩ := LinearMap.surjective_of_injective hinj E
  exact ⟨C, hC, fun D hD => hinj (hD.trans hC.symm)⟩

end Correction

/-- Evaluate a literal oriented path by multiplying in occurrence order. -/
def pathProduct {A R : Type*} [Monoid R] (labels : A → R) (path : List A) : R :=
  (path.map labels).prod

theorem pathProduct_flatMap {A B R : Type*} [Monoid R] (labels : B → R)
    (p : A → List B) (path : List A) :
    pathProduct labels (path.flatMap p) =
      pathProduct (fun e => pathProduct labels (p e)) path := by
  induction path with
  | nil => rfl
  | cons e path ih =>
    simp only [pathProduct, List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons] at ih ⊢
    rw [ih]

theorem pathProduct_map {A R : Type*} [Monoid R] (F : R →* R)
    (labels : A → R) (path : List A) :
    pathProduct (F ∘ labels) path = F (pathProduct labels path) := by
  induction path with
  | nil => simp [pathProduct]
  | cons e path ih =>
    simp only [pathProduct, List.map_cons, List.prod_cons, Function.comp_apply, map_mul] at ih ⊢
    rw [ih]

/-- Pullback along a commuting path projection preserves inflation equivariance. -/
theorem pullback_equivariant {A B R : Type*} [Monoid R]
    (f : A → List A) (g : B → List B) (p : A → List B) (F : R →* R)
    (labels : B → R)
    (hcomm : ∀ e, (f e).flatMap p = (p e).flatMap g)
    (hlabels : ∀ e, pathProduct labels (g e) = F (labels e)) (e : A) :
    pathProduct (fun a => pathProduct labels (p a)) (f e) =
      F (pathProduct labels (p e)) := by
  rw [← pathProduct_flatMap, hcomm, pathProduct_flatMap]
  have he : (fun b => pathProduct labels (g b)) = F ∘ labels := funext hlabels
  rw [he, pathProduct_map]

/-- In the top layer of a truncation the factors contribute corrections
additively. The lower terms act on this layer through their constant term. -/
theorem pathProduct_add_correction {A W R : Type*} [AddCommMonoid W] [Ring R]
    (base : A → R) (d : A → W) (j : W →+ R)
    (hleft : ∀ a t, base a * j t = j t)
    (hright : ∀ a t, j t * base a = j t)
    (hzero : ∀ s t, j s * j t = 0) (path : List A) :
    pathProduct (fun a => base a + j (d a)) path =
      pathProduct base path + j ((path.map d).sum) := by
  have hrightPath (t : W) (w : List A) : j t * pathProduct base w = j t := by
    induction w with
    | nil => simp [pathProduct]
    | cons a w ih =>
      change j t * (base a * pathProduct base w) = j t
      rw [← mul_assoc, hright, ih]
  induction path with
  | nil => simp [pathProduct]
  | cons a path ih =>
    change (base a + j (d a)) * pathProduct (fun b => base b + j (d b)) path =
      base a * pathProduct base path + j (d a + (path.map d).sum)
    rw [ih, add_mul, mul_add, mul_add, hleft, hrightPath, hzero, add_zero, map_add]
    abel

/-- Compare the original words carried by two copies of the same stack interval. -/
theorem same_stack_interval_products_eq {A B S R : Type*} [Monoid R]
    (original : A → R) (stack : S → R) (raw : B → List A) (q : B → List S)
    (hraw : ∀ e, pathProduct original (raw e) = pathProduct stack (q e))
    (u v : List B) (h : u.flatMap q = v.flatMap q) :
    pathProduct original (u.flatMap raw) = pathProduct original (v.flatMap raw) := by
  have hq (x : List B) :
      pathProduct original (x.flatMap raw) = pathProduct stack (x.flatMap q) := by
    rw [pathProduct_flatMap, pathProduct_flatMap, funext hraw]
  rw [hq u, hq v, h]

/-- A product of at least two roots of equal norm greater than one avoids
every edge eigenvalue whose norm is zero, one or the common root norm. -/
theorem tensor_norm_separates {F : Type*} [Monoid F] (norm : F →* ℚ)
    (D : ℚ) (hD : 1 < D) (roots : List F) (hdegree : 2 ≤ roots.length)
    (hroots : ∀ x ∈ roots, norm x = D) (z : F)
    (hz : norm z = 0 ∨ norm z = 1 ∨ norm z = D) : roots.prod ≠ z := by
  have hnorm (xs : List F) (hs : ∀ x ∈ xs, norm x = D) :
      norm xs.prod = D ^ xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have htail : ∀ t ∈ xs, norm t = D := fun t ht => hs t (List.mem_cons_of_mem x ht)
      simp only [List.prod_cons, map_mul, List.length_cons]
      rw [hs x List.mem_cons_self, ih htail, pow_succ']
  have hb : D < D ^ roots.length := by
    simpa only [pow_one] using pow_lt_pow_right₀ hD (show 1 < roots.length by omega)
  intro he
  rw [← he, hnorm roots hroots] at hz
  rcases hz with h | h | h
  · exact (zero_lt_one.trans (hD.trans hb)).ne' h
  · exact (hD.trans hb).ne' h
  · exact hb.ne' h

/-- Two common vertices on opposite sides give arbitrarily large comparison
intervals for tilings fixed by the same expanding inflation. -/
theorem fixedTilings_eq_of_common_intervals {α : Type*}
    {L : Psc.PeriodicPartnerHull.LengthSubst α} {T U : Set (α × ℝ)}
    (hβ : 1 < L.β) (hT : L.inflate T = T) (hU : L.inflate U = U)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (haT : ∃ c, (c, a) ∈ T) (haU : ∃ c, (c, a) ∈ U)
    (hbT : ∃ c, (c, b) ∈ T) (hbU : ∃ c, (c, b) ∈ U)
    (hagree : ∀ {x y : ℝ}, (∃ c, (c, x) ∈ T) → (∃ c, (c, x) ∈ U) →
      (∃ c, (c, y) ∈ T) → (∃ c, (c, y) ∈ U) → L.AgreeOn (Set.Ioo x y) T U) : T = U := by
  have vertex_mul_pow (x : ℝ) (n : ℕ) {S : Set (α × ℝ)} (hS : L.inflate S = S)
      (hx : ∃ c, (c, x) ∈ S) : ∃ c, (c, L.β ^ n * x) ∈ S := by
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact Psc.PeriodicPartnerEvenTails.vertex_inflate hS ih
  ext p
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (-p.2 / -a) hβ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p.2 / b) hβ
  have hleft : L.β ^ n * a < p.2 := by
    have h := (div_lt_iff₀ (neg_pos.mpr ha)).mp hn
    rw [mul_neg] at h
    exact neg_lt_neg_iff.mp h
  have hright : p.2 < L.β ^ m * b := (div_lt_iff₀ hb).mp hm
  have hmem : p.2 ∈ L.supp p := by
    simp [Psc.PeriodicPartnerHull.LengthSubst.supp, L.ℓ_pos p.1]
  exact hagree (vertex_mul_pow a n hT haT) (vertex_mul_pow a n hU haU)
    (vertex_mul_pow b m hT hbT) (vertex_mul_pow b m hU hbU) p ⟨p.2, hmem, hleft, hright⟩

/-- Equal physical length labels fail to distinguish the two Thue–Morse words. -/
theorem equal_letter_labels_control {R : Type*} [Monoid R] (label : R) :
    pathProduct (fun _ : Bool => label) [false, true] =
      pathProduct (fun _ : Bool => label) [true, false] := by simp [pathProduct]

end Psc.PeriodicPartnerStackWordRigidity
