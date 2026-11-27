import PscVerif.PeriodicPartnerRealization
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Data.Finsupp.Basic

/-!
# Finite character certificates on the actual solenoid

A certificate is a finitely supported integer vector on history levels and
letter coordinates. Its character is the exponential of the corresponding
finite sum of circle coordinates. Addition and negation of certificates give
multiplication and conjugation of characters. All compatible history levels
are retained, including in the nonunit case.

The construction and flow law use finite sums. The density endpoint reuses
Mathlib's Stone--Weierstrass theorem. No almost-everywhere singleton-fibre or
invariant-measure spectral assertion is made here.

Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerSolenoidCharacters

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization
open scoped Topology ComplexConjugate

variable {α : Type*}

/-- A coordinate of the actual quotient torus, valued in `ℝ / ℤ`. -/
noncomputable def torusCoordinate (a : α) : Torus α →+ UnitAddCircle :=
  QuotientAddGroup.lift (lattice α)
    { toFun := fun v => (v a : UnitAddCircle)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (by
      intro v hv
      obtain ⟨n, hn⟩ := hv a
      change (v a : UnitAddCircle) = 0
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simpa using hn⟩)

@[simp]
theorem torusCoordinate_mk (a : α) (v : α → ℝ) :
    torusCoordinate a (v : Torus α) = (v a : UnitAddCircle) := rfl

@[fun_prop]
theorem continuous_torusCoordinate (a : α) : Continuous (torusCoordinate a) := by
  apply (QuotientAddGroup.isQuotientMap_mk (lattice α)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (continuous_apply a)

/-- The finite family of circle coordinates determines a quotient torus point. -/
theorem torusCoordinate_ext {z w : Torus α}
    (h : ∀ a, torusCoordinate a z = torusCoordinate a w) : z = w := by
  induction z using QuotientAddGroup.induction_on
  induction w using QuotientAddGroup.induction_on
  rename_i v u
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro a
  have hz : ((v a - u a : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (h a)
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨n, by simpa using hn⟩

/-- An exact integer certificate with only finitely many nonzero history/letter entries. -/
abbrev Certificate (α : Type*) := (ℕ × α) →₀ ℤ

variable [Fintype α] [DecidableEq α] (S : LengthSubst α)

/-- A certificate's additive phase, obtained by a finite sum of circle coordinates. -/
noncomputable def phase (c : Certificate α) : Solenoid S →+ UnitAddCircle where
  toFun z := c.sum fun ni e => e • torusCoordinate ni.2 (z.1 ni.1)
  map_zero' := by simp
  map_add' z w := by
    simp only [Finsupp.sum, AddSubgroup.coe_add, Pi.add_apply, map_add, zsmul_add,
      Finset.sum_add_distrib]

@[simp]
theorem phase_zero (z : Solenoid S) : phase S 0 z = 0 := by
  simp [phase]

theorem phase_add (c d : Certificate α) (z : Solenoid S) :
    phase S (c + d) z = phase S c z + phase S d z := by
  exact Finsupp.sum_add_index' (h := fun (ni : ℕ × α) (e : ℤ) =>
    e • torusCoordinate ni.2 (z.1 ni.1))
    (fun _ => zero_zsmul _) (fun ni e f => add_zsmul _ e f)

theorem phase_neg (c : Certificate α) (z : Solenoid S) :
    phase S (-c) z = -phase S c z := by
  apply eq_neg_of_add_eq_zero_left
  rw [← phase_add, neg_add_cancel, phase_zero]

@[simp]
theorem phase_single (ni : ℕ × α) (e : ℤ) (z : Solenoid S) :
    phase S (Finsupp.single ni e) z = e • torusCoordinate ni.2 (z.1 ni.1) := by
  exact Finsupp.sum_single_index (h := fun (ni : ℕ × α) (e : ℤ) =>
    e • torusCoordinate ni.2 (z.1 ni.1))
    (zero_zsmul _)

theorem continuous_phase (c : Certificate α) : Continuous (phase S c) := by
  change Continuous (fun z : Solenoid S =>
    ∑ ni ∈ c.support, c ni • torusCoordinate ni.2 (z.1 ni.1))
  apply continuous_finsetSum
  intro ni _
  exact ((continuous_torusCoordinate ni.2).comp
    ((continuous_apply ni.1).comp continuous_subtype_val)).zsmul (c ni)

/-- The continuous unit-modulus character replayed from a finite certificate. -/
noncomputable def character (c : Certificate α) : C(Solenoid S, ℂ) where
  toFun z := AddCircle.toCircle (phase S c z)
  continuous_toFun := continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (continuous_phase S c))

@[simp]
theorem character_apply (c : Certificate α) (z : Solenoid S) :
    character S c z = (AddCircle.toCircle (phase S c z) : ℂ) := rfl

@[simp]
theorem character_zero : character S 0 = 1 := by
  ext z
  simp

theorem character_add (c d : Certificate α) :
    character S (c + d) = character S c * character S d := by
  ext z
  simp only [character_apply, phase_add, AddCircle.toCircle_add, Circle.coe_mul,
    ContinuousMap.mul_apply]

theorem character_neg (c : Certificate α) : character S (-c) = star (character S c) := by
  ext z
  simp only [character_apply, phase_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj,
    ContinuousMap.star_apply, starRingEnd_apply]

theorem character_norm (c : Certificate α) (z : Solenoid S) : ‖character S c z‖ = 1 :=
  Circle.norm_coe _

theorem character_map_add (c : Certificate α) (z w : Solenoid S) :
    character S c (z + w) = character S c z * character S c w := by
  simp only [character_apply, map_add, AddCircle.toCircle_add, Circle.coe_mul]

@[simp]
theorem character_at_zero (c : Certificate α) : character S c 0 = 1 := by
  simp

/-- The real flow frequency is a finite integer combination of the actual
normalized unstable coordinates at their specified history levels. -/
noncomputable def frequency (P : PisotData S) (c : Certificate α) : ℝ :=
  c.sum fun ni e => (e : ℝ) * P.u ni.2 / S.β ^ ni.1

@[simp]
theorem frequency_zero (P : PisotData S) : frequency S P 0 = 0 := by
  simp [frequency]

theorem frequency_add (P : PisotData S) (c d : Certificate α) :
    frequency S P (c + d) = frequency S P c + frequency S P d := by
  apply Finsupp.sum_add_index' (h := fun (ni : ℕ × α) (e : ℤ) =>
    (e : ℝ) * P.u ni.2 / S.β ^ ni.1)
  · intro ni
    simp
  · intro ni e f
    simp [Int.cast_add, add_mul, add_div]

theorem frequency_neg (P : PisotData S) (c : Certificate α) :
    frequency S P (-c) = -frequency S P c := by
  apply eq_neg_of_add_eq_zero_left
  rw [← frequency_add, neg_add_cancel, frequency_zero]

@[simp]
theorem frequency_single (P : PisotData S) (ni : ℕ × α) (e : ℤ) :
    frequency S P (Finsupp.single ni e) = (e : ℝ) * P.u ni.2 / S.β ^ ni.1 := by
  exact Finsupp.sum_single_index (h := fun (ni : ℕ × α) (e : ℤ) =>
    (e : ℝ) * P.u ni.2 / S.β ^ ni.1) (by simp)

theorem phase_flow_zero [Nonempty α] (P : PisotData S) (c : Certificate α) (t : ℝ) :
    phase S c (flow P t 0) = ((t * frequency S P c : ℝ) : UnitAddCircle) := by
  change c.sum (fun ni e => e • torusCoordinate ni.2 ((flow P t 0).1 ni.1)) = _
  simp only [flow, zero_add, torusCoordinate_mk, Pi.smul_apply, smul_eq_mul]
  unfold Finsupp.sum
  simp_rw [← AddCircle.coe_zsmul]
  rw [← QuotientAddGroup.mk_sum]
  congr 1
  simp only [frequency, Finsupp.sum, Finset.mul_sum, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro ni _
  ring

/-- Exact flow eigenfunction law, with the frequency replayed from a finite
certificate. No approximation of the flow or Perron vector is involved. -/
theorem character_flow [Nonempty α] (P : PisotData S) (c : Certificate α) (t : ℝ)
    (z : Solenoid S) :
    character S c (flow P t z) =
      Complex.exp (((2 * Real.pi * (t * frequency S P c) : ℝ) : ℂ) * Complex.I) *
        character S c z := by
  have hf : flow P t z = z + flow P t 0 := by simp [flow]
  have hzero : character S c (flow P t 0) =
      Complex.exp (((2 * Real.pi * (t * frequency S P c) : ℝ) : ℂ) * Complex.I) := by
    rw [character_apply, phase_flow_zero, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    simp only [div_one]
  rw [hf, character_map_add, hzero, mul_comm]

/-- Equality on all finite certificates determines the full compatible history. -/
theorem character_ext {z w : Solenoid S}
    (h : ∀ c : Certificate α, character S c z = character S c w) : z = w := by
  apply Subtype.ext
  funext n
  apply torusCoordinate_ext
  intro a
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.coe_injective
  simpa only [character_apply, phase_single, one_zsmul]
    using h (Finsupp.single (n, a) 1)

/-- A single history/letter coordinate separates any two distinct histories. -/
theorem exists_single_character_ne {z w : Solenoid S} (h : z ≠ w) :
    ∃ n a, character S (Finsupp.single (n, a) 1) z ≠
      character S (Finsupp.single (n, a) 1) w := by
  by_contra! hc
  apply h
  apply Subtype.ext
  funext n
  apply torusCoordinate_ext
  intro a
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.coe_injective
  simpa only [character_apply, phase_single, one_zsmul] using hc n a

local instance : CompactSpace (Solenoid S) := solenoid_compactSpace S

/-- The algebra generated by finite character certificates is closed under conjugation. -/
noncomputable def characterAlgebra : StarSubalgebra ℂ C(Solenoid S, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (character S))
  star_mem' := by
    change Algebra.adjoin ℂ (range (character S)) ≤ star (Algebra.adjoin ℂ (range (character S)))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact Algebra.subset_adjoin ⟨-c, character_neg S c⟩

/-- Products require only addition of finite certificates, so the generated algebra is a span. -/
theorem characterAlgebra_toSubmodule :
    (characterAlgebra S).toSubalgebra.toSubmodule =
      Submodule.span ℂ (range (character S)) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  refine fun x => Submonoid.closure_induction (fun _ => id) ⟨0, character_zero S⟩ ?_
  rintro _ _ _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
  exact ⟨c + d, character_add S c d⟩

theorem characterAlgebra_separatesPoints : (characterAlgebra S).SeparatesPoints := by
  intro z w hzw
  obtain ⟨n, a, hne⟩ := exists_single_character_ne S hzw
  exact ⟨_, ⟨character S (Finsupp.single (n, a) 1),
    Algebra.subset_adjoin ⟨Finsupp.single (n, a) 1, rfl⟩, rfl⟩, hne⟩

/-- The standard Stone--Weierstrass theorem supplies density after finite separation. -/
theorem characterAlgebra_closure_eq_top : (characterAlgebra S).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (characterAlgebra_separatesPoints S)

/-- Finite complex linear combinations of the explicit characters are uniformly dense. -/
theorem span_character_closure_eq_top :
    (Submodule.span ℂ (range (character S))).topologicalClosure = ⊤ := by
  rw [← characterAlgebra_toSubmodule]
  exact congrArg (fun A : StarSubalgebra ℂ C(Solenoid S, ℂ) => A.toSubalgebra.toSubmodule)
    (characterAlgebra_closure_eq_top S)

end Psc.PeriodicPartnerSolenoidCharacters
