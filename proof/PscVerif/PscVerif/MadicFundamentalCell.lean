import PscVerif.MadicHaar
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Tactic.Abel

/-!
# Exact fundamental cells for the actual matrix-adic diagonal

The real action is an invertible extension of the original integer map.
The full real chart is an arbitrary continuous linear equivalence. At depth
`q`, its image of the coordinatewise half-open parallelepiped is paired with
the kernel of the actual depth-`q` residue map. Integer floors give coverage;
the same image lattice and half-open cube give exact uniqueness.

No preservation of a preferred measure by the real chart is assumed. This
module supplies measurable fundamental domains, not a normalization,
positive overlap, finite cut count, or Pisot substitution conclusion.
Pre-code GO: `docs/c4-finite-cut-count.md`, following-increment decision,
and the linked primary-source and actual-model interface reviews.
-/

noncomputable section

open Set MeasureTheory

namespace Psc.MadicFundamentalCell

abbrev Int3 := Fin 3 → ℤ
abbrev Real3 := Fin 3 → ℝ

/-- Coordinatewise inclusion of the original integer vectors. -/
def intCast : Int3 →+ Real3 where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

@[simp] theorem intCast_apply (z : Int3) (i : Fin 3) : intCast z i = (z i : ℝ) := rfl

theorem intCast_injective : Function.Injective intCast := by
  intro z w h
  ext i
  exact Int.cast_injective (show (z i : ℝ) = (w i : ℝ) from congrFun h i)

/-- Coordinatewise half-open cube; this is not the product-order `Ico 0 1`. -/
def coordinateCube : Set Real3 := Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)

@[simp] theorem mem_coordinateCube (x : Real3) :
    x ∈ coordinateCube ↔ ∀ i, 0 ≤ x i ∧ x i < 1 := by
  simp [coordinateCube, Set.mem_pi]

theorem coordinateCube_measurableSet : MeasurableSet coordinateCube :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

theorem coordinateCube_subset_Icc : coordinateCube ⊆ Set.Icc (0 : Real3) 1 := by
  intro x hx
  exact ⟨fun i => ((mem_coordinateCube x).mp hx i).1,
    fun i => ((mem_coordinateCube x).mp hx i).2.le⟩

/-- Integer floor removes exactly the integral coordinate of each real vector. -/
theorem floor_remainder_mem (x : Real3) :
    x - intCast (fun i => ⌊x i⌋) ∈ coordinateCube := by
  rw [mem_coordinateCube]
  intro i
  exact ⟨Int.fract_nonneg (x i), Int.fract_lt_one (x i)⟩

/-- Distinct integral translates cannot meet the coordinatewise half-open cube. -/
theorem cube_integer_difference_zero {u v : Real3} (hu : u ∈ coordinateCube)
    (hv : v ∈ coordinateCube) {k : Int3} (hk : intCast k = u - v) : k = 0 := by
  ext i
  have hu0 := Int.floor_eq_zero_iff.mpr ((mem_coordinateCube u).mp hu i)
  have hv0 := Int.floor_eq_zero_iff.mpr ((mem_coordinateCube v).mp hv i)
  have hi : (k i : ℝ) = u i - v i := congrFun hk i
  have h : u i = (k i : ℝ) + v i := sub_eq_iff_eq_add.mp hi.symm
  have hf := congrArg Int.floor h
  rw [hu0, Int.floor_intCast_add, hv0, add_zero] at hf
  exact hf.symm

variable (M : Int3 →ₗ[ℤ] Int3) (A : Real3 ≃L[ℝ] Real3)

/-- Compatibility remains attached to the same original integer powers. -/
theorem real_power_intCast (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) (z : Int3) : (A ^ q) (intCast z) = intCast ((M ^ q) z) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply]
      change A ((A ^ q) (intCast z)) = intCast (M ((M ^ q) z))
      rw [ih, hA]

/-- Invertibility of the compatible real extension implies integral injectivity. -/
theorem integer_map_injective (hA : ∀ z, A (intCast z) = intCast (M z)) :
    Function.Injective M := by
  intro z w h
  apply intCast_injective
  apply A.injective
  rw [hA, hA, h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (phi : Real3 ≃L[ℝ] E)

/-- The full diagonal uses the original integral canonical map. -/
def diagonal : Int3 →+ E × MadicResidue.Carrier M :=
  ((phi.toLinearEquiv.toAddEquiv.toAddMonoidHom).comp intCast).prod
    (MadicResidue.star M).toAddMonoidHom

@[simp] theorem diagonal_apply (z : Int3) :
    diagonal M phi z = (phi (intCast z), MadicResidue.star M z) := rfl

theorem diagonal_injective : Function.Injective (diagonal M phi) := by
  intro z w h
  exact intCast_injective (phi.injective (congrArg Prod.fst h))

/-- Named action for local installation: no chart-dependent global instance. -/
abbrev diagonalAction : AddAction Int3 (E × MadicResidue.Carrier M) :=
  AddAction.compHom _ (diagonal M phi)

/-- The real parallelepiped and the residue kernel use the same depth. -/
def cell (q : ℕ) : Set (E × MadicResidue.Carrier M) :=
  (phi '' ((A ^ q) '' coordinateCube)) ×ˢ
    ((MadicResidue.eval M q) ⁻¹' {0})

/-- A translate between two points of one cell must be the zero integer vector. -/
theorem cell_translate_eq_zero (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) {x y : E × MadicResidue.Carrier M}
    (hx : x ∈ cell M A phi q) (hy : y ∈ cell M A phi q)
    {z : Int3} (h : diagonal M phi z + x = y) : z = 0 := by
  have hx0 : MadicResidue.eval M q x.2 = 0 := hx.2
  have hy0 : MadicResidue.eval M q y.2 = 0 := hy.2
  have he := congrArg (fun p : E × MadicResidue.Carrier M => MadicResidue.eval M q p.2) h
  change MadicResidue.eval M q (MadicResidue.star M z + x.2) =
    MadicResidue.eval M q y.2 at he
  rw [map_add, MadicResidue.eval_star, hx0, hy0, add_zero] at he
  obtain ⟨k, hk⟩ := (MadicResidue.quotient_eq_zero_iff M q z).mp he
  rcases hx.1 with ⟨_, ⟨u, hu, rfl⟩, hu_eq⟩
  rcases hy.1 with ⟨_, ⟨v, hv, rfl⟩, hv_eq⟩
  have hr := congrArg Prod.fst h
  change phi (intCast z) + x.1 = y.1 at hr
  rw [← hu_eq, ← hv_eq, ← map_add] at hr
  have hr' := phi.injective hr
  rw [← hk, ← real_power_intCast M A hA q k, ← map_add] at hr'
  have hkv : intCast k + u = v := (A ^ q).injective hr'
  have hk0 : k = 0 := cube_integer_difference_zero hv hu (eq_sub_iff_add_eq.mpr hkv)
  simpa [hk0] using hk.symm

/-- Every full point admits an original integer translate into the exact cell. -/
theorem exists_representative (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) (x : E × MadicResidue.Carrier M) :
    ∃ z : Int3, x - diagonal M phi z ∈ cell M A phi q := by
  obtain ⟨z0, hz0⟩ := MadicResidue.quotient_surjective M q (MadicResidue.eval M q x.2)
  let a : Real3 := (A ^ q).symm (phi.symm x.1 - intCast z0)
  let k : Int3 := fun i => ⌊a i⌋
  let u : Real3 := a - intCast k
  let z : Int3 := z0 + (M ^ q) k
  have hu : u ∈ coordinateCube := floor_remainder_mem a
  have ha : (A ^ q) a = phi.symm x.1 - intCast z0 := (A ^ q).apply_symm_apply _
  have hreal : phi ((A ^ q) u) = x.1 - phi (intCast z) := by
    dsimp only [u]
    rw [map_sub, ha, real_power_intCast M A hA q k]
    simp only [z, map_add, map_sub, phi.apply_symm_apply]
    abel
  have hz : MadicResidue.quotient M q z = MadicResidue.eval M q x.2 := by
    have hm : MadicResidue.quotient M q ((M ^ q) k) = 0 :=
      (MadicResidue.quotient_eq_zero_iff M q _).mpr ⟨k, rfl⟩
    simp only [z, map_add, hz0, hm, add_zero]
  refine ⟨z, ⟨?_, ?_⟩⟩
  · exact ⟨(A ^ q) u, ⟨u, hu, rfl⟩, hreal⟩
  · change MadicResidue.eval M q (x.2 - MadicResidue.star M z) = 0
    rw [map_sub, MadicResidue.eval_star, hz, sub_self]

/-- Unique integer translate representative, before taking any measure quotient. -/
theorem existsUnique_representative (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) (x : E × MadicResidue.Carrier M) :
    ∃! z : Int3, x - diagonal M phi z ∈ cell M A phi q := by
  obtain ⟨z, hz⟩ := exists_representative M A phi hA q x
  refine ⟨z, hz, ?_⟩
  intro w hw
  apply sub_eq_zero.mp
  apply cell_translate_eq_zero M A phi hA q hw hz
  rw [map_sub]
  abel

/-- Exact coverage and uniqueness in the convention used by fundamental domains. -/
theorem existsUnique_add_mem (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) (x : E × MadicResidue.Carrier M) :
    ∃! z : Int3, diagonal M phi z + x ∈ cell M A phi q := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_representative M A phi hA q x
  refine ⟨-z, ?_, ?_⟩
  · simpa only [map_neg, sub_eq_add_neg, add_comm] using hz
  · intro w hw
    have hw' : x - diagonal M phi (-w) ∈ cell M A phi q := by
      simpa only [map_neg, sub_neg_eq_add, add_comm] using hw
    simpa using congrArg Neg.neg (huniq (-w) hw')

/-- Distinct original integer translates of a cell are disjoint as literal sets. -/
theorem translates_disjoint (hA : ∀ z, A (intCast z) = intCast (M z)) (q : ℕ) :
    Pairwise (fun z w : Int3 => Disjoint
      ((fun x => diagonal M phi z + x) '' cell M A phi q)
      ((fun x => diagonal M phi w + x) '' cell M A phi q)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
  have hz : x - diagonal M phi z ∈ cell M A phi q := by
    rw [← hux]
    simpa only [add_sub_cancel_left] using hu
  have hw : x - diagonal M phi w ∈ cell M A phi q := by
    rw [← hvx]
    simpa only [add_sub_cancel_left] using hv
  exact hzw ((existsUnique_representative M A phi hA q x).unique hz hw)

/-- A containing compact rectangle, without replacing the joint real cell
by the product of its physical and stable projections. -/
def compactContainer (q : ℕ) : Set (E × MadicResidue.Carrier M) :=
  (phi '' ((A ^ q) '' Set.Icc (0 : Real3) 1)) ×ˢ Set.univ

theorem cell_subset_compactContainer (q : ℕ) :
    cell M A phi q ⊆ compactContainer M A phi q := by
  intro x hx
  rcases hx.1 with ⟨_, ⟨u, hu, rfl⟩, he⟩
  exact ⟨⟨(A ^ q) u, ⟨u, coordinateCube_subset_Icc hu, rfl⟩, he⟩, Set.mem_univ _⟩

theorem compactContainer_isCompact (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) : IsCompact (compactContainer M A phi q) := by
  let := MadicResidue.carrier_compactSpace M (integer_map_injective M A hA)
  exact ((isCompact_Icc.image (A ^ q).continuous).image phi.continuous).prod isCompact_univ

theorem cell_zero_subset :
    cell M A phi 0 ⊆ (phi '' Set.Icc (0 : Real3) 1) ×ˢ Set.univ := by
  have h := cell_subset_compactContainer M A phi 0
  change cell M A phi 0 ⊆
    (phi '' ((fun x : Real3 => x) '' Set.Icc (0 : Real3) 1)) ×ˢ Set.univ at h
  simpa only [Set.image_id'] using h

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- Local measurability for the actual diagonal translation action. -/
theorem diagonal_measurableConstVAdd :
    letI := diagonalAction M phi
    MeasurableConstVAdd Int3 (E × MadicResidue.Carrier M) := by
  let := diagonalAction M phi
  refine ⟨fun z => ?_⟩
  exact ((measurable_const_add (phi (intCast z))).comp measurable_fst).prodMk
    ((measurable_const_add (MadicResidue.star M z)).comp measurable_snd)

/-- Any ambient left-invariant measure is invariant under the actual diagonal
integer translations. No measure-preserving property of `phi` is used. -/
theorem diagonal_vaddInvariantMeasure (μ : Measure (E × MadicResidue.Carrier M))
    [μ.IsAddLeftInvariant] :
    letI := diagonalAction M phi
    VAddInvariantMeasure Int3 (E × MadicResidue.Carrier M) μ := by
  let := diagonalAction M phi
  let := diagonal_measurableConstVAdd M phi
  constructor
  intro z s hs
  have hm : Measurable (fun x : E × MadicResidue.Carrier M => diagonal M phi z + x) :=
    measurable_const_vadd z
  change μ ((fun x => diagonal M phi z + x) ⁻¹' s) = μ s
  rw [← Measure.map_apply hm hs, map_add_left_eq_self]

theorem cell_measurableSet (q : ℕ) : MeasurableSet (cell M A phi q) := by
  apply MeasurableSet.prod
  · apply phi.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    exact (A ^ q).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      coordinateCube_measurableSet
  · exact ((isOpen_discrete {0}).preimage (MadicResidue.continuous_eval M q)).measurableSet

/-- The actual cells are fundamental domains for the same named diagonal action,
for every measure; invariant-measure consequences are separate theorems. -/
theorem isAddFundamentalDomain (hA : ∀ z, A (intCast z) = intCast (M z))
    (q : ℕ) (μ : Measure (E × MadicResidue.Carrier M)) :
    letI := diagonalAction M phi
    IsAddFundamentalDomain Int3 (cell M A phi q) μ := by
  let := diagonalAction M phi
  exact IsAddFundamentalDomain.mk' (cell_measurableSet M A phi q).nullMeasurableSet
    (existsUnique_add_mem M A phi hA q)

end Measurable

end Psc.MadicFundamentalCell
