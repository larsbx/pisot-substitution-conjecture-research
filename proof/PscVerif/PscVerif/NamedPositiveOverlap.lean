import PscVerif.NamedCutCount
import PscVerif.NamedFundamentalCell
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Instances.Discrete

/-! The lower and upper bounds count the same original integer vectors. -/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Psc.NamedPositiveOverlap

open Psc.Descendants Psc.NamedStableChart Psc.NamedPrefixCompact
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.NamedCutNeighborhood
open Psc.NamedCutCount Psc.NamedFundamentalCell

private theorem open_add_tube {G : Type*} [TopologicalSpace G] [AddMonoid G]
    [ContinuousAdd G] {K O : Set G} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ U V : Set G, IsOpen U ∧ K ⊆ U ∧ V ∈ 𝓝 0 ∧
      ∀ u ∈ U, ∀ v ∈ V, u + v ∈ O := by
  have hprod : K ×ˢ ({0} : Set G) ⊆ (fun p : G × G => p.1 + p.2) ⁻¹' O := by
    intro p hp
    have hv : p.2 = 0 := mem_singleton_iff.mp hp.2
    change p.1 + p.2 ∈ O
    simpa only [hv, add_zero] using hKO hp.1
  obtain ⟨U, V, hU, hV, hKU, h0, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton
      (hO.preimage (continuous_fst.add continuous_snd)) hprod
  exact ⟨U, V, hU, hKU, hV.mem_nhds (h0 (mem_singleton 0)),
    fun u hu v hv => hUV (mk_mem_prod hu hv)⟩

/-- A fixed width disappears from the density bound when the strip diverges. -/
theorem density_le_of_eventually_packing {X : ℕ → ℝ} {a b W : ℝ}
    (hgrow : Tendsto X atTop atTop)
    (hpack : ∀ᶠ n in atTop, a * X n ≤ (X n + W) * b) : a ≤ b := by
  by_contra! h
  have hbig := hgrow.eventually_gt_atTop (W * b / (a - b))
  obtain ⟨n, hn, hp⟩ := (hbig.and hpack).exists
  have hgap := (div_lt_iff₀ (sub_pos.mpr h)).mp hn
  nlinarith only [hgap, hp]

private theorem source_length_pos {w : Word} (hw : w ≠ []) :
    0 < physicalLength physicalRow w := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    rw [physicalLength_cons]
    exact add_pos_of_pos_of_nonneg (physical_row_pos a)
      (physicalLength_nonneg physicalRow (fun i => (physical_row_pos i).le) w)

private theorem strip_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => beta ^ (12 * n) * t) atTop atTop := by
  have hb : 1 < beta := (by norm_num : (1 : ℝ) < 2).trans beta_gt_two
  have hp : 1 < beta ^ 12 := one_lt_pow₀ hb (by decide)
  simpa only [pow_mul] using (tendsto_pow_atTop_atTop_of_one_lt hp).atTop_mul_const ht

private theorem carrier_injective (f : Fin 2) : Function.Injective (M f) :=
  MadicFundamentalCell.integer_map_injective (M f) Psc.NamedFullChart.realIncidence
    (compatible f)

private theorem carrier_secondCountable (f : Fin 2) : SecondCountableTopology (H f) := by
  letI : ∀ q : ℕ, Finite (MadicResidue.Residue (M f) q) :=
    MadicResidue.residue_finite (M f) (carrier_injective f)
  letI : ∀ q : ℕ, SecondCountableTopology (MadicResidue.Residue (M f) q) :=
    fun _ => inferInstance
  letI : SecondCountableTopology (∀ q : ℕ, MadicResidue.Residue (M f) q) := inferInstance
  exact Subtype.secondCountableTopology
    (MadicResidue.compatibleSequences (M f) : Set (∀ q : ℕ, MadicResidue.Residue (M f) q))

variable (f : Fin 2) (ν : Measure (H f)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]

/-- A common cell mass gives a lower bound on every finite-measure open
superset of the actual compact overlap. The packing depth is chosen before
the word generation varies. -/
theorem exists_open_lower_bound {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution f) C)
    (L : ℝ) (hL : 0 < L) (hbound : ∀ B ∈ C, physicalLength physicalRow B.1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧
      (∀ q, fullMeasure f ν (cell f q) = ENNReal.ofReal c) ∧
      ∀ O : Set (Internal f), IsOpen O → carrierOverlap f C ⊆ O →
        internalMeasure f ν O ≠ ∞ → c / L ≤ (internalMeasure f ν).real O := by
  obtain ⟨c, hc, hmass, packing⟩ := exists_positive_uniform_packing f ν
  obtain ⟨T, hT⟩ := strict.nonempty
  let t := physicalLength physicalRow T.1
  have ht : 0 < t := source_length_pos (strict.isBlock T hT).1
  let X (n : ℕ) := beta ^ (12 * n) * t
  refine ⟨c, hc, hmass, ?_⟩
  intro O hO hKO hfin
  letI := carrier_secondCountable f
  obtain ⟨U, V, hU, hKU, hV, hUV⟩ :=
    open_add_tube (carrierOverlap_compact f C) hO hKO
  obtain ⟨d, hd⟩ := packing V hV
  obtain ⟨N, hN⟩ := eventually_integerStarts_mem f strict U hU hKU
  apply density_le_of_eventually_packing (strip_tendsto t ht)
    (W := NamedCellBounds.physicalWidth (12 * d))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hX : 0 ≤ X n := mul_nonneg (pow_nonneg beta_pos.le _) ht.le
  obtain ⟨hlower, hstrip⟩ := integerStarts_count_and_strip f strict L hbound n hT
  have hupper := hd d le_rfl (integerStarts f n T) (X n) hX U O
    hO.measurableSet hfin (fun z hz =>
      ⟨(hstrip z hz).1, (hstrip z hz).2, hN n hn T hT z hz⟩) hUV
  calc
    c / L * X n ≤ c * ((integerStarts f n T).card : ℝ) := by
      rw [div_mul_eq_mul_div₀, div_le_iff₀ hL]
      simpa [X, t, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hlower hc.le
    _ ≤ _ := hupper

/-- Outer regularity transfers the open-target lower bound to the overlap. -/
theorem exists_overlap_lower_bound_of_outerRegular
    [(internalMeasure f ν).OuterRegular] {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution f) C)
    (L : ℝ) (hL : 0 < L) (hbound : ∀ B ∈ C, physicalLength physicalRow B.1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧
      (∀ q, fullMeasure f ν (cell f q) = ENNReal.ofReal c) ∧
      ENNReal.ofReal (c / L) ≤ internalMeasure f ν (carrierOverlap f C) := by
  obtain ⟨c, hc, hmass, hopen⟩ := exists_open_lower_bound f ν strict L hL hbound
  refine ⟨c, hc, hmass, ?_⟩
  by_contra! h
  obtain ⟨O, hKO, hO, hsmall⟩ := (carrierOverlap f C).exists_isOpen_lt_of_lt _ h
  have hfin := (hsmall.trans_le le_top).ne
  have hlower := ENNReal.ofReal_le_ofReal (hopen O hO hKO hfin)
  rw [measureReal_def, ENNReal.ofReal_toReal hfin] at hlower
  exact (not_lt_of_ge hlower) hsmall

omit [ν.IsAddHaarMeasure] in
theorem internalMeasure_outerRegular : (internalMeasure f ν).OuterRegular := by
  letI := MadicResidue.carrier_compactSpace (M f) (carrier_injective f)
  letI := carrier_secondCountable f
  letI : RegularSpace (H f) := inferInstance
  letI : PseudoMetrizableSpace (H f) :=
    PseudoMetrizableSpace.of_regularSpace_secondCountableTopology (H f)
  letI : (internalMeasure f ν).Regular := inferInstance
  infer_instance

/-- The quantitative bound in the exact product topology and product measure. -/
theorem exists_overlap_lower_bound {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution f) C)
    (L : ℝ) (hL : 0 < L) (hbound : ∀ B ∈ C, physicalLength physicalRow B.1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧
      (∀ q, fullMeasure f ν (cell f q) = ENNReal.ofReal c) ∧
      ENNReal.ofReal (c / L) ≤ internalMeasure f ν (carrierOverlap f C) := by
  letI := internalMeasure_outerRegular f ν
  exact exists_overlap_lower_bound_of_outerRegular f ν strict L hL hbound

/-- Finiteness of the supplied strict carrier supplies a positive length bound. -/
theorem carrierOverlap_measure_pos {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution f) C) :
    0 < internalMeasure f ν (carrierOverlap f C) := by
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image C
    (fun B => physicalLength physicalRow B.1) strict.nonempty
  let L := physicalLength physicalRow T.1
  have hL : 0 < L := source_length_pos (strict.isBlock T hT).1
  obtain ⟨c, hc, -, hbound⟩ := exists_overlap_lower_bound f ν strict L hL hmax
  exact (ENNReal.ofReal_pos.mpr (div_pos hc hL)).trans_le hbound

end Psc.NamedPositiveOverlap
