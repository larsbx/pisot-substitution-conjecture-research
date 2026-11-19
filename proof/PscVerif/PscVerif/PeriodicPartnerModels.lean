/-
# Models and missing-hypothesis controls for periodic-partner deductions

These are abstract dynamical and metric models, not substitution tiling spaces.
They verify that the conditional interfaces have nonempty instances and that the
stated elementary hypotheses cannot silently be omitted.  No model here realizes
a strict rank-two PIP3 joining, and no C4 or PSC claim follows.

Pre-code decision: `docs/c4-periodic-partner-formalization-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartner
import PscVerif.PeriodicPartnerCollapse
import PscVerif.PeriodicPartnerDynamics
import PscVerif.PeriodicPartnerDichotomy
import PscVerif.PeriodicPartnerAsymptotic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

namespace Psc.PeriodicPartnerModels

open Function
open Filter
open scoped Topology

/-! ## Finite fibres do not replace injectivity -/

def constantTwo (_ : Fin 2) : Fin 2 := 0

theorem constantTwo_semiconj :
    Semiconj (fun _ : Fin 2 => ()) constantTwo (id : Unit → Unit) := by
  intro x
  rfl

theorem constantTwo_finite_fibre : {x : Fin 2 | (fun _ : Fin 2 => ()) x = ()}.Finite :=
  Set.toFinite _

theorem constantTwo_not_injective : ¬ Injective constantTwo := by
  intro h
  have heq : (0 : Fin 2) = 1 := h rfl
  exact (by decide : (0 : Fin 2) ≠ 1) heq

theorem constantTwo_iterate_positive {n : ℕ} (hn : 0 < n) (x : Fin 2) :
    constantTwo^[n] x = 0 := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n => simp [iterate_succ_apply', constantTwo]

theorem constantTwo_nonperiodic_lift : (1 : Fin 2) ∉ periodicPts constantTwo := by
  rintro ⟨n, hn, hperiod⟩
  have heq := (constantTwo_iterate_positive hn 1).symm.trans hperiod.eq
  exact (by decide : (0 : Fin 2) ≠ 1) heq

/-! ## Injectivity does not replace finiteness -/

def integerSuccessor (x : ℤ) : ℤ := x + 1

theorem integerSuccessor_injective : Injective integerSuccessor := by
  intro x y h
  exact add_right_cancel h

theorem integerSuccessor_semiconj :
    Semiconj (fun _ : ℤ => ()) integerSuccessor (id : Unit → Unit) := by
  intro x
  rfl

theorem integerSuccessor_iterate (n : ℕ) (x : ℤ) :
    integerSuccessor^[n] x = x + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih => simp [iterate_succ_apply', integerSuccessor, ih, add_assoc]

theorem integerSuccessor_nonperiodic_lift : (0 : ℤ) ∉ periodicPts integerSuccessor := by
  rintro ⟨n, hn, hperiod⟩
  have hz : (n : ℤ) = 0 := by
    simpa [integerSuccessor_iterate] using hperiod.eq
  exact Nat.ne_of_gt hn (Int.ofNat_eq_zero.mp hz)

theorem integerSuccessor_infinite_fibre :
    Set.Infinite {x : ℤ | (fun _ : ℤ => ()) x = ()} := by
  simpa using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℤ))

/-! ## Concrete local branch data with a strict star relation

The real coordinate is the branch position.  Colours `1` and `2` may share a
right ray; colour `0` is their common partner and shares no ray with either.
This is an abstract model of local statements only, not a legal tiling space.
-/

namespace BranchModel

open Psc.PeriodicPartnerDynamics

abbrev State := ℝ × Fin 3

def inflate (S : State) : State := (2 * S.1, S.2)

def translate (t : ℝ) (S : State) : State := (S.1 - t, S.2)

def base (S : State) : ℝ := S.1

def baseInflate (x : ℝ) : ℝ := 2 * x

def endsAt (S : State) (y : ℝ) (b : Fin 3) : Prop := y = S.1 ∧ b = S.2

def agreeRight (S U : State) (r : ℝ) : Prop :=
  S = U ∨ S.1 = U.1 ∧ S.1 ≤ r ∧ S.2 ≠ 0 ∧ U.2 ≠ 0

def partner (S U : State) : Prop :=
  S.1 = U.1 ∧ ((S.2 = 0 ∧ U.2 ≠ 0) ∨ (S.2 ≠ 0 ∧ U.2 = 0))

theorem inflate_injective : Injective inflate := by
  intro S U h
  apply Prod.ext
  · have heq := congrArg Prod.fst h
    dsimp [inflate] at heq
    linarith
  · simpa only [inflate] using congrArg (fun z : State => z.2) h

theorem translate_injective (t : ℝ) : Injective (translate t) := by
  intro S U h
  apply Prod.ext
  · have heq := congrArg Prod.fst h
    dsimp [translate] at heq
    linarith
  · simpa only [translate] using congrArg (fun z : State => z.2) h

theorem base_semiconj : Semiconj base inflate baseInflate := fun _ => rfl

theorem base_fibre_finite (q : ℝ) : {S : State | base S = q}.Finite := by
  apply (Set.finite_range (fun a : Fin 3 => (q, a))).subset
  intro S hS
  exact ⟨S.2, Prod.ext hS.symm rfl⟩

theorem partner_same_fibre {S U : State} (h : partner S U) : base S = base U := h.1

theorem partner_distinct {S U : State} (h : partner S U) : S ≠ U := by
  rintro rfl
  rcases h.2 with ⟨h0, hn⟩ | ⟨hn, h0⟩ <;> exact hn h0

theorem partner_translate {S U : State} (h : partner S U) (t : ℝ) :
    partner (translate t S) (translate t U) := by
  exact ⟨by dsimp [translate]; rw [h.1], h.2⟩

theorem partner_not_right_asymptotic {S U : State} (h : partner S U) :
    ¬ ∃ r, agreeRight S U r := by
  rintro ⟨r, hagree⟩
  rcases hagree with heq | ⟨_, _, hs, hu⟩
  · exact partner_distinct h heq
  · rcases h.2 with ⟨h0, _⟩ | ⟨_, h0⟩
    · exact hs h0
    · exact hu h0

theorem translate_zero (S : State) : translate 0 S = S := by simp [translate]

theorem endpoint_unique {S : State} {y : ℝ} {b c : Fin 3}
    (hb : endsAt S y b) (hc : endsAt S y c) : b = c := hb.2.trans hc.2.symm

theorem agree_endpoint {S U : State} {r y : ℝ} {b c : Fin 3}
    (h : agreeRight S U r) (hry : r < y) (hb : endsAt S y b)
    (hc : endsAt U y c) : b = c := by
  rcases h with rfl | ⟨_, hbound, _, _⟩
  · exact endpoint_unique hb hc
  · have : y ≤ r := hb.1.trans_le hbound
    exact False.elim ((not_lt_of_ge this) hry)

theorem agree_translate {S U : State} {y : ℝ} (t : ℝ) (h : agreeRight S U y) :
    agreeRight (translate t S) (translate t U) (y - t) := by
  rcases h with rfl | ⟨hx, hy, hs, hu⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by dsimp [translate]; rw [hx], sub_le_sub_right hy t, hs, hu⟩

theorem endpoint_translate {S : State} {y : ℝ} {b : Fin 3} (t : ℝ)
    (h : endsAt S y b) : endsAt (translate t S) (y - t) b := by
  exact ⟨by dsimp [translate]; rw [h.1], h.2⟩

theorem agree_inflate {S U : State} {y : ℝ} (h : agreeRight S U y) :
    agreeRight (inflate S) (inflate U) (2 * y) := by
  rcases h with rfl | ⟨hx, hy, hs, hu⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by dsimp [inflate]; rw [hx], mul_le_mul_of_nonneg_left hy (by norm_num), hs, hu⟩

theorem endpoint_inflate {S : State} {y : ℝ} {b : Fin 3} (h : endsAt S y b) :
    endsAt (inflate S) (2 * y) (id b) := by
  exact ⟨by dsimp [inflate]; rw [h.1], h.2⟩

theorem origin_fixed (a : Fin 3) : inflate (0, a) = (0, a) := by simp [inflate]

theorem origin_periodic (a : Fin 3) : (0, a) ∈ periodicPts inflate :=
  ⟨1, by decide, by
    change inflate^[1] (0, a) = (0, a)
    simpa only [iterate_one] using origin_fixed a⟩

theorem translated_periodic_pair {S U : State} (h : ∃ r, agreeRight S U r) :
    ∃ t, translate t S ∈ periodicPts inflate ∧ translate t U ∈ periodicPts inflate := by
  obtain ⟨r, h⟩ := h
  have hx : S.1 = U.1 := by
    rcases h with rfl | h
    · rfl
    · exact h.1
  refine ⟨S.1, ?_, ?_⟩
  · simpa [translate] using origin_periodic S.2
  · simpa [translate, hx] using origin_periodic U.2

theorem leaves_agree (x : ℝ) : agreeRight (x, 1) (x, 2) x := by
  exact Or.inr ⟨rfl, le_rfl, by change (1 : Fin 3) ≠ 0; decide,
    by change (2 : Fin 3) ≠ 0; decide⟩

theorem two_strict_links (x : ℝ) : partner (x, 0) (x, 1) ∧ partner (x, 0) (x, 2) := by
  exact ⟨⟨rfl, Or.inl ⟨rfl, by change (1 : Fin 3) ≠ 0; decide⟩⟩,
    ⟨rfl, Or.inl ⟨rfl, by change (2 : Fin 3) ≠ 0; decide⟩⟩⟩

/-- The complete primitive branch contract is satisfiable. -/
theorem branch_laws : RightBranchLaws inflate translate 2 id agreeRight endsAt where
  translate_zero := translate_zero
  endpoint_unique := endpoint_unique
  agree_endpoint := agree_endpoint
  agree_translate := agree_translate
  endpoint_translate := endpoint_translate
  agree_inflate := agree_inflate
  endpoint_inflate := endpoint_inflate

/-- Here the named periodicization input is proved from explicit formulas. -/
theorem periodicization : BDSPeriodicization inflate translate (RightAsymptotic agreeRight) := by
  intro S U _ h
  exact translated_periodic_pair h

theorem origin_fibre : R4ZeroFibre inflate base 0 endsAt := by
  intro S b _ h
  exact h.1.symm

theorem branch_witness (x : ℝ) : BranchAt agreeRight endsAt (x, 1) (x, 2) x 1 2 := by
  exact ⟨leaves_agree x, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by decide⟩

theorem asymptotic_translate (t : ℝ) {S U : State} (h : RightAsymptotic agreeRight S U) :
    RightAsymptotic agreeRight (translate t S) (translate t U) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r - t, agree_translate t hr⟩

/-- Lemma P applies to a distinct three-point star at every branch location. -/
theorem promoted_star_triple (x : ℝ) :
    ∃ t n, 0 < n ∧
      partner (translate t (x, 0)) (translate t (x, 1)) ∧
      partner (translate t (x, 0)) (translate t (x, 2)) ∧
      inflate^[n] (translate t (x, 0)) = translate t (x, 0) ∧
      inflate^[n] (translate t (x, 1)) = translate t (x, 1) ∧
      inflate^[n] (translate t (x, 2)) = translate t (x, 2) ∧
      translate t (x, 0) ≠ translate t (x, 1) ∧
      translate t (x, 0) ≠ translate t (x, 2) ∧
      translate t (x, 1) ≠ translate t (x, 2) := by
  obtain ⟨t, n, q, hn, hz1, hz2, hT, hS, hU, _, _, _, _, hTS, hTU, hSU, _⟩ :=
    periodic_triple_of_asymptotic_partners inflate baseInflate base translate partner
      (RightAsymptotic agreeRight) inflate_injective base_semiconj base_fibre_finite
      translate_injective (fun t _ _ h => partner_translate h t) asymptotic_translate
      partner_same_fibre partner_distinct periodicization
      (two_strict_links x).1 (two_strict_links x).2 (branch_laws.branch_ne (branch_witness x))
      ⟨x, leaves_agree x⟩
  exact ⟨t, n, hn, hz1, hz2, hT, hS, hU, hTS, hTU, hSU⟩

/-- The actual two-step/identity-fibre theorem is used, with all its inputs discharged. -/
theorem zero_fibre_from_endpoint_test :
    base (0, 1) = 0 ∧ base (0, 2) = 0 := by
  apply (ternary_two_step_iff_zero_fibre branch_laws (by norm_num) periodicization
    baseInflate base 0 inflate_injective base_semiconj (base_fibre_finite 0)
    (by simp [baseInflate]) origin_fibre (branch_witness 0)).mp
  decide

/-- The common-partner consumer also has a complete, nontrivial instance. -/
theorem zero_fibre_star_triple :
    base (0, 0) = 0 ∧ base (0, 1) = 0 ∧ base (0, 2) = 0 ∧
      ∃ n > 0, inflate^[n] (0, 0) = (0, 0) ∧
        inflate^[n] (0, 1) = (0, 1) ∧ inflate^[n] (0, 2) = (0, 2) := by
  apply ternary_zero_fibre_periodic_triple branch_laws (by norm_num) periodicization
    baseInflate base 0 inflate_injective base_semiconj (base_fibre_finite 0)
    (by simp [baseInflate]) origin_fibre (branch_witness 0)
  · decide
  · rfl

/-! The same model simultaneously satisfies the branch and metric interfaces.
The metric is pulled back from a concrete embedding.  A fixed centre-status
coordinate separates the centre from both leaves, while the leaf-colour
distance decays as a branch moves left.  Thus the metric is compatible with the
exact rays above.  No global metric instance for other uses of `ℝ × Fin 3` is
installed. -/

def centreFlag (a : Fin 3) : ℝ := if a = 0 then 0 else 1

noncomputable def metricEmbedding (S : State) : ℝ × (ℝ × ℝ) :=
  (S.1, (centreFlag S.2, (S.2.val : ℝ) / (1 + |S.1|)))

theorem metricEmbedding_injective : Injective metricEmbedding := by
  intro S U h
  apply Prod.ext
  · exact congrArg (fun z : ℝ × (ℝ × ℝ) => z.1) h
  · apply Fin.ext
    have hx : S.1 = U.1 := congrArg (fun z : ℝ × (ℝ × ℝ) => z.1) h
    have hc : (S.2.val : ℝ) / (1 + |S.1|) =
        (U.2.val : ℝ) / (1 + |U.1|) :=
      congrArg (fun z : ℝ × (ℝ × ℝ) => z.2.2) h
    rw [← hx] at hc
    have hd : (1 + |S.1| : ℝ) ≠ 0 := by positivity
    have hval : (S.2.val : ℝ) = (U.2.val : ℝ) := (div_left_inj' hd).mp hc
    exact_mod_cast hval

noncomputable abbrev stateMetricSpace : MetricSpace State :=
  MetricSpace.induced metricEmbedding metricEmbedding_injective inferInstance

noncomputable local instance : MetricSpace State := stateMetricSpace

noncomputable def exactAgreement : Psc.PeriodicPartnerCollapse.AgreementData State inflate 2 where
  Agree := fun _ S U => S = U
  restrict := fun _ _ h => h
  inflate := fun _ h => congrArg inflate h
  controls_dist := by
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro S U h
    change S = U at h
    simpa [h] using hε

theorem common_origin_patch {S U : State} {a : Fin 3} (_ : agreeRight S U 0)
    (hS : endsAt S 0 a) (hU : endsAt U 0 a) : exactAgreement.Agree 1 S U :=
  Prod.ext (hS.1.symm.trans hU.1) (hS.2.symm.trans hU.2)

theorem state_dist_eq (S U : State) :
    dist S U = max |S.1 - U.1|
      (max |centreFlag S.2 - centreFlag U.2|
        |(S.2.val : ℝ) / (1 + |S.1|) - (U.2.val : ℝ) / (1 + |U.1|)|) := rfl

theorem leaf_distance_bound {S U : State} (hx : S.1 = U.1)
    (hS : S.2 ≠ 0) (hU : U.2 ≠ 0) : dist S U ≤ 2 / (1 + |S.1|) := by
  have hd : 0 < 1 + |S.1| := by positivity
  have hs0 : (0 : ℝ) ≤ S.2.val := by positivity
  have hu0 : (0 : ℝ) ≤ U.2.val := by positivity
  have hs2 : (S.2.val : ℝ) ≤ 2 := by exact_mod_cast (Nat.le_of_lt_succ S.2.is_lt)
  have hu2 : (U.2.val : ℝ) ≤ 2 := by exact_mod_cast (Nat.le_of_lt_succ U.2.is_lt)
  have hnum : |(S.2.val : ℝ) - (U.2.val : ℝ)| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  rw [state_dist_eq, ← hx]
  simp only [centreFlag, ite_eq_right hS, ite_eq_right hU, sub_self, abs_zero]
  apply max_le (by positivity)
  apply max_le (by positivity)
  rw [← sub_div, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hnum hd.le

/-- A centred window exists when equal right rays begin at or before `-R`.
Unlike equality-only agreement, this accepts the two distinct leaf colours. -/
noncomputable def rayAgreement : Psc.PeriodicPartnerCollapse.AgreementData State inflate 2 where
  Agree := fun R S U => S = U ∨ S.1 = U.1 ∧ S.2 ≠ 0 ∧ U.2 ≠ 0 ∧ R ≤ -S.1
  restrict := by
    intro r R S U _ hr h
    rcases h with h | ⟨hx, hs, hu, hR⟩
    · exact Or.inl h
    · exact Or.inr ⟨hx, hs, hu, hr.trans hR⟩
  inflate := by
    intro R S U _ h
    rcases h with rfl | ⟨hx, hs, hu, hR⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨by dsimp [inflate]; rw [hx], hs, hu, ?_⟩
      dsimp [inflate]
      linarith
  controls_dist := by
    intro ε hε
    refine ⟨3 / ε, by positivity, ?_⟩
    intro S U h
    rcases h with rfl | ⟨hx, hs, hu, hR⟩
    · simpa using hε
    · have hd : 0 < 1 + |S.1| := by positivity
      have hbound : 3 / ε ≤ |S.1| := hR.trans (neg_le_abs S.1)
      have hmul : 3 ≤ ε * |S.1| := by
        calc
          3 = ε * (3 / ε) := by field_simp
          _ ≤ ε * |S.1| := mul_le_mul_of_nonneg_left hbound hε.le
      apply (leaf_distance_bound hx hs hu).trans_lt
      apply (div_lt_iff₀ hd).mpr
      nlinarith

theorem ray_window {R r : ℝ} {S U : State} (_ : 0 < R) (hr : r ≤ -R)
    (h : agreeRight S U r) : rayAgreement.Agree R S U := by
  rcases h with h | ⟨hx, hxbound, hs, hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨hx, hs, hu, by linarith⟩

theorem ray_common_origin_patch {S U : State} {a : Fin 3} (h : agreeRight S U 0)
    (hS : endsAt S 0 a) (hU : endsAt U 0 a) : rayAgreement.Agree 1 S U :=
  Or.inl (common_origin_patch h hS hU)

theorem coordinate_distance_le (t : ℝ) (S U : State) :
    |S.1 - U.1| ≤ dist (translate t S) (translate t U) := by
  rw [state_dist_eq]
  have hx : (translate t S).1 - (translate t U).1 = S.1 - U.1 := by
    dsimp [translate]
    ring
  rw [hx]
  exact le_max_left _ _

open Psc.PeriodicPartnerAsymptotic

theorem metric_asymptotic_same_coordinate {S U : State}
    (h : TranslationRightAsymptotic translate S U) : S.1 = U.1 := by
  have hle : |S.1 - U.1| ≤ 0 := ge_of_tendsto' h (fun t => coordinate_distance_le t S U)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- The BDS-shaped metric input is proved directly for this abstract model. -/
theorem metric_periodicization :
    BDSPeriodicization inflate translate (TranslationRightAsymptotic translate) := by
  intro S U _ h
  have hx := metric_asymptotic_same_coordinate h
  refine ⟨S.1, ?_, ?_⟩
  · simpa [translate] using origin_periodic S.2
  · simpa [translate, hx] using origin_periodic U.2

theorem leaf_translation_asymptotic (x : ℝ) :
    TranslationRightAsymptotic translate (x, 1) (x, 2) :=
  translationRightAsymptotic_of_branch_laws branch_laws rayAgreement ray_window
    ⟨x, leaves_agree x⟩

theorem periodicization_from_metric_bridge :
    BDSPeriodicization inflate translate (RightAsymptotic agreeRight) :=
  bdsPeriodicization_of_translationRightAsymptotic rayAgreement agree_translate ray_window
    metric_periodicization

theorem partner_metric_separated {S U : State} (h : partner S U) (t : ℝ) :
    1 ≤ dist (translate t S) (translate t U) := by
  rw [state_dist_eq]
  have hflag : |centreFlag (translate t S).2 - centreFlag (translate t U).2| = 1 := by
    rcases h.2 with ⟨hs, hu⟩ | ⟨hs, hu⟩ <;>
      simp [translate, centreFlag, hs, hu]
  rw [hflag]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem partner_not_metric_asymptotic {S U : State} (h : partner S U) :
    ¬ TranslationRightAsymptotic translate S U := by
  intro hasym
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hasym (partner_metric_separated h)
  norm_num at hfalse

/-- A concrete origin branch satisfies the full endpoint consumer with BDS
stated metrically, using the same metric, rays, and agreement windows. -/
theorem zero_fibre_from_metric_endpoint_test :
    base (0, 1) = 0 ∧ base (0, 2) = 0 := by
  apply (ternary_two_step_iff_zero_fibre_of_metric_BDS branch_laws (by norm_num)
    rayAgreement ray_window metric_periodicization baseInflate base 0 inflate_injective
    base_semiconj (base_fibre_finite 0) (by simp [baseInflate]) origin_fibre
    (branch_witness 0)).mp
  decide

/-- One instance discharges all geometric-interface inputs of the combined E/M
consumer simultaneously.  Its distinct origin leaves belong to the identity
fibre and therefore do not collapse under unshifted inflation. -/
theorem joint_zero_fibre_no_collapse :
    ¬ Tendsto (fun n : ℕ => dist (inflate^[n] (0, 1)) (inflate^[n] (0, 2)))
      atTop (𝓝 0) := by
  apply (Psc.PeriodicPartnerDichotomy.ternary_zero_fibre_iff_not_collapse
    branch_laws (by norm_num) periodicization_from_metric_bridge rayAgreement (fun _ => 1)
    (by intro a; norm_num) ray_common_origin_patch baseInflate base 0 inflate_injective
    base_semiconj (base_fibre_finite 0) (by simp [baseInflate]) origin_fibre
    (branch_witness 0)).mp
  exact ⟨rfl, rfl⟩

end BranchModel

/-! ## Expansion and positive seed radii are indispensable -/

open Psc.PeriodicPartnerCollapse

def boundedAgreement (R x y : ℝ) : Prop := x = y ∨ R ≤ 1

/-- All local-agreement contracts hold at expansion one; convergence still fails. -/
def identityAgreementOne : AgreementData ℝ id 1 where
  Agree := boundedAgreement
  restrict := by
    intro r R x y _ hle h
    rcases h with hxy | hR
    · exact Or.inl hxy
    · exact Or.inr (hle.trans hR)
  inflate := by
    intro R x y _ h
    simpa using h
  controls_dist := by
    intro ε hε
    refine ⟨2, by norm_num, fun x y h => ?_⟩
    rcases h with rfl | hbad
    · simpa using hε
    · norm_num at hbad

theorem identity_one_positive_agreement : identityAgreementOne.Agree 1 0 1 :=
  Or.inr le_rfl

def zeroRadiusAgreement (R x y : ℝ) : Prop := x = y ∨ R ≤ 0

/-- Radius zero can persist under genuine expansion without making points close. -/
def identityAgreementZero : AgreementData ℝ id 2 where
  Agree := zeroRadiusAgreement
  restrict := by
    intro r R x y _ hle h
    rcases h with hxy | hR
    · exact Or.inl hxy
    · exact Or.inr (hle.trans hR)
  inflate := by
    intro R x y hR h
    rcases h with hxy | hbad
    · exact Or.inl hxy
    · exact False.elim ((not_le_of_gt hR) hbad)
  controls_dist := by
    intro ε hε
    refine ⟨1, by norm_num, fun x y h => ?_⟩
    rcases h with rfl | hbad
    · simpa using hε
    · norm_num at hbad

theorem identity_zero_agreement : identityAgreementZero.Agree 0 0 1 := Or.inr le_rfl

theorem identity_distances_not_tendsto_zero :
    ¬ Tendsto (fun n : ℕ => dist ((id : ℝ → ℝ)^[n] 0) (id^[n] 1)) atTop (𝓝 0) := by
  intro h
  simp only [iterate_id, id_eq, Real.dist_eq, zero_sub, abs_neg, abs_one] at h
  have hneq : (1 : ℝ) ≠ 0 := by norm_num
  exact hneq (tendsto_nhds_unique tendsto_const_nhds h)

/-! ## A nontrivial expanding-agreement model with orbit collapse -/

noncomputable def halve (x : ℝ) : ℝ := x / 2

def contractionAgreement : AgreementData ℝ halve 2 where
  Agree := fun R x y => dist x y * R ≤ 1
  restrict := by
    intro r R x y _ hle h
    exact (mul_le_mul_of_nonneg_left hle dist_nonneg).trans h
  inflate := by
    intro R x y _ h
    change |x / 2 - y / 2| * (2 * R) ≤ 1
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |x - y| / 2 * (2 * R) = |x - y| * R := by ring
      _ ≤ 1 := by simpa only [Real.dist_eq] using h
  controls_dist := by
    intro ε hε
    refine ⟨2 / ε, div_pos (by norm_num) hε, fun x y h => ?_⟩
    have hbound : dist x y * 2 ≤ ε := by
      have h' : dist x y * 2 / ε ≤ 1 := by simpa only [mul_div_assoc] using h
      simpa using (div_le_iff₀ hε).mp h'
    linarith

theorem contraction_initial_agreement : contractionAgreement.Agree 1 0 1 := by
  norm_num [contractionAgreement, Real.dist_eq]

/-- The proved metric deduction has a nontrivial concrete instance. -/
theorem contraction_distance_tendsto_zero :
    Tendsto (fun n : ℕ => dist (halve^[n] 0) (halve^[n] 1)) atTop (𝓝 0) :=
  contractionAgreement.distance_tendsto_zero (by norm_num) (by norm_num)
    contraction_initial_agreement

theorem halve_injective : Injective halve := by
  intro x y h
  dsimp [halve] at h
  linarith

/-- These two orbits remain distinct at every finite stage despite their collapse. -/
theorem contraction_iterates_distinct (n : ℕ) : halve^[n] 0 ≠ halve^[n] 1 :=
  (halve_injective.iterate n).ne (by norm_num)

/-- A partial endpoint predicate on the unit interval.  It is deliberately an
abstract local model, not an endpoint assignment to physical substitution tilings. -/
def contractionEnd (x : ℝ) (a : Fin 2) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ ((a = 0 ∧ x ≤ 1 / 2) ∨ (a = 1 ∧ 1 / 2 < x))

/-- Under halving both endpoint labels become zero.  The remaining metric and
positive-patch contracts follow directly from interval bounds. -/
def contractionEndpoints : RightEndpointData contractionAgreement (Fin 2) constantTwo where
  CommonRightRay := fun x y => (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1)
  EndsAtZero := contractionEnd
  tileLength := fun _ => 1
  tileLength_pos := by intro a; norm_num
  ray_inflate := by
    rintro x y ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    dsimp [halve]
    constructor <;> constructor <;> linarith
  endpoint_inflate := by
    intro x a hx
    obtain ⟨hx0, hx1, _⟩ := hx
    refine ⟨?_, ?_, Or.inl ⟨rfl, ?_⟩⟩ <;> dsimp [halve] <;> linarith
  common_patch := by
    intro x y a _ hx hy
    obtain ⟨hx0, hx1, _⟩ := hx
    obtain ⟨hy0, hy1, _⟩ := hy
    change dist x y * 1 ≤ 1
    rw [mul_one, Real.dist_eq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem contraction_distinct_initial_endpoints :
    contractionEndpoints.EndsAtZero 0 0 ∧ contractionEndpoints.EndsAtZero 1 1 := by
  constructor
  · exact ⟨by norm_num, by norm_num, Or.inl ⟨rfl, by norm_num⟩⟩
  · exact ⟨by norm_num, by norm_num, Or.inr ⟨rfl, by norm_num⟩⟩

/-- The full endpoint version of Lemma M is applied to different starting
points with different initial labels and a one-step label merger. -/
theorem contraction_collapse_from_endpoint_merge :
    Tendsto (fun n : ℕ => dist (halve^[n] 0) (halve^[n] 1)) atTop (𝓝 0) := by
  apply contractionEndpoints.distance_tendsto_zero_of_endpoint_merge (by norm_num)
    (x := 0) (y := 1) (a := 0) (b := 1) (m := 1)
  · exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  · exact contraction_distinct_initial_endpoints.1
  · exact contraction_distinct_initial_endpoints.2
  · rfl

end Psc.PeriodicPartnerModels
