import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerOriginSeparation

/-! The next-tile return on the literal family's legal transversal and its
continuous roof coboundary, derived from the existing real vector lift. -/

namespace Psc.C4FamilySymbolicSection

open Function Filter Matrix Set
open scoped Topology
open Psc.ParameterFamilyTiling (geometry expansion_gt_one)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (mat_eq pisotData)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerLocalTopology (LocalHull ofExact translate translate_translate)
open Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerRealizationFinite (dot_realVec)

variable {k : ℕ} {hk : 1 ≤ k}

local notation "G" => geometry k hk
local notation "P" => pisotData k hk
local notation "V" => realVec P (inflateH_bijective k hk)

/-- The right-hand tile starts at the origin on the canonical transversal. -/
abbrev Transversal (k : ℕ) (hk : 1 ≤ k) :=
  {T : (geometry k hk).Hull // (origin T).2 = 0}

noncomputable def roof (B : Transversal k hk) : ℝ := (G).ℓ (origin B.1).1

theorem roof_pos (B : Transversal k hk) : 0 < roof B := (G).ℓ_pos _

/-- The origin after reanchoring at a tile start is that tile, translated to zero. -/
theorem origin_reanchor {T : (G).Hull} {q : Fin 3 × ℝ} (hq : q ∈ T.1) :
    origin (LengthSubst.translate q.2 T) = (q.1, 0) := by
  have htile : tileAt T q.2 = q :=
    tileAt_eq hq ⟨le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos _)⟩
  rw [origin_translate, htile, sub_self]

noncomputable def reanchor (T : (G).Hull) (q : Fin 3 × ℝ) (hq : q ∈ T.1) :
    Transversal k hk :=
  ⟨LengthSubst.translate q.2 T, congrArg Prod.snd (origin_reanchor hq)⟩

/-- The next boundary to the right lies at the full length of the origin tile. -/
noncomputable def next (B : Transversal k hk) : Transversal k hk :=
  ⟨LengthSubst.translate (roof B) B.1, by
    have h := tileAt_next (tileAt_spec B.1 0).1
    change (tileAt B.1 ((origin B.1).2 + roof B)).2 = (origin B.1).2 + roof B at h
    rw [B.2, zero_add] at h
    rw [origin_translate, h, sub_self]⟩

theorem continuous_next : Continuous (next (k := k) (hk := hk)) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro B
  have h := (Psc.PeriodicPartnerOriginContinuity.isLocallyConstant_origin
    (S := G)).eventually_eq B.1
  have hh := (continuous_subtype_val.tendsto B).eventually h
  refine ((LengthSubst.continuous_translate (roof B)).comp
    continuous_subtype_val).continuousAt.congr ?_
  filter_upwards [hh] with B' hB'
  change origin B'.1 = origin B.1 at hB'
  change LengthSubst.translate (roof B) B'.1 = LengthSubst.translate (roof B') B'.1
  simp [roof, hB']

private theorem mat_apply (v : Fin 3 → ℝ) :
    mat G *ᵥ v = ![v 1 + 2 * v 2, v 0 + (k : ℝ) * v 1 + v 2, v 1] := by
  rw [mat_eq, Psc.ParameterFamilyPisot.incidenceQ_eq]
  funext a
  fin_cases a <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply, add_assoc]

private theorem mat_det : (mat G).det = 2 := by
  rw [mat_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Psc.ParameterFamilyPisot.determinant]
  norm_num

/-- Integral vectors cannot contract to zero under this invertible incidence
matrix unless they already vanish. -/
theorem eq_zero_of_lattice_of_dot_zero {v : Fin 3 → ℝ} (hv : v ∈ lattice (Fin 3))
    (h : (G).ℓ ⬝ᵥ v = 0) : v = 0 := by
  have hproj : (P).proj v = v := by simp [PisotData.proj, h]
  have hlim := (P).tendsto_pow_proj_zero (d := fun _ => v) (fun _ => le_rfl)
  simp only [hproj] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds (0 : Fin 3 → ℝ)
    (by norm_num : (0 : ℝ) < 1))).exists
  have hnorm : ‖(mat G ^ n) *ᵥ v‖ < 1 := by simpa [Metric.mem_ball] using hn
  have hL := pow_mulVec_mem_lattice G hv n
  have hzero : (mat G ^ n) *ᵥ v = 0 := by
    funext a
    obtain ⟨z, hz⟩ := hL a
    have ha := (norm_le_pi_norm (f := (mat G ^ n) *ᵥ v) a).trans_lt hnorm
    rw [← hz, Real.norm_eq_abs, abs_lt] at ha
    have hz' : z = 0 := by
      have h₁ : (-1 : ℤ) < z := by exact_mod_cast ha.1
      have h₂ : z < (1 : ℤ) := by exact_mod_cast ha.2
      omega
    simpa [hz'] using hz.symm
  have hunit : IsUnit (mat G) := (Matrix.isUnit_iff_isUnit_det (mat G)).mpr <| by
    rw [mat_det]
    norm_num
  exact Matrix.mulVec_injective_iff_isUnit.mpr (hunit.pow n) (by simpa using hzero)

private theorem right_pos (a : Fin 3) : 0 < (P).u a := by
  have hβ : 0 < (G).β := (G).β_pos
  have he := (P).u_eigen
  rw [mat_apply] at he
  have h₀ : (P).u 1 + 2 * (P).u 2 = (G).β * (P).u 0 := congrFun he 0
  have h₂ : (P).u 1 = (G).β * (P).u 2 := congrFun he 2
  have hu₂ : 0 < (P).u 2 := by
    by_contra! h₂'
    have h₁' : (P).u 1 ≤ 0 := h₂ ▸ mul_nonpos_of_nonneg_of_nonpos hβ.le h₂'
    have h₀' : (P).u 0 ≤ 0 := nonpos_of_mul_nonpos_right
      (h₀ ▸ (by linarith : (P).u 1 + 2 * (P).u 2 ≤ 0)) hβ
    have hsum : (G).ℓ ⬝ᵥ (P).u ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      apply mul_nonpos_of_nonneg_of_nonpos ((G).ℓ_pos j).le
      fin_cases j
      · exact h₀'
      · exact h₁'
      · exact h₂'
    rw [(P).dot_u] at hsum
    linarith
  have hu₁ : 0 < (P).u 1 := h₂ ▸ mul_pos hβ hu₂
  have hu₀ : 0 < (P).u 0 := pos_of_mul_pos_right
    (h₀ ▸ (by linarith : 0 < (P).u 1 + 2 * (P).u 2)) hβ.le
  fin_cases a
  · exact hu₀
  · exact hu₁
  · exact hu₂

/-- The mean tile length, with the right PF vector normalized to total mass one. -/
noncomputable def meanRoof (k : ℕ) (hk : 1 ≤ k) : ℝ := (∑ a, (pisotData k hk).u a)⁻¹

theorem meanRoof_pos : 0 < meanRoof k hk :=
  inv_pos.mpr (Finset.sum_pos (fun a _ => right_pos (hk := hk) a) Finset.univ_nonempty)

private theorem vec_next (B : Transversal k hk) :
    V (next B).1 - V B.1 - roof B • (P).u = -Pi.single (origin B.1).1 1 := by
  have htorus : (V (next B).1 : Torus (Fin 3)) =
      ((V B.1 + roof B • (P).u : Fin 3 → ℝ) : Torus (Fin 3)) := by
    rw [QuotientAddGroup.mk_add]
    exact torusRealize_translate P (inflateH_bijective k hk) (expansion_gt_one k hk) _ _
  have hl : V (next B).1 - V B.1 - roof B • (P).u ∈ lattice (Fin 3) := by
    simpa only [sub_add_eq_sub_sub] using QuotientAddGroup.eq_iff_sub_mem.mp htorus
  have hsingle : (Pi.single (origin B.1).1 1 : Fin 3 → ℝ) ∈ lattice (Fin 3) :=
    ((P).near_bound (Or.inl (Or.inr ⟨(origin B.1).1, rfl⟩))).1
  have hzero := eq_zero_of_lattice_of_dot_zero (add_mem hl hsingle) (by
    rw [dotProduct_add, dotProduct_sub, dotProduct_sub, dot_realVec, dot_realVec,
      B.2, (next B).2, dotProduct_smul, (P).dot_u, dotProduct_single]
    simp [roof])
  exact eq_neg_of_add_eq_zero_left hzero

/-- Continuous height correction at a tile boundary, from the real lift. -/
noncomputable def correction (B : Transversal k hk) : ℝ :=
  meanRoof k hk * ∑ a, V B.1 a

theorem continuous_correction : Continuous (correction (k := k) (hk := hk)) := by
  have hv := (Psc.PeriodicPartnerRealizationContinuity.continuous_realVec
    P (inflateH_bijective k hk)).comp
    (continuous_subtype_val : Continuous ((↑) : Transversal k hk → (G).Hull))
  unfold correction
  exact continuous_const.mul (continuous_finsetSum Finset.univ fun a _ => (continuous_apply a).comp hv)

/-- The physical roof and the constant mean roof differ by an exact coboundary. -/
theorem roof_eq_mean_add_coboundary (B : Transversal k hk) :
    roof B = meanRoof k hk + correction (next B) - correction B := by
  have h : (∑ a, V (next B).1 a) - (∑ a, V B.1 a) -
      roof B * (∑ a, (P).u a) = -1 := by
    simpa only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true]
      using congrArg (fun w : Fin 3 → ℝ => ∑ a, w a) (vec_next B)
  have hc : meanRoof k hk * (∑ a, (P).u a) = 1 :=
    inv_mul_cancel₀ (ne_of_gt <| inv_pos.mp (meanRoof_pos (k := k) (hk := hk)))
  have he := congrArg (fun x => meanRoof k hk * x) h
  simp only [mul_sub, mul_neg, mul_one, ← mul_assoc] at he
  rw [mul_assoc (meanRoof k hk) (roof B), mul_comm (roof B), ← mul_assoc, hc, one_mul] at he
  unfold correction
  linarith

/-- The corrected section advances by exactly the constant roof. -/
noncomputable def corrected (B : Transversal k hk) : LocalHull G :=
  translate G (-correction B) (ofExact G B.1)

theorem corrected_next (B : Transversal k hk) :
    corrected (next B) = translate G (meanRoof k hk) (corrected B) := by
  have h := roof_eq_mean_add_coboundary B
  unfold corrected
  change translate G (-correction (next B)) (translate G (roof B) (ofExact G B.1)) = _
  rw [translate_translate, translate_translate]
  congr 1
  linarith


theorem continuous_corrected : Continuous (corrected (k := k) (hk := hk)) :=
  (Psc.PeriodicPartnerLocalTopology.continuous_translate G).comp
    ((continuous_correction.neg).prodMk
      ((Psc.PeriodicPartnerLocalTopology.continuous_ofExact G).comp continuous_subtype_val))

theorem continuous_roof : Continuous (roof (k := k) (hk := hk)) :=
  ((Psc.PeriodicPartnerOriginContinuity.isLocallyConstant_origin (S := G)).comp
    (fun p => (G).ℓ p.1)).continuous.comp continuous_subtype_val

/-- A physical strip at the original tile starts, using the half-open convention. -/
def PhysicalStrip (k : ℕ) (hk : 1 ≤ k) : Set (Transversal k hk × ℝ) :=
  {p | p.2 ∈ Ico 0 (roof p.1)}

noncomputable def physical (p : Transversal k hk × ℝ) : LocalHull G :=
  translate G p.2 (ofExact G p.1.1)

private theorem origin_physical {p : Transversal k hk × ℝ} (hp : p ∈ PhysicalStrip k hk) :
    origin (physical p).toHull = ((origin p.1.1).1, -p.2) := by
  change origin (LengthSubst.translate p.2 p.1.1) = _
  have htile : tileAt p.1.1 p.2 = origin p.1.1 := by
    apply tileAt_eq (tileAt_spec p.1.1 0).1
    change (origin p.1.1).2 ≤ p.2 ∧ p.2 < (origin p.1.1).2 + roof p.1
    rw [p.1.2, zero_add]
    exact ⟨hp.1, hp.2⟩
  rw [origin_translate, htile, p.1.2, zero_sub]

/-- There is no earlier positive return to the original tile-start section. -/
theorem no_boundary_before_roof (B : Transversal k hk) {s : ℝ}
    (hs : 0 < s) (hr : s < roof B) :
    (origin (LengthSubst.translate s B.1)).2 ≠ 0 := by
  have h := congrArg (fun q : Fin 3 × ℝ => q.2) (origin_physical
    (show (B, s) ∈ PhysicalStrip k hk from ⟨hs.le, hr⟩))
  change (origin (LengthSubst.translate s B.1)).2 = -s at h
  rw [h]
  exact neg_ne_zero.mpr hs.ne'

theorem physical_injOn : InjOn (physical (k := k) (hk := hk)) (PhysicalStrip k hk) := by
  intro p hp q hq h
  have htime := congrArg (fun T : LocalHull G => (origin T.toHull).2) h
  rw [origin_physical hp, origin_physical hq] at htime
  have hs : p.2 = q.2 := neg_injective htime
  have he := congrArg LocalHull.toHull h
  change LengthSubst.translate p.2 p.1.1 = LengthSubst.translate q.2 q.1.1 at he
  rw [← hs] at he
  exact Prod.ext (Subtype.ext (LengthSubst.translate_injective _ he)) hs

theorem exists_physical (T : LocalHull G) :
    ∃ p ∈ PhysicalStrip k hk, physical p = T := by
  let q := origin T.toHull
  have hq := tileAt_spec T.toHull 0
  let B := reanchor T.toHull q hq.1
  refine ⟨(B, -q.2), ?_, ?_⟩
  · have ha : origin B.1 = (q.1, 0) := origin_reanchor hq.1
    have hs : q.2 ≤ 0 ∧ 0 < q.2 + (G).ℓ q.1 := hq.2
    change 0 ≤ -q.2 ∧ -q.2 < (G).ℓ (origin B.1).1
    rw [ha]
    constructor <;> linarith [hs.1, hs.2]
  · change translate G (-q.2) (translate G q.2 (ofExact G T.toHull)) = T
    rw [translate_translate, neg_add_cancel, Psc.PeriodicPartnerLocalTopology.translate_zero]
    cases T
    rfl

open Psc.PeriodicPartnerHullCompact (rightTile leftTile rightTile_mem leftTile_mem
  rightTile_start_succ leftTile_end_succ rightTile_start_lower leftTile_start_upper
  rightTile_cover leftTile_cover)

private theorem next_reanchor {T : (G).Hull} {q r : Fin 3 × ℝ} (hq : q ∈ T.1)
    (hr : r ∈ T.1) (h : r.2 = q.2 + (G).ℓ q.1) :
    next (reanchor T q hq) = reanchor T r hr := by
  have hroof : roof (reanchor T q hq) = (G).ℓ q.1 := by
    unfold roof
    rw [show origin (reanchor T q hq).1 = (q.1, 0) from origin_reanchor hq]
  apply Subtype.ext
  change LengthSubst.translate (roof (reanchor T q hq)) (LengthSubst.translate q.2 T) =
    LengthSubst.translate r.2 T
  rw [LengthSubst.translate_translate, hroof, h, add_comm]

private noncomputable def right (T : (G).Hull) (n : ℕ) :=
  reanchor T (rightTile T n) (rightTile_mem T n)

private noncomputable def left (T : (G).Hull) (n : ℕ) :=
  reanchor T (leftTile T n) (leftTile_mem T n)

private theorem right_succ (T : (G).Hull) (n : ℕ) :
    next (right T n) = right T (n + 1) :=
  next_reanchor _ _ (rightTile_start_succ T n)

private theorem left_succ (T : (G).Hull) (n : ℕ) :
    next (left T (n + 1)) = left T n :=
  next_reanchor _ _ (leftTile_end_succ T n).symm

private theorem right_zero (B : Transversal k hk) : right B.1 0 = B := by
  apply Subtype.ext
  change LengthSubst.translate (origin B.1).2 B.1 = B.1
  rw [B.2, LengthSubst.translate_zero]

private theorem left_zero (B : Transversal k hk) : left B.1 0 = B := by
  apply Subtype.ext
  change LengthSubst.translate (origin B.1).2 B.1 = B.1
  rw [B.2, LengthSubst.translate_zero]

private theorem corrected_right (B : Transversal k hk) (n : ℕ) :
    corrected (right B.1 n) = translate G (n * meanRoof k hk) (corrected B) := by
  induction n with
  | zero => simp [right_zero]
  | succ n ih =>
    rw [← right_succ, corrected_next, ih, translate_translate]
    push_cast
    congr 1
    ring

private theorem corrected_left (B : Transversal k hk) (n : ℕ) :
    corrected (left B.1 n) = translate G (-(n * meanRoof k hk)) (corrected B) := by
  induction n with
  | zero => simp [left_zero]
  | succ n ih =>
    apply (Psc.PeriodicPartnerLocalTopology.translateHomeomorph G (meanRoof k hk)).injective
    change translate G (meanRoof k hk) (corrected (left B.1 (n + 1))) = _
    rw [← corrected_next, left_succ, ih]
    change _ = translate G (meanRoof k hk)
      (translate G (-((↑(n + 1) : ℝ) * meanRoof k hk)) (corrected B))
    rw [translate_translate]
    push_cast
    congr 1
    ring

/-- Adjacent steps in both directions enumerate every tile. -/
theorem exists_right_or_left {T : (G).Hull} {q : Fin 3 × ℝ} (hq : q ∈ T.1) :
    ∃ n, q = rightTile T n ∨ q = leftTile T n := by
  have hm := minLen_pos (S := G)
  have hqs : q.2 ∈ (G).supp q :=
    ⟨le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos _)⟩
  by_cases hside : (origin T).2 ≤ q.2
  · obtain ⟨N, hN⟩ := exists_nat_gt ((q.2 - (origin T).2) / minLen G)
    have hb := rightTile_start_lower T N
    have hlt : q.2 < (rightTile T N).2 := by
      linarith [(div_lt_iff₀ hm).mp hN]
    obtain ⟨i, _, hi⟩ := rightTile_cover T N hside hlt
    exact ⟨i, Or.inl ((T.2.1 _).unique ⟨hq, hqs⟩ ⟨rightTile_mem T i, hi⟩)⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt (((origin T).2 - q.2) / minLen G)
    have hb := leftTile_start_upper T N
    have hlo : (leftTile T N).2 ≤ q.2 := by
      linarith [(div_lt_iff₀ hm).mp hN]
    obtain ⟨i, _, hi⟩ := leftTile_cover T N hlo (lt_of_not_ge hside)
    exact ⟨i, Or.inr ((T.2.1 _).unique ⟨hq, hqs⟩ ⟨leftTile_mem T i, hi⟩)⟩

private theorem anchored_translate_cases (B D : Transversal k hk) (t : ℝ)
    (h : LengthSubst.translate t B.1 = D.1) :
    ∃ n, D = right B.1 n ∨ D = left B.1 n := by
  have hstart : (tileAt B.1 t).2 = t := by
    have hh := congrArg (fun U : (G).Hull => (origin U).2) h
    rw [origin_translate, D.2] at hh
    exact sub_eq_zero.mp hh
  let q := tileAt B.1 t
  have hq := (tileAt_spec B.1 t).1
  have hD : reanchor B.1 q hq = D := by
    apply Subtype.ext
    change LengthSubst.translate q.2 B.1 = D.1
    rwa [hstart]
  obtain ⟨n, hn | hn⟩ := exists_right_or_left hq
  · refine ⟨n, Or.inl (Subtype.ext ?_)⟩
    change D.1 = LengthSubst.translate (rightTile B.1 n).2 B.1
    rw [← hn]
    exact congrArg Subtype.val hD.symm
  · refine ⟨n, Or.inr (Subtype.ext ?_)⟩
    change D.1 = LengthSubst.translate (leftTile B.1 n).2 B.1
    rw [← hn]
    exact congrArg Subtype.val hD.symm

/-- A fundamental strip for the constant return time, embedded in the actual hull. -/
noncomputable def strip (p : Transversal k hk × ℝ) : LocalHull G :=
  translate G p.2 (corrected p.1)

def ConstantStrip (k : ℕ) (hk : 1 ≤ k) : Set (Transversal k hk × ℝ) :=
  {p | p.2 ∈ Ico 0 (meanRoof k hk)}

theorem continuous_strip : Continuous (strip (k := k) (hk := hk)) :=
  (Psc.PeriodicPartnerLocalTopology.continuous_translate G).comp
    (continuous_snd.prodMk (continuous_corrected.comp continuous_fst))

theorem continuous_physical : Continuous (physical (k := k) (hk := hk)) :=
  (Psc.PeriodicPartnerLocalTopology.continuous_translate G).comp
    (continuous_snd.prodMk ((Psc.PeriodicPartnerLocalTopology.continuous_ofExact G).comp
      (continuous_subtype_val.comp continuous_fst)))

private theorem translate_time_injective (T : LocalHull G) :
    Injective (fun t : ℝ => translate G t T) := by
  intro s t h
  change translate G s T = translate G t T at h
  have he : translate G (-t + s) T = T := by
    rw [← translate_translate, h, translate_translate, neg_add_cancel,
      Psc.PeriodicPartnerLocalTopology.translate_zero]
  linarith [Psc.ParameterFamilyTiling.action_aperiodic k hk T _ he]

theorem strip_injOn : InjOn (strip (k := k) (hk := hk)) (ConstantStrip k hk) := by
  rintro ⟨B, s⟩ hs ⟨D, t⟩ ht hBD
  change s ∈ Ico 0 (meanRoof k hk) at hs
  change t ∈ Ico 0 (meanRoof k hk) at ht
  have hs' := hs.2
  have ht' := ht.2
  have he := congrArg LocalHull.toHull hBD
  change LengthSubst.translate s (LengthSubst.translate (-correction B) B.1) =
    LengthSubst.translate t (LengthSubst.translate (-correction D) D.1) at he
  rw [LengthSubst.translate_translate, LengthSubst.translate_translate] at he
  obtain ⟨n, hn | hn⟩ := anchored_translate_cases B D (s - correction B - (t - correction D))
    (by
      apply LengthSubst.translate_injective (t - correction D)
      rw [LengthSubst.translate_translate, show t - correction D +
        (s - correction B - (t - correction D)) = s + -correction B by ring]
      exact he)
  · have h : translate G s (corrected B) =
        translate G (t + n * meanRoof k hk) (corrected B) := by
      simpa only [strip, hn, corrected_right, translate_translate] using hBD
    have hz := translate_time_injective (corrected B) h
    have hzero : n = 0 := by
      by_contra hn₀
      have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn₀)
      have hn' := mul_le_mul_of_nonneg_right h₁ (meanRoof_pos (k := k) (hk := hk)).le
      linarith [ht.1]
    subst n
    have hst : s = t := by simpa using hz
    exact Prod.ext (by simpa [right_zero] using hn.symm) hst
  · have h : translate G s (corrected B) =
        translate G (t + -(n * meanRoof k hk)) (corrected B) := by
      simpa only [strip, hn, corrected_left, translate_translate] using hBD
    have hz := translate_time_injective (corrected B) h
    have hzero : n = 0 := by
      by_contra hn₀
      have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn₀)
      have hn' := mul_le_mul_of_nonneg_right h₁ (meanRoof_pos (k := k) (hk := hk)).le
      linarith [hs.1]
    subst n
    have hst : s = t := by simpa using hz
    exact Prod.ext (by simpa [left_zero] using hn.symm) hst

theorem exists_strip (T : LocalHull G) :
    ∃ p ∈ ConstantStrip k hk, strip p = T := by
  obtain ⟨⟨B, s⟩, _, hT⟩ := exists_physical T
  let c := meanRoof k hk
  have hc : 0 < c := meanRoof_pos
  let t := s + correction B
  let n : ℤ := ⌊t / c⌋
  let r := t - n * c
  have hr : r ∈ Ico 0 c := by
    have h₁ := (le_div_iff₀ hc).mp (Int.floor_le (t / c))
    have h₂ := (div_lt_iff₀ hc).mp (Int.lt_floor_add_one (t / c))
    dsimp [r, n]
    constructor <;> nlinarith
  have ht : translate G t (corrected B) = T := by
    rw [corrected, translate_translate, show t + -correction B = s by dsimp [t]; ring]
    exact hT
  have hanchor : ∃ D, corrected D = translate G ((n : ℝ) * c) (corrected B) := by
    cases n with
    | ofNat i => exact ⟨right B.1 i, by simpa [c] using corrected_right B i⟩
    | negSucc i =>
      refine ⟨left B.1 (i + 1), ?_⟩
      rw [corrected_left]
      congr 1
      push_cast
      ring
  obtain ⟨D, hD⟩ := hanchor
  refine ⟨(D, r), hr, ?_⟩
  change translate G r (corrected D) = T
  rw [hD, translate_translate, show r + (n : ℝ) * c = t by dsimp [r]; ring, ht]

/-- At time equal to the mean roof the strip coordinate stays fixed and the
base point advances one tile. -/
theorem translate_mean_strip (B : Transversal k hk) (s : ℝ) :
    translate G (meanRoof k hk) (strip (B, s)) = strip (next B, s) := by
  simp only [strip, corrected_next, translate_translate]
  rw [add_comm s]

theorem isCompact_transversal : IsCompact {T : (G).Hull | (origin T).2 = 0} := by
  have h : {T : (G).Hull | (origin T).2 = 0} =
      ⋃ a : Fin 3, {T : (G).Hull | origin T = (a, 0)} := by
    ext T
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun he => ⟨(origin T).1, Prod.ext rfl he⟩, fun ⟨_, he⟩ => congrArg Prod.snd he⟩
  rw [h]
  exact isCompact_iUnion fun a => Psc.PeriodicPartnerHullCompact.isCompact_origin_fibre (a, 0)

instance : CompactSpace (Transversal k hk) := isCompact_iff_compactSpace.mp isCompact_transversal

theorem next_bijective : Bijective (next (k := k) (hk := hk)) := by
  constructor
  · intro B D h
    have h₀ : (0 : ℝ) ∈ Ico 0 (meanRoof k hk) := ⟨le_rfl, meanRoof_pos⟩
    have he : corrected B = corrected D := by
      apply (Psc.PeriodicPartnerLocalTopology.translateHomeomorph G (meanRoof k hk)).injective
      exact (corrected_next B).symm.trans ((congrArg corrected h).trans (corrected_next D))
    have hh : strip (B, 0) = strip (D, 0) := congrArg (translate G 0) he
    exact congrArg Prod.fst (strip_injOn (show (B, (0 : ℝ)) ∈ ConstantStrip k hk from h₀)
      (show (D, (0 : ℝ)) ∈ ConstantStrip k hk from h₀) hh)
  · intro B
    exact ⟨left B.1 1, (left_succ B.1 0).trans (left_zero B)⟩

/-- The next-tile map is the forward shift on the anchored legal tilings. -/
noncomputable def nextHomeomorph : Transversal k hk ≃ₜ Transversal k hk :=
  (Equiv.ofBijective next next_bijective).toHomeomorphOfContinuousClosed continuous_next continuous_next.isClosedMap


private theorem next_pow_eq_right (B : Transversal k hk) (n : ℕ) :
    (nextHomeomorph ^ n) B = right B.1 n := by
  induction n with
  | zero => simpa using (right_zero B).symm
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih]
    exact right_succ B.1 n

private theorem prev_pow_eq_left (B : Transversal k hk) (n : ℕ) :
    (nextHomeomorph⁻¹ ^ n) B = left B.1 n := by
  induction n with
  | zero => simpa using (left_zero B).symm
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih]
    apply (nextHomeomorph (k := k) (hk := hk)).injective
    rw [Homeomorph.inv_apply, Homeomorph.apply_symm_apply]
    exact (left_succ B.1 n).symm

theorem origin_pow_label (B : Transversal k hk) (n : ℕ) :
    (origin ((nextHomeomorph ^ (n : ℤ)) B).1).1 = (rightTile B.1 n).1 := by
  rw [zpow_natCast, next_pow_eq_right]
  rw [show origin (right B.1 n).1 = ((rightTile B.1 n).1, 0) from
    origin_reanchor (rightTile_mem B.1 n)]

theorem origin_neg_pow_label (B : Transversal k hk) (n : ℕ) :
    (origin ((nextHomeomorph ^ (-(n : ℤ))) B).1).1 = (leftTile B.1 n).1 := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, prev_pow_eq_left]
  rw [show origin (left B.1 n).1 = ((leftTile B.1 n).1, 0) from
    origin_reanchor (leftTile_mem B.1 n)]

private theorem separate_of_tile {T U : LocalHull G} {q : Fin 3 × ℝ}
    (hT : q ∈ T.toHull.1) (hU : q ∉ U.toHull.1) :
    ∃ A B : Set (LocalHull G), IsOpen A ∧ IsOpen B ∧ T ∈ A ∧ U ∈ B ∧ Disjoint A B := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|q.2| + 1)
  have hf : (LengthSubst.window U.toHull n).Finite := by
    obtain ⟨A, hA, hc⟩ := Psc.PeriodicPartnerHullCompact.exists_finite_window_container
      (origin U.toHull) n
    exact hA.subset (hc _ rfl)
  let D := (fun p : Fin 3 × ℝ => p.2 - q.2) '' LengthSubst.window U.toHull n
  obtain ⟨d, hd, hgap⟩ := Psc.PeriodicPartnerOriginSeparation.finite_nonzero_gap (hf.image _)
    (D := D)
  let ε := min (1 / 3 : ℝ) (d / 3)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have he₁ : ε ≤ (1 / 3 : ℝ) := min_le_left _ _
  have he₂ : ε ≤ d / 3 := min_le_right _ _
  let A := Psc.PeriodicPartnerLocalTopology.patch G T ε n
  let B := Psc.PeriodicPartnerLocalTopology.patch G U ε n
  have hself (Y : LocalHull G) : Y ∈ Psc.PeriodicPartnerLocalTopology.patch G Y ε n :=
    ⟨0, by simpa using hε, by
      rw [neg_zero, LengthSubst.translate_zero]
      exact fun _ _ => Iff.rfl⟩
  refine ⟨A, B, Psc.PeriodicPartnerLocalTopology.isOpen_patch _ _ _ _,
    Psc.PeriodicPartnerLocalTopology.isOpen_patch _ _ _ _, hself T, hself U,
    Set.disjoint_left.mpr ?_⟩
  intro W hWA hWB
  obtain ⟨s, hs, hsA⟩ := hWA
  obtain ⟨t, ht, htB⟩ := hWB
  have hwindow {p : Fin 3 × ℝ} (hp : |p.2 - q.2| < 1) :
      ((G).supp p ∩ Ioo (-(n : ℝ)) n).Nonempty := by
    refine ⟨p.2, ⟨le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos _)⟩, ?_⟩
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hp
    exact ⟨by linarith [neg_abs_le q.2], by linarith [le_abs_self q.2]⟩
  have hW := (hsA q (hwindow (by simp))).mp hT
  change (q.1, q.2 + -s) ∈ W.toHull.1 at hW
  let p := (q.1, q.2 + t - s)
  have hdist : |p.2 - q.2| < ε + ε := by
    change |q.2 + t - s - q.2| < _
    rw [show q.2 + t - s - q.2 = t - s by ring]
    exact (abs_sub _ _).trans_lt (by linarith)
  have hwin := hwindow (p := p) (hdist.trans (by linarith))
  have hpW : p ∈ (LengthSubst.translate (-t) W.toHull).1 := by
    change (q.1, q.2 + t - s + -t) ∈ W.toHull.1
    rwa [show q.2 + t - s + -t = q.2 + -s by ring]
  have hpU := (htB p hwin).mpr hpW
  have hne : p.2 - q.2 ≠ 0 := by
    intro h
    exact hU ((Prod.ext (show p.1 = q.1 from rfl) (sub_eq_zero.mp h)) ▸ hpU)
  have hm : p.2 - q.2 ∈ D := ⟨p, ⟨hpU, hwin⟩, rfl⟩
  linarith [hgap _ hm hne]

/-- Different ordinary legal tilings are separated by translated-window opens. -/
instance : T2Space (LocalHull G) where
  t2 T U h := by
    have hne : T.toHull.1 ≠ U.toHull.1 := fun he => h (LocalHull.ext (Subtype.ext he))
    obtain ⟨q, hq⟩ : ∃ q, ¬ (q ∈ T.toHull.1 ↔ q ∈ U.toHull.1) := by
      by_contra! ha
      exact hne (Set.ext ha)
    by_cases hT : q ∈ T.toHull.1
    · exact separate_of_tile hT (fun hU => hq (iff_of_true hT hU))
    · have hU : q ∈ U.toHull.1 := by
        by_contra hn
        exact hq (iff_of_false hT hn)
      obtain ⟨A, B, hA, hB, hu, ht, hd⟩ := separate_of_tile hU hT
      exact ⟨B, A, hB, hA, ht, hu, hd.symm⟩

end Psc.C4FamilySymbolicSection
