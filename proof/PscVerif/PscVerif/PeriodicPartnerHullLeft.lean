/-
# The left-hand periodic-partner consumers on the legal hull

Gap 6 of `docs/c4-tiling-hull-realization-2026-11-19.md`: the reflected consumers of
`PeriodicPartnerReflection` were not instantiated on the hull.  This module supplies the
left-oriented predicates of the hull and proves their local contract:

* `AgreeLeft T U y`: the same tiles among those meeting the open left ray `(-∞, y)`;
* `StartsAt T y b`: the tile labelled `b` starts at `y`;
* `leftBranchLaws`: `LeftBranchLaws inflateH translate β g_L AgreeLeft StartsAt`,
  with `g_L` the first-letter map;
* `left_common_patch`: a common left ray at `0` and a common start label `a` give
  centred agreement of radius `ℓ a`;
* `leftAsymptotic_iff_metric`: exact left-ray agreement is metric asymptoticity under the
  reflected flow `t ↦ translate (-t)`, so the two forms of the left BDS input coincide;
* `r4_startsAt_iff_endsAt` (finite alphabets): (R4) at tiles starting at `0` is (R4) at
  tiles ending at `0`.  The realization's proved (R4) therefore serves both orientations.

The consumers then follow from the existing reflection theorems.  The left BDS input is a
separate published statement, the mirror of the right one; it is not derived from it.

Source decision: `docs/c4-hull-left-consumers-stop-go-2026-11-21.md`.
-/
import PscVerif.PeriodicPartnerHullNonempty
import PscVerif.PeriodicPartnerReflection

namespace Psc.PeriodicPartnerHull

open Function Filter Set Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerCollapse
  Psc.PeriodicPartnerAsymptotic Psc.PeriodicPartnerReflection
open scoped Topology

namespace LengthSubst

variable {α : Type*} {S : LengthSubst α}

/-! ## Left-oriented predicates and their local laws -/

/-- Exact agreement on the open left ray `(-∞, y)`. -/
def AgreeLeft (T U : S.Hull) (y : ℝ) : Prop := S.AgreeOn (Iio y) T.1 U.1

/-- The tile labelled `b` starts at `y`. -/
def StartsAt (T : S.Hull) (y : ℝ) (b : α) : Prop := (b, y) ∈ T.1

theorem startsAt_unique {T : S.Hull} {y : ℝ} {b c : α}
    (hb : StartsAt T y b) (hc : StartsAt T y c) : b = c :=
  congrArg Prod.fst ((T.2.1 y).unique ⟨hb, le_rfl, by simpa using S.ℓ_pos b⟩
    ⟨hc, le_rfl, by simpa using S.ℓ_pos c⟩)

theorem agree_start {T U : S.Hull} {r y : ℝ} {b c : α} (h : AgreeLeft T U r)
    (hr : y < r) (hb : StartsAt T y b) (hc : StartsAt U y c) : b = c :=
  startsAt_unique ((h (b, y) ⟨y, ⟨le_rfl, by simpa using S.ℓ_pos b⟩, hr⟩).mp hb) hc

/-- The left branch contract, proved for the hull. -/
theorem leftBranchLaws [Nonempty α] :
    LeftBranchLaws (inflateH (S := S)) translate S.β S.firstLetter AgreeLeft StartsAt where
  translate_zero T := Subtype.ext (shift_zero T.1)
  start_unique := startsAt_unique
  agree_start := agree_start
  agree_translate t h := h.shift (by intro z hz; simp only [mem_Iio] at hz ⊢; linarith)
  start_translate {T y b} t h := by
    have h' : (b, y) ∈ T.1 := h
    change (b, y - t + t) ∈ T.1
    simpa using h'
  agree_inflate {T U y} h := by
    have hβ := S.β_pos
    refine AgreeOn.inflate h ?_
    intro z hz
    simp only [mem_Iio] at hz ⊢
    rw [div_lt_iff₀ hβ]
    linarith
  start_inflate {T y b} h := by
    refine ⟨(b, y), h, ?_⟩
    have hcons := List.cons_head_tail (S.ne_nil b)
    rw [← hcons]
    simp [place, firstLetter]

/-- A common left ray at `0` and a common start label `a` there give a common centred patch
of the full radius `ℓ a`. -/
theorem left_common_patch {T U : S.Hull} {a : α} (hray : AgreeLeft T U 0)
    (hT : StartsAt T 0 a) (hU : StartsAt U 0 a) : Agree (S.ℓ a) T U := by
  intro p ⟨z, hz, hzW⟩
  by_cases hleft : (S.supp p ∩ Iio 0).Nonempty
  · exact hray p hleft
  have hstart : 0 ≤ p.2 := not_lt.mp fun h => hleft ⟨p.2, ⟨le_rfl, by
    simpa using S.ℓ_pos p.1⟩, h⟩
  have hz0 : 0 ≤ z := hstart.trans hz.1
  have hza : z ∈ S.supp (a, 0) := ⟨hz0, by simpa using hzW.2⟩
  have side : ∀ V : S.Hull, StartsAt V 0 a → (p ∈ V.1 ↔ p = (a, 0)) := by
    intro V hV
    exact ⟨fun hp => (V.2.1 z).unique ⟨hp, hz⟩ ⟨hV, hza⟩, fun h => h ▸ hV⟩
  rw [side T hT, side U hU]

/-- The common-patch fact in the reflected coordinates of `PeriodicPartnerReflection`. -/
theorem reflected_common_patch [Nonempty α] {T U : S.Hull} {a : α}
    (hray : reflectedAgreement AgreeLeft T U 0) (hT : reflectedEndpoint StartsAt T 0 a)
    (hU : reflectedEndpoint StartsAt U 0 a) : agreementData.Agree (S.ℓ a) T U := by
  simp only [reflectedAgreement, reflectedEndpoint, neg_zero] at hray hT hU
  exact left_common_patch hray hT hU

/-! ## Left rays and the reflected metric flow -/

theorem reflected_window_of_ray {R r : ℝ} {T U : S.Hull} (_hR : 0 < R) (hr : r ≤ -R)
    (h : reflectedAgreement AgreeLeft T U r) : Agree R T U :=
  AgreeOn.mono h (fun _ hz => lt_of_lt_of_le hz.2 (by linarith))

/-- Exact left-ray agreement is metric asymptoticity under `t ↦ translate (-t)`. -/
theorem leftAsymptotic_iff_metric [Nonempty α] {T U : S.Hull} :
    LeftAsymptotic AgreeLeft T U ↔
      TranslationRightAsymptotic (reflectedTranslation translate) T U := by
  rw [← rightAsymptotic_reflection_iff]
  constructor
  · exact translationRightAsymptotic_of_rightAsymptotic agreementData
      (leftBranchLaws (S := S)).toRightBranchLaws.agree_translate reflected_window_of_ray
  · intro h
    obtain ⟨t₀, ht₀⟩ := Metric.tendsto_atTop.mp h ((1 / 2) ^ 1) (by norm_num)
    refine ⟨t₀, fun p ⟨z, hz, hzt⟩ => ?_⟩
    simp only [mem_Iio] at hzt
    have hd : dist (translate z T) (translate z U) < (1 / 2) ^ 1 := by
      have := ht₀ (-z) (by linarith)
      simp only [reflectedTranslation, neg_neg] at this
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at this
    have h0 : (0 : ℝ) ∈ S.supp (p.1, p.2 - z) := by
      have := S.mem_supp_shift (t := z) (z := 0) (p := (p.1, p.2 - z))
      simp only [zero_add, sub_add_cancel] at this
      exact this.mp hz
    have hagree := agree_of_dist_lt hd (p.1, p.2 - z) ⟨0, h0, by norm_num⟩
    change (p.1, p.2 - z + z) ∈ T.1 ↔ (p.1, p.2 - z + z) ∈ U.1 at hagree
    simpa using hagree

/-- On this hull the metric and exact-ray forms of the left BDS input are one statement. -/
theorem left_bds_ray_iff_metric [Nonempty α] :
    BDSPeriodicization (inflateH (S := S)) translate (LeftAsymptotic AgreeLeft) ↔
      BDSPeriodicization (inflateH (S := S)) translate
        (fun T U => TranslationRightAsymptotic (reflectedTranslation translate) T U) := by
  constructor
  · intro h T U hne hasym
    exact h hne (leftAsymptotic_iff_metric.mpr hasym)
  · intro h T U hne hasym
    exact h hne (leftAsymptotic_iff_metric.mp hasym)

/-! ## Origin starts and origin ends -/

/-- A tile ending at `y` is followed by a tile starting at `y`. -/
theorem startsAt_of_endsAt {T : S.Hull} {y : ℝ} {c : α} (hc : EndsAt T y c) :
    ∃ b, StartsAt T y b := by
  obtain ⟨q, ⟨hq, hyq⟩, -⟩ := T.2.1 y
  refine ⟨q.1, ?_⟩
  rcases eq_or_lt_of_le hyq.1 with heq | hlt
  · simpa [StartsAt, ← heq] using hq
  exfalso
  -- `q` would overlap the tile `(c, y - ℓ c)` just left of `y`
  set w := max q.2 (y - S.ℓ c)
  have hℓ := S.ℓ_pos c
  have hℓq := S.ℓ_pos q.1
  have hw1 : w ∈ S.supp q := ⟨le_max_left _ _, max_lt (by linarith [hyq.2]) (by
    linarith [hyq.2])⟩
  have hw2 : w ∈ S.supp (c, y - S.ℓ c) := ⟨le_max_right _ _, by
    show w < y - S.ℓ c + S.ℓ c
    rw [sub_add_cancel]
    exact max_lt hlt (by linarith)⟩
  have := (T.2.1 w).unique ⟨hq, hw1⟩ ⟨hc, hw2⟩
  rw [this] at hyq
  exact absurd hyq.2 (by simp)

/-- On a finite alphabet, a tile starting at `y` is preceded by a tile ending at `y`. -/
theorem endsAt_of_startsAt [Fintype α] [DecidableEq α] [Nonempty α] {T : S.Hull} {y : ℝ}
    {b : α} (hb : StartsAt T y b) : ∃ c, EndsAt T y c := by
  set m := Psc.PeriodicPartnerRealization.minLen S
  have hm : 0 < m := Psc.PeriodicPartnerRealization.minLen_pos
  obtain ⟨q, ⟨hq, hzq⟩, -⟩ := T.2.1 (y - m / 2)
  refine ⟨q.1, ?_⟩
  -- the end `e` of `q` is at most `y`, and a gap before `y` would be covered by a tile
  -- starting in it and reaching past `y`
  have he_le : q.2 + S.ℓ q.1 ≤ y := by
    by_contra hgt
    push Not at hgt
    have := (T.2.1 y).unique ⟨hq, by linarith [hzq.1], hgt⟩
      ⟨hb, le_rfl, by simpa using S.ℓ_pos b⟩
    rw [this] at hzq
    linarith [hzq.1]
  rcases eq_or_lt_of_le he_le with heq | hlt
  · simp only [EndsAt]; convert hq using 2; linarith
  exfalso
  obtain ⟨r, hrs⟩ := startsAt_of_endsAt (T := T) (y := q.2 + S.ℓ q.1) (c := q.1)
    (by simpa [EndsAt] using hq)
  have hrℓ := Psc.PeriodicPartnerRealization.minLen_le (S := S) r
  have := (T.2.1 y).unique ⟨hrs, by linarith, by linarith [hzq.2]⟩
    ⟨hb, le_rfl, by simpa using S.ℓ_pos b⟩
  simp only [Prod.mk.injEq] at this
  linarith [this.2]

/-- (R4) at origin starts is (R4) at origin ends, on a finite alphabet. -/
theorem r4_startsAt_iff_endsAt [Fintype α] [DecidableEq α] [Nonempty α] {Y : Type*}
    (h : S.Hull → Y) (q₀ : Y) :
    R4ZeroFibre (inflateH (S := S)) h q₀ StartsAt ↔ R4ZeroFibre inflateH h q₀ EndsAt := by
  constructor
  · intro hR T c hp hc
    obtain ⟨b, hb⟩ := startsAt_of_endsAt hc
    exact hR hp hb
  · intro hR T b hp hb
    obtain ⟨c, hc⟩ := endsAt_of_startsAt hb
    exact hR hp hc

end LengthSubst

/-! ## The left-hand consumers on the hull -/

open LengthSubst

section Ternary

variable {S : LengthSubst (Fin 3)} {Y : Type*}

/-- The metric left BDS input for this hull: the mirror of `PublishedInputs.bds`. -/
def LeftBDS (S : LengthSubst (Fin 3)) : Prop :=
  BDSPeriodicization (inflateH (S := S)) translate
    (fun T U => TranslationRightAsymptotic (reflectedTranslation translate) T U)

/-- Left Lemma E on the hull: the two-step start-label test is joint periodicity. -/
theorem hull_left_two_step_iff_pairPeriodic (hβ : 1 < S.β) (hBDS : LeftBDS S)
    {T U : S.Hull} {b c : Fin 3}
    (hbranch : LeftBranchAt AgreeLeft StartsAt T U 0 b c) :
    S.firstLetter^[2] b ≠ S.firstLetter^[2] c ↔ PairPeriodic inflateH T U :=
  left_ternary_two_step_iff_pairPeriodic leftBranchLaws hβ
    (left_bds_ray_iff_metric.mpr hBDS) hbranch

/-- Left Lemma E with the zero fibre.  The (R4) field of `PublishedInputs`, stated at origin
ends, is converted to origin starts. -/
theorem hull_left_two_step_iff_zero_fibre (hβ : 1 < S.β) (P : PublishedInputs S Y)
    (hBDS : LeftBDS S) {T U : S.Hull} {b c : Fin 3}
    (hbranch : LeftBranchAt AgreeLeft StartsAt T U 0 b c) :
    S.firstLetter^[2] b ≠ S.firstLetter^[2] c ↔ P.realize T = P.q₀ ∧ P.realize U = P.q₀ :=
  left_ternary_two_step_iff_zero_fibre leftBranchLaws hβ (left_bds_ray_iff_metric.mpr hBDS)
    P.A P.realize P.q₀ P.inflate_injective P.semiconj (P.finite_fibres P.q₀) P.q₀_fixed
    ((r4_startsAt_iff_endsAt P.realize P.q₀).mpr P.r4) hbranch

/-- Left Lemma M on the hull, with no external input. -/
theorem hull_left_collapse_of_merge (hβ : 1 < S.β) {T U : S.Hull} {a b : Fin 3}
    (hray : AgreeLeft T U 0) (hT : StartsAt T 0 a) (hU : StartsAt U 0 b) (m : ℕ)
    (hmerge : S.firstLetter^[m] a = S.firstLetter^[m] b) :
    Tendsto (fun n : ℕ => dist (inflateH^[n] T) (inflateH^[n] U)) atTop (𝓝 0) :=
  (Psc.PeriodicPartnerDichotomy.endpointDataOfBranch (leftBranchLaws (S := S)).toRightBranchLaws
    agreementData S.ℓ S.ℓ_pos reflected_common_patch).distance_tendsto_zero_of_endpoint_merge hβ
    (by show AgreeLeft T U (-0); simpa using hray) (by show StartsAt T (-0) a; simpa using hT)
    (by show StartsAt U (-0) b; simpa using hU) m hmerge

/-- The left branch-origin triple dichotomy on the hull. -/
theorem hull_left_branch_triple_dichotomy (hβ : 1 < S.β) (P : PublishedInputs S Y)
    (hBDS : LeftBDS S) {T₀ T U : S.Hull} {b c : Fin 3}
    (hbranch : LeftBranchAt AgreeLeft StartsAt T U 0 b c)
    (hT₀T : P.realize T₀ = P.realize T) (hT₀U : P.realize T₀ = P.realize U) :
    (S.firstLetter^[2] b ≠ S.firstLetter^[2] c ∧ P.realize T₀ = P.q₀ ∧ P.realize T = P.q₀ ∧
      P.realize U = P.q₀ ∧
      ∃ n > 0, inflateH^[n] T₀ = T₀ ∧ inflateH^[n] T = T ∧ inflateH^[n] U = U) ∨
    (S.firstLetter^[2] b = S.firstLetter^[2] c ∧ P.realize T₀ ≠ P.q₀ ∧ P.realize T ≠ P.q₀ ∧
      P.realize U ≠ P.q₀ ∧ ¬ PairPeriodic inflateH T U ∧
      Tendsto (fun n : ℕ => dist (inflateH^[n] T) (inflateH^[n] U)) atTop (𝓝 0)) :=
  Psc.PeriodicPartnerDichotomy.ternary_branch_triple_dichotomy
    (leftBranchLaws (S := S)).toRightBranchLaws hβ
    ((bdsPeriodicization_reflection_iff _ _ _).mpr (left_bds_ray_iff_metric.mpr hBDS))
    agreementData S.ℓ S.ℓ_pos reflected_common_patch P.A P.realize P.q₀ P.inflate_injective
    P.semiconj (P.finite_fibres P.q₀) P.q₀_fixed
    ((r4ZeroFibre_reflection_iff _ _ _ _).mpr ((r4_startsAt_iff_endsAt P.realize P.q₀).mpr P.r4))
    ((leftBranchAt_zero_iff_reflected _ _ _ _ _ _).mp hbranch) hT₀T hT₀U

end Ternary

end Psc.PeriodicPartnerHull
