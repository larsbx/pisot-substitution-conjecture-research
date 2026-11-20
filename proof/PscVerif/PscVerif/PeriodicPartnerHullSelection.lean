/-
Local vertex and branch laws for the legal half-open tiling hull.
The two contracts of PeriodicPartnerSelection follow from disjoint tiles,
positive lengths, and a uniform positive lower length bound for a finite
alphabet. No realization assumption enters those proofs.
-/
import PscVerif.PeriodicPartnerHull
import PscVerif.PeriodicPartnerSelection

namespace Psc.PeriodicPartnerHull.LengthSubst

open Function Set Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerSelection

variable {α : Type*} {S : LengthSubst α}

/-- A tile with the given label starts at the indicated physical position. -/
def StartsAt (T : S.Hull) (y : ℝ) (a : α) : Prop := (a, y) ∈ T.1

private theorem tile_end_le_of_start_lt {T : S.Hull} {p q : α × ℝ}
    (hp : p ∈ T.1) (hq : q ∈ T.1) (hpq : p.2 < q.2) : p.2 + S.ℓ p.1 ≤ q.2 := by
  by_contra h
  have hpz : q.2 ∈ S.supp p := ⟨hpq.le, lt_of_not_ge h⟩
  have hqz : q.2 ∈ S.supp q := ⟨le_rfl, lt_add_of_pos_right _ (S.ℓ_pos q.1)⟩
  exact hpq.ne (congrArg Prod.snd ((T.2.1 q.2).unique ⟨hp, hpz⟩ ⟨hq, hqz⟩))

/-- The tile covering a known endpoint starts there. -/
theorem startsAt_of_endsAt {T : S.Hull} {y : ℝ} {b : α}
    (hb : EndsAt T y b) : ∃ a, StartsAt T y a := by
  obtain ⟨⟨a, x⟩, ⟨ha, hx⟩, -⟩ := T.2.1 y
  change x ≤ y ∧ y < x + S.ℓ a at hx
  have eq : x = y := by
    by_contra hne
    have hxy := lt_of_le_of_ne hx.1 hne
    let z := max (y - S.ℓ b) x
    have hzy : z < y := max_lt (sub_lt_self _ (S.ℓ_pos b)) hxy
    have hz₁ : z ∈ S.supp (b, y - S.ℓ b) := S.mem_supp_endpoint (le_max_left _ _) hzy
    have hz₂ : z ∈ S.supp (a, x) := ⟨le_max_right _ _, hzy.trans hx.2⟩
    have he := (T.2.1 z).unique ⟨hb, hz₁⟩ ⟨ha, hz₂⟩
    have hends := congrArg (fun p : α × ℝ => p.2 + S.ℓ p.1) he
    change y - S.ℓ b + S.ℓ b = x + S.ℓ a at hends
    linarith [hx.2]
  exact ⟨a, by simpa only [StartsAt, eq] using ha⟩

private theorem endsAt_of_startsAt {T : S.Hull} {y : ℝ} {a : α}
    (ha : StartsAt T y a) {d : ℝ} (hd : 0 < d) (hbound : ∀ c, d ≤ S.ℓ c) :
    ∃ b, EndsAt T y b := by
  obtain ⟨⟨b, x⟩, ⟨hb, hx⟩, -⟩ := T.2.1 (y - d)
  change x ≤ y - d ∧ y - d < x + S.ℓ b at hx
  have hxy : x < y := by linarith [hx.1]
  have hle : x + S.ℓ b ≤ y := tile_end_le_of_start_lt hb ha hxy
  have eq : x + S.ℓ b = y := by
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have hb' : EndsAt T (x + S.ℓ b) b := by simpa [EndsAt] using hb
    obtain ⟨c, hc⟩ := startsAt_of_endsAt hb'
    have hnext : x + S.ℓ b + S.ℓ c ≤ y := tile_end_le_of_start_lt hc ha hlt
    linarith [hx.2, hbound c]
  exact ⟨b, by
    change (b, y - S.ℓ b) ∈ T.1
    have h : y - S.ℓ b = x := by linarith
    simpa only [h] using hb⟩

/-- A common tile that reaches the ray's cutoff lets the agreement start
at the left endpoint of that tile. -/
theorem agreeRight_extend_to_common_tile {T U : S.Hull} {p : α × ℝ} {r : ℝ}
    (agree : AgreeRight T U r) (hpT : p ∈ T.1) (hpU : p ∈ U.1)
    (hr : r ≤ p.2 + S.ℓ p.1) : AgreeRight T U p.2 := by
  intro q hq
  by_cases h : r < q.2 + S.ℓ q.1
  · exact agree q (S.supp_inter_Ioi h)
  obtain ⟨z, hzq, hzw⟩ := hq
  have hzp : z ∈ S.supp p := ⟨hzw.le, hzq.2.trans_le ((le_of_not_gt h).trans hr)⟩
  constructor
  · intro hT
    have eq := (T.2.1 z).unique ⟨hT, hzq⟩ ⟨hpT, hzp⟩
    exact eq ▸ hpU
  · intro hU
    have eq := (U.2.1 z).unique ⟨hU, hzq⟩ ⟨hpU, hzp⟩
    exact eq ▸ hpT

/-- Distinct right-asymptotic tilings on a finite alphabet have a first
common ray, preceded by different endpoint labels. -/
theorem branchExistence [Finite α] [Nonempty α] :
    BranchExistence (AgreeRight (S := S)) EndsAt := by
  classical
  intro T U hne
  rintro ⟨r, hr⟩
  let D : Set ℝ :=
    {x | ∃ p : α × ℝ, ¬ (p ∈ T.1 ↔ p ∈ U.1) ∧ x = p.2 + S.ℓ p.1}
  have hD : D.Nonempty := by
    by_contra he
    apply hne
    apply Subtype.ext
    ext p
    by_contra hp
    exact he ⟨p.2 + S.ℓ p.1, p, hp, rfl⟩
  have upper {cut : ℝ} (hcut : AgreeRight T U cut) : ∀ x ∈ D, x ≤ cut := by
    rintro x ⟨p, hp, rfl⟩
    exact le_of_not_gt fun h => hp (hcut p (S.supp_inter_Ioi h))
  have bounded : BddAbove D := ⟨r, upper hr⟩
  let y := sSup D
  have agree : AgreeRight T U y := by
    intro p hp
    by_contra hd
    obtain ⟨z, hz, hzy⟩ := hp
    have hle : p.2 + S.ℓ p.1 ≤ y := le_csSup bounded ⟨p, hd, rfl⟩
    exact (not_lt_of_ge hle) (hzy.trans hz.2)
  obtain ⟨⟨a, x⟩, ⟨hpT, hpy⟩, -⟩ := T.2.1 y
  change x ≤ y ∧ y < x + S.ℓ a at hpy
  have hpU : (a, x) ∈ U.1 := (agree _ (S.supp_inter_Ioi hpy.2)).mp hpT
  have hxy : x = y := le_antisymm hpy.1
    (csSup_le hD (upper (agreeRight_extend_to_common_tile agree hpT hpU hpy.2.le)))
  have startT : StartsAt T y a := by simpa only [StartsAt, hxy] using hpT
  have startU : StartsAt U y a := by simpa only [StartsAt, hxy] using hpU
  obtain ⟨d, -, hd⟩ := Set.exists_min_image (univ : Set α) S.ℓ Set.finite_univ Set.univ_nonempty
  have lower (c : α) : S.ℓ d ≤ S.ℓ c := hd c (mem_univ c)
  obtain ⟨b, hb⟩ := endsAt_of_startsAt startT (S.ℓ_pos d) lower
  obtain ⟨c, hc⟩ := endsAt_of_startsAt startU (S.ℓ_pos d) lower
  refine ⟨y, b, c, agree, hb, hc, ?_⟩
  intro eq
  subst c
  have extend : AgreeRight T U (y - S.ℓ b) :=
    agreeRight_extend_to_common_tile agree hb hc (by dsimp; linarith)
  have h := csSup_le hD (upper extend)
  exact (not_le_of_gt (sub_lt_self y (S.ℓ_pos b))) h

private theorem inflateH_iterate_tiles [Nonempty α] (T : S.Hull) (n : ℕ) :
    ((inflateH^[n]) T).1 = S.inflate^[n] T.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply', inflateH, ih]

/-- A common origin tile of two periodic tilings inflates to a common
supertile covering every positive position. -/
theorem periodic_ray_of_startsAt [Nonempty α] (hβ : 1 < S.β) {T U : S.Hull} {a : α}
    (hT : T ∈ periodicPts (inflateH (S := S))) (hU : U ∈ periodicPts (inflateH (S := S)))
    (haT : StartsAt T 0 a) (haU : StartsAt U 0 a) : AgreeRight T U 0 := by
  let seed : Set (α × ℝ) := {(a, 0)}
  have hSeed : S.TilesOn (Ico 0 (S.ℓ a)) seed := by
    constructor
    · intro p hp
      have eq : p = (a, 0) := mem_singleton_iff.mp hp
      subst p
      simp [supp]
    · intro z hz
      refine ⟨(a, 0), ⟨mem_singleton _, by simpa [supp] using hz⟩, ?_⟩
      exact fun p hp => mem_singleton_iff.mp hp.1
  obtain ⟨n, hn, hTn, hUn⟩ := pairPeriodic_of_mem hT hU
  have periodT : IsPeriodicPt (inflateH (S := S)) n T := hTn
  have periodU : IsPeriodicPt (inflateH (S := S)) n U := hUn
  intro p hp
  obtain ⟨z, hz, hpos⟩ := hp
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (z / S.ℓ a) (one_lt_pow₀ hβ (Nat.ne_of_gt hn))
  have hz' : z < S.β ^ (k * n) * S.ℓ a := by
    rw [← div_lt_iff₀ (S.ℓ_pos a), Nat.mul_comm k n, pow_mul]
    exact hk
  have patch : S.TilesOn (Ico 0 (S.β ^ (k * n) * S.ℓ a)) (S.inflate^[k * n] seed) := by
    simpa only [mul_zero] using S.tilesOn_inflate_iterate hSeed (k * n)
  obtain ⟨q, ⟨hq, hzq⟩, -⟩ := patch.2 z ⟨hpos.le, hz'⟩
  have hsubT := S.inflate_iterate_mono (singleton_subset_iff.mpr haT : seed ⊆ T.1) (k * n)
  have hsubU := S.inflate_iterate_mono (singleton_subset_iff.mpr haU : seed ⊆ U.1) (k * n)
  rw [← inflateH_iterate_tiles T, (periodT.const_mul k).eq] at hsubT
  rw [← inflateH_iterate_tiles U, (periodU.const_mul k).eq] at hsubU
  constructor
  · intro hpT
    have eq := (T.2.1 z).unique ⟨hpT, hz⟩ ⟨hsubT hq, hzq⟩
    exact eq ▸ hsubU hq
  · intro hpU
    have eq := (U.2.1 z).unique ⟨hpU, hz⟩ ⟨hsubU hq, hzq⟩
    exact eq ▸ hsubT hq

/-- The local vertex laws required by Theorem S hold on the actual hull. -/
theorem vertexLaws [Nonempty α] (hβ : 1 < S.β) :
    VertexLaws (inflateH (S := S)) AgreeRight EndsAt StartsAt where
  agree_symm h p hp := (h p hp).symm
  start_of_end := startsAt_of_endsAt
  periodic_ray := periodic_ray_of_startsAt hβ

/-- The injective endpoint direction of Lemma A, with first-branch
existence discharged on the hull. -/
theorem periodic_branch_at_origin_of_injective [Finite α] [Nonempty α]
    (hβ : 1 < S.β) (hg : Injective S.lastLetter) {T U : S.Hull}
    (hp : PairPeriodic inflateH T U) (hne : T ≠ U) (hA : RightAsymptotic AgreeRight T U) :
    ∃ b c, BranchAt AgreeRight EndsAt T U 0 b c := by
  obtain ⟨y, b, c, hb⟩ := branchExistence hne hA
  have hy := branch_eq_zero_of_persistent rightBranchLaws hβ hp hb
    (fun n eq => hb.2.2.2 ((hg.iterate n) eq))
  exact ⟨b, c, hy ▸ hb⟩

end Psc.PeriodicPartnerHull.LengthSubst

namespace Psc.PeriodicPartnerHull

open Function LengthSubst Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerSelection

variable {S : LengthSubst (Fin 3)} {Y : Type*}

/-- A witness in an injective endpoint direction can be periodicized with
its branch at the origin and all three tilings in the distinguished fibre. -/
theorem hull_origin_witness_of_injective (hβ : 1 < S.β) (P : PublishedInputs S Y)
    (hg : Injective S.lastLetter) (Z : S.Hull → S.Hull → Prop)
    (hTranslate : ∀ t {T U}, Z T U → Z (translate t T) (translate t U))
    (hFibre : ∀ {T U}, Z T U → P.realize T = P.realize U)
    (hDistinct : ∀ {T U}, Z T U → T ≠ U) {T U V : S.Hull}
    (hTU : Z T U) (hTV : Z T V) (hUV : U ≠ V) (hA : RightAsymptotic AgreeRight U V) :
    ∃ t n b c, 0 < n ∧ Z (translate t T) (translate t U) ∧
      Z (translate t T) (translate t V) ∧ inflateH^[n] (translate t T) = translate t T ∧
      inflateH^[n] (translate t U) = translate t U ∧
      inflateH^[n] (translate t V) = translate t V ∧
      BranchAt AgreeRight EndsAt (translate t U) (translate t V) 0 b c ∧
      P.realize (translate t T) = P.q₀ ∧ P.realize (translate t U) = P.q₀ ∧
      P.realize (translate t V) = P.q₀ := by
  have shiftAsym : ∀ t {x y : S.Hull}, RightAsymptotic AgreeRight x y →
      RightAsymptotic AgreeRight (translate t x) (translate t y) := by
    rintro t x y ⟨r, hr⟩
    exact ⟨r - t, rightBranchLaws.agree_translate t hr⟩
  obtain ⟨t, n, _, hn, hTU', hTV', hTn, hUn, hVn, -, -, -, -, -, -, hUV', hA'⟩ :=
    periodic_triple_of_asymptotic_partners inflateH P.A P.realize translate Z
      (RightAsymptotic AgreeRight) P.inflate_injective P.semiconj P.finite_fibres
      translate_injective hTranslate shiftAsym hFibre hDistinct (bds_ray_iff_metric.mpr P.bds)
      hTU hTV hUV hA
  have hp : PairPeriodic inflateH (translate t U) (translate t V) := ⟨n, hn, hUn, hVn⟩
  obtain ⟨b, c, hbranch⟩ := periodic_branch_at_origin_of_injective hβ hg hp hUV' hA'
  have hu := P.r4 hp.mem_left hbranch.2.1
  have hv := P.r4 hp.mem_right hbranch.2.2.1
  exact ⟨t, n, b, c, hn, hTU', hTV', hTn, hUn, hVn, hbranch, (hFibre hTU').trans hu, hu, hv⟩

/-- Theorem S on the legal tiling hull with its two local contracts supplied.
The realization, asymptotic periodicization and (NM_V) inputs stay named. -/
theorem hull_selection_dichotomy (hβ : 1 < S.β) (P : PublishedInputs S Y)
    (Z : S.Hull → S.Hull → Prop)
    (hTranslate : ∀ t {T U}, Z T U → Z (translate t T) (translate t U))
    (hFibre : ∀ {T U}, Z T U → P.realize T = P.realize U)
    (hDistinct : ∀ {T U}, Z T U → T ≠ U)
    (hE1 : AsymptoticSameFibre P.realize AgreeRight)
    (hNMV : NMVRight P.realize P.q₀ AgreeRight EndsAt StartsAt)
    (hTwo : TwoPeriodicLetters S.lastLetter) {T U V : S.Hull}
    (hTU : Z T U) (hTV : Z T V) (hUV : U ≠ V) (hA : RightAsymptotic AgreeRight U V) :
    ∃ t n, 0 < n ∧
      Z (translate t T) (translate t U) ∧ Z (translate t T) (translate t V) ∧
      inflateH^[n] (translate t T) = translate t T ∧
      inflateH^[n] (translate t U) = translate t U ∧
      inflateH^[n] (translate t V) = translate t V ∧
      ∃ y b c, BranchAt AgreeRight EndsAt (translate t U) (translate t V) y b c ∧
        ((y = 0 ∧ S.lastLetter^[2] b ≠ S.lastLetter^[2] c ∧ P.realize (translate t T) = P.q₀ ∧
            P.realize (translate t U) = P.q₀ ∧ P.realize (translate t V) = P.q₀) ∨
         (0 < y ∧ S.lastLetter^[2] b = S.lastLetter^[2] c ∧ S.lastLetter b = S.lastLetter c ∧
            ¬ VertexAtOrigin EndsAt (translate t U) ∧ ¬ VertexAtOrigin EndsAt (translate t V))) :=
  selection_dichotomy rightBranchLaws (vertexLaws hβ) hβ branchExistence
    (bds_ray_iff_metric.mpr P.bds) P.A P.realize P.q₀ Z P.inflate_injective P.semiconj
    P.finite_fibres translate_injective hTranslate hFibre hDistinct P.r4 hE1 hNMV hTwo
    hTU hTV hUV hA

end Psc.PeriodicPartnerHull
