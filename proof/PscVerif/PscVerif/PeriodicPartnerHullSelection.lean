/-
# Theorem S on the legal tiling hull, and the vertex-partner case of (A)

`PeriodicPartnerSelection` proves Theorem S from two local contracts that were not yet
discharged on `PeriodicPartnerHull`: `VertexLaws` (symmetry of ray agreement, a tile after
every vertex, and the periodic-ray law) and `BranchExistence` (a first branch point of two
distinct asymptotic tilings).  This module proves both for the concrete hull and
instantiates Theorem S there.  The remaining inputs are the fields of `PublishedInputs`, the
joining relation with its translation and fibre laws, (E1) and (NM_V); each is a named
hypothesis, none is an axiom.

It also proves one new step towards the global contradiction.  In case (A) the two leaves
end tiles `b ≠ c` at the origin.  If the common partner also has a vertex there, ending a
tile `x`, then (Z2) at level zero gives `x ≠ b` and `x ≠ c`, and periodicity makes all three
letters periodic for the last-letter map.  Three periodic letters on three letters force a
permutation: **a vertex-type common partner puts the right side in the injective regime of
round-4 Lemma A.**  It does not exclude the configuration.

`BranchExistence` needs a finite alphabet (a positive minimal tile length); `periodic_ray`
needs `1 < β`.
-/
import PscVerif.PeriodicPartnerHull
import PscVerif.PeriodicPartnerSelection

namespace Psc.PeriodicPartnerHullSelection

open Function Set Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerSelection
  Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

/-! ## Abstract: a vertex-type common partner forces a permutation -/

section Abstract

variable {X α : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}

/-- The letter ending a tile at the origin of a periodic tiling is periodic for `g`. -/
theorem periodic_letter (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    {T : X} {x : α} (hT : T ∈ periodicPts f) (hx : EndsAt T 0 x) : x ∈ periodicPts g := by
  obtain ⟨n, hn, hTn⟩ := hT
  refine ⟨n, hn, ?_⟩
  have h := laws.endpoint_iterate n hx
  rw [mul_zero, hTn.eq] at h
  exact laws.endpoint_unique h hx

end Abstract

/-- Three distinct periodic letters make a ternary map injective. -/
theorem injective_of_three_periodic :
    ∀ (g : Fin 3 → Fin 3) (x b c : Fin 3), x ≠ b → x ≠ c → b ≠ c →
      g^[6] x = x → g^[6] b = b → g^[6] c = c → Injective g := by
  decide

/-- Two periodic letters alone do not suffice: `(0,1,1)` is the control. -/
theorem two_periodic_not_injective :
    TwoPeriodicLetters ![0, 1, 1] ∧ ¬ Injective (![0, 1, 1] : Fin 3 → Fin 3) := by
  refine ⟨collapsed_pair_example.1, fun h => absurd (h collapsed_pair_example.2) (by decide)⟩

section AbstractTernary

variable {X : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}

/-- **Vertex partner.**  Three periodic tilings ending pairwise different tiles at the
origin force the last-letter map to be a permutation.  In case (A) the leaves end `b ≠ c`,
and (Z2) at level zero separates the partner's letter `x` from both. -/
theorem injective_of_vertex_partner (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    {T S U : X} {x b c : Fin 3}
    (hT : T ∈ periodicPts f) (hS : S ∈ periodicPts f) (hU : U ∈ periodicPts f)
    (hx : EndsAt T 0 x) (hb : EndsAt S 0 b) (hc : EndsAt U 0 c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hbc : b ≠ c) : Injective g :=
  injective_of_three_periodic g x b c hxb hxc hbc
    (six_of_mem_periodicPts (periodic_letter laws hT hx))
    (six_of_mem_periodicPts (periodic_letter laws hS hb))
    (six_of_mem_periodicPts (periodic_letter laws hU hc))

end AbstractTernary

/-! ## The hull: vertex laws -/

variable {α : Type*} {L : LengthSubst α}

/-- The tile labelled `a` starts at `y`. -/
def StartsAt (T : L.Hull) (y : ℝ) (a : α) : Prop := (a, y) ∈ T.1

theorem agreeRight_symm {T U : L.Hull} {y : ℝ} (h : AgreeRight T U y) : AgreeRight U T y :=
  fun p hp => (h p hp).symm

/-- The tile covering an endpoint starts there. -/
theorem startsAt_of_endsAt {T : L.Hull} {y : ℝ} {b : α} (h : EndsAt T y b) :
    ∃ a, StartsAt T y a := by
  obtain ⟨⟨a, x⟩, ⟨hp, hy⟩, -⟩ := T.2.1 y
  refine ⟨a, ?_⟩
  simp only [LengthSubst.supp, mem_Ico] at hy
  have hb := L.ℓ_pos b
  rcases hy.1.lt_or_eq with hlt | heq
  · exfalso
    have hzy : max x (y - L.ℓ b) < y := max_lt hlt (by linarith)
    have h1 : max x (y - L.ℓ b) ∈ L.supp (a, x) :=
      ⟨le_max_left _ _, lt_trans hzy hy.2⟩
    have h2 : max x (y - L.ℓ b) ∈ L.supp (b, y - L.ℓ b) :=
      L.mem_supp_endpoint (le_max_right _ _) hzy
    have hpq := (T.2.1 _).unique ⟨hp, h1⟩ ⟨h, h2⟩
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    linarith [hy.2]
  · change (a, y) ∈ T.1
    rwa [← heq]

theorem inflateH_iterate_val [Nonempty α] (T : L.Hull) (n : ℕ) :
    (inflateH^[n] T).1 = L.inflate^[n] T.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

/-- A periodic tiling with the tile `a` at the origin contains every supertile of `a` at
multiples of its period. -/
theorem supertile_subset [Nonempty α] {T : L.Hull} {a : α} {n : ℕ}
    (hT : inflateH^[n] T = T) (ha : StartsAt T 0 a) (k : ℕ) :
    L.supertile a (n * k) ⊆ T.1 := by
  have hfix : inflateH^[n * k] T = T := (IsPeriodicPt.mul_const hT k).eq
  calc L.supertile a (n * k) = L.inflate^[n * k] {(a, 0)} := rfl
    _ ⊆ L.inflate^[n * k] T.1 := L.inflate_iterate_mono (singleton_subset_iff.mpr ha) _
    _ = T.1 := by rw [← inflateH_iterate_val, hfix]

theorem tilesOn_supertile [Nonempty α] (a : α) (m : ℕ) :
    L.TilesOn (Ico 0 (L.β ^ m * L.ℓ a)) (L.supertile a m) := by
  have h0 : L.TilesOn (Ico 0 (L.ℓ a)) {(a, 0)} := by
    refine ⟨fun p hp => ?_, fun z hz => ⟨(a, 0), ⟨rfl, ?_⟩, fun q hq => hq.1⟩⟩
    · rw [mem_singleton_iff.mp hp]
      intro z hz
      simpa [LengthSubst.supp] using hz
    · simpa [LengthSubst.supp] using hz
  simpa [LengthSubst.supertile] using L.tilesOn_inflate_iterate h0 m

/-- **Periodic-ray law.**  Two inflation-periodic tilings starting the same tile at the
origin agree on `(0, ∞)`: both contain its supertiles at a common period. -/
theorem periodic_ray [Nonempty α] (hβ : 1 < L.β) {T U : L.Hull} {a : α}
    (hT : T ∈ periodicPts inflateH) (hU : U ∈ periodicPts inflateH)
    (haT : StartsAt T 0 a) (haU : StartsAt U 0 a) : AgreeRight T U 0 := by
  obtain ⟨n, hn, hTn⟩ := hT
  obtain ⟨m, hm, hUm⟩ := hU
  have hT' : inflateH^[n * m] T = T := (hTn.mul_const m).eq
  have hU' : inflateH^[n * m] U = U := by rw [mul_comm]; exact (hUm.mul_const n).eq
  have key : ∀ V W : L.Hull, inflateH^[n * m] V = V → inflateH^[n * m] W = W →
      StartsAt V 0 a → StartsAt W 0 a →
      ∀ p, (L.supp p ∩ Ioi 0).Nonempty → p ∈ V.1 → p ∈ W.1 := by
    intro V W hV hW haV haW p ⟨z, hz, hz0⟩ hp
    have hℓ := L.ℓ_pos a
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (z / L.ℓ a) hβ
    have hkle : k ≤ n * m * k := Nat.le_mul_of_pos_left k (Nat.mul_pos hn hm)
    have hzk : z < L.β ^ (n * m * k) * L.ℓ a := by
      rw [div_lt_iff₀ hℓ] at hk
      exact hk.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hβ.le hkle) hℓ.le)
    obtain ⟨q, ⟨hq, hzq⟩, -⟩ :=
      (tilesOn_supertile (L := L) a (n * m * k)).2 z ⟨le_of_lt hz0, hzk⟩
    have hpq : p = q := (V.2.1 z).unique ⟨hp, hz⟩ ⟨supertile_subset hV haV k hq, hzq⟩
    exact hpq ▸ supertile_subset hW haW k hq
  exact fun p hp => ⟨key T U hT' hU' haT haU p hp, key U T hU' hT' haU haT p hp⟩

/-- `VertexLaws` holds on the hull. -/
theorem vertexLaws [Nonempty α] (hβ : 1 < L.β) :
    VertexLaws (inflateH (S := L)) AgreeRight EndsAt StartsAt where
  agree_symm h := agreeRight_symm h
  start_of_end h := startsAt_of_endsAt h
  periodic_ray hT hU haT haU := periodic_ray hβ hT hU haT haU

/-! ## The hull: branch existence -/

/-- A tile common to both tilings and reaching `y` extends ray agreement back to its start. -/
theorem agree_extend {T U : L.Hull} {y : ℝ} {p : α × ℝ} (h : AgreeRight T U y)
    (hpT : p ∈ T.1) (hpU : p ∈ U.1) (hyp : y ≤ p.2 + L.ℓ p.1) :
    AgreeRight T U p.2 := by
  have side : ∀ V : L.Hull, p ∈ V.1 → ∀ q, (L.supp q ∩ Ioi p.2).Nonempty →
      ¬ (L.supp q ∩ Ioi y).Nonempty → (q ∈ V.1 ↔ q = p) := by
    intro V hpV q ⟨w, hw, hwp⟩ hqy
    have hend : q.2 + L.ℓ q.1 ≤ y := not_lt.mp fun hlt => hqy (L.supp_inter_Ioi hlt)
    have hwp' : w ∈ L.supp p := ⟨le_of_lt hwp, lt_of_lt_of_le (lt_of_lt_of_le hw.2 hend) hyp⟩
    exact ⟨fun hq => (V.2.1 w).unique ⟨hq, hw⟩ ⟨hpV, hwp'⟩, fun hq => hq ▸ hpV⟩
  intro q hq
  by_cases hqy : (L.supp q ∩ Ioi y).Nonempty
  · exact h q hqy
  · rw [side T hpT q hq hqy, side U hpU q hq hqy]

/-- At the least point of agreement a tile starts. -/
theorem startsAt_of_least {T U : L.Hull} {y : ℝ} (h : AgreeRight T U y)
    (hmin : ∀ x < y, ¬ AgreeRight T U x) : ∃ a, StartsAt T y a := by
  obtain ⟨⟨a, x⟩, ⟨hp, hy⟩, -⟩ := T.2.1 y
  refine ⟨a, ?_⟩
  simp only [LengthSubst.supp, mem_Ico] at hy
  rcases hy.1.lt_or_eq with hlt | heq
  · exfalso
    have hpU : (a, x) ∈ U.1 := (h (a, x) (L.supp_inter_Ioi (p := (a, x)) hy.2)).mp hp
    exact hmin x hlt (agree_extend (p := (a, x)) h hp hpU hy.2.le)
  · change (a, y) ∈ T.1
    rwa [← heq]

/-- With a finite alphabet, a tile starting at `y` is preceded by a tile ending at `y`. -/
theorem endsAt_of_startsAt [Finite α] {T : L.Hull} {y : ℝ} {a : α} (ha : StartsAt T y a) :
    ∃ b, EndsAt T y b := by
  have : Nonempty α := ⟨a⟩
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min L.ℓ
  have hm := L.ℓ_pos c₀
  have ha' : y ∈ L.supp (a, y) := ⟨le_rfl, by simpa using L.ℓ_pos a⟩
  obtain ⟨⟨b, x⟩, ⟨hq, hw⟩, -⟩ := T.2.1 (y - L.ℓ c₀ / 2)
  simp only [LengthSubst.supp, mem_Ico] at hw
  -- a tile meeting `y` is the tile starting there
  have notcover : ∀ d s, (d, s) ∈ T.1 → s < y → s + L.ℓ d ≤ y := by
    intro d s hds hsy
    by_contra hlt
    have hpq := (T.2.1 y).unique ⟨hds, ⟨hsy.le, not_le.mp hlt⟩⟩ ⟨ha, ha'⟩
    simp only [Prod.mk.injEq] at hpq
    linarith [hpq.2]
  have hle := notcover b x hq (by linarith)
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨c, hc⟩ := startsAt_of_endsAt (T := T) (y := x + L.ℓ b) (b := b)
      (by change (b, x + L.ℓ b - L.ℓ b) ∈ T.1; simpa using hq)
    have hce := notcover c _ hc hlt
    linarith [hc₀ c]
  · exact ⟨b, by change (b, y - L.ℓ b) ∈ T.1; rw [← heq]; simpa using hq⟩

/-- `BranchExistence` holds on the hull of a substitution on a finite alphabet: the least
point of agreement of two distinct right-asymptotic tilings is a common vertex with
different tiles ending there. -/
theorem branchExistence [Finite α] :
    BranchExistence (AgreeRight (S := L)) (EndsAt (S := L)) := by
  intro T U hne hasym
  obtain ⟨r, hr⟩ := hasym
  set A := {x : ℝ | AgreeRight T U x}
  have hA : A.Nonempty := ⟨r, hr⟩
  have hbdd : BddBelow A := by
    by_contra hnb
    refine hne (Subtype.ext (Set.ext fun p => ?_))
    obtain ⟨x, hx, hxp⟩ := not_bddBelow_iff.mp hnb p.2
    exact hx p ⟨p.2, ⟨le_rfl, by linarith [L.ℓ_pos p.1]⟩, hxp⟩
  have hy : AgreeRight T U (sInf A) := by
    intro p ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxz⟩ := exists_lt_of_csInf_lt hA hzy
    exact hx p ⟨z, hz, hxz⟩
  have hmin : ∀ x < sInf A, ¬ AgreeRight T U x :=
    fun x hx hAx => not_le.mpr hx (csInf_le hbdd hAx)
  obtain ⟨a, haT⟩ := startsAt_of_least hy hmin
  obtain ⟨a', haU⟩ := startsAt_of_least (agreeRight_symm hy)
    (fun x hx h' => hmin x hx (agreeRight_symm h'))
  obtain ⟨b, hb⟩ := endsAt_of_startsAt haT
  obtain ⟨c, hc⟩ := endsAt_of_startsAt haU
  refine ⟨sInf A, b, c, hy, hb, hc, ?_⟩
  rintro rfl
  have hbℓ := L.ℓ_pos b
  exact hmin (sInf A - L.ℓ b) (by linarith)
    (agree_extend (p := (b, sInf A - L.ℓ b)) hy hb hc (by simp))

/-! ## Theorem S on the hull -/

section Ternary

variable {L : LengthSubst (Fin 3)} {Y : Type*}

/-- **Theorem S on the legal tiling hull.**  Every local contract is discharged; the inputs
are the fields of `PublishedInputs`, the joining relation `Z` with its translation and fibre
laws, (E1) and (NM_V). -/
theorem hull_selection_dichotomy (hβ : 1 < L.β) (P : PublishedInputs L Y)
    (Z : L.Hull → L.Hull → Prop)
    (hZtranslate : ∀ t {x y}, Z x y → Z (translate t x) (translate t y))
    (hZfibre : ∀ {x y}, Z x y → P.realize x = P.realize y) (hZne : ∀ {x y}, Z x y → x ≠ y)
    (hE1 : AsymptoticSameFibre P.realize AgreeRight)
    (hNMV : NMVRight P.realize P.q₀ AgreeRight EndsAt StartsAt)
    (hTwo : TwoPeriodicLetters L.lastLetter)
    {T S U : L.Hull} (hTS : Z T S) (hTU : Z T U) (hSU : S ≠ U)
    (hAsym : RightAsymptotic AgreeRight S U) :
    ∃ t n, 0 < n ∧
      Z (translate t T) (translate t S) ∧ Z (translate t T) (translate t U) ∧
      inflateH^[n] (translate t T) = translate t T ∧
      inflateH^[n] (translate t S) = translate t S ∧
      inflateH^[n] (translate t U) = translate t U ∧
      ∃ y b c, BranchAt AgreeRight EndsAt (translate t S) (translate t U) y b c ∧
        ((y = 0 ∧ L.lastLetter^[2] b ≠ L.lastLetter^[2] c ∧ P.realize (translate t T) = P.q₀ ∧
            P.realize (translate t S) = P.q₀ ∧ P.realize (translate t U) = P.q₀) ∨
         (0 < y ∧ L.lastLetter^[2] b = L.lastLetter^[2] c ∧ L.lastLetter b = L.lastLetter c ∧
            ¬ VertexAtOrigin EndsAt (translate t S) ∧
            ¬ VertexAtOrigin EndsAt (translate t U))) :=
  selection_dichotomy rightBranchLaws (vertexLaws hβ) hβ branchExistence
    (bds_ray_iff_metric.mpr P.bds) P.A P.realize P.q₀ Z P.inflate_injective P.semiconj
    P.finite_fibres translate_injective hZtranslate hZfibre hZne P.r4 hE1 hNMV hTwo
    hTS hTU hSU hAsym

/-- Two hull tilings share no tile at level zero: the level-zero part of (Z2). -/
def NoCommonTile (T U : L.Hull) : Prop := ∀ p, p ∈ T.1 → p ∉ U.1

/-- **Case (A), vertex-type common partner, on the hull.**  If the leaves branch at the
origin and the common partner also has a vertex there, sharing no tile with either leaf,
then the last-letter map is a permutation.  So the right side lies in round-4 Lemma A's
injective regime, where (NM_V) on the right holds and case (B) is empty. -/
theorem hull_lastLetter_injective_of_vertex_partner
    {T S U : L.Hull} {x b c : Fin 3}
    (hT : T ∈ periodicPts inflateH) (hS : S ∈ periodicPts inflateH)
    (hU : U ∈ periodicPts inflateH) (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hx : EndsAt T 0 x) (hTS : NoCommonTile T S) (hTU : NoCommonTile T U) :
    Injective L.lastLetter := by
  have hb : EndsAt S 0 b := hbranch.2.1
  have hc : EndsAt U 0 c := hbranch.2.2.1
  refine injective_of_vertex_partner rightBranchLaws hT hS hU hx hb hc ?_ ?_ hbranch.2.2.2
  · rintro rfl; exact hTS _ hx hb
  · rintro rfl; exact hTU _ hx hc

end Ternary

end Psc.PeriodicPartnerHullSelection
