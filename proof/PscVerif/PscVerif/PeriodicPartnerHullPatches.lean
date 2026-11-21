import PscVerif.PeriodicPartnerEvenTails
import Mathlib.Data.Set.Finite.List
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Patch recurrence and finite local complexity for the literal legal hull

A sufficiently wide legal window contains a whole supertile of any specified
level. If a power of the substitution contains every letter in every image,
this transfers every legal window between any two hull tilings. Positive tile
lengths over a finite alphabet also give a finite list of patches up to shifts.
-/

namespace Psc.PeriodicPartnerHull.LengthSubst

open Function Set Psc.PeriodicPartnerEvenTails

variable {α : Type*} (S : LengthSubst α)

theorem tilesOn_place (w : List α) (x : ℝ) :
    S.TilesOn (Ico x (x + (w.map S.ℓ).sum)) {p | p ∈ S.place w x} := by
  refine ⟨fun _ hp => S.supp_subset_of_mem_place hp, fun z hz => ?_⟩
  obtain ⟨q, hq, hzq⟩ := S.place_cover hz
  exact ⟨q, ⟨hq, hzq⟩, fun p ⟨hp, hzp⟩ => S.place_unique hp hq hzp hzq⟩

theorem supertile_eq_place (a : α) (n : ℕ) :
    S.supertile a n = {p | p ∈ S.place (S.iterWord n a) 0} := by
  rw [supertile, ← inflate_pow]
  ext p
  simp only [inflate, mem_ofPred_eq, mem_singleton_iff, exists_eq_left, mul_zero]
  change p ∈ (S.pow n).place (S.iterWord n a) 0 ↔ _
  rw [place_pow]

theorem supertile_tilesOn [Nonempty α] (a : α) (n : ℕ) :
    S.TilesOn (Ico 0 (S.β ^ n * S.ℓ a)) (S.supertile a n) := by
  have h : S.TilesOn (Ico 0 (S.ℓ a)) {(a, 0)} := by
    have hset : {p | p ∈ S.place [a] 0} = {(a, 0)} := by ext p; simp [place]
    simpa only [hset, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, zero_add] using S.tilesOn_place [a] 0
  simpa [supertile] using S.tilesOn_inflate_iterate h n

/-- The complete descendant supertile of an occurrence, with its scaled position. -/
theorem shifted_supertile_subset {a : α} {p : α × ℝ} {m : ℕ}
    (hp : p ∈ S.supertile a m) (n : ℕ) :
    shift (-(S.β ^ n * p.2)) (S.supertile p.1 n) ⊆ S.supertile a (m + n) := by
  have h : shift (-p.2) ({(p.1, 0)} : Set (α × ℝ)) ⊆ S.supertile a m := by
    intro q hq
    have heq : (q.1, q.2 + -p.2) = (p.1, 0) := hq
    have hqp : q = p := Prod.ext (Prod.mk.inj heq).1 (by linarith [(Prod.mk.inj heq).2])
    rwa [hqp]
  have h' := S.inflate_iterate_mono h n
  rw [S.inflate_iterate_shift, mul_neg] at h'
  simpa only [supertile, add_comm m n, iterate_add_apply] using h'

/-- Every hull tiling contains a complete translated supertile at any chosen
level. The proof uses only legality and positive expanding tile lengths. -/
theorem contains_supertile_of_level [Finite α] [Nonempty α] (hβ : 1 ≤ S.β)
    (T : S.Hull) (j : ℕ) : ∃ a x, shift (-x) (S.supertile a j) ⊆ T.1 := by
  obtain ⟨aMax, hMax⟩ := Finite.exists_max S.ℓ
  let B := S.β ^ j * S.ℓ aMax
  let R := B + 1
  have hB : 0 < B := mul_pos (pow_pos S.β_pos _) (S.ℓ_pos _)
  obtain ⟨c, n, t, hlegal⟩ := T.2.2 R
  have htile := S.supertile_tilesOn c n
  have hspan (z : ℝ) (hz : z ∈ Ioo (-R) R) : z + t ∈ Ico 0 (S.β ^ n * S.ℓ c) := by
    obtain ⟨q, ⟨hq, hzs⟩, _⟩ := T.2.1 z
    exact htile.1 _ (hlegal _ hq ⟨z, hzs, hz⟩) (S.mem_supp_shift.mpr hzs)
  have hmid : t ∈ Ico 0 (S.β ^ n * S.ℓ c) := by
    simpa using hspan 0 (by constructor <;> dsimp [R] <;> linarith)
  have hjn : j ≤ n := by
    by_contra! hn
    have hupper : S.β ^ n * S.ℓ c ≤ B :=
      mul_le_mul (pow_le_pow_right₀ hβ hn.le) (hMax c) (S.ℓ_pos _).le
        (pow_nonneg S.β_pos.le _)
    have hEnd := (hspan B (by constructor <;> dsimp [R] <;> linarith)).2
    linarith [hmid.1]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjn
  have hsmall : t / S.β ^ j ∈ Ico 0 (S.β ^ m * S.ℓ c) := by
    constructor
    · exact div_nonneg hmid.1 (pow_nonneg S.β_pos.le _)
    · rw [div_lt_iff₀ (pow_pos S.β_pos _)]
      simpa only [pow_add, mul_assoc, mul_comm (S.β ^ m * S.ℓ c)] using hmid.2
  obtain ⟨p, ⟨hp, hpz⟩, _⟩ := (S.supertile_tilesOn c m).2 _ hsmall
  let x := S.β ^ j * p.2 - t
  have hleft : x ≤ 0 := by
    have hl := (le_div_iff₀ (pow_pos S.β_pos j)).mp hpz.1
    dsimp [x]
    linarith
  have hright : 0 < x + S.β ^ j * S.ℓ p.1 := by
    have hr := (div_lt_iff₀ (pow_pos S.β_pos j)).mp hpz.2
    dsimp [x]
    nlinarith
  have hsize : S.β ^ j * S.ℓ p.1 ≤ B := mul_le_mul_of_nonneg_left (hMax _) (pow_nonneg S.β_pos.le _)
  refine ⟨p.1, x, fun q hq => ?_⟩
  have hq' : (q.1, q.2 + -x) ∈ S.supertile p.1 j := hq
  have hstart : q.2 + -x ∈ S.supp (q.1, q.2 + -x) :=
    ⟨le_rfl, by have := S.ℓ_pos q.1; dsimp; linarith⟩
  have hqspan := (S.supertile_tilesOn p.1 j).1 _ hq' hstart
  have hqR : q.2 ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [hqspan.1, hqspan.2]
  have hqn : (q.1, q.2 + t) ∈ S.supertile c (j + m) := by
    rw [add_comm j m]
    apply S.shifted_supertile_subset hp j
    change (q.1, q.2 + t + -(S.β ^ j * p.2)) ∈ S.supertile p.1 j
    convert hq' using 2
    dsimp [x]
    ring
  obtain ⟨u, ⟨hu, huz⟩, _⟩ := T.2.1 q.2
  have hun := hlegal u hu ⟨q.2, huz, hqR⟩
  have huniq := (htile.2 (q.2 + t) (hspan q.2 hqR)).unique
    ⟨hqn, S.mem_supp_shift.mpr ⟨le_rfl, by simpa using S.ℓ_pos q.1⟩⟩
    ⟨hun, S.mem_supp_shift.mpr huz⟩
  have hqu : q = u := Prod.ext (Prod.mk.inj huniq).1 (by linarith [(Prod.mk.inj huniq).2])
  rwa [hqu]

/-- Any prescribed legal window occurs in any hull tiling, provided there is
a common level at which every letter occurs in every supertile. -/
theorem window_occurs [Finite α] [Nonempty α] (hβ : 1 ≤ S.β) {e : ℕ}
    (hprim : ∀ a c, ∃ t, (a, t) ∈ S.supertile c e) (T U : S.Hull) (R : ℝ) :
    ∃ s, Agree R U (translate s T) := by
  obtain ⟨a, n, t, hlegal⟩ := U.2.2 R
  obtain ⟨c, x, hpart⟩ := S.contains_supertile_of_level hβ T (e + n)
  obtain ⟨p, hp⟩ := hprim a c
  let s := x + S.β ^ n * p + t
  have hforward (q : α × ℝ) (hq : q ∈ U.1) (hz : (S.supp q ∩ Ioo (-R) R).Nonempty) :
      q ∈ (translate s T).1 := by
    change (q.1, q.2 + s) ∈ T.1
    apply hpart
    change (q.1, q.2 + s + -x) ∈ S.supertile c (e + n)
    apply S.shifted_supertile_subset hp n
    change (q.1, q.2 + s + -x + -(S.β ^ n * p)) ∈ S.supertile a n
    convert hlegal q hq hz using 2
    dsimp [s]
    ring
  refine ⟨s, fun q hz => ⟨fun hq => hforward q hq hz, fun hq => ?_⟩⟩
  obtain ⟨z, hzq, hzW⟩ := hz
  obtain ⟨u, ⟨hu, hzu⟩, _⟩ := U.2.1 z
  have heq := ((translate s T).2.1 z).unique ⟨hq, hzq⟩ ⟨hforward u hu ⟨z, hzu, hzW⟩, hzu⟩
  exact heq ▸ hu

/-- Translational finite local complexity for all hull windows at once. -/
theorem finite_local_complexity [Finite α] [Nonempty α] (R : ℝ) (hR : 0 < R) :
    ∃ F : Set (Set (α × ℝ)), F.Finite ∧ ∀ T : S.Hull,
      ∃ x, shift x {p ∈ T.1 | (S.supp p ∩ Ioo (-R) R).Nonempty} ∈ F := by
  obtain ⟨aMin, hMin⟩ := Finite.exists_min S.ℓ
  obtain ⟨aMax, hMax⟩ := Finite.exists_max S.ℓ
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * R + 2 * S.ℓ aMax) / S.ℓ aMin)
  rw [div_lt_iff₀ (S.ℓ_pos _)] at hN
  let F := ⋃ w ∈ {w : List α | w.length ≤ N}, 𝒫 {p | p ∈ S.place w 0}
  have hF : F.Finite := (List.finite_length_le (α := α) (n := N)).biUnion
    (fun w _ => (List.finite_toSet (S.place w 0)).powerset)
  refine ⟨F, hF, fun T => ?_⟩
  obtain ⟨p, ⟨hp, hps⟩, _⟩ := T.2.1 (-R)
  obtain ⟨q, ⟨hq, hqs⟩, _⟩ := T.2.1 R
  have hab : p.2 ≤ q.2 + S.ℓ q.1 := by linarith [hps.1, hqs.2]
  obtain ⟨w, hw, hlen⟩ := exists_word T.2.1 hab ⟨p.1, hp⟩ (start_after T.2.1 hq)
  have hminlen (v : List α) : (v.length : ℝ) * S.ℓ aMin ≤ (v.map S.ℓ).sum := by
    induction v with
    | nil => simp
    | cons a v ih => simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
        List.sum_cons, add_mul, one_mul]; linarith [hMin a]
  have hwlen : w.length ≤ N := by
    have hx : (w.map S.ℓ).sum < (N : ℝ) * S.ℓ aMin := by
      linarith [hps.2, hqs.1, hMax p.1, hMax q.1]
    exact Nat.le_of_lt (by exact_mod_cast (lt_of_mul_lt_mul_right
      ((hminlen w).trans_lt hx) (S.ℓ_pos _).le))
  refine ⟨p.2, mem_iUnion₂.mpr ⟨w, hwlen, ?_⟩⟩
  intro r hr
  obtain ⟨hrT, z, hrs, hzW⟩ := hr
  have hz : z ∈ Ico p.2 (p.2 + (w.map S.ℓ).sum) := by
    rw [hlen]
    exact ⟨hps.1.trans hzW.1.le, hzW.2.trans hqs.2⟩
  obtain ⟨u, hu, hzu⟩ := S.place_cover hz
  have heq := (T.2.1 z).unique ⟨hrT, hrs⟩ ⟨hw _ hu, hzu⟩
  rw [← zero_add p.2, S.place_add] at hu
  obtain ⟨v, hv, hvu⟩ := List.mem_map.mp hu
  have hvr : v = r := by
    have he := Prod.mk.inj (heq.trans hvu.symm)
    exact Prod.ext he.1.symm (by linarith [he.2])
  exact hvr ▸ hv

private def periods (T : S.Hull) : AddSubgroup ℝ where
  carrier := {t | translate t T = T}
  zero_mem' := Subtype.ext (shift_zero _)
  add_mem' {s t} hs ht := by
    change translate _ _ = _
    rw [← translate_translate, show translate t T = T from ht]
    exact hs
  neg_mem' {t} ht := by
    have h := congrArg (translate (-t)) (show translate t T = T from ht)
    rw [translate_translate, neg_add_cancel] at h
    exact h.symm.trans (Subtype.ext (shift_zero _))

/-- A tiling fixed by a power of inflation with irrational expansion at
that power has no nonzero translation period. -/
theorem aperiodic_of_inflate_fixed [Nonempty α] {T : S.Hull} {n : ℕ}
    (hfix : inflateH^[n] T = T) (hirr : Irrational (S.β ^ n)) :
    ∀ t, translate t T = T → t = 0 := by
  let G := S.periods T
  obtain ⟨p, ⟨hp, _⟩, _⟩ := T.2.1 0
  have hdisj : Disjoint (G : Set ℝ) (Ioo 0 (S.ℓ p.1)) := by
    refine disjoint_left.mpr fun s hs hsmall => ?_
    have heq : translate s T = T := hs
    have hp' : (p.1, p.2 + s) ∈ T.1 := by
      change p ∈ (translate s T).1
      rwa [heq]
    have h := (T.2.1 (p.2 + s)).unique
      ⟨hp, by constructor <;> linarith [hsmall.1, hsmall.2]⟩
      ⟨hp', by constructor <;> linarith [S.ℓ_pos p.1]⟩
    linarith [congrArg Prod.snd h, hsmall.1]
  have hnd : ¬ Dense (G : Set ℝ) := by
    intro hd
    obtain ⟨s, hsG, hs⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (S.ℓ_pos p.1))
    exact disjoint_left.mp hdisj hsG hs
  obtain ⟨a, ha⟩ := G.dense_or_cyclic.resolve_left hnd
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  intro t ht
  by_contra hne
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    have hm : t ∈ AddSubgroup.zmultiples (0 : ℝ) := ha ▸ (show t ∈ G from ht)
    exact hne (by simpa using hm)
  have haG : a ∈ G := ha.symm ▸ AddSubgroup.mem_zmultiples a
  have hi : translate (S.β ^ n * a) T = T := by
    have hs : (inflateH^[n]) (translate a T) = translate (S.β ^ n * a) (inflateH^[n] T) := by
      apply Subtype.ext
      rw [hull_iterate_val]
      change S.inflate^[n] (shift a T.1) = shift (S.β ^ n * a) (inflateH^[n] T).1
      rw [hull_iterate_val, S.inflate_iterate_shift]
    rw [show translate a T = T from haG, hfix] at hs
    exact hs.symm
  have hmem : S.β ^ n * a ∈ AddSubgroup.zmultiples a := ha ▸ (show _ ∈ G from hi)
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hz' : (z : ℝ) * a = S.β ^ n * a := by simpa [zsmul_eq_mul] using hz
  exact hirr.ne_int z (mul_right_cancel₀ ha0 hz').symm

/-- A translation period transfers to every tiling whose finite windows
occur in the given tiling. Exact agreement suffices on each window. -/
theorem period_of_windows {T U : S.Hull} {t : ℝ} (ht : translate t T = T)
    (h : ∀ R, ∃ s, Agree R U (translate s T)) : translate t U = U := by
  apply Subtype.ext
  ext p
  let R := max |p.2| |p.2 + t| + 1
  obtain ⟨s, hs⟩ := h R
  have ht' : translate t (translate s T) = translate s T := by
    rw [translate_translate, add_comm t s, ← translate_translate, ht]
  have hW (q : α × ℝ) (hq : |q.2| < R) : (S.supp q ∩ Ioo (-R) R).Nonempty :=
    ⟨q.2, ⟨le_rfl, by linarith [S.ℓ_pos q.1]⟩, abs_lt.mp hq⟩
  have hb : (p.1, p.2 + t) ∈ (translate s T).1 ↔ p ∈ (translate s T).1 := by
    change p ∈ (translate t (translate s T)).1 ↔ _
    rw [ht']
  change (p.1, p.2 + t) ∈ U.1 ↔ p ∈ U.1
  exact (hs _ (hW _ (lt_of_le_of_lt (le_max_right _ _) (by dsimp [R]; linarith)))).trans
    (hb.trans (hs _ (hW _ (lt_of_le_of_lt (le_max_left _ _) (by dsimp [R]; linarith)))).symm)

end Psc.PeriodicPartnerHull.LengthSubst
