import PscVerif.PeriodicPartnerEventualCoincidence
import PscVerif.PeriodicPartnerHullPatches

/-!
# Transfer of dense eventual coincidence to legal patches

Primitivity embeds two legal patches in translates of the same sufficiently
inflated periodic tiling. Their shared tile supplies the initial coincidence.
The translated periodic pair has dense eventual coincidence, which restricts
to the open overlap by local agreement.
-/

namespace Psc.PeriodicPartnerLegalCoincidence

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerEventualCoincidence

variable {α : Type*} (S : LengthSubst α)

/-- A patch is legal if a translate embeds in a supertile. -/
def LegalPatch (A : Set (α × ℝ)) : Prop := ∃ a m t, A ⊆ shift t (S.supertile a m)

def patchSupport (A : Set (α × ℝ)) : Set ℝ := {x | ∃ q ∈ A, x ∈ S.supp q}

/-- The open region covered by both patches. -/
def openOverlap (A B : Set (α × ℝ)) : Set ℝ := interior (patchSupport S A ∩ patchSupport S B)

private theorem agree_of_cover {A B : Set (α × ℝ)} {W : Set ℝ}
    (hB : S.IsTiling B) (h : A ⊆ B) (hW : W ⊆ patchSupport S A) : S.AgreeOn W A B := by
  rintro q ⟨x, hxq, hxW⟩
  refine ⟨fun hq => h hq, fun hq => ?_⟩
  obtain ⟨p, hp, hxp⟩ := hW hxW
  have he := (hB x).unique ⟨hq, hxq⟩ ⟨h hp, hxp⟩
  exact he ▸ hp

private theorem legalPatch_embed [Nonempty α] {P A : Set (α × ℝ)} (hP : S.IsTiling P) {e : ℕ}
    (hprim : ∀ a b, ∃ t, (a, t) ∈ S.supertile b e) {a : α} {m : ℕ} {t : ℝ}
    (hA : A ⊆ shift t (S.supertile a m)) (j : ℕ) :
    ∃ s, A ⊆ shift s (S.inflate^[e + m + j] P) := by
  obtain ⟨q, ⟨hq, _⟩, _⟩ := tiling_iterate S hP j 0
  obtain ⟨y, hy⟩ := hprim a q.1
  let u := -(S.β ^ m * y)
  let v := -(S.β ^ (e + m) * q.2)
  have h₁ := S.shifted_supertile_subset hy m
  have h₂ := S.shifted_supertile_subset_inflate hq (e + m)
  have h₃ : shift v (shift u (S.supertile a m)) ⊆ shift v (S.supertile q.1 (e + m)) :=
    fun _ hx => h₁ hx
  have h₄ : shift (v + u) (S.supertile a m) ⊆ S.inflate^[e + m + j] P := by
    rw [iterate_add_apply, ← shift_shift]
    exact h₃.trans h₂
  let s := t - (v + u)
  have h₅ : shift s (shift (v + u) (S.supertile a m)) ⊆ shift s (S.inflate^[e + m + j] P) :=
    fun _ hx => h₄ hx
  rw [shift_shift, show s + (v + u) = t from sub_add_cancel _ _] at h₅
  exact ⟨s, hA.trans h₅⟩

/-- A periodic test tiling with one irrational dense coincidence shift
forces dense eventual coincidence on the open overlap of any two legal
patches sharing a tile. -/
theorem dense_legal_overlap [Nonempty α] {P : Set (α × ℝ)} (hP : S.IsTiling P) {p g : ℝ}
    (hp : shift p P = P) (hirr : Irrational (g / p))
    (hg : Dense (eventual S P (shift g P))) {e : ℕ}
    (hprim : ∀ a b, ∃ t, (a, t) ∈ S.supertile b e)
    {A B : Set (α × ℝ)} (hA : LegalPatch S A) (hB : LegalPatch S B) (hcommon : (A ∩ B).Nonempty) :
    openOverlap S A B ⊆ closure (eventual S A B ∩ openOverlap S A B) := by
  obtain ⟨a, m, u, hu⟩ := hA
  obtain ⟨b, n, v, hv⟩ := hB
  obtain ⟨s, hs⟩ := legalPatch_embed S hP hprim hu n
  obtain ⟨t, ht⟩ := legalPatch_embed S hP hprim hv m
  let d := e + m + n
  let R := S.inflate^[d] P
  have hRA : A ⊆ shift s R := hs
  have hRB : B ⊆ shift t R := by simpa only [R, d, Nat.add_assoc, Nat.add_comm m n] using ht
  let X := shift s R
  let w := t - s
  let period := S.β ^ d * p
  let g' := S.β ^ d * g
  have hXw : shift w X = shift t R := by simp only [X, w, shift_shift, sub_add_cancel]
  have hRT := tiling_iterate S hP d
  have hXT := S.isTiling_shift hRT s
  have hRperiod : shift period R = R := by
    dsimp [period, R]
    rw [← S.inflate_iterate_shift, hp]
  have hXperiod : shift period X = X := by
    dsimp only [X]
    rw [shift_shift, add_comm period s, ← shift_shift, hRperiod]
  have hirr' : Irrational (g' / period) := by
    dsimp [g', period]
    rwa [mul_div_mul_left _ _ (pow_ne_zero _ S.β_pos.ne')]
  have hdR : Dense (eventual S R (shift g' R)) := by
    simpa only [R, g', S.inflate_iterate_shift] using dense_inflate_iterate S hg d
  have hdX : Dense (eventual S X (shift g' X)) := by
    simpa only [X, shift_shift, add_comm s g'] using dense_shift S hdR s
  obtain ⟨q, hqA, hqB⟩ := hcommon
  have hhit : (eventual S X (shift w X)).Nonempty := by
    refine ⟨q.2 + S.ℓ q.1 / 2, mem_eventual_of_common S (hRA hqA) ?_ ?_⟩
    · rw [hXw]; exact hRB hqB
    · constructor <;> linarith [S.ℓ_pos q.1]
  have hd := dense_of_one_hit S hXT hXperiod hirr' hdX hhit
  rw [hXw] at hd
  let W := openOverlap S A B
  have hW : IsOpen W := isOpen_interior
  have hWA : S.AgreeOn W A X := agree_of_cover S hXT hRA (fun _ hx => (interior_subset hx).1)
  have hWB : S.AgreeOn W B (shift t R) := agree_of_cover S (S.isTiling_shift hRT t) hRB
    (fun _ hx => (interior_subset hx).2)
  change W ⊆ closure (eventual S A B ∩ W)
  rw [eventual_inter_eq S hW hWA hWB, inter_comm]
  exact hd.open_subset_closure_inter hW

private def windowPatch (T : S.Hull) (W : Set ℝ) : Set (α × ℝ) :=
  {q ∈ T.1 | (S.supp q ∩ W).Nonempty}

private theorem cover_window (T : S.Hull) (W : Set ℝ) :
    W ⊆ patchSupport S (windowPatch S T W) := by
  intro x hx
  obtain ⟨q, ⟨hq, hqx⟩, _⟩ := T.2.1 x
  exact ⟨q, ⟨hq, x, hqx, hx⟩, hqx⟩

private theorem legal_window (T : S.Hull) (r : ℝ) : LegalPatch S (windowPatch S T (Ioo (-r) r)) := by
  obtain ⟨a, n, t, h⟩ := T.2.2 r
  exact ⟨a, n, t, fun q hq => h q hq.1 hq.2⟩

/-- The patch result applies on the entire line to legal hull tilings
that share a tile. Each point and the shared tile fit in one legal window. -/
theorem dense_hull_of_common_tile [Nonempty α]
    (hpatch : ∀ {A B}, LegalPatch S A → LegalPatch S B → (A ∩ B).Nonempty →
      openOverlap S A B ⊆ closure (eventual S A B ∩ openOverlap S A B))
    {T U : S.Hull} (hc : (T.1 ∩ U.1).Nonempty) : Dense (eventual S T.1 U.1) := by
  obtain ⟨q, hqT, hqU⟩ := hc
  intro x
  let r := max |x| |q.2| + 1
  let W := Ioo (-r) r
  have hx : x ∈ W := abs_lt.mp (lt_of_le_of_lt (le_max_left _ _) (by dsimp [r]; linarith))
  have hq : (S.supp q ∩ W).Nonempty :=
    ⟨q.2, ⟨le_rfl, by linarith [S.ℓ_pos q.1]⟩,
      abs_lt.mp (lt_of_le_of_lt (le_max_right _ _) (by dsimp [r]; linarith))⟩
  let A := windowPatch S T W
  let B := windowPatch S U W
  have hAB : (A ∩ B).Nonempty := ⟨q, ⟨hqT, hq⟩, ⟨hqU, hq⟩⟩
  have hW : W ⊆ openOverlap S A B := interior_maximal
    (fun y hy => ⟨cover_window S T W hy, cover_window S U W hy⟩) isOpen_Ioo
  have h := hpatch (legal_window S T r) (legal_window S U r) hAB (hW hx)
  exact closure_mono (inter_subset_left.trans (eventual_mono S (fun _ ha => ha.1) (fun _ hb => hb.1))) h

/-- A shared tile after inflation is already present in a pair of tilings
fixed by a common positive power of inflation. -/
theorem common_tile_of_periodic_eventual [Nonempty α] {P Q : Set (α × ℝ)} {m : ℕ}
    (hm : 0 < m) (hP : S.inflate^[m] P = P) (hQ : S.inflate^[m] Q = Q)
    (h : (eventual S P Q).Nonempty) : (P ∩ Q).Nonempty := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  have hmn : n ≤ m * (n + 1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hm)
  obtain ⟨q, hqP, hqQ, _⟩ := level_mono S P Q hmn (interior_subset hn)
  have hP' : S.inflate^[m * (n + 1)] P = P := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hP _
  have hQ' : S.inflate^[m * (n + 1)] Q = Q := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hQ _
  exact ⟨q, hP' ▸ hqP, hQ' ▸ hqQ⟩

/-- The periodic-partner contradiction in the geometric proof. Local
witnesses agreeing with the respective periodic tilings on an open window
and sharing a tile anywhere force the periodic tilings themselves to share
a tile. -/
theorem periodic_common_tile_of_local_witnesses [Nonempty α]
    (hd : ∀ {T U : S.Hull}, (T.1 ∩ U.1).Nonempty → Dense (eventual S T.1 U.1))
    {T U T' U' : S.Hull} {m : ℕ} (hm : 0 < m)
    (hT : inflateH^[m] T = T) (hU : inflateH^[m] U = U)
    {W : Set ℝ} (hW : IsOpen W) (hw : W.Nonempty)
    (h₁ : S.AgreeOn W T.1 T'.1) (h₂ : S.AgreeOn W U.1 U'.1)
    (hc : (T'.1 ∩ U'.1).Nonempty) : (T.1 ∩ U.1).Nonempty := by
  obtain ⟨x, hx, hxW⟩ := (hd hc).exists_mem_open hW hw
  have h : x ∈ eventual S T'.1 U'.1 ∩ W := ⟨hx, hxW⟩
  rw [← eventual_inter_eq S hW h₁ h₂] at h
  apply common_tile_of_periodic_eventual S hm _ _ ⟨x, h.1⟩
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hT
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hU

/-- The paper's `B₀`, with closed support so that both tiles are retained
when the origin is a seam. -/
def originPatch (P : Set (α × ℝ)) : Set (α × ℝ) :=
  {q ∈ P | 0 ∈ Icc q.2 (q.2 + S.ℓ q.1)}

private theorem tile_ends_at_origin [Finite α] [Nonempty α] {P : Set (α × ℝ)}
    (hP : S.IsTiling P) {a : α} (hp : (a, 0) ∈ P) :
    ∃ q ∈ P, q.2 < 0 ∧ q.2 + S.ℓ q.1 = 0 := by
  obtain ⟨b, hmin⟩ := Finite.exists_min S.ℓ
  let δ := S.ℓ b / 2
  have hδ : 0 < δ := half_pos (S.ℓ_pos b)
  obtain ⟨q, ⟨hq, hqδ⟩, _⟩ := hP (-δ)
  have hs : q.2 < 0 := hqδ.1.trans_lt (neg_lt_zero.mpr hδ)
  have horigin : (0 : ℝ) ∈ S.supp (a, 0) := ⟨le_rfl, by simpa using S.ℓ_pos a⟩
  have he : q.2 + S.ℓ q.1 ≤ 0 := by
    by_contra! hn
    have hh := (hP 0).unique ⟨hq, hs.le, hn⟩ ⟨hp, horigin⟩
    exact hs.ne (congrArg Prod.snd hh)
  refine ⟨q, hq, hs, he.eq_of_not_lt ?_⟩
  intro hneg
  obtain ⟨c, hc⟩ := Psc.PeriodicPartnerEvenTails.start_after hP hq
  have hpos := hqδ.2
  have hcs : (0 : ℝ) ∈ S.supp (c, q.2 + S.ℓ q.1) := by
    refine ⟨hneg.le, ?_⟩
    change 0 < q.2 + S.ℓ q.1 + S.ℓ c
    dsimp [δ] at hpos
    linarith [hmin c, S.ℓ_pos b]
  have hh := (hP 0).unique ⟨hc, hcs⟩ ⟨hp, horigin⟩
  exact hneg.ne (congrArg Prod.snd hh)

/-- Equality of closed origin patches gives exact agreement on an open
window around the origin, including the case of an origin seam. -/
theorem agree_near_origin [Finite α] [Nonempty α] {P Q : Set (α × ℝ)}
    (hP : S.IsTiling P) (hQ : S.IsTiling Q) (h : originPatch S P = originPatch S Q) :
    ∃ r > 0, S.AgreeOn (Ioo (-r) r) P Q := by
  let A := originPatch S P
  have hAP : A ⊆ P := fun _ hp => hp.1
  have hAQ : A ⊆ Q := by
    change originPatch S P ⊆ Q
    rw [h]
    exact fun _ hq => hq.1
  obtain ⟨p, ⟨hp, hpz⟩, _⟩ := hP 0
  have hpA : p ∈ A := ⟨hp, hpz.1, hpz.2.le⟩
  have hw : ∃ l < 0, ∀ x ∈ Ioo l (p.2 + S.ℓ p.1), x ∈ patchSupport S A := by
    rcases hpz.1.lt_or_eq with hs | hs
    · exact ⟨p.2, hs, fun x hx => ⟨p, hpA, hx.1.le, hx.2⟩⟩
    · have hp' : (p.1, 0) ∈ P := by
        rwa [show (p.1, 0) = p from Prod.ext rfl hs.symm]
      obtain ⟨q, hq, hqs, hqe⟩ := tile_ends_at_origin S hP hp'
      have hqA : q ∈ A := ⟨hq, hqs.le, hqe.ge⟩
      refine ⟨q.2, hqs, fun x hx => ?_⟩
      by_cases hx' : x < 0
      · exact ⟨q, hqA, hx.1.le, hqe ▸ hx'⟩
      · exact ⟨p, hpA, hs ▸ le_of_not_gt hx', hx.2⟩
  obtain ⟨l, hl, hcover⟩ := hw
  let r := min (-l) (p.2 + S.ℓ p.1)
  have hr : 0 < r := lt_min (neg_pos.mpr hl) hpz.2
  have hW : Ioo (-r) r ⊆ patchSupport S A := by
    intro x hx
    exact hcover x ⟨by linarith [hx.1, min_le_left (-l) (p.2 + S.ℓ p.1)],
      hx.2.trans_le (min_le_right _ _)⟩
  refine ⟨r, hr, fun q hq => ?_⟩
  exact ((agree_of_cover S hP hAP hW) q hq).symm.trans ((agree_of_cover S hQ hAQ hW) q hq)

/-- The closed-origin witnesses in Barge–Štimac–Williams force the
inflation-periodic tilings themselves to share a tile. Their periods can
be different. -/
theorem periodic_common_tile_of_origin_witnesses [Finite α] [Nonempty α]
    (hd : ∀ {T U : S.Hull}, (T.1 ∩ U.1).Nonempty → Dense (eventual S T.1 U.1))
    {T U T' U' : S.Hull} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hT : inflateH^[m] T = T) (hU : inflateH^[n] U = U) {v : ℝ}
    (h₁ : originPatch S T.1 = originPatch S T'.1)
    (h₂ : originPatch S U.1 = originPatch S U'.1)
    (hc : originPatch S (shift v T'.1) = originPatch S (shift v U'.1)) : (T.1 ∩ U.1).Nonempty := by
  have hTm : inflateH^[m * n] T = T := by rw [iterate_mul]; exact IsFixedPt.iterate hT n
  have hUn : inflateH^[m * n] U = U := by rw [Nat.mul_comm, iterate_mul]; exact IsFixedPt.iterate hU m
  obtain ⟨r, hr, hTr⟩ := agree_near_origin S T.2.1 T'.2.1 h₁
  obtain ⟨s, hs, hUr⟩ := agree_near_origin S U.2.1 U'.2.1 h₂
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  have h₁' := hTr.mono (Ioo_subset_Ioo (neg_le_neg (min_le_left r s)) (min_le_left r s))
  have h₂' := hUr.mono (Ioo_subset_Ioo (neg_le_neg (min_le_right r s)) (min_le_right r s))
  have hcommon : (T'.1 ∩ U'.1).Nonempty := by
    obtain ⟨q, ⟨hq, hqz⟩, _⟩ := S.isTiling_shift T'.2.1 v 0
    have hq' : q ∈ originPatch S (shift v T'.1) := ⟨hq, hqz.1, hqz.2.le⟩
    rw [hc] at hq'
    exact ⟨(q.1, q.2 + v), hq, hq'.1⟩
  exact periodic_common_tile_of_local_witnesses S hd (Nat.mul_pos hm hn) hTm hUn isOpen_Ioo
    ⟨0, neg_lt_zero.mpr hR, hR⟩ h₁' h₂' hcommon

end Psc.PeriodicPartnerLegalCoincidence
