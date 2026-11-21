import PscVerif.PeriodicPartnerHullContinuity
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Eventual coincidence of literal one-dimensional tile sets

At each inflation depth we use the interior of the region covered by common
tiles, measured in original coordinates. This includes a shared internal
seam, so passing to a later common inflation depth preserves coincidence.
-/

namespace Psc.PeriodicPartnerEventualCoincidence

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-- Points covered by a common tile at level `n`, pulled back by dilation. -/
def level (P Q : Set (α × ℝ)) (n : ℕ) : Set ℝ :=
  {x | ∃ q ∈ S.inflate^[n] P, q ∈ S.inflate^[n] Q ∧ S.β ^ n * x ∈ S.supp q}

/-- Points with a neighborhood covered by common tiles at one depth. -/
def eventual (P Q : Set (α × ℝ)) : Set ℝ := ⋃ n : ℕ, interior (level S P Q n)

theorem eventual_open (P Q : Set (α × ℝ)) : IsOpen (eventual S P Q) :=
  isOpen_iUnion fun _ => isOpen_interior

theorem eventual_mono {P P' Q Q' : Set (α × ℝ)} (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    eventual S P Q ⊆ eventual S P' Q' := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨n, interior_mono ?_ hn⟩
  rintro y ⟨q, hqP, hqQ, hqy⟩
  exact ⟨q, S.inflate_iterate_mono hP n hqP, S.inflate_iterate_mono hQ n hqQ, hqy⟩

theorem eventual_symm (P Q : Set (α × ℝ)) : eventual S P Q = eventual S Q P := by
  have he (n : ℕ) : level S P Q n = level S Q P n := by
    ext x
    exact ⟨fun ⟨q, hP, hQ, hx⟩ => ⟨q, hQ, hP, hx⟩, fun ⟨q, hQ, hP, hx⟩ => ⟨q, hP, hQ, hx⟩⟩
  simp only [eventual, he]

theorem mem_eventual_of_tile_interior {P Q : Set (α × ℝ)} {q : α × ℝ} {x : ℝ} {n : ℕ}
    (hP : q ∈ S.inflate^[n] P) (hQ : q ∈ S.inflate^[n] Q)
    (hx : S.β ^ n * x ∈ Ioo q.2 (q.2 + S.ℓ q.1)) : x ∈ eventual S P Q := by
  let W := (fun y : ℝ => S.β ^ n * y) ⁻¹' Ioo q.2 (q.2 + S.ℓ q.1)
  have hW : IsOpen W := isOpen_Ioo.preimage (continuous_const.mul continuous_id)
  have hsub : W ⊆ level S P Q n := by
    intro y hy
    exact ⟨q, hP, hQ, hy.1.le, hy.2⟩
  exact mem_iUnion.mpr ⟨n, interior_maximal hsub hW hx⟩

theorem mem_eventual_of_common {P Q : Set (α × ℝ)} {q : α × ℝ} {x : ℝ}
    (hP : q ∈ P) (hQ : q ∈ Q) (hx : x ∈ Ioo q.2 (q.2 + S.ℓ q.1)) : x ∈ eventual S P Q :=
  mem_eventual_of_tile_interior S (n := 0) hP hQ (by simpa only [pow_zero, one_mul] using hx)

theorem level_mono [Nonempty α] (P Q : Set (α × ℝ)) : Monotone (level S P Q) := by
  refine monotone_nat_of_le_succ fun n x ⟨q, hP, hQ, hx⟩ => ?_
  have hβ := S.β_pos
  have hz : S.β ^ (n + 1) * x ∈ Ico (S.β * q.2)
      (S.β * q.2 + ((S.σ q.1).map S.ℓ).sum) := by
    rw [S.eigen, pow_succ', mul_assoc, ← mul_add]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hβ.le, mul_lt_mul_of_pos_left hx.2 hβ⟩
  obtain ⟨p, hp, hpx⟩ := S.place_cover hz
  exact ⟨p, by rw [iterate_succ_apply']; exact ⟨q, hP, hp⟩,
    by rw [iterate_succ_apply']; exact ⟨q, hQ, hp⟩, hpx⟩

theorem tiling_iterate [Nonempty α] {P : Set (α × ℝ)} (hP : S.IsTiling P) (n : ℕ) :
    S.IsTiling (S.inflate^[n] P) := by
  induction n with
  | zero => exact hP
  | succ n ih => rw [iterate_succ_apply']; exact S.isTiling_inflate ih

/-- Transitivity advances both witnesses to the same level and uses the
unique tile at each point of the middle track. -/
theorem eventual_trans [Nonempty α] {P Q R : Set (α × ℝ)} (hQ : S.IsTiling Q) {x : ℝ}
    (hp : x ∈ eventual S P Q) (hr : x ∈ eventual S Q R) : x ∈ eventual S P R := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp
  obtain ⟨k, hk⟩ := mem_iUnion.mp hr
  let n := max j k
  have h : level S P Q n ∩ level S Q R n ⊆ level S P R n := by
    rintro y ⟨⟨p, hpP, hpQ, hyp⟩, q, hqQ, hqR, hyq⟩
    have he := ((tiling_iterate S hQ n) _).unique ⟨hpQ, hyp⟩ ⟨hqQ, hyq⟩
    exact ⟨p, hpP, he ▸ hqR, hyp⟩
  refine mem_iUnion.mpr ⟨n, interior_mono h ?_⟩
  rw [interior_inter]
  exact ⟨interior_mono (level_mono S P Q (le_max_left j k)) hj,
    interior_mono (level_mono S Q R (le_max_right j k)) hk⟩

private theorem level_shift (P Q : Set (α × ℝ)) (t : ℝ) (n : ℕ) :
    level S (shift t P) (shift t Q) n = (fun x => x + t) ⁻¹' level S P Q n := by
  ext x
  change (∃ q ∈ S.inflate^[n] (shift t P), q ∈ S.inflate^[n] (shift t Q) ∧ _ ∈ S.supp q) ↔
    ∃ q ∈ S.inflate^[n] P, q ∈ S.inflate^[n] Q ∧ S.β ^ n * (x + t) ∈ S.supp q
  simp only [S.inflate_iterate_shift]
  constructor
  · rintro ⟨q, hP, hQ, hx⟩
    exact ⟨(q.1, q.2 + S.β ^ n * t), hP, hQ, by simpa only [mul_add] using S.mem_supp_shift.mpr hx⟩
  · rintro ⟨⟨a, y⟩, hP, hQ, hx⟩
    have he : y - S.β ^ n * t + S.β ^ n * t = y := sub_add_cancel _ _
    refine ⟨(a, y - S.β ^ n * t), ?_, ?_, (S.mem_supp_shift (t := S.β ^ n * t)).mp ?_⟩
    · change (a, y - S.β ^ n * t + S.β ^ n * t) ∈ S.inflate^[n] P
      rwa [he]
    · change (a, y - S.β ^ n * t + S.β ^ n * t) ∈ S.inflate^[n] Q
      rwa [he]
    · simpa only [Prod.fst, Prod.snd, he, ← mul_add] using hx

theorem eventual_shift (P Q : Set (α × ℝ)) (t : ℝ) :
    eventual S (shift t P) (shift t Q) = (fun x => x + t) ⁻¹' eventual S P Q := by
  simp only [eventual, preimage_iUnion, level_shift]
  exact congrArg iUnion (funext fun n => (Homeomorph.addRight t).preimage_interior (level S P Q n) |>.symm)

private theorem agreeOn_iterate [Nonempty α] {P Q : Set (α × ℝ)} {W : Set ℝ}
    (h : S.AgreeOn W P Q) (n : ℕ) :
    S.AgreeOn ((fun z => z / S.β ^ n) ⁻¹' W) (S.inflate^[n] P) (S.inflate^[n] Q) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact ih.inflate (fun z hz => by simpa [pow_succ', div_div] using hz)

private theorem level_inter_eq [Nonempty α] {P P' Q Q' : Set (α × ℝ)} {W : Set ℝ}
    (hP : S.AgreeOn W P P') (hQ : S.AgreeOn W Q Q') (n : ℕ) :
    level S P Q n ∩ W = level S P' Q' n ∩ W := by
  ext x
  have hin (hx : x ∈ W) {q : α × ℝ} (hq : S.β ^ n * x ∈ S.supp q) :
      (S.supp q ∩ ((fun z => z / S.β ^ n) ⁻¹' W)).Nonempty := by
    refine ⟨S.β ^ n * x, hq, ?_⟩
    change S.β ^ n * x / S.β ^ n ∈ W
    rwa [mul_div_cancel_left₀ _ (pow_ne_zero _ S.β_pos.ne')]
  constructor
  · rintro ⟨⟨q, hp, hq, hqx⟩, hx⟩
    exact ⟨⟨q, (agreeOn_iterate S hP n q (hin hx hqx)).mp hp,
      (agreeOn_iterate S hQ n q (hin hx hqx)).mp hq, hqx⟩, hx⟩
  · rintro ⟨⟨q, hp, hq, hqx⟩, hx⟩
    exact ⟨⟨q, (agreeOn_iterate S hP n q (hin hx hqx)).mpr hp,
      (agreeOn_iterate S hQ n q (hin hx hqx)).mpr hq, hqx⟩, hx⟩

/-- Eventual coincidence on an open window depends only on the tiles
meeting that window, even though the witness can use a later level. -/
theorem eventual_inter_eq [Nonempty α] {P P' Q Q' : Set (α × ℝ)} {W : Set ℝ}
    (hW : IsOpen W) (hP : S.AgreeOn W P P') (hQ : S.AgreeOn W Q Q') :
    eventual S P Q ∩ W = eventual S P' Q' ∩ W := by
  have hi (n : ℕ) : interior (level S P Q n) ∩ W = interior (level S P' Q' n) ∩ W := by
    simpa only [interior_inter, hW.interior_eq] using congrArg interior (level_inter_eq S hP hQ n)
  simp only [eventual, iUnion_inter, hi]

theorem dense_inflate_iterate [Nonempty α] {P Q : Set (α × ℝ)}
    (hd : Dense (eventual S P Q)) (m : ℕ) :
    Dense (eventual S (S.inflate^[m] P) (S.inflate^[m] Q)) := by
  let f := Homeomorph.mulLeft₀ (S.β ^ m) (pow_ne_zero _ S.β_pos.ne')
  have hle (n : ℕ) : level S P Q n ⊆ f ⁻¹' level S (S.inflate^[m] P) (S.inflate^[m] Q) n := by
    intro x hx
    have hm := level_mono S P Q (Nat.le_add_right n m) hx
    simpa only [level, mem_preimage, mem_ofPred_eq, f, Homeomorph.coe_mulLeft₀,
      ← iterate_add_apply, ← mul_assoc, ← pow_add] using hm
  have hm : MapsTo f (eventual S P Q) (eventual S (S.inflate^[m] P) (S.inflate^[m] Q)) := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have h := interior_mono (hle n) hn
    rwa [← f.preimage_interior] at h
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact hm.closure f.continuous (hd x)

private theorem dense_add_preimage {U : Set ℝ} (hd : Dense U) (t : ℝ) :
    Dense ((fun x => x + t) ⁻¹' U) := by
  have hm : MapsTo (fun x : ℝ => x - t) U ((fun x => x + t) ⁻¹' U) := by
    intro x hx
    simpa only [mem_preimage, sub_add_cancel] using hx
  intro x
  have h := hm.closure (continuous_id.sub continuous_const) (hd (x + t))
  simpa only [add_sub_cancel_right] using h

theorem dense_shift {P Q : Set (α × ℝ)} (hd : Dense (eventual S P Q)) (t : ℝ) :
    Dense (eventual S (shift t P) (shift t Q)) := by
  rw [eventual_shift]
  exact dense_add_preimage hd t

private theorem reverse_dense {P : Set (α × ℝ)} {g : ℝ}
    (hd : Dense (eventual S P (shift g P))) : Dense (eventual S P (shift (-g) P)) := by
  have h := dense_shift S (P := shift g P) (Q := P) (by rwa [eventual_symm S (shift g P) P]) (-g)
  simpa only [shift_shift, neg_add_cancel, shift_zero] using h

private theorem closure_add_generator [Nonempty α] {P : Set (α × ℝ)}
    (hP : S.IsTiling P) {g : ℝ} (hg : Dense (eventual S P (shift g P))) (w : ℝ) :
    MapsTo (fun x => x + g) (closure (eventual S P (shift w P)))
      (closure (eventual S P (shift w P))) := by
  let U := eventual S P (shift w P)
  let V := eventual S P (shift g P)
  let D := V ∩ (fun x => x + w) ⁻¹' V
  have hD : Dense D := hg.inter_of_isOpen_left (dense_add_preimage hg w) (eventual_open S _ _)
  have hU : U ⊆ closure (U ∩ D) := hD.open_subset_closure_inter (eventual_open S _ _)
  have hprop : MapsTo (fun x : ℝ => x + g) (U ∩ D) U := by
    rintro x ⟨hx, hxg, hxw⟩
    have h₁ : x ∈ eventual S (shift g P) P := by rwa [eventual_symm S (shift g P) P]
    have hwg : shift g (shift w P) = shift w (shift g P) := by rw [shift_shift, shift_shift, add_comm]
    have h₂ : x ∈ eventual S (shift w P) (shift g (shift w P)) := by
      rwa [hwg, eventual_shift]
    have h₃ := eventual_trans S hP h₁ hx
    have h₄ := eventual_trans S (S.isTiling_shift hP w) h₃ h₂
    rwa [eventual_shift] at h₄
  exact fun x hx => (hprop.closure (continuous_id.add continuous_const))
    (closure_minimal hU isClosed_closure hx)

private theorem closure_add_period {P : Set (α × ℝ)} {p : ℝ} (hp : shift p P = P) (w : ℝ) :
    MapsTo (fun x => x + p) (closure (eventual S P (shift w P)))
      (closure (eventual S P (shift w P))) := by
  have hw : shift p (shift w P) = shift w P := by
    rw [shift_shift, add_comm p w, ← shift_shift, hp]
  have h : MapsTo (fun x : ℝ => x + p) (eventual S P (shift w P)) (eventual S P (shift w P)) := by
    intro x hx
    change x ∈ (fun y => y + p) ⁻¹' eventual S P (shift w P)
    rwa [← eventual_shift, hp, hw]
  exact h.closure (continuous_id.add continuous_const)

/-- The first step of Barge–Štimac–Williams Theorem 3.1 in one dimension.
For a periodic tiling with a dense coincidence set at one irrational
shift, any displacement with a single eventual coincidence has dense
eventual coincidence. -/
theorem dense_of_one_hit [Nonempty α] {P : Set (α × ℝ)} (hP : S.IsTiling P) {p g : ℝ}
    (hp : shift p P = P) (hirr : Irrational (g / p))
    (hg : Dense (eventual S P (shift g P))) {w : ℝ}
    (hhit : (eventual S P (shift w P)).Nonempty) : Dense (eventual S P (shift w P)) := by
  let C := closure (eventual S P (shift w P))
  let H : AddSubgroup ℝ := {
    carrier := {a | ∀ x : ℝ, x + a ∈ C ↔ x ∈ C}
    zero_mem' := fun x => by simp
    add_mem' := fun {a b} ha hb x => by
      rw [← add_assoc]
      exact (hb (x + a)).trans (ha x)
    neg_mem' := fun {a} ha x => by
      have h := ha (x - a)
      rw [sub_add_cancel] at h
      simpa only [sub_eq_add_neg] using h.symm }
  have memH {a : ℝ} (hf : MapsTo (fun x => x + a) C C) (hb : MapsTo (fun x => x + -a) C C) : a ∈ H := by
    intro x
    exact ⟨fun hx => by simpa only [add_neg_cancel_right] using hb hx, fun hx => hf hx⟩
  have hnegp : shift (-p) P = P := by
    have h := congrArg (shift (-p)) hp
    simpa only [shift_shift, neg_add_cancel, shift_zero] using h.symm
  have hpH := memH (closure_add_period S hp w) (closure_add_period S hnegp w)
  have hgH := memH (closure_add_generator S hP hg w) (closure_add_generator S hP (reverse_dense S hg) w)
  let G := AddSubgroup.closure ({g, p} : Set ℝ)
  have hGH : G ≤ H := by
    change AddSubgroup.closure ({g, p} : Set ℝ) ≤ H
    rw [AddSubgroup.closure_le]
    exact pair_subset_iff.mpr ⟨hgH, hpH⟩
  have hdG : Dense (G : Set ℝ) := dense_addSubgroupClosure_pair_iff.mpr hirr
  obtain ⟨x, hxo⟩ := hhit
  have hx : x ∈ C := subset_closure hxo
  have hC : (fun y => y + -x) ⁻¹' (G : Set ℝ) ⊆ C := by
    intro y hy
    have hh : ∀ z : ℝ, z + (y + -x) ∈ C ↔ z ∈ C := hGH hy
    simpa only [show x + (y + -x) = y by ring] using (hh x).mpr hx
  exact fun y => closure_minimal hC isClosed_closure (dense_add_preimage hdG (-x) y)

end Psc.PeriodicPartnerEventualCoincidence
