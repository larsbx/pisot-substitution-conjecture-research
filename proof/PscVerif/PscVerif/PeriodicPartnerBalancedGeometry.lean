import PscVerif.PeriodicPartnerEvenTails
import PscVerif.Reduction

/-!
# Balanced factors in the geometric swap cell

This is the shrinking-block step in Barge–Štimac–Williams Theorem 3.2.
It works on placements of actual substituted words with positive lengths.
The conclusion gives a common tile interior in every open subinterval of
the fundamental cell after returning from a sufficiently inflated cell.
-/

namespace Psc.PeriodicPartnerBalancedGeometry

open Function Set Psc.Binomial Psc.Reduction Psc.PeriodicPartnerHull Psc.PeriodicPartnerEvenTails

variable {α : Type*} (S : LengthSubst α)

private abbrev lengthOf (w : List α) : ℝ := (w.map S.ℓ).sum

private theorem length_append (u v : List α) :
    lengthOf S (u ++ v) = lengthOf S u + lengthOf S v := by simp [lengthOf]

private theorem subst_eq_flatMap (s : α → List α) : subst s = fun w => w.flatMap s := rfl

/-- Repeat one placed word at integer multiples of its length. -/
def repeatWord (w : List α) : Set (α × ℝ) :=
  {q | ∃ m : ℤ, q ∈ S.place w ((m : ℝ) * (w.map S.ℓ).sum)}

/-- The repeated tile set has the word length as a translation period. -/
theorem repeatWord_period (w : List α) :
    LengthSubst.shift ((w.map S.ℓ).sum) (repeatWord S w) = repeatWord S w := by
  let d := lengthOf S w
  ext ⟨a, x⟩
  change (∃ m : ℤ, (a, x + d) ∈ S.place w (m * d)) ↔
    ∃ m : ℤ, (a, x) ∈ S.place w (m * d)
  constructor
  · rintro ⟨m, hm⟩
    rw [show (m : ℝ) * d = ((m - 1 : ℤ) : ℝ) * d + d by push_cast; ring, S.place_add] at hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    have he' : q = (a, x) := Prod.ext (Prod.mk.inj he).1 (add_right_cancel (Prod.mk.inj he).2)
    exact ⟨m - 1, he' ▸ hq⟩
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [show (((m + 1 : ℤ) : ℝ) * d) = (m : ℝ) * d + d by push_cast; ring, S.place_add]
    exact List.mem_map.mpr ⟨(a, x), hm, rfl⟩

private theorem in_cell_iff {x d : ℝ} (hd : 0 < d) (m : ℤ) :
    x ∈ Ico ((m : ℝ) * d) ((m : ℝ) * d + d) ↔ ⌊x / d⌋ = m := by
  rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hd, div_lt_iff₀ hd, add_mul, one_mul]

/-- The repeated word tiles the whole line if the word is nonempty. -/
theorem isTiling_repeatWord {w : List α} (hw : w ≠ []) :
    S.IsTiling (repeatWord S w) := by
  intro x
  let d := lengthOf S w
  let m := ⌊x / d⌋
  have hd : 0 < d := S.sum_pos hw
  have hx := (in_cell_iff hd m).mpr rfl
  obtain ⟨q, hq, hqx⟩ := S.place_cover (w := w) hx
  refine ⟨q, ⟨⟨m, hq⟩, hqx⟩, ?_⟩
  rintro p ⟨⟨n, hp⟩, hpx⟩
  have hn := (in_cell_iff hd n).mp (S.supp_subset_of_mem_place hp hpx)
  subst n
  exact S.place_unique hp hq hpx hqx

private theorem place_iterate_inflate {w : List α} {x : ℝ} {Q : Set (α × ℝ)}
    (h : ∀ p ∈ S.place w x, p ∈ Q) {j : ℕ} {q : α × ℝ}
    (hq : q ∈ S.place ((subst S.σ)^[j] w) (S.β ^ j * x)) :
    q ∈ S.inflate^[j] Q := by
  have hq' : q ∈ (S.pow j).place (w.flatMap (S.pow j).σ) ((S.pow j).β * x) := by
    rw [place_pow]
    change q ∈ S.place (w.flatMap (S.iterWord j)) (S.β ^ j * x)
    rwa [flatMap_iterWord, ← subst_eq_flatMap]
  obtain ⟨p, hp, hqp⟩ := mem_place_flatMap.mp hq'
  rw [place_pow] at hp
  rw [← inflate_pow]
  exact ⟨p, h p hp, hqp⟩

private theorem mem_inflate_repeatWord {w : List α} {j : ℕ} {q : α × ℝ}
    (hq : q ∈ S.place ((subst S.σ)^[j] w) 0) (m : ℤ) :
    (q.1, q.2 + S.β ^ j * (m * lengthOf S w)) ∈ S.inflate^[j] (repeatWord S w) := by
  refine place_iterate_inflate S (Q := repeatWord S w) (x := m * lengthOf S w) (fun p hp => ⟨m, hp⟩) ?_
  rw [← zero_add (S.β ^ j * (m * lengthOf S w)), S.place_add]
  exact List.mem_map.mpr ⟨q, hq, by rw [zero_add]⟩

/-- Local density on one cell gives global density after periodization.
The seam case uses an interior point of the neighboring cell. -/
theorem dense_coincidence_repeatWord [Nonempty α] {u v : List α}
    (hu : u ≠ []) (hlen : (u.map S.ℓ).sum = (v.map S.ℓ).sum)
    (h : ∀ t ∈ Ioo 0 (u.map S.ℓ).sum, ∀ ε > 0,
      ∃ y ∈ Ioo 0 (u.map S.ℓ).sum, |y - t| < ε ∧
        ∃ (j : ℕ) (q : α × ℝ), q ∈ S.place ((subst S.σ)^[j] u) 0 ∧
          q ∈ S.place ((subst S.σ)^[j] v) 0 ∧ S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1)) :
    Dense {y : ℝ | ∃ (j : ℕ) (q : α × ℝ), q ∈ S.inflate^[j] (repeatWord S u) ∧
      q ∈ S.inflate^[j] (repeatWord S v) ∧ S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1)} := by
  rw [Metric.dense_iff]
  intro x ε hε
  let d := lengthOf S u
  let m := ⌊x / d⌋
  let r := x - m * d
  have hd : 0 < d := S.sum_pos hu
  have hx := (in_cell_iff hd m (x := x)).mpr rfl
  have hr0 : 0 ≤ r := sub_nonneg.mpr hx.1
  have hrd : r < d := by dsimp [r]; linarith [hx.2]
  let s := r + min (ε / 2) (d - r) / 2
  have hspos : 0 < min (ε / 2) (d - r) / 2 :=
    half_pos (lt_min (half_pos hε) (sub_pos.mpr hrd))
  have hs0 : 0 < s := add_pos_of_nonneg_of_pos hr0 hspos
  have hsd : s < d := by dsimp [s]; linarith [min_le_right (ε / 2) (d - r)]
  have hsnear : |s - r| < ε / 2 := by
    rw [abs_of_nonneg (by dsimp [s]; linarith [hspos])]
    dsimp [s]
    linarith [min_le_left (ε / 2) (d - r)]
  obtain ⟨y, _, hys, j, q, hqu, hqv, hq⟩ := h s ⟨hs0, hsd⟩ (ε / 2) (half_pos hε)
  let z := y + m * d
  have hclose : |z - x| < ε := by
    rw [show z - x = (y - s) + (s - r) by dsimp [z, r]; ring]
    exact (abs_add_le _ _).trans_lt (by linarith)
  refine ⟨z, by rwa [Metric.mem_ball, Real.dist_eq], ?_⟩
  refine ⟨j, (q.1, q.2 + S.β ^ j * (m * d)), mem_inflate_repeatWord S hqu m, ?_, ?_⟩
  · have hv := mem_inflate_repeatWord S hqv m
    change lengthOf S u = lengthOf S v at hlen
    rwa [← hlen] at hv
  · change S.β ^ j * (y + m * d) ∈ Ioo (q.2 + S.β ^ j * (m * d))
      (q.2 + S.β ^ j * (m * d) + S.ℓ q.1)
    rw [mul_add]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

private theorem placed_iterate_subset {u v : List α} {x y : ℝ}
    (h : ∀ q ∈ S.place u x, q ∈ S.place v y) (j : ℕ) :
    ∀ q ∈ S.place ((subst S.σ)^[j] u) (S.β ^ j * x),
      q ∈ S.place ((subst S.σ)^[j] v) (S.β ^ j * y) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    simp only [iterate_succ_apply', subst_eq_flatMap, pow_succ', mul_assoc] at ih ⊢
    intro q hq
    obtain ⟨p, hp, hq'⟩ := mem_place_flatMap.mp hq
    exact mem_place_flatMap.mpr ⟨p, ih p hp, hq'⟩

private theorem iterate_length (w : List α) (j : ℕ) :
    lengthOf S ((subst S.σ)^[j] w) = S.β ^ j * lengthOf S w := by
  simpa only [subst_eq_flatMap] using sum_iterate (L := S) j w

private theorem factor_cover {bs : List (List α × List α)}
    (hbal : ∀ U ∈ bs, U.1.Perm U.2) {x z : ℝ}
    (hz : z ∈ Ico x (x + lengthOf S (bs.flatMap Prod.fst))) :
    ∃ U ∈ bs, ∃ y, z ∈ Ico y (y + lengthOf S U.1) ∧
      (∀ q ∈ S.place U.1 y, q ∈ S.place (bs.flatMap Prod.fst) x) ∧
      (∀ q ∈ S.place U.2 y, q ∈ S.place (bs.flatMap Prod.snd) x) := by
  induction bs generalizing x with
  | nil => simp [lengthOf] at hz
  | cons U bs ih =>
    have he : lengthOf S U.1 = lengthOf S U.2 := ((hbal U (by simp)).map S.ℓ).sum_eq
    simp only [List.flatMap_cons, place_append, List.mem_append]
    by_cases h : z < x + lengthOf S U.1
    · exact ⟨U, by simp, x, ⟨hz.1, h⟩, fun q hq => Or.inl hq, fun q hq => Or.inl hq⟩
    · obtain ⟨V, hV, y, hy, ht, hb⟩ := ih (fun V hV => hbal V (by simp [hV]))
        (x := x + lengthOf S U.1) ⟨le_of_not_gt h, by
          simpa only [List.flatMap_cons, length_append, add_assoc] using hz.2⟩
      refine ⟨V, by simp [hV], y, hy, fun q hq => Or.inr (ht q hq), fun q hq => Or.inr ?_⟩
      have hq' := hb q hq
      rwa [he] at hq'

private theorem length_eq (bs : List (List α × List α)) (hb : ∀ U ∈ bs, U.1.Perm U.2) :
    lengthOf S (bs.flatMap Prod.fst) = lengthOf S (bs.flatMap Prod.snd) := by
  induction bs with
  | nil => rfl
  | cons U bs ih =>
    have he : lengthOf S U.1 = lengthOf S U.2 := ((hb U (by simp)).map S.ℓ).sum_eq
    simp only [List.flatMap_cons, length_append, he, ih (fun V hV => hb V (by simp [hV]))]

variable [DecidableEq α]

private theorem common_tile_of_factor {u v : List α} (h : Equiv1 u v) {a : α}
    (ha : ([a], [a]) ∈ red u v) (x : ℝ) :
    ∃ q, q ∈ S.place u x ∧ q ∈ S.place v x := by
  have hlen := (equiv1_iff_perm.mp h).length_eq
  have hb := red_isBlock h
  obtain ⟨bs, cs, hs⟩ := List.append_of_mem ha
  have hbs : ∀ U ∈ bs, U.1.Perm U.2 := by
    intro U hU
    exact equiv1_iff_perm.mp (hb U (by rw [hs]; simp [hU])).2.1
  have htop : u = bs.flatMap Prod.fst ++ [a] ++ cs.flatMap Prod.fst := by
    simpa [hs, List.flatMap_def, List.append_assoc] using (red_top hlen).symm
  have hbot : v = bs.flatMap Prod.snd ++ [a] ++ cs.flatMap Prod.snd := by
    simpa [hs, List.flatMap_def, List.append_assoc] using (red_bot hlen).symm
  refine ⟨(a, x + lengthOf S (bs.flatMap Prod.fst)), ?_, ?_⟩
  · simp [htop, place_append, LengthSubst.place]
  · rw [hbot, length_eq S bs hbs]
    simp [place_append, LengthSubst.place]

private theorem iterate_balanced {u v : List α} (h : Equiv1 u v) (n : ℕ) :
    Equiv1 ((subst S.σ)^[n] u) ((subst S.σ)^[n] v) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iterate_succ_apply'] using equiv1_subst S.σ ih

/-- The pulled-back common tile interiors of the two inflated tracks are
dense inside their common fundamental cell. `y` is measured in the original
cell, while `q` is the identical labelled tile at level `j`. -/
theorem dense_coincidence_in_cell [Nonempty α] (hβ : 1 < S.β) {u v : List α}
    (hb : Equiv1 u v)
    (hf : {U | ∃ n, U ∈ red ((subst S.σ)^[n] u) ((subst S.σ)^[n] v)}.Finite)
    (hp : ∀ U, (∃ n, U ∈ red ((subst S.σ)^[n] u) ((subst S.σ)^[n] v)) →
      ∃ m a, ([a], [a]) ∈ red ((subst S.σ)^[m] U.1) ((subst S.σ)^[m] U.2)) :
    ∀ t ∈ Ioo 0 (u.map S.ℓ).sum, ∀ ε > 0,
      ∃ y ∈ Ioo 0 (u.map S.ℓ).sum, |y - t| < ε ∧
        ∃ (j : ℕ) (q : α × ℝ), q ∈ S.place ((subst S.σ)^[j] u) 0 ∧
          q ∈ S.place ((subst S.σ)^[j] v) 0 ∧ S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1) := by
  intro t ht ε hε
  let W := subst S.σ
  obtain ⟨B, hB⟩ := (hf.image (fun U => lengthOf S U.1)).bddAbove
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / ε) hβ
  have hn' : B < S.β ^ n * ε := (div_lt_iff₀ hε).mp hn
  set bs := red (W^[n] u) (W^[n] v)
  have hb' := iterate_balanced S hb n
  have hlen := (equiv1_iff_perm.mp hb').length_eq
  have htop : bs.flatMap Prod.fst = W^[n] u := by
    simpa [bs, List.flatMap_def] using red_top hlen
  have hbot : bs.flatMap Prod.snd = W^[n] v := by
    simpa [bs, List.flatMap_def] using red_bot hlen
  have hz : S.β ^ n * t ∈ Ico 0 (0 + lengthOf S (bs.flatMap Prod.fst)) := by
    rw [htop, iterate_length, zero_add]
    exact ⟨(mul_pos (pow_pos S.β_pos _) ht.1).le, mul_lt_mul_of_pos_left ht.2 (pow_pos S.β_pos _)⟩
  obtain ⟨U, hU, x, hx, hu, hv⟩ := factor_cover S
    (fun V hV => equiv1_iff_perm.mp (red_isBlock hb' V hV).2.1) hz
  rw [htop] at hu
  rw [hbot] at hv
  have hUlen : lengthOf S U.1 ≤ B := hB ⟨U, ⟨n, hU⟩, rfl⟩
  obtain ⟨m, a, ha⟩ := hp U ⟨n, hU⟩
  obtain ⟨q, hqu, hqv⟩ := common_tile_of_factor S
    (iterate_balanced S (red_isBlock hb' U hU).2.1 m) ha (S.β ^ m * x)
  have hqu' : q ∈ S.place (W^[m + n] u) 0 := by
    simpa only [iterate_add_apply, mul_zero] using placed_iterate_subset S hu m q hqu
  have hqv' : q ∈ S.place (W^[m + n] v) 0 := by
    simpa only [iterate_add_apply, mul_zero] using placed_iterate_subset S hv m q hqv
  let z := q.2 + S.ℓ q.1 / 2
  let y := z / S.β ^ (m + n)
  have hy : S.β ^ (m + n) * y = z := by dsimp [y]; field_simp [S.β_pos.ne']
  have hint : z ∈ Ioo q.2 (q.2 + S.ℓ q.1) := by
    constructor <;> dsimp [z] <;> linarith [S.ℓ_pos q.1]
  have hsh : S.β ^ m * x ≤ q.2 ∧ q.2 + S.ℓ q.1 ≤
      S.β ^ m * x + lengthOf S (W^[m] U.1) := S.place_mem_bounds hqu
  rw [iterate_length, ← mul_add] at hsh
  have hL : S.β ^ n * (t - ε) < x := by rw [mul_sub]; linarith [hx.2]
  have hR : x + lengthOf S U.1 < S.β ^ n * (t + ε) := by rw [mul_add]; linarith [hx.1]
  have hyL : t - ε < y := by
    apply (mul_lt_mul_iff_of_pos_left (pow_pos S.β_pos (m + n))).mp
    rw [hy, pow_add, mul_assoc]
    exact (mul_lt_mul_of_pos_left hL (pow_pos S.β_pos _)).trans (hsh.1.trans_lt hint.1)
  have hyR : y < t + ε := by
    apply (mul_lt_mul_iff_of_pos_left (pow_pos S.β_pos (m + n))).mp
    rw [hy, pow_add, mul_assoc]
    exact (hint.2.trans_le hsh.2).trans (mul_lt_mul_of_pos_left hR (pow_pos S.β_pos _))
  have hfull : 0 ≤ q.2 ∧ q.2 + S.ℓ q.1 ≤ 0 + lengthOf S (W^[m + n] u) :=
    S.place_mem_bounds hqu'
  rw [iterate_length, zero_add] at hfull
  refine ⟨y, ⟨?_, ?_⟩, abs_lt.mpr ⟨by linarith, by linarith⟩,
    m + n, q, hqu', hqv', by simpa only [hy] using hint⟩
  · apply (mul_lt_mul_iff_of_pos_left (pow_pos S.β_pos (m + n))).mp
    rw [mul_zero, hy]
    exact hfull.1.trans_lt hint.1
  · apply (mul_lt_mul_iff_of_pos_left (pow_pos S.β_pos (m + n))).mp
    rw [hy]
    exact hint.2.trans_le hfull.2

end Psc.PeriodicPartnerBalancedGeometry
