/-
# Even incidence: the tail argument on literal tilings

`PeriodicPartnerLiteralDefect.eq_of_common_padding` is the word theorem: if every image of a
substitution has even letter counts, then `u.flatMap s = l ++ u ++ r` and
`v.flatMap s = l ++ v ++ r` force `u = v`.  The companion note
`docs/c4-literal-periodic-defect-2026-11-20.md` transfers it to tilings by a written interval
argument.  This module checks that transfer for tile sets of a `LengthSubst` with half-open
supports:

* `eq_of_two_tails`: two inflation-fixed tilings that agree to the left of a common vertex
  `a ≤ 0` and to the right of a common vertex `b ≥ 0` are equal;
* `agree_right_of_vertex`: two inflation-fixed tilings with a vertex at the origin that agree
  to the right of a common vertex `b ≥ 0` agree on all of `(0, ∞)`.

The bridge from tile sets to words is `exists_word` (a finite alphabet gives a positive
minimal length), `word_unique`, `place_flatMap_subset` and `inflate_word`.  The tilings need
not be legal, and no Pisot or primitivity hypothesis enters.  `1 ≤ β` places the inflated
interval around the original one.

The hypothesis is on the images of the substitution used.  For the C4 application it is
`σ^(jp)` with `M^j ≡ 0 (mod 2)` and common period `p`; `pow` builds that power as a
`LengthSubst`, `inflate_pow` identifies its inflation with the iterate, and the `hull_`
theorems state both results for hull tilings at a common period.
-/
import PscVerif.PeriodicPartnerHull
import PscVerif.PeriodicPartnerLiteralDefect
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

namespace Psc.PeriodicPartnerEvenTails

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

variable {α : Type*} {L : LengthSubst α}

/-! ## Words placed in tile sets -/

theorem place_append (u v : List α) (x : ℝ) :
    L.place (u ++ v) x = L.place u x ++ L.place v (x + (u.map L.ℓ).sum) := by
  induction u generalizing x with
  | nil => simp [LengthSubst.place]
  | cons a u ih =>
    simp only [List.cons_append, LengthSubst.place, ih, List.map_cons, List.sum_cons, add_assoc]

theorem sum_flatMap (w : List α) :
    ((w.flatMap L.σ).map L.ℓ).sum = L.β * (w.map L.ℓ).sum := by
  induction w with
  | nil => simp
  | cons a w ih => simp [List.flatMap_cons, L.eigen, ih, mul_add]

/-- Inflation places the image word of a placed word. -/
theorem place_flatMap_subset {T : Set (α × ℝ)} {w : List α} {x : ℝ}
    (h : ∀ q ∈ L.place w x, q ∈ T) :
    ∀ q ∈ L.place (w.flatMap L.σ) (L.β * x), q ∈ L.inflate T := by
  induction w generalizing x with
  | nil => simp [LengthSubst.place]
  | cons a w ih =>
    intro q hq
    rw [List.flatMap_cons, place_append, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ⟨(a, x), h _ (by simp [LengthSubst.place]), hq⟩
    · rw [L.eigen, ← mul_add] at hq
      exact ih (fun q hq' => h q (by simp [LengthSubst.place, hq'])) q hq

/-- Two words placed from the same point of a tiling, with the same total length, are equal. -/
theorem word_unique {T : Set (α × ℝ)} (hT : L.IsTiling T) {u v : List α} {x : ℝ}
    (hu : ∀ q ∈ L.place u x, q ∈ T) (hv : ∀ q ∈ L.place v x, q ∈ T)
    (hlen : (u.map L.ℓ).sum = (v.map L.ℓ).sum) : u = v := by
  induction u generalizing v x with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v =>
      have h := L.sum_pos (List.cons_ne_nil b v)
      rw [← hlen] at h
      simp at h
  | cons a u ih =>
    cases v with
    | nil =>
      have h := L.sum_pos (List.cons_ne_nil a u)
      rw [hlen] at h
      simp at h
    | cons b v =>
      have ha := hu (a, x) (by simp [LengthSubst.place])
      have hb := hv (b, x) (by simp [LengthSubst.place])
      have hab : (a, x) = (b, x) := (hT x).unique
        ⟨ha, by simp [LengthSubst.supp, L.ℓ_pos a]⟩ ⟨hb, by simp [LengthSubst.supp, L.ℓ_pos b]⟩
      obtain rfl : a = b := congrArg Prod.fst hab
      congr 1
      exact ih (x := x + L.ℓ a) (fun q hq => hu q (List.mem_cons_of_mem _ hq))
        (fun q hq => hv q (List.mem_cons_of_mem _ hq)) (by simpa using hlen)

/-- The tile covering the end of a tile starts there. -/
theorem start_after {T : Set (α × ℝ)} (hT : L.IsTiling T) {p : α × ℝ} (hp : p ∈ T) :
    ∃ c, (c, p.2 + L.ℓ p.1) ∈ T := by
  obtain ⟨⟨c, x⟩, ⟨hq, hy⟩, -⟩ := hT (p.2 + L.ℓ p.1)
  refine ⟨c, ?_⟩
  simp only [LengthSubst.supp, mem_Ico] at hy
  have hℓ := L.ℓ_pos p.1
  rcases hy.1.lt_or_eq with hlt | heq
  · exfalso
    have hz : max x p.2 < p.2 + L.ℓ p.1 := max_lt hlt (by linarith)
    have h1 : max x p.2 ∈ L.supp (c, x) := ⟨le_max_left _ _, lt_trans hz hy.2⟩
    have h2 : max x p.2 ∈ L.supp p := ⟨le_max_right _ _, hz⟩
    have hpq := (hT _).unique ⟨hq, h1⟩ ⟨hp, h2⟩
    rw [Prod.ext_iff] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    linarith [hy.2]
  · rwa [heq] at hq

/-- Between two vertices of a tiling over a finite alphabet lies a placed word. -/
theorem exists_word [Finite α] {T : Set (α × ℝ)} (hT : L.IsTiling T) {a b : ℝ} (hab : a ≤ b)
    (ha : ∃ c, (c, a) ∈ T) (hb : ∃ c, (c, b) ∈ T) :
    ∃ w, (∀ q ∈ L.place w a, q ∈ T) ∧ a + (w.map L.ℓ).sum = b := by
  have : Nonempty α := ⟨ha.choose⟩
  obtain ⟨m₀, hm₀⟩ := Finite.exists_min L.ℓ
  have hm := L.ℓ_pos m₀
  obtain ⟨d, hd⟩ := hb
  suffices key : ∀ n : ℕ, ∀ a : ℝ, a ≤ b → b - a < n * L.ℓ m₀ → (∃ c, (c, a) ∈ T) →
      ∃ w, (∀ q ∈ L.place w a, q ∈ T) ∧ a + (w.map L.ℓ).sum = b by
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / L.ℓ m₀)
    exact key n a hab (by rwa [div_lt_iff₀ hm] at hn) ha
  intro n
  induction n with
  | zero => intro a hab hn _; simp at hn; linarith
  | succ n ih =>
    intro a hab hn ⟨c, hc⟩
    rcases hab.lt_or_eq with hlt | heq
    · have hcb : a + L.ℓ c ≤ b := by
        by_contra hcon
        have hpq := (hT b).unique ⟨hc, ⟨hlt.le, not_le.mp hcon⟩⟩
          ⟨hd, by simp [LengthSubst.supp, L.ℓ_pos d]⟩
        have := congrArg Prod.snd hpq
        simp only at this
        linarith
      obtain ⟨w, hw, hsum⟩ := ih (a + L.ℓ c) hcb
        (by push_cast at hn; linarith [hm₀ c]) (start_after hT hc)
      refine ⟨c :: w, fun q hq => ?_, by simp only [List.map_cons, List.sum_cons]; linarith⟩
      simp only [LengthSubst.place, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hc
      · exact hw q hq
    · exact ⟨[], by simp [LengthSubst.place], by simp [heq]⟩

/-- An inflation-fixed tiling has a vertex at `β a` when it has one at `a`. -/
theorem vertex_inflate {T : Set (α × ℝ)} (hfix : L.inflate T = T) {a : ℝ}
    (ha : ∃ c, (c, a) ∈ T) : ∃ c, (c, L.β * a) ∈ T := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, w, hw⟩ := List.exists_cons_of_ne_nil (L.ne_nil c)
  refine ⟨d, hfix ▸ ⟨(c, a), hc, ?_⟩⟩
  simp [hw, LengthSubst.place]

/-- **Decomposition.**  In an inflation-fixed tiling, the image of the word on `[a, b]`, with
`a ≤ 0 ≤ b`, is that word padded by the words on `[β a, a]` and `[b, β b]`. -/
theorem inflate_word [Finite α] {T : Set (α × ℝ)} (hT : L.IsTiling T)
    (hfix : L.inflate T = T) (hβ : 1 ≤ L.β) {u : List α} {a b : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (hu : ∀ q ∈ L.place u a, q ∈ T) (hub : a + (u.map L.ℓ).sum = b)
    (hav : ∃ c, (c, a) ∈ T) (hbv : ∃ c, (c, b) ∈ T) :
    ∃ l r, (∀ q ∈ L.place l (L.β * a), q ∈ T) ∧ L.β * a + (l.map L.ℓ).sum = a ∧
      (∀ q ∈ L.place r b, q ∈ T) ∧ b + (r.map L.ℓ).sum = L.β * b ∧
      u.flatMap L.σ = l ++ u ++ r := by
  obtain ⟨l, hl, hlsum⟩ := exists_word hT (by nlinarith) (vertex_inflate hfix hav) hav
  obtain ⟨r, hr, hrsum⟩ := exists_word hT (by nlinarith) hbv (vertex_inflate hfix hbv)
  refine ⟨l, r, hl, hlsum, hr, hrsum, word_unique (x := L.β * a) hT ?_ ?_ ?_⟩
  · intro q hq
    have := place_flatMap_subset hu q hq
    rwa [hfix] at this
  · intro q hq
    rw [place_append, place_append, List.mem_append, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact hl q hq
    · rw [hlsum] at hq; exact hu q hq
    · rw [List.map_append, List.sum_append, ← add_assoc, hlsum, hub] at hq; exact hr q hq
  · simp only [sum_flatMap, List.map_append, List.sum_append]
    rw [show (u.map L.ℓ).sum = b - a by linarith, mul_sub]
    linarith

/-! ## The two tail theorems -/

/-- A placed word in `T` that also lies in `U` covers every tile of `T` inside its span. -/
theorem mem_of_word {T U : Set (α × ℝ)} (hT : L.IsTiling T) {u : List α} {a : ℝ}
    (huT : ∀ q ∈ L.place u a, q ∈ T) (huU : ∀ q ∈ L.place u a, q ∈ U)
    {p : α × ℝ} (hp : p ∈ T) (h1 : a ≤ p.2) (h2 : p.2 < a + (u.map L.ℓ).sum) : p ∈ U := by
  obtain ⟨q, hq, hzq⟩ := L.place_cover (w := u) (x := a) (z := p.2) ⟨h1, h2⟩
  have hpq : p = q :=
    (hT p.2).unique ⟨hp, by simp [LengthSubst.supp, L.ℓ_pos p.1]⟩ ⟨huT q hq, hzq⟩
  exact hpq ▸ huU q hq

/-- Words of two tilings on a common agreement interval coincide. -/
theorem pad_eq {T U : Set (α × ℝ)} (hU : L.IsTiling U) {W : Set ℝ} (hTU : L.AgreeOn W T U)
    {l l' : List α} {x y : ℝ} (hl : ∀ q ∈ L.place l x, q ∈ T) (hl' : ∀ q ∈ L.place l' x, q ∈ U)
    (hsum : x + (l.map L.ℓ).sum = y) (hsum' : x + (l'.map L.ℓ).sum = y)
    (hW : ∀ q ∈ L.place l x, (L.supp q ∩ W).Nonempty) : l = l' :=
  word_unique hU (fun q hq => (hTU q (hW q hq)).mp (hl q hq)) hl' (by linarith)

/-- Right pads agree when the tilings agree beyond `b`. -/
theorem right_pads {S U : Set (α × ℝ)} (hU : L.IsTiling U) {b : ℝ}
    (hright : L.AgreeOn (Ioi b) S U) {r r' : List α} (hr : ∀ q ∈ L.place r b, q ∈ S)
    (hr' : ∀ q ∈ L.place r' b, q ∈ U) (hrsum : b + (r.map L.ℓ).sum = L.β * b)
    (hrsum' : b + (r'.map L.ℓ).sum = L.β * b) : r = r' :=
  pad_eq hU hright hr hr' hrsum hrsum' fun q hq => L.supp_inter_Ioi (by
    linarith [(L.place_mem_bounds hq).1, L.ℓ_pos q.1])

/-- Left pads agree when the tilings agree before `a`. -/
theorem left_pads {S U : Set (α × ℝ)} (hU : L.IsTiling U) {a : ℝ}
    (hleft : L.AgreeOn (Iio a) S U) {l l' : List α} (hl : ∀ q ∈ L.place l (L.β * a), q ∈ S)
    (hl' : ∀ q ∈ L.place l' (L.β * a), q ∈ U) (hlsum : L.β * a + (l.map L.ℓ).sum = a)
    (hlsum' : L.β * a + (l'.map L.ℓ).sum = a) : l = l' :=
  pad_eq hU hleft hl hl' hlsum hlsum' fun q hq =>
    ⟨q.2, by simp [LengthSubst.supp, L.ℓ_pos q.1], by
      show q.2 < a
      linarith [(L.place_mem_bounds hq).2, L.ℓ_pos q.1, hlsum]⟩

/-- Pads at the inflation centre are empty. -/
theorem centre_pad {l : List α} (h : L.β * 0 + (l.map L.ℓ).sum = 0) : l = [] := by
  by_contra hne
  have := L.sum_pos hne
  simp at h
  linarith

theorem two_sided_words [Finite α] [DecidableEq α] (hev : ∀ a b, Even ((L.σ a).count b))
    (hβ : 1 ≤ L.β) {S U : Set (α × ℝ)} (hS : L.IsTiling S) (hU : L.IsTiling U)
    (hSf : L.inflate S = S) (hUf : L.inflate U = U) {a b : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (haS : ∃ c, (c, a) ∈ S) (haU : ∃ c, (c, a) ∈ U)
    (hbS : ∃ c, (c, b) ∈ S) (hbU : ∃ c, (c, b) ∈ U)
    (hleft : ∀ {l l' : List α}, (∀ q ∈ L.place l (L.β * a), q ∈ S) →
      (∀ q ∈ L.place l' (L.β * a), q ∈ U) → L.β * a + (l.map L.ℓ).sum = a →
      L.β * a + (l'.map L.ℓ).sum = a → l = l')
    (hright : ∀ {r r' : List α}, (∀ q ∈ L.place r b, q ∈ S) → (∀ q ∈ L.place r' b, q ∈ U) →
      b + (r.map L.ℓ).sum = L.β * b → b + (r'.map L.ℓ).sum = L.β * b → r = r') :
    ∃ u, (∀ q ∈ L.place u a, q ∈ S) ∧ (∀ q ∈ L.place u a, q ∈ U) ∧
      a + (u.map L.ℓ).sum = b := by
  have hab : a ≤ b := ha0.trans hb0
  obtain ⟨u, hu, husum⟩ := exists_word hS hab haS hbS
  obtain ⟨v, hv, hvsum⟩ := exists_word hU hab haU hbU
  obtain ⟨l, r, hl, hlsum, hr, hrsum, huimg⟩ := inflate_word hS hSf hβ ha0 hb0 hu husum haS hbS
  obtain ⟨l', r', hl', hlsum', hr', hrsum', hvimg⟩ :=
    inflate_word hU hUf hβ ha0 hb0 hv hvsum haU hbU
  have hll : l = l' := hleft hl hl' hlsum hlsum'
  have hrr : r = r' := hright hr hr' hrsum hrsum'
  subst hll hrr
  have huv : u = v := Psc.PeriodicPartnerLiteralDefect.eq_of_common_padding L.σ hev huimg hvimg
  subst huv
  exact ⟨u, hu, hv, husum⟩

/-- **Both tails.**  Under even incidence, two inflation-fixed tilings that agree to the left
of a common vertex `a ≤ 0` and to the right of a common vertex `b ≥ 0` are equal. -/
theorem eq_of_two_tails [Finite α] [DecidableEq α] (hev : ∀ a b, Even ((L.σ a).count b))
    (hβ : 1 ≤ L.β) {S U : Set (α × ℝ)} (hS : L.IsTiling S) (hU : L.IsTiling U)
    (hSf : L.inflate S = S) (hUf : L.inflate U = U) {a b : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (haS : ∃ c, (c, a) ∈ S) (haU : ∃ c, (c, a) ∈ U)
    (hbS : ∃ c, (c, b) ∈ S) (hbU : ∃ c, (c, b) ∈ U)
    (hleft : L.AgreeOn (Iio a) S U) (hright : L.AgreeOn (Ioi b) S U) : S = U := by
  obtain ⟨u, huS, huU, husum⟩ := two_sided_words hev hβ hS hU hSf hUf ha0 hb0 haS haU hbS hbU
    (left_pads hU hleft) (right_pads hU hright)
  have side : ∀ {T V : Set (α × ℝ)}, L.IsTiling T → L.AgreeOn (Iio a) T V →
      L.AgreeOn (Ioi b) T V → (∀ q ∈ L.place u a, q ∈ T) → (∀ q ∈ L.place u a, q ∈ V) →
      ∀ p ∈ T, p ∈ V := by
    intro T V hT hl hr hut huv p hp
    by_cases hpl : p.2 < a
    · exact (hl p ⟨p.2, by simp [LengthSubst.supp, L.ℓ_pos p.1], hpl⟩).mp hp
    by_cases hpr : b < p.2 + L.ℓ p.1
    · exact (hr p (L.supp_inter_Ioi hpr)).mp hp
    exact mem_of_word hT hut huv hp (not_lt.mp hpl) (by linarith [L.ℓ_pos p.1])
  have symm : ∀ {W : Set ℝ}, L.AgreeOn W S U → L.AgreeOn W U S := fun h p hp => (h p hp).symm
  ext p
  exact ⟨side hS hleft hright huS huU p, side hU (symm hleft) (symm hright) huU huS p⟩

/-- **Vertex at the origin.**  Under even incidence, two inflation-fixed tilings with a vertex
at the origin that agree to the right of a common vertex `b ≥ 0` agree on `(0, ∞)`. -/
theorem agree_right_of_vertex [Finite α] [DecidableEq α]
    (hev : ∀ a b, Even ((L.σ a).count b)) (hβ : 1 ≤ L.β) {S U : Set (α × ℝ)}
    (hS : L.IsTiling S) (hU : L.IsTiling U) (hSf : L.inflate S = S) (hUf : L.inflate U = U)
    (h0S : ∃ c, (c, 0) ∈ S) (h0U : ∃ c, (c, 0) ∈ U) {b : ℝ} (hb0 : 0 ≤ b)
    (hbS : ∃ c, (c, b) ∈ S) (hbU : ∃ c, (c, b) ∈ U) (hright : L.AgreeOn (Ioi b) S U) :
    L.AgreeOn (Ioi 0) S U := by
  obtain ⟨u, huS, huU, husum⟩ := two_sided_words hev hβ hS hU hSf hUf le_rfl hb0 h0S h0U
    hbS hbU (fun _ _ hlsum hlsum' => (centre_pad hlsum).trans (centre_pad hlsum').symm)
    (right_pads hU hright)
  have side : ∀ {T V : Set (α × ℝ)}, L.IsTiling T → (∃ c, (c, 0) ∈ T) →
      L.AgreeOn (Ioi b) T V → (∀ q ∈ L.place u 0, q ∈ T) → (∀ q ∈ L.place u 0, q ∈ V) →
      ∀ p ∈ T, (L.supp p ∩ Ioi 0).Nonempty → p ∈ V := by
    intro T V hT ⟨c, hc⟩ hr hut huv p hp hp0
    by_cases hpr : b < p.2 + L.ℓ p.1
    · exact (hr p (L.supp_inter_Ioi hpr)).mp hp
    have hstart : 0 ≤ p.2 := by
      by_contra hneg
      replace hneg := not_le.mp hneg
      obtain ⟨z, hz, hz0⟩ := hp0
      have hpc := (hT 0).unique ⟨hp, ⟨hneg.le, by linarith [hz.2, hz0.out]⟩⟩
        ⟨hc, by simp [LengthSubst.supp, L.ℓ_pos c]⟩
      have := congrArg Prod.snd hpc
      simp only at this
      linarith
    exact mem_of_word hT hut huv hp (by simpa using hstart) (by linarith [L.ℓ_pos p.1])
  intro p hp
  exact ⟨fun h => side hS h0S hright huS huU p h hp,
    fun h => side hU h0U (fun q hq => (hright q hq).symm) huU huS p h hp⟩

/-- **Origin vertex, left side.**  Under even incidence, two inflation-fixed tilings with a
vertex at the origin that agree before a common vertex `a ≤ 0` agree on `(-∞, 0)`. -/
theorem agree_left_of_vertex [Finite α] [DecidableEq α]
    (hev : ∀ a b, Even ((L.σ a).count b)) (hβ : 1 ≤ L.β) {S U : Set (α × ℝ)}
    (hS : L.IsTiling S) (hU : L.IsTiling U) (hSf : L.inflate S = S) (hUf : L.inflate U = U)
    (h0S : ∃ c, (c, 0) ∈ S) (h0U : ∃ c, (c, 0) ∈ U) {a : ℝ} (ha0 : a ≤ 0)
    (haS : ∃ c, (c, a) ∈ S) (haU : ∃ c, (c, a) ∈ U) (hleft : L.AgreeOn (Iio a) S U) :
    L.AgreeOn (Iio 0) S U := by
  obtain ⟨u, huS, huU, husum⟩ := two_sided_words hev hβ hS hU hSf hUf ha0 le_rfl haS haU
    h0S h0U (left_pads hU hleft) (fun _ _ hrsum hrsum' =>
      (centre_pad (by linarith : L.β * 0 + _ = 0)).trans
        (centre_pad (by linarith : L.β * 0 + _ = 0)).symm)
  have side : ∀ {T V : Set (α × ℝ)}, L.IsTiling T → L.AgreeOn (Iio a) T V →
      (∀ q ∈ L.place u a, q ∈ T) → (∀ q ∈ L.place u a, q ∈ V) →
      ∀ p ∈ T, (L.supp p ∩ Iio 0).Nonempty → p ∈ V := by
    intro T V hT hl hut huv p hp ⟨z, hz, hz0⟩
    by_cases hpl : p.2 < a
    · exact (hl p ⟨p.2, by simp [LengthSubst.supp, L.ℓ_pos p.1], hpl⟩).mp hp
    exact mem_of_word hT hut huv hp (not_lt.mp hpl) (by
      rw [husum]; exact lt_of_le_of_lt hz.1 hz0)
  intro p hp
  exact ⟨fun h => side hS hleft huS huU p h hp,
    fun h => side hU (fun q hq => (hleft q hq).symm) huU huS p h hp⟩

/-! ## Powers of the substitution -/

/-- The image of `a` under the `k`-th power of the substitution. -/
def _root_.Psc.PeriodicPartnerHull.LengthSubst.iterWord (L : LengthSubst α) (k : ℕ) (a : α) : List α := (fun w => w.flatMap L.σ)^[k] [a]

theorem iterate_flatMap_append (k : ℕ) (u v : List α) :
    (fun w => w.flatMap L.σ)^[k] (u ++ v) =
      (fun w => w.flatMap L.σ)^[k] u ++ (fun w => w.flatMap L.σ)^[k] v := by
  induction k generalizing u v with
  | zero => rfl
  | succ k ih => simp only [iterate_succ_apply, List.flatMap_append, ih]

theorem flatMap_iterWord (k : ℕ) (w : List α) :
    w.flatMap (L.iterWord k) = (fun w => w.flatMap L.σ)^[k] w := by
  induction w with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply', ← ih]; rfl
  | cons a w ih =>
    rw [List.flatMap_cons, ih, show a :: w = [a] ++ w from rfl, iterate_flatMap_append]; rfl

theorem sum_iterate (k : ℕ) (w : List α) :
    (((fun w => w.flatMap L.σ)^[k] w).map L.ℓ).sum = L.β ^ k * (w.map L.ℓ).sum := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', sum_flatMap, ih, pow_succ', mul_assoc]

theorem iterWord_ne_nil (k : ℕ) (a : α) : L.iterWord k a ≠ [] := by
  intro h
  have : Nonempty α := ⟨a⟩
  have := sum_iterate (L := L) k [a]
  rw [← iterWord, h] at this
  simp at this
  rcases this with h0 | h0
  · exact absurd h0.1 L.β_pos.ne'
  · exact (L.ℓ_pos a).ne' h0

/-- The `k`-th power as a substitution with the same tile lengths and dilation `β ^ k`. -/
def _root_.Psc.PeriodicPartnerHull.LengthSubst.pow (L : LengthSubst α) (k : ℕ) : LengthSubst α where
  σ := L.iterWord k
  ne_nil := iterWord_ne_nil k
  ℓ := L.ℓ
  ℓ_pos := L.ℓ_pos
  β := L.β ^ k
  eigen a := by simpa [iterWord] using sum_iterate (L := L) k [a]

theorem mem_place_flatMap {w : List α} {x : ℝ} {q : α × ℝ} :
    q ∈ L.place (w.flatMap L.σ) (L.β * x) ↔
      ∃ p ∈ L.place w x, q ∈ L.place (L.σ p.1) (L.β * p.2) := by
  induction w generalizing x with
  | nil => simp [LengthSubst.place]
  | cons a w ih =>
    rw [List.flatMap_cons, place_append, List.mem_append, L.eigen, ← mul_add, ih]
    simp [LengthSubst.place]

theorem place_pow (k : ℕ) (w : List α) (x : ℝ) : (L.pow k).place w x = L.place w x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact congrArg _ (ih _)

/-- Inflating by the power is iterating the inflation. -/
theorem inflate_pow (k : ℕ) (T : Set (α × ℝ)) : (L.pow k).inflate T = L.inflate^[k] T := by
  have key : ∀ q, q ∈ L.inflate^[k] T ↔
      ∃ p ∈ T, q ∈ L.place (L.iterWord k p.1) (L.β ^ k * p.2) := by
    induction k with
    | zero => intro q; simp [iterWord, LengthSubst.place]
    | succ k ih =>
      intro q
      rw [iterate_succ_apply']
      constructor
      · rintro ⟨p', hp', hq⟩
        obtain ⟨p, hp, hp'p⟩ := (ih p').mp hp'
        refine ⟨p, hp, ?_⟩
        rw [iterWord, iterate_succ_apply', ← iterWord, pow_succ', mul_assoc]
        exact mem_place_flatMap.mpr ⟨p', hp'p, hq⟩
      · rintro ⟨p, hp, hq⟩
        rw [iterWord, iterate_succ_apply', ← iterWord, pow_succ', mul_assoc] at hq
        obtain ⟨p', hp'p, hq'⟩ := mem_place_flatMap.mp hq
        exact ⟨p', (ih p').mpr ⟨p, hp, hp'p⟩, hq'⟩
  ext q
  rw [key]
  change (∃ p ∈ T, q ∈ (L.pow k).place (L.iterWord k p.1) (L.β ^ k * p.2)) ↔ _
  simp only [place_pow]

/-! ## On the hull, at a common period -/

theorem hull_iterate_val [Nonempty α] (T : L.Hull) (n : ℕ) :
    (inflateH^[n] T).1 = L.inflate^[n] T.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

/-- **Both tails on the hull.**  Hull tilings fixed by `Φⁿ`, where the images of `σⁿ` have even
letter counts, that agree beyond common vertices `a ≤ 0 ≤ b` on both sides are equal. -/
theorem hull_eq_of_two_tails [Finite α] [Nonempty α] [DecidableEq α] {n : ℕ}
    (hev : ∀ a b, Even ((L.iterWord n a).count b)) (hβ : 1 ≤ L.β) {S U : L.Hull}
    (hS : inflateH^[n] S = S) (hU : inflateH^[n] U = U) {a b : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (haS : ∃ c, (c, a) ∈ S.1) (haU : ∃ c, (c, a) ∈ U.1)
    (hbS : ∃ c, (c, b) ∈ S.1) (hbU : ∃ c, (c, b) ∈ U.1)
    (hleft : L.AgreeOn (Iio a) S.1 U.1) (hright : L.AgreeOn (Ioi b) S.1 U.1) : S = U :=
  Subtype.ext <| eq_of_two_tails (L := L.pow n) hev (one_le_pow₀ hβ) S.2.1 U.2.1
    (by rw [inflate_pow, ← hull_iterate_val, hS]) (by rw [inflate_pow, ← hull_iterate_val, hU])
    ha0 hb0 haS haU hbS hbU hleft hright

/-- **Origin vertex on the hull.**  Hull tilings fixed by `Φⁿ`, with even images of `σⁿ`,
a vertex at the origin, and agreement beyond a common vertex `b ≥ 0`, agree on `(0, ∞)`. -/
theorem hull_agree_right_of_vertex [Finite α] [Nonempty α] [DecidableEq α] {n : ℕ}
    (hev : ∀ a b, Even ((L.iterWord n a).count b)) (hβ : 1 ≤ L.β) {S U : L.Hull}
    (hS : inflateH^[n] S = S) (hU : inflateH^[n] U = U)
    (h0S : ∃ c, (c, 0) ∈ S.1) (h0U : ∃ c, (c, 0) ∈ U.1) {b : ℝ} (hb0 : 0 ≤ b)
    (hbS : ∃ c, (c, b) ∈ S.1) (hbU : ∃ c, (c, b) ∈ U.1)
    (hright : L.AgreeOn (Ioi b) S.1 U.1) : AgreeRight S U 0 :=
  agree_right_of_vertex (L := L.pow n) hev (one_le_pow₀ hβ) S.2.1 U.2.1
    (by rw [inflate_pow, ← hull_iterate_val, hS]) (by rw [inflate_pow, ← hull_iterate_val, hU])
    h0S h0U hb0 hbS hbU hright

/-- **Origin vertex, left side, on the hull.** -/
theorem hull_agree_left_of_vertex [Finite α] [Nonempty α] [DecidableEq α] {n : ℕ}
    (hev : ∀ a b, Even ((L.iterWord n a).count b)) (hβ : 1 ≤ L.β) {S U : L.Hull}
    (hS : inflateH^[n] S = S) (hU : inflateH^[n] U = U)
    (h0S : ∃ c, (c, 0) ∈ S.1) (h0U : ∃ c, (c, 0) ∈ U.1) {a : ℝ} (ha0 : a ≤ 0)
    (haS : ∃ c, (c, a) ∈ S.1) (haU : ∃ c, (c, a) ∈ U.1)
    (hleft : L.AgreeOn (Iio a) S.1 U.1) : L.AgreeOn (Iio 0) S.1 U.1 :=
  agree_left_of_vertex (L := L.pow n) hev (one_le_pow₀ hβ) S.2.1 U.2.1
    (by rw [inflate_pow, ← hull_iterate_val, hS]) (by rw [inflate_pow, ← hull_iterate_val, hU])
    h0S h0U ha0 haS haU hleft

/-! ## Image counts are the columns of the incidence powers -/

/-- The incidence matrix: entry `(b, a)` counts `b` in `σ(a)`. -/
def _root_.Psc.PeriodicPartnerHull.LengthSubst.incidence [Fintype α] [DecidableEq α]
    (L : LengthSubst α) : Matrix α α ℕ :=
  fun b a => (L.σ a).count b

theorem count_flatMap [Fintype α] [DecidableEq α] (w : List α) (b : α) :
    (w.flatMap L.σ).count b = ∑ c, w.count c * L.incidence b c := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    simp only [List.count_cons, beq_iff_eq, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [add_comm]
    rfl

/-- The letter counts of `σⁿ(a)` are the column `a` of `Mⁿ`. -/
theorem count_iterWord [Fintype α] [DecidableEq α] (n : ℕ) (a b : α) :
    (L.iterWord n a).count b = (L.incidence ^ n) b a := by
  induction n generalizing b with
  | zero =>
    simp only [LengthSubst.iterWord, iterate_zero, id, pow_zero, Matrix.one_apply,
      List.count_cons, List.count_nil, beq_iff_eq, zero_add]
    by_cases h : a = b <;> simp_all [eq_comm]
  | succ n ih =>
    rw [LengthSubst.iterWord, iterate_succ_apply', ← LengthSubst.iterWord, count_flatMap,
      pow_succ', Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [ih, mul_comm]

/-- Nilpotence modulo two at `j` makes every image of `σ^(j * p)` even, for `0 < p`. -/
theorem even_of_nilpotent [Fintype α] [DecidableEq α] {j p : ℕ} (hp : 0 < p)
    (hnil : (L.incidence.map (Nat.cast : ℕ → ZMod 2)) ^ j = 0) (a b : α) :
    Even ((L.iterWord (j * p) a).count b) := by
  rw [count_iterWord, ← ZMod.natCast_eq_zero_iff_even]
  have hmap : ∀ m : ℕ, (L.incidence ^ m).map (Nat.cast : ℕ → ZMod 2) =
      (L.incidence.map (Nat.cast : ℕ → ZMod 2)) ^ m := fun m =>
    map_pow ((Nat.castRingHom (ZMod 2)).mapMatrix) L.incidence m
  have h0 : (L.incidence.map (Nat.cast : ℕ → ZMod 2)) ^ (j * p) = 0 := by
    rw [pow_mul, hnil, zero_pow hp.ne']
  have h := congrFun (congrFun (hmap (j * p)) b) a
  rw [h0] at h
  simpa using h

/-! ## The hull theorems under nilpotence modulo two -/

/-- **Both tails, nilpotent form.**  If `M^j ≡ 0 (mod 2)` and `S`, `U` are fixed by `Φ^p`,
`0 < p`, agreement beyond common vertices `a ≤ 0 ≤ b` on both sides forces `S = U`. -/
theorem hull_eq_of_two_tails_of_nilpotent [Fintype α] [Nonempty α] [DecidableEq α]
    {j p : ℕ} (hp : 0 < p) (hnil : (L.incidence.map (Nat.cast : ℕ → ZMod 2)) ^ j = 0)
    (hβ : 1 ≤ L.β) {S U : L.Hull} (hS : inflateH^[p] S = S) (hU : inflateH^[p] U = U)
    {a b : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (haS : ∃ c, (c, a) ∈ S.1) (haU : ∃ c, (c, a) ∈ U.1)
    (hbS : ∃ c, (c, b) ∈ S.1) (hbU : ∃ c, (c, b) ∈ U.1)
    (hleft : L.AgreeOn (Iio a) S.1 U.1) (hright : L.AgreeOn (Ioi b) S.1 U.1) : S = U := by
  have hfix : ∀ {T : L.Hull}, inflateH^[p] T = T → inflateH^[j * p] T = T := fun h => by
    rw [mul_comm]; exact (Function.IsPeriodicPt.mul_const h j).eq
  exact hull_eq_of_two_tails (even_of_nilpotent hp hnil) hβ (hfix hS) (hfix hU) ha0 hb0
    haS haU hbS hbU hleft hright

/-- **Origin vertex, nilpotent form.**  Under `M^j ≡ 0 (mod 2)`, `Φ^p`-fixed tilings with a
vertex at the origin share their whole right ray once they agree beyond a common vertex
`b ≥ 0`, and their whole left ray once they agree before a common vertex `a ≤ 0`. -/
theorem hull_rays_of_nilpotent [Fintype α] [Nonempty α] [DecidableEq α]
    {j p : ℕ} (hp : 0 < p) (hnil : (L.incidence.map (Nat.cast : ℕ → ZMod 2)) ^ j = 0)
    (hβ : 1 ≤ L.β) {S U : L.Hull} (hS : inflateH^[p] S = S) (hU : inflateH^[p] U = U)
    (h0S : ∃ c, (c, 0) ∈ S.1) (h0U : ∃ c, (c, 0) ∈ U.1) :
    (∀ {b : ℝ}, 0 ≤ b → (∃ c, (c, b) ∈ S.1) → (∃ c, (c, b) ∈ U.1) →
      L.AgreeOn (Ioi b) S.1 U.1 → AgreeRight S U 0) ∧
    (∀ {a : ℝ}, a ≤ 0 → (∃ c, (c, a) ∈ S.1) → (∃ c, (c, a) ∈ U.1) →
      L.AgreeOn (Iio a) S.1 U.1 → L.AgreeOn (Iio 0) S.1 U.1) := by
  have hfix : ∀ {T : L.Hull}, inflateH^[p] T = T → inflateH^[j * p] T = T := fun h => by
    rw [mul_comm]; exact (Function.IsPeriodicPt.mul_const h j).eq
  exact ⟨fun hb0 hbS hbU hr => hull_agree_right_of_vertex (even_of_nilpotent hp hnil) hβ
      (hfix hS) (hfix hU) h0S h0U hb0 hbS hbU hr,
    fun ha0 haS haU hl => hull_agree_left_of_vertex (even_of_nilpotent hp hnil) hβ
      (hfix hS) (hfix hU) h0S h0U ha0 haS haU hl⟩

/-! ## Control: even incidence alone admits a strict bigon system -/

/-- The square of Thue–Morse, `0 ↦ 0110`, `1 ↦ 1001`. -/
def thueMorseSq : Fin 2 → List (Fin 2) := ![[0, 1, 1, 0], [1, 0, 0, 1]]

/-- Its incidence is zero modulo two: every image count is even. -/
theorem thueMorseSq_even : ∀ a b : Fin 2, Even ((thueMorseSq a).count b) := by
  decide

/-- The bigon `(01, 10)` has image `(01101001, 10010110)`, which cuts at every second letter
into the irreducible noncoincident blocks `(01,10), (10,01), (10,01), (01,10)`.  So
`{(01,10), (10,01)}` is closed under children and never coincides: even incidence does not by
itself exclude a strict system.  Any exclusion at even determinant must use more than the
reduction modulo two, such as the irreducible Pisot cubic. -/
theorem thueMorseSq_strict_bigons :
    [0, 1].flatMap thueMorseSq = [0, 1] ++ [1, 0] ++ [1, 0] ++ [0, 1] ∧
    [1, 0].flatMap thueMorseSq = [1, 0] ++ [0, 1] ++ [0, 1] ++ [1, 0] ∧
    ([0, 1] : List (Fin 2)).head? ≠ ([1, 0] : List (Fin 2)).head? := by
  decide

/-- Period doubling, `0 ↦ 01`, `1 ↦ 00`: the unordered quotient of Thue–Morse. -/
def periodDoubling : Fin 2 → List (Fin 2) := ![[0, 1], [0, 0]]

/-- Its incidence modulo two, entry `(b, a)` the parity of `b` in the image of `a`. -/
def periodDoublingModTwo : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun b a => ((periodDoubling a).count b : ZMod 2)

/-- The reduced incidence is a nonzero idempotent other than the identity, so its eventual
image is a single fixed line: `H¹(PD; 𝔽₂) ≅ 𝔽₂` for the proper square, as in the even
residue's base `Y`. -/
theorem periodDoubling_mod_two_fixed_line :
    periodDoublingModTwo * periodDoublingModTwo = periodDoublingModTwo ∧
      periodDoublingModTwo ≠ 0 ∧ periodDoublingModTwo ≠ 1 := by
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · have := congrFun (congrFun h 0) 0
    revert this; decide
  · have := congrFun (congrFun h 1) 1
    revert this; decide

end Psc.PeriodicPartnerEvenTails
