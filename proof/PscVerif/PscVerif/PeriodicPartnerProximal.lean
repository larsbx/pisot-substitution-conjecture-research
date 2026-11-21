import PscVerif.PeriodicPartnerHullContinuity
import PscVerif.PeriodicPartnerEvenTails
import PscVerif.PeriodicPartnerLegalCoincidence

/-!
# Exact proximality of inflation-periodic tilings

A common labelled tile in a pair fixed by positive inflation powers expands
to arbitrarily large common windows, after translating both tilings by the
same amount. The hypotheses use the existing hull and its literal inflation;
no factor map, maximality, coincidence rank or measure-theoretic input occurs.

The source decision is `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
This is the elementary periodic expansion step surrounding the argument in
Barge–Štimac–Williams, Theorem 3.1, and Barge–Kellendonk, Lemma 5.12.
-/

namespace Psc.PeriodicPartnerProximal

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-- Arbitrarily large exact windows after a common translation. This is an
explicit geometric predicate, independent of any choice of ordinary hull metric. -/
def ExactProximal (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ t : ℝ, Agree R (translate t T) (translate t U)

/-- Positive-radius exact agreement retains both tiles at a closed origin
seam. This exposes the previously private family bridge for any alphabet. -/
theorem originPatch_eq_of_agree {R : ℝ} (hR : 0 < R) {T U : S.Hull}
    (h : Agree R T U) :
    Psc.PeriodicPartnerLegalCoincidence.originPatch S T.1 =
      Psc.PeriodicPartnerLegalCoincidence.originPatch S U.1 := by
  ext p
  change (p ∈ T.1 ∧ 0 ∈ Icc p.2 (p.2 + S.ℓ p.1)) ↔
    (p ∈ U.1 ∧ 0 ∈ Icc p.2 (p.2 + S.ℓ p.1))
  apply and_congr_left
  intro hp
  exact h p ⟨max (-R / 2) p.2,
    ⟨le_max_right _ _, max_lt (by linarith [hp.2])
      (lt_add_of_pos_right _ (S.ℓ_pos p.1))⟩,
    ⟨(by linarith : -R < -R / 2).trans_le (le_max_left _ _),
      max_lt (by linarith) (hp.1.trans_lt hR)⟩⟩

/-- At the midpoint of a common tile, both tilings agree on its open interior. -/
theorem agree_at_common_tile {T U : S.Hull} {q : α × ℝ}
    (hqT : q ∈ T.1) (hqU : q ∈ U.1) :
    Agree (S.ℓ q.1 / 2) (translate (q.2 + S.ℓ q.1 / 2) T)
      (translate (q.2 + S.ℓ q.1 / 2) U) := by
  have hlocal : S.AgreeOn (Ioo q.2 (q.2 + S.ℓ q.1)) T.1 U.1 := by
    rintro p ⟨x, hxp, hx⟩
    have hxq : x ∈ S.supp q := ⟨hx.1.le, hx.2⟩
    constructor
    · intro hp
      have hpq := (T.2.1 x).unique ⟨hp, hxp⟩ ⟨hqT, hxq⟩
      exact hpq.symm ▸ hqU
    · intro hp
      have hpq := (U.2.1 x).unique ⟨hp, hxp⟩ ⟨hqU, hxq⟩
      exact hpq.symm ▸ hqT
  apply hlocal.shift
  rintro x ⟨hx₁, hx₂⟩
  constructor <;> linarith

/-- Iterated inflation scales the common translation by the corresponding power. -/
theorem inflateH_iterate_translate [Nonempty α] (T : S.Hull) (t : ℝ) (n : ℕ) :
    inflateH^[n] (translate t T) = translate (S.β ^ n * t) (inflateH^[n] T) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, inflateH_translate]
    simp only [iterate_succ_apply', pow_succ', mul_assoc]

/-- Simultaneous inflation preserves the arbitrary-window condition. The
requested radius is first divided by the positive expansion power. -/
theorem ExactProximal.inflate_iterate [Nonempty α] {T U : S.Hull}
    (h : ExactProximal S T U) (d : ℕ) :
    ExactProximal S (inflateH^[d] T) (inflateH^[d] U) := by
  intro R hR
  have hp : 0 < S.β ^ d := pow_pos S.β_pos d
  have hr : 0 < R / S.β ^ d := div_pos hR hp
  obtain ⟨t, ht⟩ := h (R / S.β ^ d) hr
  have hlarge := (agreementData (S := S)).agreement_iterate S.β_pos hr ht d
  change Agree (S.β ^ d * (R / S.β ^ d)) (inflateH^[d] (translate t T))
    (inflateH^[d] (translate t U)) at hlarge
  have he : S.β ^ d * (R / S.β ^ d) = R := by field_simp
  rw [he, inflateH_iterate_translate, inflateH_iterate_translate] at hlarge
  exact ⟨S.β ^ d * t, hlarge⟩

/-- Positive-period inflation returns the pair while making its shared tile
large enough for every requested radius. The two periods need not coincide. -/
theorem exactProximal_of_periodic_common_tile [Nonempty α] (hβ : 1 < S.β)
    {T U : S.Hull} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hT : inflateH^[m] T = T) (hU : inflateH^[n] U = U)
    (hc : (T.1 ∩ U.1).Nonempty) : ExactProximal S T U := by
  obtain ⟨q, hqT, hqU⟩ := hc
  let r := S.ℓ q.1 / 2
  let c := q.2 + r
  have hr : 0 < r := half_pos (S.ℓ_pos q.1)
  have hagree : Agree r (translate c T) (translate c U) := agree_at_common_tile S hqT hqU
  intro R hR
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / r) hβ
  let d := m * n * (N + 1)
  have hNd : N ≤ d := (Nat.le_succ N).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hn))
  have hRd : R ≤ S.β ^ d * r :=
    ((div_lt_iff₀ hr).mp (hN.trans_le (pow_le_pow_right₀ hβ.le hNd))).le
  have hTd : inflateH^[d] T = T := by
    dsimp only [d]
    rw [Nat.mul_assoc, iterate_mul]
    exact IsFixedPt.iterate hT _
  have hUd : inflateH^[d] U = U := by
    dsimp only [d]
    rw [Nat.mul_comm m n, Nat.mul_assoc, iterate_mul]
    exact IsFixedPt.iterate hU _
  have hlarge := (agreementData (S := S)).agreement_iterate S.β_pos hr hagree d
  change Agree (S.β ^ d * r) (inflateH^[d] (translate c T))
    (inflateH^[d] (translate c U)) at hlarge
  rw [inflateH_iterate_translate, inflateH_iterate_translate, hTd, hUd] at hlarge
  exact ⟨S.β ^ d * c, agree_mono hlarge hRd⟩

/-- One positive exact window after a common shift already contains a shared tile. -/
theorem common_tile_of_exactProximal {T U : S.Hull}
    (h : ExactProximal S T U) : (T.1 ∩ U.1).Nonempty := by
  obtain ⟨t, ht⟩ := h 1 (by norm_num)
  obtain ⟨q, ⟨hq, hqz⟩, _⟩ := (translate t T).2.1 0
  have hq' : q ∈ (translate t U).1 :=
    (ht q ⟨0, hqz, by constructor <;> norm_num⟩).mp hq
  exact ⟨(q.1, q.2 + t), hq, hq'⟩

/-- For an inflation-periodic pair, sharing one tile is exactly the arbitrary
common-translation window condition. This does not assert either side for a fibre. -/
theorem exactProximal_iff_common_tile_of_periodic [Nonempty α] (hβ : 1 < S.β)
    {T U : S.Hull} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hT : inflateH^[m] T = T) (hU : inflateH^[n] U = U) :
    ExactProximal S T U ↔ (T.1 ∩ U.1).Nonempty :=
  ⟨common_tile_of_exactProximal S,
    exactProximal_of_periodic_common_tile S hβ hm hn hT hU⟩

end Psc.PeriodicPartnerProximal
