import PscVerif.C4ParameterFamilyInteriorZero
import PscVerif.C4ParameterFamilyZeroFibreControls
import PscVerif.C4ParameterFamilyZeroFibreWitnesses

/-!
# The zero-fibre anchor theorem reduced to an origin-tile recurrence

The origin tile of an inflated tiling depends only on the origin tile of
the tiling: it is the child of that tile whose support contains zero. An
inflation-periodic tiling therefore has an origin tile that is periodic
under this map of placed tiles, a statement with no hull in it.

For the literal family at `k ≥ 2` the anchor theorem is proved for every
zero-fibre tiling with a vertex at the origin, with no hypothesis. For
the tilings whose origin is interior to a tile it is proved from one
arithmetic premise, `PeriodicLatticeOriginsClassified`: the only periodic
placed tiles with a lattice start strictly left of the origin are the
three phases of the constructed interior cycle. That premise is stated
here and is not proved here.

Source decision: `docs/c4-zero-fibre-anchor-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerRealization

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The child of a placed tile whose support contains the origin. A tile
whose inflation does not cover the origin is returned unchanged. -/
noncomputable def originChild (S : LengthSubst α) (q : α × ℝ) : α × ℝ :=
  open Classical in
  if h : ∃ p ∈ S.place (S.σ q.1) (S.β * q.2), (0 : ℝ) ∈ S.supp p then h.choose else q

variable {S : LengthSubst α}

/-- The origin tile of an inflation is a function of the origin tile. -/
theorem origin_inflateH (U : S.Hull) : origin (inflateH U) = originChild S (origin U) := by
  have hmem : origin (inflateH U) ∈ S.place (S.σ (origin U).1) (S.β * (origin U).2) := by
    simpa [origin] using tileAt_inflate U 0
  have hz : (0 : ℝ) ∈ S.supp (origin (inflateH U)) := (tileAt_spec (inflateH U) 0).2
  have h : ∃ p ∈ S.place (S.σ (origin U).1) (S.β * (origin U).2), (0 : ℝ) ∈ S.supp p :=
    ⟨_, hmem, hz⟩
  unfold originChild
  split_ifs
  exact S.place_unique hmem h.choose_spec.1 hz h.choose_spec.2

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The origin child is any child whose support contains the origin. -/
theorem originChild_eq {q p : α × ℝ} (hp : p ∈ S.place (S.σ q.1) (S.β * q.2))
    (hz : (0 : ℝ) ∈ S.supp p) : originChild S q = p := by
  have h : ∃ p ∈ S.place (S.σ q.1) (S.β * q.2), (0 : ℝ) ∈ S.supp p := ⟨p, hp, hz⟩
  unfold originChild
  split_ifs
  exact S.place_unique h.choose_spec.1 hp h.choose_spec.2 hz

theorem origin_inflateH_iterate (U : S.Hull) (n : ℕ) :
    origin (inflateH^[n] U) = (originChild S)^[n] (origin U) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', origin_inflateH, ih]

/-- The origin tile of an inflation-periodic tiling is a periodic placed tile. -/
theorem originChild_periodic_of_periodic {U : S.Hull} {n : ℕ}
    (h : inflateH^[n] U = U) : (originChild S)^[n] (origin U) = origin U := by
  rw [← origin_inflateH_iterate, h]

end Psc.PeriodicPartnerRealization

namespace Psc.ParameterFamilyZeroFibreAnchor

open Function Matrix Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilyInteriorZero
open Psc.ParameterFamilyInteriorProximal Psc.ParameterFamilyZeroFibreControls
open Psc.ParameterFamilyZeroFibreWitnesses Psc.PeriodicPartnerProximal
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerPeriodicZero
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

variable (k : ℕ) (hk : 1 ≤ k)

/-- The arithmetic premise. Among placed tiles `(a, x)` with `x` the
negative length of an integer vector and the origin strictly inside the
tile, the only ones periodic under the origin-child map are the three
phases of the interior cycle. No tiling occurs in the statement. -/
def PeriodicLatticeOriginsClassified : Prop :=
  ∀ (q : Fin 3 × ℝ) (n : ℕ), 0 < n →
    (originChild (geometry k hk))^[n] q = q →
    q.2 < 0 → 0 < q.2 + (geometry k hk).ℓ q.1 →
    (∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧ q.2 = -((geometry k hk).ℓ ⬝ᵥ v)) →
    q = (1, -(geometry k hk).ℓ 0) ∨
      q = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∨
      q = (1, -(geometry k hk).ℓ 2)

/-- The first child of a tile starts where the inflated tile starts and
never has type `2`. -/
theorem head_child {V : (geometry k hk).Hull} {a : Fin 3} {x : ℝ}
    (h : (a, x) ∈ V.1) :
    ∃ b : Fin 3, b ≠ 2 ∧ (b, (geometry k hk).β * x) ∈ (inflateH V).1 := by
  let S := geometry k hk
  have hσ : ∃ b : Fin 3, b ≠ 2 ∧ ∃ w, S.σ a = b :: w := by
    change ∃ b : Fin 3, b ≠ 2 ∧ ∃ w, Psc.ParameterFamilyRows.substitution k a = b :: w
    fin_cases a
    · exact ⟨1, by decide, [], by simp [Psc.ParameterFamilyRows.substitution]⟩
    · exact ⟨0, by decide, _, by simp [Psc.ParameterFamilyRows.substitution]; rfl⟩
    · exact ⟨0, by decide, [0, 1], by simp [Psc.ParameterFamilyRows.substitution]⟩
  obtain ⟨b, hb, w, hw⟩ := hσ
  refine ⟨b, hb, (a, x), h, ?_⟩
  change (b, S.β * x) ∈ S.place (S.σ a) (S.β * x)
  rw [hw]
  simp [LengthSubst.place]

/-- A vertex at the origin persists under inflation. -/
theorem origin_vertex_iterate {U : (geometry k hk).Hull} {a : Fin 3}
    (h : (a, (0 : ℝ)) ∈ U.1) (m : ℕ) :
    ∃ b : Fin 3, (b, (0 : ℝ)) ∈ (inflateH^[m] U).1 := by
  induction m with
  | zero => exact ⟨a, h⟩
  | succ m ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨c, -, hc⟩ := head_child k hk hb
    rw [iterate_succ_apply']
    exact ⟨c, by simpa using hc⟩

/-- A tile starting at the origin of an inflation-periodic tiling has
type `0` or `1`. -/
theorem origin_vertex_ne_two {U : (geometry k hk).Hull} {n : ℕ} (hn : 0 < n)
    (hper : inflateH^[n] U = U) {a : Fin 3} (h : (a, (0 : ℝ)) ∈ U.1) : a ≠ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, hb⟩ := origin_vertex_iterate k hk h m
  obtain ⟨c, hc, hmem⟩ := head_child k hk hb
  rw [iterate_succ_apply'] at hper
  rw [hper, mul_zero] at hmem
  have hz (d : Fin 3) : (0 : ℝ) ∈ (geometry k hk).supp (d, 0) :=
    ⟨le_rfl, by simpa using (geometry k hk).ℓ_pos d⟩
  have heq : (a, (0 : ℝ)) = (c, 0) := (tileAt_eq h (hz a)).symm.trans (tileAt_eq hmem (hz c))
  rw [(Prod.mk.inj heq).1]
  exact hc

/-- Control: the premise needs its strict inequality. The vertex tile
`(1, 0)` has a lattice start, is periodic under the origin-child map and
is none of the three interior phases. -/
theorem vertex_tile_periodic :
    (originChild (geometry k hk))^[2] ((1 : Fin 3), (0 : ℝ)) = (1, 0) := by
  let S := geometry k hk
  have h₁ : originChild S ((1 : Fin 3), (0 : ℝ)) = (0, 0) := by
    apply originChild_eq
    · change ((0 : Fin 3), (0 : ℝ)) ∈
        S.place (Psc.ParameterFamilyRows.substitution k 1) (S.β * 0)
      simp [Psc.ParameterFamilyRows.substitution, LengthSubst.place]
    · exact ⟨le_rfl, by simpa using S.ℓ_pos 0⟩
  have h₂ : originChild S ((0 : Fin 3), (0 : ℝ)) = (1, 0) := by
    apply originChild_eq
    · change ((1 : Fin 3), (0 : ℝ)) ∈
        S.place (Psc.ParameterFamilyRows.substitution k 0) (S.β * 0)
      simp [Psc.ParameterFamilyRows.substitution, LengthSubst.place]
    · exact ⟨le_rfl, by simpa using S.ℓ_pos 1⟩
  change originChild S (originChild S ((1 : Fin 3), (0 : ℝ))) = (1, 0)
  rw [h₁, h₂]

variable (hk₂ : 2 ≤ k)

include hk₂

/-- Non-vacuity: the first interior phase satisfies every hypothesis of
the premise, so the premise is not an empty quantification. -/
theorem interior_phase_periodic :
    (originChild (geometry k hk))^[3] ((1 : Fin 3), -(geometry k hk).ℓ 0) =
        (1, -(geometry k hk).ℓ 0) ∧
      -(geometry k hk).ℓ 0 < 0 ∧
      0 < -(geometry k hk).ℓ 0 + (geometry k hk).ℓ 1 ∧
      ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
        -(geometry k hk).ℓ 0 = -((geometry k hk).ℓ ⬝ᵥ v) := by
  obtain ⟨T, hT, h₀, -, -, hz, -, -, -⟩ := interior_zero_cycle k hk hk₂
  have hper := originChild_periodic_of_periodic hT
  rw [h₀] at hper
  obtain ⟨h1, h2⟩ := (tileAt_spec T 0).2
  have ho : tileAt T 0 = (1, -(geometry k hk).ℓ 0) := h₀
  rw [ho] at h1 h2
  refine ⟨hper, neg_lt_zero.mpr ((geometry k hk).ℓ_pos 0), h2, ?_⟩
  obtain ⟨v, hv, hx⟩ := lattice_origin_of_realize_zero _ _ hz
  rw [h₀] at hx
  exact ⟨v, hv, hx⟩

/-- The anchor theorem for zero-fibre tilings with a vertex at the
origin. It has no classification premise: the tile at the origin is
shared with the seam anchor or with its inflation, and the anchor
shares a tile with its inflation. -/
theorem anchor_common_tile_of_origin_vertex
    {V U : (geometry k hk).Hull}
    (hV0 : (1, 0) ∈ V.1) (hV : inflateH^[2] V = V)
    (hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    {a : Fin 3} (ha : (a, (0 : ℝ)) ∈ U.1) : (V.1 ∩ U.1).Nonempty := by
  obtain ⟨n, hn, hper⟩ := periodic_of_realize_zero k hk hzU
  have ha2 := origin_vertex_ne_two k hk hn hper ha
  have ha01 : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl ha2
  rcases ha01 with rfl | rfl
  · have hV1 : ((0 : Fin 3), (0 : ℝ)) ∈ (inflateH V).1 := by
      refine ⟨(1, 0), hV0, ?_⟩
      change ((0 : Fin 3), (0 : ℝ)) ∈
        (geometry k hk).place (Psc.ParameterFamilyRows.substitution k 1) ((geometry k hk).β * 0)
      simp [Psc.ParameterFamilyRows.substitution, LengthSubst.place]
    exact common_tile_trans k hk hk₂ hzV hzU
      ⟨_, seam_pair_common_tile k hk hk₂ hV0 hV⟩ ⟨_, hV1, ha⟩
  · exact ⟨_, hV0, ha⟩

/-- The anchor theorem for a zero-fibre tiling whose origin tile is one
of the three interior phases. -/
theorem anchor_common_tile_of_interior_phase
    {V U : (geometry k hk).Hull}
    (hV0 : (1, 0) ∈ V.1) (hV : inflateH^[2] V = V)
    (hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    (horigin : origin U = (1, -(geometry k hk).ℓ 0) ∨
      origin U = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∨
      origin U = (1, -(geometry k hk).ℓ 2)) : (V.1 ∩ U.1).Nonempty := by
  obtain ⟨T, hT, h₀, h₁, h₂, hz₀, hz₁, hz₂, -⟩ := interior_zero_cycle k hk hk₂
  have htile : (1, -(geometry k hk).ℓ 0) ∈ T.1 := by
    rw [← h₀]
    exact (tileAt_spec T 0).1
  have key (i : ℕ)
      (hz : realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[i] T) = 0)
      (ho : origin U = origin (inflateH^[i] T)) : (V.1 ∩ U.1).Nonempty := by
    have hVT : (V.1 ∩ (inflateH^[i] T).1).Nonempty :=
      (exactProximal_iff_common_tile k hk hzV hz).mp
        (seam_interior_orbit_exactProximal k hk hk₂ hV0 hV htile hT i)
    have hTU : ((inflateH^[i] T).1 ∩ U.1).Nonempty :=
      ⟨origin U, by rw [ho]; exact (tileAt_spec _ 0).1, (tileAt_spec U 0).1⟩
    exact common_tile_trans k hk hk₂ hzV hzU hVT hTU
  rcases horigin with h | h | h
  · exact key 0 hz₀ (h.trans h₀.symm)
  · exact key 1 hz₁ (h.trans h₁.symm)
  · exact key 2 hz₂ (h.trans h₂.symm)

/-- The anchor theorem from the arithmetic premise. Every zero-fibre
tiling shares a labelled tile with the period-two seam anchor. -/
theorem anchor_common_tile_of_classified
    (hC : PeriodicLatticeOriginsClassified k hk)
    {V U : (geometry k hk).Hull}
    (hV0 : (1, 0) ∈ V.1) (hV : inflateH^[2] V = V)
    (hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (V.1 ∩ U.1).Nonempty := by
  by_cases hvertex : (origin U).2 = 0
  · refine anchor_common_tile_of_origin_vertex k hk hk₂ hV0 hV hzV hzU
      (a := (origin U).1) ?_
    have h := (tileAt_spec U 0).1
    rwa [show tileAt U 0 = ((origin U).1, (0 : ℝ)) from Prod.ext rfl hvertex] at h
  · obtain ⟨n, hn, hper⟩ := periodic_of_realize_zero k hk hzU
    obtain ⟨h1, h2⟩ := (tileAt_spec U 0).2
    exact anchor_common_tile_of_interior_phase k hk hk₂ hV0 hV hzV hzU
      (hC (origin U) n hn (originChild_periodic_of_periodic hper)
        (lt_of_le_of_ne h1 hvertex) h2
        (lattice_origin_of_realize_zero _ _ hzU))

/-- The requested all-pairs witness statement from the arithmetic
premise. The seam anchor is the constructed one; its zero image is
proved, not assumed. -/
theorem all_pair_witnesses_of_classified
    (hC : PeriodicLatticeOriginsClassified k hk)
    (T U : (geometry k hk).Hull)
    (hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    WindowWitnesses (geometry k hk) 1 T U := by
  obtain ⟨V, hleft, hright, hV⟩ := fixed_hull_tiling k hk
  have hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0 := by
    apply realize_r4 (pisotData k hk) (inflateH_bijective k hk) (b := 1)
    · exact ⟨2, by decide, hV⟩
    · exact (show (1, 0 - (geometry k hk).ℓ 1) ∈ V.1 by simpa using hleft)
  have hVT := anchor_common_tile_of_classified k hk hk₂ hC hright hV hzV hzT
  have hVU := anchor_common_tile_of_classified k hk hk₂ hC hright hV hzV hzU
  have hTV : (T.1 ∩ V.1).Nonempty := by simpa only [inter_comm] using hVT
  exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hzT hzU).mpr
    (common_tile_trans k hk hk₂ hzT hzU hTV hVU)

/-- Every pair over zero is exactly proximal, from the arithmetic premise. -/
theorem zero_fibre_exactProximal_of_classified
    (hC : PeriodicLatticeOriginsClassified k hk)
    (T U : (geometry k hk).Hull)
    (hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ExactProximal (geometry k hk) T U :=
  (exactProximal_iff_common_tile k hk hzT hzU).mpr
    ((windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hzT hzU).mp
      (all_pair_witnesses_of_classified k hk hk₂ hC T U hzT hzU))

end Psc.ParameterFamilyZeroFibreAnchor
