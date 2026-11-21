import PscVerif.C4ParameterFamilyZeroFibreWitnesses
import PscVerif.PeriodicPartnerReturnModule
import PscVerif.C4ParameterFamilyZeroFibreControls

/-!
# Every pair in the zero solenoid fibre of the literal family shares a tile

For `k ≥ 2` the legal words `00` (in the image of `2`) and `11` (in the
image of `1`) make the lengths of `0` and `1` return vectors of every hull
tiling. The length of `2` is the expansion times the length of `1` minus
the other tiles of that image. Hence every tile length is a coincidence
shift of every hull tiling, and two hull tilings whose origin-tile starts
differ by an integer combination of the tile lengths are densely eventually
coincident. On the zero fibre both starts lie in the length lattice and
both tilings are inflation-periodic, which turns one eventual coincidence
into an actual common tile.

This discharges the universal witness obligation left open by
`C4ParameterFamilyZeroFibreWitnesses`. It does not assert coincidence rank
one on every fibre, almost-everywhere injectivity, or the invariant-measure
`L²` conclusion.

Source decision: `docs/c4-zero-fibre-return-group-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyZeroFibreAnchor

open Function Set Matrix Psc.ParameterFamilyTiling Psc.ParameterFamilyPisot
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyZeroFibreWitnesses
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyWords (ones)
open Psc.PeriodicPartnerProximal Psc.PeriodicPartnerEventualCoincidence
open Psc.PeriodicPartnerReturnModule
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree shift translate)
open Psc.PeriodicPartnerRealization (realize torusRealize realVec Solenoid origin lattice tileAt_spec)
open Psc.PeriodicPartnerRealizationFinite (dot_realVec)
open Psc.PeriodicPartnerPeriodicZero

variable (k : ℕ) (hk : 1 ≤ k)

/-- Every hull tiling contains a translate of the level-one supertile of
each letter. -/
theorem contains_image_patch (T : (geometry k hk).Hull) (c : Fin 3) :
    ∃ s, shift s ((geometry k hk).supertile c 1) ⊆ T.1 := by
  let S := geometry k hk
  obtain ⟨a, x, hT⟩ := S.contains_supertile_of_level (expansion_gt_one k hk).le T 3
  obtain ⟨y, hy⟩ := every_letter_in_square k hk c a
  have h := S.shifted_supertile_subset hy 1
  refine ⟨-x + -(S.β ^ 1 * y), fun q hq => hT ?_⟩
  rw [← LengthSubst.shift_shift] at hq
  exact h hq

/-- The two adjacent tiles of type `0` in the image of `2`. -/
theorem zero_pair_in_image :
    ((0 : Fin 3), (0 : ℝ)) ∈ (geometry k hk).supertile 2 1 ∧
      ((0 : Fin 3), (geometry k hk).ℓ 0) ∈ (geometry k hk).supertile 2 1 := by
  let S := geometry k hk
  constructor
  · refine ⟨(2, 0), rfl, ?_⟩
    change ((0 : Fin 3), (0 : ℝ)) ∈ S.place (substitution k 2) (S.β * 0)
    simp [substitution, LengthSubst.place]
  · refine ⟨(2, 0), rfl, ?_⟩
    change ((0 : Fin 3), S.ℓ 0) ∈ S.place (substitution k 2) (S.β * 0)
    simp [substitution, LengthSubst.place]

/-- The first two adjacent tiles of type `1` in the image of `1`, for
`k ≥ 2`. -/
theorem one_pair_in_image (hk₂ : 2 ≤ k) :
    ((1 : Fin 3), (geometry k hk).ℓ 0) ∈ (geometry k hk).supertile 1 1 ∧
      ((1 : Fin 3), (geometry k hk).ℓ 0 + (geometry k hk).ℓ 1) ∈
        (geometry k hk).supertile 1 1 := by
  let S := geometry k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hw : substitution (j + 2) 1 = 0 :: 1 :: 1 :: (ones j ++ [2]) := by
    simp [substitution, ones, List.replicate_succ]
  constructor
  · refine ⟨(1, 0), rfl, ?_⟩
    change ((1 : Fin 3), S.ℓ 0) ∈ S.place (substitution (j + 2) 1) (S.β * 0)
    rw [hw]
    simp [LengthSubst.place]
  · refine ⟨(1, 0), rfl, ?_⟩
    change ((1 : Fin 3), S.ℓ 0 + S.ℓ 1) ∈ S.place (substitution (j + 2) 1) (S.β * 0)
    rw [hw]
    simp [LengthSubst.place]

/-- The length of `2` is an integer combination of the expansion times the
length of `1` and the lengths of `0` and `1`. -/
theorem length_two_eq :
    (geometry k hk).ℓ 2 =
      (geometry k hk).β * (geometry k hk).ℓ 1 - (geometry k hk).ℓ 0 - k • (geometry k hk).ℓ 1 := by
  have he := expansion_equation k hk
  change expansion k hk + 2 =
    expansion k hk * expansion k hk ^ 2 - expansion k hk - k • expansion k hk ^ 2
  rw [nsmul_eq_mul]
  linarith

/-- Equal solenoid images put the two origin-tile starts in one coset of
the length lattice. Only the zeroth torus coordinate is used. -/
theorem lattice_offset_of_realize_eq {T U : (geometry k hk).Hull}
    (h : realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U) :
    ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
      (origin T).2 - (origin U).2 = (geometry k hk).ℓ ⬝ᵥ v := by
  have h0 : torusRealize (pisotData k hk) (inflateH_bijective k hk) T =
      torusRealize (pisotData k hk) (inflateH_bijective k hk) U :=
    congrArg (fun z : Solenoid (geometry k hk) => z.1 0) h
  refine ⟨_, QuotientAddGroup.eq.mp h0, ?_⟩
  rw [dotProduct_add, dotProduct_neg, dot_realVec, dot_realVec]
  ring

/-- Boundary control for the guard `k ≥ 2`: at `k = 1` the image of `1` is
`012`, and the second tile of type `1` used for the return vector is absent. -/
theorem one_pair_absent_at_one :
    ((1 : Fin 3), (geometry 1 le_rfl).ℓ 0 + (geometry 1 le_rfl).ℓ 1) ∉
      (geometry 1 le_rfl).supertile 1 1 := by
  let S := geometry 1 le_rfl
  rintro ⟨p, hp, hq⟩
  obtain rfl : p = (1, 0) := hp
  change ((1 : Fin 3), S.ℓ 0 + S.ℓ 1) ∈ S.place (substitution 1 1) (S.β * 0) at hq
  have h₁ := S.ℓ_pos 1
  simp [substitution, ones, LengthSubst.place] at hq
  linarith

variable (hk₂ : 2 ≤ k)
include hk₂

/-- The family's legal-patch theorem in the form consumed by the return
module. -/
theorem hull_dense {T U : (geometry k hk).Hull} (h : (T.1 ∩ U.1).Nonempty) :
    Dense (eventual (geometry k hk) T.1 U.1) :=
  hull_dense_eventual k hk₂ h

/-- Every tile length is a coincidence shift of every hull tiling. -/
theorem length_mem_coincidenceShifts (T : (geometry k hk).Hull) (a : Fin 3) :
    (geometry k hk).ℓ a ∈ coincidenceShifts (hull_dense k hk hk₂) T := by
  let S := geometry k hk
  have h₀ (U : S.Hull) : S.ℓ 0 ∈ coincidenceShifts (hull_dense k hk hk₂) U := by
    obtain ⟨s, hs⟩ := contains_image_patch k hk U 2
    obtain ⟨hx, hy⟩ := zero_pair_in_image k hk
    simpa only [sub_zero] using return_mem_of_patch (hull_dense k hk hk₂) hs hx hy
  have h₁ (U : S.Hull) : S.ℓ 1 ∈ coincidenceShifts (hull_dense k hk hk₂) U := by
    obtain ⟨s, hs⟩ := contains_image_patch k hk U 1
    obtain ⟨hx, hy⟩ := one_pair_in_image k hk hk₂
    simpa only [add_sub_cancel_left] using return_mem_of_patch (hull_dense k hk hk₂) hs hx hy
  have h₂ : S.ℓ 2 ∈ coincidenceShifts (hull_dense k hk hk₂) T := by
    obtain ⟨T', rfl⟩ := (inflateH_bijective k hk).2 T
    rw [show S.ℓ 2 = S.β * S.ℓ 1 - S.ℓ 0 - k • S.ℓ 1 from length_two_eq k hk]
    exact sub_mem (sub_mem (inflate_mem (hull_dense k hk hk₂) (h₁ T')) (h₀ _))
      (nsmul_mem (h₁ _) k)
  fin_cases a
  · exact h₀ T
  · exact h₁ T
  · exact h₂

/-- Two hull tilings whose origin-tile starts differ by an integer
combination of the tile lengths are densely eventually coincident. Neither
tiling is assumed periodic or over zero. -/
theorem dense_eventual_of_lattice_offset {T U : (geometry k hk).Hull}
    {v : Fin 3 → ℝ} (hv : v ∈ lattice (Fin 3))
    (h : (origin T).2 - (origin U).2 = (geometry k hk).ℓ ⬝ᵥ v) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  let S := geometry k hk
  obtain ⟨s, hs⟩ := contains_image_patch k hk T 1
  obtain ⟨t, ht⟩ := contains_image_patch k hk U 1
  obtain ⟨h₁, _⟩ := one_pair_in_image k hk hk₂
  have hx : ((1 : Fin 3), S.ℓ 0 - s) ∈ T.1 :=
    hs (by change ((1 : Fin 3), S.ℓ 0 - s + s) ∈ S.supertile 1 1; rwa [sub_add_cancel])
  have hy : ((1 : Fin 3), S.ℓ 0 - t) ∈ U.1 :=
    ht (by change ((1 : Fin 3), S.ℓ 0 - t + t) ∈ S.supertile 1 1; rwa [sub_add_cancel])
  have hT := start_sub_mem_lengthGroup S T (tileAt_spec T 0).1 hx
  have hU := start_sub_mem_lengthGroup S U (tileAt_spec U 0).1 hy
  have hTU : (origin T).2 - (origin U).2 ∈ lengthGroup S := h ▸ dot_mem_lengthGroup S hv
  refine dense_eventual_of_lengthGroup (hull_dense k hk hk₂)
    (length_mem_coincidenceShifts k hk hk₂ T) hx hy ?_
  have he : S.ℓ 0 - s - (S.ℓ 0 - t) =
      (S.ℓ 0 - s - (origin T).2) - (S.ℓ 0 - t - (origin U).2) +
        ((origin T).2 - (origin U).2) := by ring
  rw [he]
  exact add_mem (sub_mem hT hU) hTU

/-- Two hull tilings with the same solenoid image are densely eventually
coincident. This holds on every fibre, not only over zero, and assumes no
periodicity. It is not an assertion that the two tilings share a tile. -/
theorem fibre_dense_eventual {T U : (geometry k hk).Hull}
    (h : realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  obtain ⟨v, hv, hTU⟩ := lattice_offset_of_realize_eq k hk h
  exact dense_eventual_of_lattice_offset k hk hk₂ hv hTU

/-- Inflation-periodic hull tilings with origin-tile starts in one coset of
the length lattice share a tile. The two periods may differ. -/
theorem periodic_common_tile_of_lattice_offset {T U : (geometry k hk).Hull} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hTm : inflateH^[m] T = T) (hUn : inflateH^[n] U = U)
    {v : Fin 3 → ℝ} (hv : v ∈ lattice (Fin 3))
    (h : (origin T).2 - (origin U).2 = (geometry k hk).ℓ ⬝ᵥ v) : (T.1 ∩ U.1).Nonempty := by
  let S := geometry k hk
  have he : (eventual S T.1 U.1).Nonempty :=
    (dense_eventual_of_lattice_offset k hk hk₂ hv h).nonempty
  have hTm' : inflateH^[m * n] T = T := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hTm n
  have hUn' : inflateH^[m * n] U = U := by
    rw [Nat.mul_comm, iterate_mul]
    exact IsFixedPt.iterate hUn m
  apply Psc.PeriodicPartnerLegalCoincidence.common_tile_of_periodic_eventual S
    (Nat.mul_pos hm hn) ?_ ?_ he
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hTm'
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hUn'

/-- Any two tilings over the zero solenoid history share a labelled tile at
the same position. -/
theorem zero_fibre_common_tile {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (T.1 ∩ U.1).Nonempty := by
  obtain ⟨m, hm, hTm, v, hv, hTv⟩ := (realize_zero_iff_periodic_lattice_origin k hk).mp hT
  obtain ⟨n, hn, hUn, w, hw, hUw⟩ := (realize_zero_iff_periodic_lattice_origin k hk).mp hU
  refine periodic_common_tile_of_lattice_offset k hk hk₂ hm hn hTm hUn (sub_mem hw hv) ?_
  rw [hTv, hUw, dotProduct_sub]
  ring

/-- Inflation-periodic tilings in one fibre of the solenoid map share a
tile, over any periodic solenoid point. -/
theorem periodic_fibre_common_tile {T U : (geometry k hk).Hull} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hTm : inflateH^[m] T = T) (hUn : inflateH^[n] U = U)
    (h : realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U) : (T.1 ∩ U.1).Nonempty := by
  obtain ⟨v, hv, hTU⟩ := lattice_offset_of_realize_eq k hk h
  exact periodic_common_tile_of_lattice_offset k hk hk₂ hm hn hTm hUn hv hTU

/-- The anchor form of the former remaining obligation: every legal
inflation-periodic tiling with origin start in the length lattice shares a
tile with any chosen zero-fibre tiling. -/
theorem periodic_lattice_anchor {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (U : (geometry k hk).Hull)
    (hU : ∃ n > 0, inflateH^[n] U = U ∧
      ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
        (origin U).2 = -((geometry k hk).ℓ ⬝ᵥ v)) :
    (V.1 ∩ U.1).Nonempty :=
  zero_fibre_common_tile k hk hk₂ hV ((realize_zero_iff_periodic_lattice_origin k hk).mpr hU)

/-- Arbitrarily large exact common-translation windows on the zero fibre. -/
theorem zero_fibre_exactProximal {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ExactProximal (geometry k hk) T U :=
  (exactProximal_iff_common_tile k hk hT hU).mpr (zero_fibre_common_tile k hk hk₂ hT hU)

/-- The three exact agreements with one common translation, at every
positive radius, for every pair over zero. -/
theorem zero_fibre_stronglyRegionallyProximal {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    StronglyRegionallyProximal (geometry k hk) T U :=
  (stronglyRegionallyProximal_iff_common_tile k hk hk₂ hT hU).mpr
    (zero_fibre_common_tile k hk hk₂ hT hU)

/-- The radius-one common-shift witnesses requested by
`common_tile_of_zero_fibre_witnesses` exist for every pair over zero. -/
theorem zero_fibre_window_witnesses :
    ∀ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      WindowWitnesses (geometry k hk) 1 T U :=
  fun _ _ hT hU => zero_fibre_stronglyRegionallyProximal k hk hk₂ hT hU 1 (by norm_num)

/-- The published closed-origin witnesses exist for every pair over zero. -/
theorem zero_fibre_closedOriginWitnesses {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ClosedOriginWitnesses (geometry k hk) T U :=
  (closedOriginWitnesses_iff_common_tile k hk hk₂ hT hU).mpr
    (zero_fibre_common_tile k hk hk₂ hT hU)

/-- Control on the strength of the conclusion: a pair over zero can be
distinct, with different closed origin patches and no direct radius-one
agreement, while being densely eventually coincident and sharing a tile.
The theorems above therefore do not assert injectivity of the solenoid map
or equality of same-fibre tilings. -/
theorem same_fibre_distinct_control :
    ∃ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T =
        realize (pisotData k hk) (inflateH_bijective k hk) U ∧
      T ≠ U ∧ ¬ Agree 1 T U ∧
      Dense (eventual (geometry k hk) T.1 U.1) ∧ (T.1 ∩ U.1).Nonempty := by
  obtain ⟨T, U, _, _, hT, hU, _, _, hne, _, hna⟩ :=
    Psc.ParameterFamilyZeroFibreControls.zero_fibre_seam_control k hk
  exact ⟨T, U, hT.trans hU.symm, hne, hna,
    fibre_dense_eventual k hk hk₂ (hT.trans hU.symm), zero_fibre_common_tile k hk hk₂ hT hU⟩

end Psc.ParameterFamilyZeroFibreAnchor
