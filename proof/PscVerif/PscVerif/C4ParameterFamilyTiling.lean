import PscVerif.C4ParameterFamilyBridge
import PscVerif.PeriodicPartnerBalancedGeometry
import PscVerif.PeriodicPartnerLegalCoincidence
import PscVerif.PeriodicPartnerHullPatches
import PscVerif.PeriodicPartnerLocalTopology
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# The literal geometric substitution for the C4 parameter family

The same root and words as in `C4ParameterFamilyBridge` give the length
substitution on the existing ordinary legal hull. The seam `1.1` gives an
actual tiling fixed by the square of inflation.
-/

namespace Psc.ParameterFamilyTiling

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerEvenTails
open Psc.PeriodicPartnerHull.LengthSubst (inflateH)
open Psc.PeriodicPartnerBalancedGeometry (repeatWord)
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyWords (ones)
open Psc.ParameterFamilyPisot (incidenceQ)
open scoped Topology

private theorem exists_expansion (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℝ, 2 < b ∧ b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0 ∧
      Polynomial.aeval (b : ℂ) (incidenceQ k).charpoly = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z (incidenceQ k).charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨b, hb2, hb, hother⟩ := Psc.ParameterFamilyPisot.pisot k hk
  refine ⟨b, hb2, ?_, hb, hother⟩
  rw [Psc.ParameterFamilyPisot.charpoly_eq, Psc.ParameterFamilyPisot.aeval_polynomial] at hb
  exact_mod_cast hb

/-- The expanding root of the actual incidence polynomial. -/
noncomputable def expansion (k : ℕ) (hk : 1 ≤ k) : ℝ := (exists_expansion k hk).choose

theorem two_lt_expansion (k : ℕ) (hk : 1 ≤ k) : 2 < expansion k hk :=
  (exists_expansion k hk).choose_spec.1

theorem expansion_equation (k : ℕ) (hk : 1 ≤ k) :
    expansion k hk ^ 3 - (k : ℝ) * expansion k hk ^ 2 - 2 * expansion k hk - 2 = 0 :=
  (exists_expansion k hk).choose_spec.2.1

theorem expansion_pisot (k : ℕ) (hk : 1 ≤ k) :
    Polynomial.aeval (expansion k hk : ℂ) (incidenceQ k).charpoly = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z (incidenceQ k).charpoly = 0 →
        z ≠ expansion k hk → ‖z‖ < 1 :=
  (exists_expansion k hk).choose_spec.2.2

/-- The Perron-length geometric substitution. The labels `0`, `1`, `2` have
lengths `β`, `β²`, `β + 2`, respectively. -/
noncomputable def geometry (k : ℕ) (hk : 1 ≤ k) : LengthSubst (Fin 3) where
  σ := substitution k
  ne_nil a := by
    fin_cases a <;> simp [substitution]
  ℓ := ![expansion k hk, expansion k hk ^ 2, expansion k hk + 2]
  ℓ_pos a := by
    have hb := two_lt_expansion k hk
    fin_cases a <;> simp <;> positivity
  β := expansion k hk
  eigen a := by
    have hb := expansion_equation k hk
    fin_cases a <;>
      simp [substitution, ones, nsmul_eq_mul] <;> nlinarith

@[simp] theorem geometry_image (k : ℕ) (hk : 1 ≤ k) :
    (geometry k hk).σ = substitution k := rfl

theorem expansion_gt_one (k : ℕ) (hk : 1 ≤ k) : 1 < (geometry k hk).β :=
  lt_trans (by norm_num) (two_lt_expansion k hk)

private theorem iterWord_two (S : LengthSubst (Fin 3)) (a : Fin 3) :
    S.iterWord 2 a = (S.σ a).flatMap S.σ := by
  simp [LengthSubst.iterWord, iterate_succ_apply', List.flatMap_cons]

/-- The literal seed `1.1` lies in `σ²(2)` and is nested under `σ²`.
The dot indicates the origin and both `1` tiles are entire tiles. -/
theorem fixed_hull_tiling (k : ℕ) (hk : 1 ≤ k) :
    ∃ T : (geometry k hk).Hull,
      (1, -(geometry k hk).ℓ 1) ∈ T.1 ∧ (1, 0) ∈ T.1 ∧ inflateH^[2] T = T := by
  let S := geometry k hk
  let l := S.ℓ 1
  let P : Set (Fin 3 × ℝ) := {(1, -l), (1, 0)}
  have hl : 0 < l := S.ℓ_pos 1
  have h0 : S.σ 0 = [1] := by simp [S, substitution]
  have h1 : S.σ 1 = [0] ++ ones k ++ [2] := by simp [S, substitution]
  have h2 : S.σ 2 = [0, 0, 1] := by simp [S, substitution]
  have hfirst : S.iterWord 2 1 = [1] ++ (ones k).flatMap S.σ ++ [0, 0, 1] := by
    simp only [iterWord_two, h1, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, h0, h2]
  have hlegalWord : S.iterWord 2 2 = [1, 1] ++ S.σ 1 := by
    simp [iterWord_two, h2, h0, List.flatMap_cons]
  have htiles : S.TilesOn (Ico (-l) l) P := by
    have hsum : -l + (([1, 1] : List (Fin 3)).map S.ℓ).sum = l := by
      simp [l]
    have hplace : S.place [1, 1] (-l) = [(1, -l), (1, 0)] := by
      simp [LengthSubst.place, l]
    have hset : {q | q ∈ ([(1, -l), (1, 0)] : List (Fin 3 × ℝ))} = P := by
      ext q
      simp only [P, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
        mem_insert_iff, mem_singleton_iff]
    have h := S.tilesOn_place [1, 1] (-l)
    rwa [hsum, hplace, hset] at h
  have hsum : ((S.iterWord 2 1).map S.ℓ).sum = S.β ^ 2 * l := (S.pow 2).eigen 1
  have hgrow : P ⊆ S.inflate^[2] P := by
    rw [← inflate_pow]
    rintro p (rfl | hp)
    · refine ⟨(1, -l), Or.inl rfl, ?_⟩
      rw [place_pow]
      have hlast : (S.iterWord 2 1).getLast (iterWord_ne_nil 2 1) = 1 := by
        simp [hfirst]
      have hm := S.place_last (iterWord_ne_nil (L := S) 2 1) (S.β ^ 2 * -l)
      rw [hlast, hsum, show S.β ^ 2 * -l + S.β ^ 2 * l - S.ℓ 1 = -l by
        change S.β ^ 2 * -l + S.β ^ 2 * l - l = -l
        ring] at hm
      exact hm
    · have hp0 : p = (1, 0) := by simpa using hp
      subst p
      refine ⟨(1, 0), Or.inr rfl, ?_⟩
      rw [place_pow]
      simp [LengthSubst.pow, hfirst, LengthSubst.place]
  have hlegal : ∃ c n t, P ⊆ LengthSubst.shift t (S.supertile c n) := by
    refine ⟨2, 2, l, ?_⟩
    intro p hp
    change (p.1, p.2 + l) ∈ S.inflate^[2] {(2, 0)}
    rw [← inflate_pow]
    refine ⟨(2, 0), rfl, ?_⟩
    rw [place_pow]
    rcases hp with rfl | hp
    · simp [LengthSubst.pow, hlegalWord, LengthSubst.place]
    · have hp0 : p = (1, 0) := by simpa using hp
      subst p
      simp [LengthSubst.pow, hlegalWord, LengthSubst.place, l]
  obtain ⟨T, hP, hT⟩ := S.periodic_hull_of_seed (expansion_gt_one k hk) (by decide)
    (neg_lt_zero.mpr hl) hl htiles hgrow hlegal
  exact ⟨T, hP (Or.inl rfl), hP (Or.inr rfl), hT⟩

/-- Each letter occurs in each literal level-two supertile. -/
theorem every_letter_in_square (k : ℕ) (hk : 1 ≤ k) (a c : Fin 3) :
    ∃ x, (a, x) ∈ (geometry k hk).supertile c 2 := by
  let S := geometry k hk
  have h1 : (1 : Fin 3) ∈ ones k := by simp [ones, show k ≠ 0 by omega]
  have hall : ∀ d : Fin 3, d ∈ S.σ 1 := by
    intro d
    fin_cases d <;> simp [S, substitution, h1]
  have hmem : a ∈ S.iterWord 2 c := by
    rw [iterWord_two, List.mem_flatMap]
    fin_cases c
    · exact ⟨1, by simp [S, substitution], hall a⟩
    · exact ⟨1, hall 1, hall a⟩
    · exact ⟨1, by simp [S, substitution], hall a⟩
  have hlabels (w : List (Fin 3)) (x : ℝ) : (S.place w x).map Prod.fst = w := by
    induction w generalizing x with
    | nil => rfl
    | cons b w ih => simp [LengthSubst.place, ih]
  rw [← hlabels (S.iterWord 2 c) 0] at hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
  exact ⟨p.2, by rwa [S.supertile_eq_place]⟩

private theorem square_irrational (k : ℕ) (hk : 1 ≤ k) : Irrational ((geometry k hk).β ^ 2) := by
  let b := expansion k hk
  have hb : 2 < b := two_lt_expansion k hk
  have he : b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0 := expansion_equation k hk
  intro ⟨q, hq⟩
  change (q : ℝ) = b ^ 2 at hq
  have hq2 : 2 < (q : ℝ) := by nlinarith
  have hr : ((((k : ℚ) * q + 2) / (q - 2) : ℚ) : ℝ) = b := by
    push_cast
    apply (div_eq_iff (by linarith : (q : ℝ) - 2 ≠ 0)).2
    rw [hq]
    nlinarith
  exact (Psc.ParameterFamilyPisot.root_irrational k hk he) ⟨_, hr⟩

/-- Every tiling in the literal family hull is translation aperiodic. -/
theorem aperiodic (k : ℕ) (hk : 1 ≤ k) (T : (geometry k hk).Hull) (t : ℝ)
    (ht : LengthSubst.translate t T = T) : t = 0 := by
  let S := geometry k hk
  obtain ⟨U, _, _, hU⟩ := fixed_hull_tiling k hk
  exact S.aperiodic_of_inflate_fixed hU (square_irrational k hk) t
    (S.period_of_windows ht fun R => S.window_occurs (expansion_gt_one k hk).le
      (every_letter_in_square k hk) T U R)

/-- The family tiling carrier with the ordinary small-translation topology. -/
abbrev TilingSpace (k : ℕ) (hk : 1 ≤ k) :=
  Psc.PeriodicPartnerLocalTopology.LocalHull (geometry k hk)

open Psc.PeriodicPartnerLocalTopology (LocalHull translate)

theorem tiling_space_nonempty (k : ℕ) (hk : 1 ≤ k) : Nonempty (TilingSpace k hk) := by
  obtain ⟨T, _, _, _⟩ := fixed_hull_tiling k hk
  exact ⟨⟨T⟩⟩

/-- The action in the ordinary topology is continuous jointly in time and tiling. -/
theorem continuous_action (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun p : ℝ × TilingSpace k hk => translate (geometry k hk) p.1 p.2) :=
  Psc.PeriodicPartnerLocalTopology.continuous_translate (geometry k hk)

/-- Aperiodicity for the action on the ordinary-topology presentation. -/
theorem action_aperiodic (k : ℕ) (hk : 1 ≤ k) (T : TilingSpace k hk) (t : ℝ)
    (ht : translate (geometry k hk) t T = T) : t = 0 :=
  aperiodic k hk T.toHull t (congrArg LocalHull.toHull ht)

/-- One finite set of translated patches covers all tilings and shifts at
each prescribed window radius. -/
theorem finite_local_complexity (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 < R) :
    ∃ F : Set (Set (Fin 3 × ℝ)), F.Finite ∧ ∀ T : TilingSpace k hk,
      ∃ x, LengthSubst.shift x {p ∈ T.toHull.1 |
        ((geometry k hk).supp p ∩ Ioo (-R) R).Nonempty} ∈ F := by
  obtain ⟨F, hF, h⟩ := (geometry k hk).finite_local_complexity R hR
  exact ⟨F, hF, fun T => h T.toHull⟩

/-- The shift from `01` to `10`, as a fraction of the period of the cell. -/
theorem swap_rotation_irrational (k : ℕ) (hk : 1 ≤ k) :
    Irrational ((geometry k hk).ℓ 0 / ((geometry k hk).ℓ 0 + (geometry k hk).ℓ 1)) := by
  let b := expansion k hk
  change Irrational (b / (b + b ^ 2))
  have hb : 2 < b := two_lt_expansion k hk
  rw [show b / (b + b ^ 2) = (1 + b)⁻¹ by
    field_simp [show b + b ^ 2 ≠ 0 by nlinarith, show 1 + b ≠ 0 by linarith], irrational_inv_iff]
  have hi := Psc.ParameterFamilyPisot.root_irrational k hk (expansion_equation k hk)
  simpa using (irrational_ratCast_add_iff (q := 1)).2 hi

/-- The swap translation generates a dense orbit on the circle of one
swap cell, hence every circle orbit is dense. -/
theorem swap_rotation_dense (k : ℕ) (hk : 1 ≤ k) :
    let S := geometry k hk
    DenseRange (fun n : ℤ => n • (S.ℓ 0 : AddCircle (S.ℓ 0 + S.ℓ 1))) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr (swap_rotation_irrational k hk)

/-- The full finite certificate produces geometric coincidences on the two
actual swap tracks densely throughout the fundamental cell. -/
theorem dense_swap_coincidences (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    ∀ t ∈ Ioo 0 (S.ℓ 0 + S.ℓ 1), ∀ ε > 0,
      ∃ y ∈ Ioo 0 (S.ℓ 0 + S.ℓ 1), |y - t| < ε ∧
        ∃ (j : ℕ) (q : Fin 3 × ℝ),
          q ∈ S.place ((Psc.Binomial.subst (substitution k))^[j] [0, 1]) 0 ∧
          q ∈ S.place ((Psc.Binomial.subst (substitution k))^[j] [1, 0]) 0 ∧
          S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1) := by
  let hk' : 1 ≤ k := by omega
  let S := geometry k hk'
  have hb : Psc.Binomial.Equiv1 ([0, 1] : List (Fin 3)) [1, 0] :=
    Psc.Reduction.equiv1_iff_perm.mpr (List.Perm.swap _ _ [])
  obtain ⟨hf, hp⟩ := Psc.ParameterFamilyBridge.full_factor_termination k hk
  simpa only [S, geometry_image, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] using
    Psc.PeriodicPartnerBalancedGeometry.dense_coincidence_in_cell S
      (expansion_gt_one k hk') hb hf hp

/-- Translating the repeated `01` patch by the length of `0` gives the
repeated `10` patch, including the tiles crossing the choice of cell. -/
theorem shift_swap_periodic_patch (S : LengthSubst (Fin 3)) :
    LengthSubst.shift (S.ℓ 0) (repeatWord S [0, 1]) = repeatWord S [1, 0] := by
  ext ⟨a, x⟩
  change (a, x + S.ℓ 0) ∈ repeatWord S [0, 1] ↔ (a, x) ∈ repeatWord S [1, 0]
  simp only [repeatWord, mem_ofPred_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, LengthSubst.place, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨m, ⟨ha, hx⟩ | ⟨ha, hx⟩⟩
    · exact ⟨m - 1, Or.inr ⟨ha, by push_cast; nlinarith only [hx]⟩⟩
    · exact ⟨m, Or.inl ⟨ha, by nlinarith only [hx]⟩⟩
  · rintro ⟨m, ⟨ha, hx⟩ | ⟨ha, hx⟩⟩
    · exact ⟨m, Or.inr ⟨ha, by nlinarith only [hx]⟩⟩
    · exact ⟨m + 1, Or.inl ⟨ha, by push_cast; nlinarith only [hx]⟩⟩

/-- The periodically repeated `01` seed tiles the line. Its translate by
the length of `0` is densely eventually coincident with it on the line. -/
theorem periodic_swap_geometry (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    let Q := repeatWord S [0, 1]
    S.IsTiling Q ∧ Dense {y : ℝ | ∃ (j : ℕ) (q : Fin 3 × ℝ),
      q ∈ S.inflate^[j] Q ∧ q ∈ S.inflate^[j] (LengthSubst.shift (S.ℓ 0) Q) ∧
      S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1)} := by
  let S := geometry k (show 1 ≤ k by omega)
  change S.IsTiling (repeatWord S [0, 1]) ∧ Dense {y : ℝ | ∃ (j : ℕ) (q : Fin 3 × ℝ),
    q ∈ S.inflate^[j] (repeatWord S [0, 1]) ∧
      q ∈ S.inflate^[j] (LengthSubst.shift (S.ℓ 0) (repeatWord S [0, 1])) ∧
      S.β ^ j * y ∈ Ioo q.2 (q.2 + S.ℓ q.1)}
  refine ⟨Psc.PeriodicPartnerBalancedGeometry.isTiling_repeatWord S (by simp), ?_⟩
  rw [shift_swap_periodic_patch]
  apply Psc.PeriodicPartnerBalancedGeometry.dense_coincidence_repeatWord S (by simp) (by simp [add_comm])
  simpa [S, geometry_image] using dense_swap_coincidences k hk

open Psc.PeriodicPartnerEventualCoincidence (eventual)
open Psc.PeriodicPartnerLegalCoincidence (LegalPatch openOverlap originPatch)

/-- Every two legal patches sharing a tile have dense eventual coincidence
on their open overlap for the literal family. -/
theorem legal_patches_dense_eventual (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    ∀ {A B}, LegalPatch S A → LegalPatch S B → (A ∩ B).Nonempty →
      openOverlap S A B ⊆ closure (eventual S A B ∩ openOverlap S A B) := by
  let hk' : 1 ≤ k := by omega
  let S := geometry k hk'
  let Q := repeatWord S [0, 1]
  obtain ⟨hQ, hd⟩ := periodic_swap_geometry k hk
  have hp : LengthSubst.shift (S.ℓ 0 + S.ℓ 1) Q = Q := by
    simpa [Q] using Psc.PeriodicPartnerBalancedGeometry.repeatWord_period S [0, 1]
  have hg : Dense (eventual S Q (LengthSubst.shift (S.ℓ 0) Q)) := hd.mono (by
    rintro x ⟨j, q, hL, hR, hx⟩
    exact Psc.PeriodicPartnerEventualCoincidence.mem_eventual_of_tile_interior S hL hR hx)
  exact fun {_ _} hA hB hc => Psc.PeriodicPartnerLegalCoincidence.dense_legal_overlap S hQ hp
    (swap_rotation_irrational k hk') hg (every_letter_in_square k hk') hA hB hc

/-- Two legal hull tilings sharing a tile are densely eventually coincident
on the whole line. -/
theorem hull_dense_eventual (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    ∀ {T U : S.Hull}, (T.1 ∩ U.1).Nonempty → Dense (eventual S T.1 U.1) :=
  Psc.PeriodicPartnerLegalCoincidence.dense_hull_of_common_tile _ (legal_patches_dense_eventual k hk)

/-- The literal family excludes disjoint inflation-periodic partners with
the published closed-origin witnesses. -/
theorem periodic_common_tile_of_origin_witnesses (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    ∀ {T U T' U' : S.Hull} {m n : ℕ}, 0 < m → 0 < n → inflateH^[m] T = T → inflateH^[n] U = U →
      ∀ {v : ℝ}, originPatch S T.1 = originPatch S T'.1 → originPatch S U.1 = originPatch S U'.1 →
        originPatch S (LengthSubst.shift v T'.1) = originPatch S (LengthSubst.shift v U'.1) →
          (T.1 ∩ U.1).Nonempty :=
  Psc.PeriodicPartnerLegalCoincidence.periodic_common_tile_of_origin_witnesses _ (hull_dense_eventual k hk)

/-- With injective inflation and the finite-fibre and two-point witness
properties of the published factor, the fibre of the constructed periodic
tiling contains no disjoint pair. -/
theorem periodic_fibre_common_tiles {Y : Type*} (k : ℕ) (hk : 2 ≤ k) :
    let S := geometry k (show 1 ≤ k by omega)
    ∀ (g : S.Hull → Y) (f : Y → Y), Injective (inflateH (S := S)) → Semiconj g inflateH f →
      (∀ y, {T | g T = y}.Finite) →
      (∀ {T U}, g T = g U → ∃ (T' U' : S.Hull) (v : ℝ),
        originPatch S T.1 = originPatch S T'.1 ∧ originPatch S U.1 = originPatch S U'.1 ∧
        originPatch S (LengthSubst.shift v T'.1) = originPatch S (LengthSubst.shift v U'.1)) →
      ∃ y, {T | g T = y}.Nonempty ∧ ∀ T U, g T = y → g U = y → (T.1 ∩ U.1).Nonempty := by
  intro S g f hinj hsem hfin hw
  obtain ⟨V, _, _, hV⟩ := fixed_hull_tiling k (show 1 ≤ k by omega)
  let y := g V
  have hy : f^[2] y = y := by
    dsimp only [y]
    rw [← (hsem.iterate_right 2) V, hV]
  refine ⟨y, ⟨V, rfl⟩, fun T U ht hu => ?_⟩
  obtain ⟨m, hm, _, hT⟩ := Psc.PeriodicPartner.periodic_lift_of_finite_fibre
    _ f g hinj hsem (hfin y) (by decide : 0 < 2) hy ht
  obtain ⟨n, hn, _, hU⟩ := Psc.PeriodicPartner.periodic_lift_of_finite_fibre
    _ f g hinj hsem (hfin y) (by decide : 0 < 2) hy hu
  obtain ⟨T', U', v, h₁, h₂, hv⟩ := hw (ht.trans hu.symm)
  exact periodic_common_tile_of_origin_witnesses k hk hm hn hT hU h₁ h₂ hv

end Psc.ParameterFamilyTiling
