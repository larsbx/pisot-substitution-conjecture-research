import PscVerif.PeriodicPartnerRealizationContinuity
import Mathlib.Data.Set.Finite.Powerset

/-!
# Finite fibres of the compatible-history realization

Equal torus coordinates give bounded integer differences of vector lifts.
At every desubstitution level this leaves finitely many possible bounded
windows relative to a fixed member of the fibre. Inflation expands those
windows to distinguish any finite collection of distinct fibre members.
-/

namespace Psc.PeriodicPartnerRealizationFinite

open Function Filter Matrix Set
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerRealizationContinuity Psc.PeriodicPartnerLocalRealization
open scoped Topology

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- The length coordinate of the vector lift is the negative origin-tile start. -/
theorem dot_realVec (T : S.Hull) : S.ℓ ⬝ᵥ realVec P hR T = -(origin T).2 := by
  have hcont : Continuous (fun v : α → ℝ => S.ℓ ⬝ᵥ v) := by
    unfold dotProduct
    fun_prop
  have hlim := (hcont.continuousAt (x := realVec P hR T)).tendsto.comp
    (P.tendsto_psum (cs_bound P hR T))
  have hproj (v : α → ℝ) (n : ℕ) : S.ℓ ⬝ᵥ ((mat S ^ n) *ᵥ P.proj v) = 0 := by
    induction n with
    | zero => simp [P.dot_proj]
    | succ n ih => rw [pow_succ', ← mulVec_mulVec, dot_mat_mulVec, ih, mul_zero]
  have hterm (n : ℕ) : S.ℓ ⬝ᵥ ((mat S ^ n) *ᵥ P.proj (cs hR T n)) = 0 := hproj _ n
  have hsum (n : ℕ) : S.ℓ ⬝ᵥ P.psum (xs hR T) (cs hR T) n = -(origin T).2 := by
    simp [PisotData.psum, dotProduct_sub, dotProduct_neg, dotProduct_smul, P.dot_u,
      dotProduct_sum, hterm, xs, level]
  change Tendsto (fun n => S.ℓ ⬝ᵥ P.psum (xs hR T) (cs hR T) n) atTop
    (𝓝 (S.ℓ ⬝ᵥ realVec P hR T)) at hlim
  simp only [hsum] at hlim
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds (x := -(origin T).2) (f := atTop (α := ℕ)))

/-- One bound works for every tiling and every desubstitution depth. -/
theorem exists_realVec_bound : ∃ K : ℝ, ∀ T : S.Hull, ‖realVec P hR T‖ ≤ K := by
  refine ⟨(∑ a, S.ℓ a) * ‖P.u‖ + ∑' n, P.C * P.offsetBound * P.ρ ^ n, fun T => ?_⟩
  have hsup := (tileAt_spec T 0).2
  change (origin T).2 ≤ 0 ∧ 0 < (origin T).2 + S.ℓ (origin T).1 at hsup
  have hx : |(origin T).2| ≤ ∑ a, S.ℓ a := by
    rw [abs_of_nonpos hsup.1]
    exact (show -(origin T).2 ≤ S.ℓ (origin T).1 by linarith [hsup.2]).trans
      (Finset.single_le_sum (f := S.ℓ) (fun a _ => (S.ℓ_pos a).le)
        (Finset.mem_univ (origin T).1))
  have hterm := summable_realization_majorant P
  have hsum : Summable (fun n => ‖(mat S ^ n) *ᵥ P.proj (cs hR T n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => realization_term_norm_le P hR n T)
      hterm
  rw [realVec, PisotData.vec]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (by simpa [xs, level] using hx) (norm_nonneg _)
  · exact (norm_tsum_le_tsum_norm hsum).trans
      (hsum.tsum_le_tsum (fun n => realization_term_norm_le P hR n T) hterm)

private theorem finite_lattice_ball (K : ℝ) :
    {v : α → ℝ | v ∈ lattice α ∧ ‖v‖ ≤ K}.Finite := by
  classical
  let I := Finset.Icc (-⌈K⌉) ⌈K⌉
  let code : (α → I) → (α → ℝ) := fun v a => ((v a).1 : ℝ)
  refine (finite_range code).subset ?_
  rintro v ⟨hv, hK⟩
  choose c hc using (show ∀ a, ∃ n : ℤ, (n : ℝ) = v a from hv)
  have hI (a : α) : c a ∈ I := by
    have hn : |(c a : ℝ)| ≤ K := by
      rw [hc, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm (f := v) a).trans hK
    have hceil : K ≤ (⌈K⌉ : ℝ) := Int.le_ceil K
    have h := abs_le.mp (hn.trans hceil)
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  exact ⟨fun a => ⟨c a, hI a⟩, funext hc⟩

private def window (T : S.Hull) : Set (α × ℝ) :=
  {p ∈ T.1 | (S.supp p ∩ Ioo (-minLen S) (minLen S)).Nonempty}

private theorem agree_of_window_eq {T U : S.Hull} (h : window T = window U) :
    Agree (minLen S) T U := by
  intro p hp
  have hmem := Set.ext_iff.mp h p
  simpa [window, hp] using hmem

/-- The centered small windows of equal-coordinate tilings lie in one
finite collection of patches, independent of the reference tiling. -/
private theorem exists_finite_windows :
    ∃ F : Set (Set (α × ℝ)), F.Finite ∧ ∀ T U : S.Hull,
      torusRealize P hR T = torusRealize P hR U →
      shift (origin U).2 (window T) ∈ F := by
  classical
  obtain ⟨K, hK⟩ := exists_realVec_bound P hR
  let A : Set (α → ℝ) := {v | v ∈ lattice α ∧ ‖v‖ ≤ 2 * K}
  have hA : A.Finite := finite_lattice_ball _
  let D : Set (α → ℝ) :=
    {0} ∪ range (fun a => (Pi.single a 1 : α → ℝ)) ∪
      range (fun a => -(Pi.single a 1 : α → ℝ))
  have hD : D.Finite := ((finite_singleton 0).union (finite_range _)).union (finite_range _)
  let Q := (univ : Set α) ×ˢ image2 (fun v d => S.ℓ ⬝ᵥ (v + d)) A D
  have hQ : Q.Finite := finite_univ.prod (hA.image2 _ hD)
  refine ⟨𝒫 Q, hQ.powerset, fun T U h p hp => ?_⟩
  let v := realVec P hR U - realVec P hR T
  have hv : v ∈ A := by
    refine ⟨(QuotientAddGroup.eq_iff_sub_mem).mp h.symm, ?_⟩
    exact (norm_sub_le _ _).trans (by linarith [hK U, hK T])
  have hx : S.ℓ ⬝ᵥ v = (origin T).2 - (origin U).2 := by
    simp only [v, dotProduct_sub, dot_realVec]
    ring
  change (p.1, p.2 + (origin U).2) ∈ window T at hp
  obtain ⟨hpT, s, hsupp, hs⟩ := hp
  obtain ⟨d, hd, hstart⟩ := tileAt_near T (abs_lt.mpr hs)
  rw [tileAt_eq hpT hsupp] at hstart
  refine ⟨trivial, ⟨v, hv, d, hd, ?_⟩⟩
  change S.ℓ ⬝ᵥ (v + d) = p.2
  rw [dotProduct_add, hx]
  dsimp at hstart
  linarith

private theorem exists_agree_radius (T U : S.Hull) :
    ∃ n : ℕ, Agree (n : ℝ) T U → T = U := by
  by_cases h : T = U
  · exact ⟨0, fun _ => h⟩
  have hv : T.1 ≠ U.1 := fun h' => h (Subtype.ext h')
  obtain ⟨p, hp⟩ : ∃ p, ¬ (p ∈ T.1 ↔ p ∈ U.1) := by
    by_contra! ha
    exact hv (Set.ext ha)
  obtain ⟨n, hn⟩ := exists_nat_gt |p.2|
  refine ⟨n, fun hA => (hp (hA p ⟨p.2, ?_, abs_lt.mp hn⟩)).elim⟩
  exact ⟨le_rfl, lt_add_of_pos_right _ (S.ℓ_pos p.1)⟩

private theorem level_agree_expands {T U : S.Hull} (n : ℕ)
    (h : Agree (minLen S) (level hR n T) (level hR n U)) :
    Agree (S.β ^ n * minLen S) T U := by
  induction n generalizing T U with
  | zero => simpa [level] using h
  | succ n ih =>
    rw [show level hR (n + 1) T = level hR n (desub hR T) from level_add hR n 1 T,
      show level hR (n + 1) U = level hR n (desub hR U) from level_add hR n 1 U] at h
    simpa [pow_succ', mul_assoc, inflateH_desub] using (ih h).inflate

/-- Every fibre of the same concrete realization has a uniform finite bound. -/
theorem realize_finite_fibres (hβ : 1 < S.β) (z : Solenoid S) :
    {T : S.Hull | realize P hR T = z}.Finite := by
  classical
  let E : Set S.Hull := {T | realize P hR T = z}
  change E.Finite
  by_contra hE
  let : Infinite E := Set.infinite_coe_iff.mpr hE
  let e := Infinite.natEmbedding E
  obtain ⟨F, hF, hpatch⟩ := exists_finite_windows P hR
  let := hF.fintype
  let N := Fintype.card F + 1
  let T : Fin N → S.Hull := fun i => (e i.val).val
  have hinj : Injective T := fun i j hij =>
    Fin.ext (e.injective (Subtype.ext hij))
  choose r hr using fun ij : Fin N × Fin N => exists_agree_radius (T ij.1) (T ij.2)
  let R := Finset.univ.sup r
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((R : ℝ) / minLen S) hβ
  have hRn := (div_lt_iff₀ (minLen_pos (S := S))).mp hn
  let U := level hR n (e 0).val
  have hz (i : Fin N) : torusRealize P hR (level hR n (T i)) = torusRealize P hR U := by
    have hi : realize P hR (T i) = z := (e i.val).property
    have h0 : realize P hR (e 0).val = z := (e 0).property
    exact congrArg (fun w : Solenoid S => w.1 n) (hi.trans h0.symm)
  let f : Fin N → F := fun i =>
    ⟨shift (origin U).2 (window (level hR n (T i))), hpatch _ _ (hz i)⟩
  have hf : Injective f := by
    intro i j hij
    have hw := shift_injective (origin U).2 (congrArg Subtype.val hij)
    have ha := level_agree_expands hR n (agree_of_window_eq hw)
    have hle : r (i, j) ≤ R := Finset.le_sup (f := r) (Finset.mem_univ (i, j))
    exact hinj (hr (i, j) (agree_mono ha ((Nat.cast_le.mpr hle).trans hRn.le)))
  have hcard := Fintype.card_le_of_injective f hf
  simp [N] at hcard

/-- The ordinary local hull has the very same finite solenoid fibres. -/
theorem realizeLocal_finite_fibres (hβ : 1 < S.β) (z : Solenoid S) :
    {T | realizeLocal P hR T = z}.Finite := by
  exact Set.Finite.preimage (fun T _ U _ h => by cases T; cases U; cases h; rfl)
    (realize_finite_fibres P hR hβ z)

end Psc.PeriodicPartnerRealizationFinite
