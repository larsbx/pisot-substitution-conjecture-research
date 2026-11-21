import PscVerif.PeriodicPartnerEventualCoincidence
import PscVerif.PeriodicPartnerProximal
import Mathlib.Topology.Baire.Lemmas

/-!
# Simultaneous coincidence for finitely many legal tilings

An anchor and finitely many eventual-coincidence witnesses can be advanced
to their maximum inflation depth. Tile uniqueness in the anchor then gives
one labelled tile shared by every member at that depth. A finite intersection
of open dense sets supplies the witnesses simultaneously. Further finite
inflation and a common translation give a prescribed shared window.

Only the finite-intersection lemma from `Baire.Lemmas` is used; no Baire
category theorem, sequence limit, or measure statement enters this argument.
The depth and translation may depend on the whole finite family and radius.
Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerFiniteCoincidence

open Function Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerEventualCoincidence Psc.PeriodicPartnerProximal
open Psc.PeriodicPartnerEvenTails (hull_iterate_val)

variable {α ι : Type*} [Nonempty α] [Fintype ι] (S : LengthSubst α)

/-- A maximum of finitely many depths supplies one common labelled tile.
The selected point is retained in the inflated support of that tile. -/
theorem common_tile_of_finite_eventual (T : ι → S.Hull) (i₀ : ι) {x : ℝ}
    (h : ∀ i, x ∈ eventual S (T i₀).1 (T i).1) :
    ∃ n : ℕ, ∃ q : α × ℝ,
      (∀ i, q ∈ (inflateH^[n] (T i)).1) ∧ S.β ^ n * x ∈ S.supp q := by
  classical
  choose depth hdepth using fun i => mem_iUnion.mp (h i)
  let n := Finset.univ.sup depth
  have hlevel (i : ι) : x ∈ level S (T i₀).1 (T i).1 n :=
    level_mono S (T i₀).1 (T i).1
      (Finset.le_sup (f := depth) (Finset.mem_univ i)) (interior_subset (hdepth i))
  obtain ⟨q, hq₀, _, hqx⟩ := hlevel i₀
  refine ⟨n, q, fun i => ?_, hqx⟩
  obtain ⟨p, hp₀, hpi, hpx⟩ := hlevel i
  have hpq := ((tiling_iterate S (T i₀).2.1 n) (S.β ^ n * x)).unique
    ⟨hp₀, hpx⟩ ⟨hq₀, hqx⟩
  simpa only [hull_iterate_val, hpq] using hpi

/-- Finitely many open dense anchor-coincidence sets have a common point.
All members therefore share a tile after one common finite depth. -/
theorem common_tile_of_finite_dense_eventual (T : ι → S.Hull) (i₀ : ι)
    (hd : ∀ i, Dense (eventual S (T i₀).1 (T i).1)) :
    ∃ n : ℕ, ∃ q : α × ℝ, ∀ i, q ∈ (inflateH^[n] (T i)).1 := by
  let E : ι → Set ℝ := fun i => eventual S (T i₀).1 (T i).1
  have hE : Dense (⋂₀ range E) :=
    (finite_range E).dense_sInter
      (by rintro W ⟨i, rfl⟩; exact eventual_open S (T i₀).1 (T i).1)
      (by rintro W ⟨i, rfl⟩; exact hd i)
  obtain ⟨x, hx⟩ := hE.nonempty
  obtain ⟨n, q, hq, _⟩ := common_tile_of_finite_eventual S T i₀
    (fun i => hx (E i) ⟨i, rfl⟩)
  exact ⟨n, q, hq⟩

/-- A shared tile in a finite family expands to any prescribed window.
One depth and one translation work for every pair in the family. -/
theorem common_window_of_finite_dense_eventual (hβ : 1 < S.β)
    (T : ι → S.Hull) (i₀ : ι)
    (hd : ∀ i, Dense (eventual S (T i₀).1 (T i).1))
    {R : ℝ} (_hR : 0 < R) :
    ∃ n : ℕ, ∃ t : ℝ, ∀ i j,
      Agree R (translate t (inflateH^[n] (T i)))
        (translate t (inflateH^[n] (T j))) := by
  obtain ⟨n, q, hq⟩ := common_tile_of_finite_dense_eventual S T i₀ hd
  let r := S.ℓ q.1 / 2
  let c := q.2 + r
  have hr : 0 < r := half_pos (S.ℓ_pos q.1)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (R / r) hβ
  have hRm : R ≤ S.β ^ m * r := ((div_lt_iff₀ hr).mp hm).le
  refine ⟨m + n, S.β ^ m * c, fun i j => ?_⟩
  have hsmall : Agree r (translate c (inflateH^[n] (T i)))
      (translate c (inflateH^[n] (T j))) := agree_at_common_tile S (hq i) (hq j)
  have hlarge := (agreementData (S := S)).agreement_iterate S.β_pos hr hsmall m
  change Agree (S.β ^ m * r) (inflateH^[m] (translate c (inflateH^[n] (T i))))
    (inflateH^[m] (translate c (inflateH^[n] (T j)))) at hlarge
  rw [inflateH_iterate_translate, inflateH_iterate_translate] at hlarge
  simpa only [iterate_add_apply] using agree_mono hlarge hRm

end Psc.PeriodicPartnerFiniteCoincidence
