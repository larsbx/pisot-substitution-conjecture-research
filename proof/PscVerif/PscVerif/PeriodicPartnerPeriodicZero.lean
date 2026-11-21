import PscVerif.PeriodicPartnerRealizationFinite

/-!
# Periodic tilings over the zero history

For an inflation-periodic legal tiling, the full solenoid realization is zero
exactly when the start of its origin tile is the negative length of an integer
vector. This includes strictly interior origin positions; a vertex at zero is
not necessary. The proof uses the existing stable series and its integer
partial-sum identity, without a maximal-factor or coincidence assumption.

Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerPeriodicZero

open Function Filter Matrix Set
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerRealizationFinite
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- Periodicity promotes a zero torus coordinate to the entire zero history.
The nonunit torus map itself is not assumed injective. -/
theorem realize_zero_of_periodic_torus_zero {T : S.Hull} {p : ℕ} (hp : 0 < p)
    (hper : inflateH^[p] T = T) (hzero : torusRealize P hR T = 0) :
    realize P hR T = 0 := by
  have hlevel : level hR p T = T := by
    conv_lhs => rw [← hper]
    exact level_inflate_iterate hR p T
  have h0 : (realize P hR T).1 0 = 0 := hzero
  refine Subtype.ext (funext fun n => ?_)
  set z := realize P hR T
  have hfix : (torusMap S)^[p] (z.1 n) = z.1 n := by
    conv_lhs => rw [show z.1 n = z.1 (n + p) by
      change torusRealize P hR (level hR n T) = torusRealize P hR (level hR (n + p) T)
      rw [level_add, hlevel]]
    exact iterate_coord S z p n
  have hkill : (torusMap S)^[n] (z.1 n) = 0 := by
    simpa [h0] using iterate_coord S z n 0
  have hmul : (torusMap S)^[p * n] (z.1 n) = z.1 n := by
    rw [iterate_mul]
    exact iterate_fixed hfix n
  have hle : n ≤ p * n := Nat.le_mul_of_pos_left n hp
  rw [← hmul, ← Nat.sub_add_cancel hle, iterate_add_apply, hkill]
  exact iterate_fixed (map_zero _) _

/-- A periodic origin start in the length lattice has an integer torus lift.
Integer partial sums plus a vanishing stable correction converge to the
actual realization vector; no origin-vertex premise is needed. -/
theorem torusRealize_zero_of_periodic_lattice_origin {T : S.Hull} {p : ℕ}
    (hp : 0 < p) (hper : inflateH^[p] T = T)
    {v : α → ℝ} (hv : v ∈ lattice α) (horigin : (origin T).2 = -(S.ℓ ⬝ᵥ v)) :
    torusRealize P hR T = 0 := by
  have hlevel : level hR p T = T := by
    conv_lhs => rw [← hper]
    exact level_inflate_iterate hR p T
  have hlevel_mul (j : ℕ) : level hR (p * j) T = T := by
    rw [level, iterate_mul]
    exact iterate_fixed hlevel j
  have hsub : Tendsto (fun j : ℕ => p * j) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun j hj => hj.trans (Nat.le_mul_of_pos_left j hp)⟩
  have hstable := P.tendsto_pow_proj_zero (d := fun _ => v)
    (K := ‖P.proj v‖) (fun _ => le_rfl)
  have hlim := ((P.tendsto_psum (x := xs hR T) (cs_bound P hR T)).comp hsub).add
    (hstable.comp hsub)
  have hlim' : Tendsto
      (fun j : ℕ => P.psum (xs hR T) (cs hR T) (p * j) +
        (mat S ^ (p * j)) *ᵥ P.proj v) atTop (𝓝 (realVec P hR T)) := by
    simpa only [Function.comp_def, realVec, add_zero] using hlim
  have hmem : realVec P hR T ∈ lattice α := by
    refine isClosed_lattice.mem_of_tendsto hlim' (Eventually.of_forall fun j => ?_)
    have h := add_mem (P.partial_sub_mem (xs_succ hR T) (cs_mem hR T) (p * j))
      (pow_mulVec_mem_lattice S hv (p * j))
    have he : P.psum (xs hR T) (cs hR T) (p * j) +
        (mat S ^ (p * j)) *ᵥ P.proj v =
        (P.psum (xs hR T) (cs hR T) (p * j) -
          (-((S.β ^ (p * j) * xs hR T (p * j)) • P.u))) +
            (mat S ^ (p * j)) *ᵥ v := by
      rw [P.pow_mulVec_proj]
      simp only [xs, hlevel_mul, horigin, mul_neg, neg_smul, neg_neg]
      abel
    rwa [he]
  exact (QuotientAddGroup.eq_zero_iff _).mpr hmem

theorem realize_zero_of_periodic_lattice_origin {T : S.Hull} {p : ℕ}
    (hp : 0 < p) (hper : inflateH^[p] T = T)
    {v : α → ℝ} (hv : v ∈ lattice α) (horigin : (origin T).2 = -(S.ℓ ⬝ᵥ v)) :
    realize P hR T = 0 :=
  realize_zero_of_periodic_torus_zero P hR hp hper
    (torusRealize_zero_of_periodic_lattice_origin P hR hp hper hv horigin)

/-- Zero realization always puts the actual origin start in the length lattice. -/
theorem lattice_origin_of_realize_zero {T : S.Hull} (h : realize P hR T = 0) :
    ∃ v : α → ℝ, v ∈ lattice α ∧ (origin T).2 = -(S.ℓ ⬝ᵥ v) := by
  have h0 : torusRealize P hR T = 0 := congrArg (fun z : Solenoid S => z.1 0) h
  refine ⟨realVec P hR T, (QuotientAddGroup.eq_zero_iff _).mp h0, ?_⟩
  rw [dot_realVec]
  simp

/-- Exact characterization for periodic tilings. This retains the whole
inverse-limit zero history, rather than only the zeroth torus coordinate. -/
theorem realize_zero_iff_lattice_origin_of_periodic {T : S.Hull} {p : ℕ}
    (hp : 0 < p) (hper : inflateH^[p] T = T) :
    realize P hR T = 0 ↔
      ∃ v : α → ℝ, v ∈ lattice α ∧ (origin T).2 = -(S.ℓ ⬝ᵥ v) := by
  refine ⟨lattice_origin_of_realize_zero P hR, ?_⟩
  rintro ⟨v, hv, horigin⟩
  exact realize_zero_of_periodic_lattice_origin P hR hp hper hv horigin

end Psc.PeriodicPartnerPeriodicZero
