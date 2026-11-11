import PscVerif.NamedPrefixCompact
import PscVerif.GeometricPacketCarrier

/-!
# Authenticated enclosures for the two named prefix systems

Every point of each actual closed prefix tile inherits the proved stable
ball bound. The full physical/stable reconstruction gives an explicit
inverse chart on integer translations, and actual image lengths scale by
the Perron root at every literal substitution power.

The radius is the authenticated `8 * digitBound fixture`, not a sharper
external numerical enclosure. The ambient group remains the original
`Stable × H_M`; neither the word period nor the completion is changed.

Pre-code gate: `docs/c4-named-finite-carrier-literature-2026-11-11.md`.
-/

namespace Psc.NamedGeometricEnclosure

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceResidue
open Psc.PrefixClosure Psc.NamedStableChart Psc.NamedPrefixCompact
open Psc.GeometricPacketCarrier Matrix

/-- Evaluation of an actual stable coordinate in the original product
carrier. The completion coordinate is retained in the domain. -/
def stableCoordinate (fixture : Fin 2) (i : Fin 2) :
    Ambient (substitution fixture) Stable →+ ℝ where
  toFun x := x.1 i
  map_zero' := rfl
  map_add' := by intro x y; rfl

@[simp] theorem stableCoordinate_apply (fixture : Fin 2) (i : Fin 2)
    (x : Ambient (substitution fixture) Stable) :
    stableCoordinate fixture i x = x.1 i := rfl

/-- The closed inequality passes from every actual prefix point to the
entire closure defining each named tile. -/
theorem tile_stable_norm_bound (fixture : Fin 2) (letter : Fin 3)
    (x : Ambient (substitution fixture) Stable) (hx : x ∈ tiles fixture letter) :
    ‖x.1‖ ≤ radius fixture := by
  have hclosed : IsClosed
      {y : Ambient (substitution fixture) Stable | ‖y.1‖ ≤ radius fixture} :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have hraw : raw (word fixture) (ambientStar (substitution fixture) piZ) letter ⊆
      {y : Ambient (substitution fixture) Stable | ‖y.1‖ ≤ radius fixture} := by
    rintro y ⟨n, hn, rfl⟩
    exact prefix_norm_bound fixture n
  change x ∈ closure (raw (word fixture)
    (ambientStar (substitution fixture) piZ) letter) at hx
  exact closure_minimal hraw hclosed hx

/-- Both coordinate bounds use the same authenticated sup-norm radius. -/
theorem tile_coordinate_bound (fixture : Fin 2) (letter : Fin 3)
    (x : Ambient (substitution fixture) Stable) (hx : x ∈ tiles fixture letter)
    (i : Fin 2) : |stableCoordinate fixture i x| ≤ radius fixture := by
  simpa only [stableCoordinate_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm x.1 i).trans (tile_stable_norm_bound fixture letter x hx)

/-- A common physical length bound; no sharp numerical optimization is
required for finite integer coordinate bounds. -/
noncomputable def physicalBound : ℝ := 1 + beta + c

theorem length_le_physicalBound (letter : Fin 3) :
    physicalRow letter ≤ physicalBound := by
  fin_cases letter <;> simp [physicalRow, physicalBound] <;>
    linarith [beta_pos, c_gt_one]

/-- Inverse coefficients in the order physical, first stable coordinate,
second stable coordinate. They come from the corrected stable section. -/
noncomputable def inverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a / kappa, 1 - a / kappa, -(a * c) / kappa;
     1 / kappa, -(1 / kappa), -c / kappa;
     b / kappa, -b / kappa, 1 - b * c / kappa]

theorem inverse_reconstruct (x : AmbientReal) (j : Fin 3) :
    x j = inverse j 0 * physical x + inverse j 1 * (W *ᵥ x) 0 +
      inverse j 2 * (W *ᵥ x) 1 := by
  calc
    x j = (L (W *ᵥ x) + (physical x / kappa) • r) j :=
      congrFun (reconstruction x) j
    _ = inverse j 0 * physical x + inverse j 1 * (W *ᵥ x) 0 +
        inverse j 2 * (W *ᵥ x) 1 := by
      generalize (W *ᵥ x) = y
      fin_cases j <;>
        simp [inverse, L, J_mulVec, physical_apply, r, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem integer_reconstruct (fixture : Fin 2) (z : Fin 3 → ℤ) (j : Fin 3) :
    (z j : ℝ) = inverse j 0 * offset physicalRow z +
      inverse j 1 * stableCoordinate fixture 0
        (ambientStar (substitution fixture) piZ z) +
      inverse j 2 * stableCoordinate fixture 1
        (ambientStar (substitution fixture) piZ z) := by
  change (castZ z) j = inverse j 0 * physical (castZ z) +
    inverse j 1 * (W *ᵥ castZ z) 0 + inverse j 2 * (W *ᵥ castZ z) 1
  exact inverse_reconstruct (castZ z) j

/-- All geometric inputs are discharged for the actual named closed
prefix tiles, including their physical direction. -/
noncomputable def chart (fixture : Fin 2) :
    ChartEnclosure (ambientStar (substitution fixture) piZ)
      (tiles fixture) physicalRow where
  coordinate := stableCoordinate fixture
  radius := fun _ => NamedPrefixCompact.radius fixture
  physicalBound := physicalBound
  length_le := length_le_physicalBound
  inverse := inverse
  reconstruct := integer_reconstruct fixture
  enclosed := fun letter x hx i => tile_coordinate_bound fixture letter x hx i

/-- Literal one-step image lengths, including the two distinct orders of
the middle image, scale by the authenticated Perron root. -/
theorem physicalLength_image (fixture : Fin 2) (letter : Fin 3) :
    physicalLength physicalRow (substitution fixture letter) = beta * physicalRow letter := by
  have hmiddle : 1 + beta + c = beta ^ 2 := by unfold c; ring
  fin_cases fixture <;> fin_cases letter <;>
    simp [substitution, sigma0, sigma1, physicalRow] <;>
    nlinarith [beta_mul_c]

theorem physicalLength_subst (fixture : Fin 2) (w : Word) :
    physicalLength physicalRow (subst (substitution fixture) w) =
      beta * physicalLength physicalRow w := by
  induction w with
  | nil => simp [subst]
  | cons letter w ih =>
      rw [subst_cons, physicalLength_append, physicalLength_image fixture letter,
        ih, physicalLength_cons]
      ring

/-- Exact scaling for every actual substitution power. This supplies the
physical-strip transport at its authentic chosen block scale. -/
theorem physicalLength_iterateImages (fixture : Fin 2) (k : ℕ) (letter : Fin 3) :
    physicalLength physicalRow (iterateImages (substitution fixture) k letter) =
      beta ^ k * physicalRow letter := by
  unfold iterateImages
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', physicalLength_subst, ih, pow_succ]
      ring

end Psc.NamedGeometricEnclosure
