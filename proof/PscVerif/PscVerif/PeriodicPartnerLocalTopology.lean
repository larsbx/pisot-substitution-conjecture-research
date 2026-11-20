/-
# The ordinary local topology on the legal tiling hull

`LocalHull` is a separate topological presentation of the existing literal
tilings. Its topology is the open quotient of `ℝ × Hull` by
`(t,T) ↦ T - t`, where `Hull` retains its exact-agreement metric.
The neighbourhood basis is proved to be small translation plus agreement on
a large window. Translation is jointly continuous and inflation is continuous.

No recognizability, primitivity, Pisot or finite-fibre hypothesis enters the
topology construction. A final criterion transfers continuity of equivariant
maps from the exact hull; it does not assume or prove that inverse inflation
or the geometric realization is continuous.

Source decision: `docs/c4-ordinary-hull-topology-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerHullContinuity
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Maps.OpenQuotient

namespace Psc.PeriodicPartnerLocalTopology

open Function Filter Set Topology Psc.PeriodicPartnerHull
open LengthSubst
open scoped Topology

variable {α : Type*} (S : LengthSubst α)

/-- The same legal tilings, with a separate instance for the ordinary topology. -/
@[ext] structure LocalHull where
  toHull : S.Hull

/-- The translation chart from the exact hull. -/
def chart (p : ℝ × S.Hull) : LocalHull S := ⟨LengthSubst.translate p.1 p.2⟩

noncomputable instance : TopologicalSpace (LocalHull S) :=
  TopologicalSpace.coinduced (chart S) inferInstance

/-- The identity of carriers, from the exact presentation to the local one. -/
def ofExact (T : S.Hull) : LocalHull S := ⟨T⟩

@[simp] theorem chart_zero (T : S.Hull) : chart S (0, T) = ofExact S T := by
  apply LocalHull.ext
  exact LengthSubst.translate_zero T

theorem chart_surjective : Surjective (chart S) := by
  intro T
  exact ⟨(0, T.toHull), by simp [chart]⟩

theorem continuous_chart : Continuous (chart S) := continuous_coinduced_rng

theorem continuous_ofExact : Continuous (ofExact S) := by
  have h : Continuous (fun T : S.Hull => ((0 : ℝ), T)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def, chart_zero] using
    (continuous_chart S).comp h

/-- Changing the representative while keeping the represented tiling fixed. -/
def fibreShift (t : ℝ) (p : ℝ × S.Hull) : ℝ × S.Hull :=
  (p.1 + t, LengthSubst.translate (-t) p.2)

theorem continuous_fibreShift (t : ℝ) : Continuous (fibreShift S t) :=
  (continuous_fst.add continuous_const).prodMk
    ((LengthSubst.continuous_translate (-t)).comp continuous_snd)

@[simp] theorem chart_fibreShift (t : ℝ) (p : ℝ × S.Hull) :
    chart S (fibreShift S t p) = chart S p := by
  apply LocalHull.ext
  change LengthSubst.translate (p.1 + t) (LengthSubst.translate (-t) p.2) = _
  rw [LengthSubst.translate_translate]
  congr 1
  ring

theorem chart_saturation (U : Set (ℝ × S.Hull)) :
    chart S ⁻¹' (chart S '' U) = ⋃ t : ℝ, fibreShift S t ⁻¹' U := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨q, hq, heq⟩
    refine mem_iUnion.mpr ⟨q.1 - p.1, ?_⟩
    have he : fibreShift S (q.1 - p.1) p = q := by
      apply Prod.ext
      · change p.1 + (q.1 - p.1) = q.1
        ring
      · apply LengthSubst.translate_injective q.1
        change LengthSubst.translate q.1
          (LengthSubst.translate (-(q.1 - p.1)) p.2) =
            LengthSubst.translate q.1 q.2
        rw [LengthSubst.translate_translate]
        have ht : q.1 + -(q.1 - p.1) = p.1 := by ring
        rw [ht]
        exact (congrArg LocalHull.toHull heq).symm
    change fibreShift S (q.1 - p.1) p ∈ U
    rw [he]
    exact hq
  · intro hp
    obtain ⟨t, ht⟩ := mem_iUnion.mp hp
    exact ⟨fibreShift S t p, ht, chart_fibreShift S t p⟩

theorem isOpenMap_chart : IsOpenMap (chart S) := by
  intro U hU
  change IsOpen (chart S ⁻¹' (chart S '' U))
  rw [chart_saturation]
  exact isOpen_iUnion fun t => hU.preimage (continuous_fibreShift S t)

/-- Openness is essential when taking products of this quotient map. -/
theorem isOpenQuotientMap_chart : IsOpenQuotientMap (chart S) :=
  ⟨chart_surjective S, continuous_chart S, isOpenMap_chart S⟩

/-- Agreement with the centre after undoing one translation of size below `ε`. -/
def patch (T : LocalHull S) (ε : ℝ) (n : ℕ) : Set (LocalHull S) :=
  {U | ∃ t : ℝ, |t| < ε ∧
    Agree (n : ℝ) T.toHull (LengthSubst.translate (-t) U.toHull)}

theorem patch_eq_image (T : LocalHull S) (ε : ℝ) (n : ℕ) :
    patch S T ε n = chart S ''
      (Metric.ball (0 : ℝ) ε ×ˢ {U : S.Hull | Agree (n : ℝ) T.toHull U}) := by
  apply Set.ext
  intro U
  constructor
  · rintro ⟨t, ht, hA⟩
    refine ⟨(t, LengthSubst.translate (-t) U.toHull), ⟨?_, hA⟩, ?_⟩
    · simpa [Real.dist_eq] using ht
    · apply LocalHull.ext
      simp only [chart, LengthSubst.translate_translate, add_neg_cancel,
        LengthSubst.translate_zero]
  · rintro ⟨⟨t, V⟩, ⟨ht, hA⟩, he⟩
    refine ⟨t, by simpa [Real.dist_eq] using ht, ?_⟩
    have hU : U.toHull = LengthSubst.translate t V :=
      (congrArg LocalHull.toHull he).symm
    rw [hU, LengthSubst.translate_translate, neg_add_cancel, LengthSubst.translate_zero]
    exact hA

theorem isOpen_patch (T : LocalHull S) (ε : ℝ) (n : ℕ) : IsOpen (patch S T ε n) := by
  rw [patch_eq_image]
  exact isOpenMap_chart S _ (Metric.isOpen_ball.prod (LengthSubst.isOpen_agreement T.toHull n))

/-- This identifies the coinduced topology with ordinary local tiling convergence. -/
theorem nhds_patch_basis (T : LocalHull S) :
    (𝓝 T).HasBasis (fun i : ℝ × ℕ => 0 < i.1) (fun i => patch S T i.1 i.2) := by
  have h := ((Metric.nhds_basis_ball (x := (0 : ℝ))).prod_nhds
    (LengthSubst.nhds_agreement_basis T.toHull)).map (chart S)
  rw [(isOpenQuotientMap_chart S).map_nhds_eq] at h
  have hc : chart S (0, T.toHull) = T := by simp [chart]
  rw [hc] at h
  simpa only [and_true, ← patch_eq_image] using h

theorem mem_nhds_iff (T : LocalHull S) (U : Set (LocalHull S)) :
    U ∈ 𝓝 T ↔ ∃ ε > 0, ∃ n : ℕ, patch S T ε n ⊆ U := by
  rw [(nhds_patch_basis S T).mem_iff]
  simp only [Prod.exists]
  aesop

theorem isOpen_iff (U : Set (LocalHull S)) :
    IsOpen U ↔ ∀ T ∈ U, ∃ ε > 0, ∃ n : ℕ, patch S T ε n ⊆ U := by
  rw [isOpen_iff_mem_nhds]
  simp only [mem_nhds_iff]

/-- Translation on the ordinary local hull. -/
def translate (t : ℝ) (T : LocalHull S) : LocalHull S :=
  ⟨LengthSubst.translate t T.toHull⟩

@[simp] theorem translate_zero (T : LocalHull S) : translate S 0 T = T := by
  apply LocalHull.ext
  exact LengthSubst.translate_zero T.toHull

theorem translate_translate (s t : ℝ) (T : LocalHull S) :
    translate S s (translate S t T) = translate S (s + t) T := by
  apply LocalHull.ext
  exact LengthSubst.translate_translate s t T.toHull

theorem translate_chart (s : ℝ) (p : ℝ × S.Hull) :
    translate S s (chart S p) = chart S (s + p.1, p.2) := by
  apply LocalHull.ext
  exact LengthSubst.translate_translate s p.1 p.2

/-- Joint continuity in time and tiling, proved through an open quotient. -/
theorem continuous_translate :
    Continuous (fun p : ℝ × LocalHull S => translate S p.1 p.2) := by
  apply ((IsOpenQuotientMap.id (X := ℝ)).prodMap
    (isOpenQuotientMap_chart S)).isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun p : ℝ × (ℝ × S.Hull) => (p.1 + p.2.1, p.2.2)) :=
    (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  change Continuous (fun p : ℝ × (ℝ × S.Hull) => translate S p.1 (chart S p.2))
  simpa only [Function.comp_def, translate_chart] using
    (continuous_chart S).comp h

def translateHomeomorph (t : ℝ) : LocalHull S ≃ₜ LocalHull S where
  toFun := translate S t
  invFun := translate S (-t)
  left_inv T := by rw [translate_translate, neg_add_cancel, translate_zero]
  right_inv T := by rw [translate_translate, add_neg_cancel, translate_zero]
  continuous_toFun := (continuous_translate S).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_translate S).comp (continuous_const.prodMk continuous_id)

/-- Literal inflation on the same carrier with the ordinary topology. -/
def inflate [Nonempty α] (T : LocalHull S) : LocalHull S := ⟨inflateH T.toHull⟩

theorem inflate_chart [Nonempty α] (p : ℝ × S.Hull) :
    inflate S (chart S p) = chart S (S.β * p.1, inflateH p.2) := by
  apply LocalHull.ext
  exact inflateH_translate p.1 p.2

theorem continuous_inflate [Nonempty α] : Continuous (inflate S) := by
  apply (isOpenQuotientMap_chart S).isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun p : ℝ × S.Hull => (S.β * p.1, inflateH p.2)) :=
    (continuous_const.mul continuous_fst).prodMk
      (LengthSubst.continuous_inflateH.comp continuous_snd)
  simpa only [Function.comp_def, inflate_chart] using (continuous_chart S).comp h

/-- For an equivariant map to a continuous flow, exact-source continuity is
precisely the remaining continuity obligation. This is a criterion, not a
proof that any particular realization satisfies it. -/
theorem continuous_iff_exact_of_equivariant {Y : Type*} [TopologicalSpace Y]
    (f : LocalHull S → Y) (flow : ℝ → Y → Y)
    (hflow : Continuous (fun p : ℝ × Y => flow p.1 p.2))
    (hequiv : ∀ t T, f (translate S t T) = flow t (f T)) :
    Continuous f ↔ Continuous (f ∘ ofExact S) := by
  constructor
  · exact fun hf => hf.comp (continuous_ofExact S)
  · intro hf
    apply (isOpenQuotientMap_chart S).isQuotientMap.continuous_iff.mpr
    have h := hflow.comp (continuous_fst.prodMk (hf.comp continuous_snd))
    have hEq : (f ∘ chart S) =
        (fun p : ℝ × S.Hull => flow p.1 (f (ofExact S p.2))) := by
      funext p
      exact hequiv p.1 (ofExact S p.2)
    rw [hEq]
    exact h

end Psc.PeriodicPartnerLocalTopology
