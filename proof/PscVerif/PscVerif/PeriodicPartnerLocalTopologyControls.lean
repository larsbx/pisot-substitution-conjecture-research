/-
# The exact-agreement topology does not carry the translation flow

The control applies to every tiling in the existing legal hull, without a Pisot,
primitivity, recognizability or finite-fibre hypothesis.  A nonzero translation
smaller than the length of a tile cannot preserve that tile's exact position:
otherwise two distinct tiles of the original tiling overlap.  Consequently,
arbitrarily small positive translations fail to agree on the radius-one window,
and their orbit map is discontinuous at zero in the old exact-agreement metric.

The ordinary local orbit is continuous, whereas the identity of carriers back
to the exact presentation is not.  This checks that the separate wrapper uses
the intended topology rather than inheriting the old metric instance.
See `docs/c4-ordinary-hull-topology-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerLocalTopology

namespace Psc.PeriodicPartnerLocalTopologyControls

open Function Filter Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open scoped Topology

variable {α : Type*} {S : LengthSubst α}

/-- A small translation preserving a tile on an exact agreement window is zero.
The bound is the length of that particular tile; no global minimum is needed. -/
theorem small_translate_eq_zero_of_agree {T : S.Hull} {p : α × ℝ} {R t : ℝ}
    (hp : p ∈ T.1) (hwindow : (S.supp p ∩ Ioo (-R) R).Nonempty)
    (hsmall : |t| < S.ℓ p.1) (hagree : Agree R T (translate t T)) : t = 0 := by
  have hp' : (p.1, p.2 + t) ∈ T.1 := (hagree p hwindow).mp hp
  have hℓ := S.ℓ_pos p.1
  obtain ⟨htlo, hthi⟩ := abs_lt.mp hsmall
  let z := max p.2 (p.2 + t)
  have hz : z ∈ S.supp p := by
    change p.2 ≤ max p.2 (p.2 + t) ∧ max p.2 (p.2 + t) < p.2 + S.ℓ p.1
    exact ⟨le_max_left _ _, max_lt (by linarith) (by linarith)⟩
  have hz' : z ∈ S.supp (p.1, p.2 + t) := by
    change p.2 + t ≤ max p.2 (p.2 + t) ∧
      max p.2 (p.2 + t) < p.2 + t + S.ℓ p.1
    exact ⟨le_max_right _ _, max_lt (by linarith) (by linarith)⟩
  have heq := (T.2.1 z).unique ⟨hp, hz⟩ ⟨hp', hz'⟩
  have hx := congrArg Prod.snd heq
  change p.2 = p.2 + t at hx
  linarith

/-- Every positive time scale contains a translation that changes the exact
radius-one patch.  This is an unbounded control, not a finite sample. -/
theorem exists_small_translate_not_agree (T : S.Hull) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ ¬ Agree 1 T (translate t T) := by
  obtain ⟨p, ⟨hp, hp0⟩, _⟩ := T.2.1 0
  have hm : 0 < min δ (S.ℓ p.1) := lt_min hδ (S.ℓ_pos p.1)
  let t := min δ (S.ℓ p.1) / 2
  have ht : 0 < t := half_pos hm
  have htd : t < δ := by dsimp [t]; linarith [min_le_left δ (S.ℓ p.1)]
  have htℓ : |t| < S.ℓ p.1 := by
    rw [abs_of_pos ht]
    dsimp [t]
    linarith [min_le_right δ (S.ℓ p.1)]
  refine ⟨t, ht, htd, fun hagree => ?_⟩
  have hzero := small_translate_eq_zero_of_agree hp
    ⟨0, hp0, by constructor <;> norm_num⟩ htℓ hagree
  exact (ne_of_gt ht) hzero

/-- The old exact-agreement metric makes every translation orbit discontinuous
at zero.  In particular it cannot serve as the topology of a continuous flow. -/
theorem not_continuousAt_exact_orbit (T : S.Hull) :
    ¬ ContinuousAt (fun t : ℝ => translate t T) 0 := by
  intro hc
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  obtain ⟨t, ht, htd, hnot⟩ := exists_small_translate_not_agree T hδ
  have hdist := hclose (show dist t 0 < δ by simpa [Real.dist_eq, abs_of_pos ht] using htd)
  have hz : translate 0 T = T := Subtype.ext (shift_zero T.1)
  rw [hz] at hdist
  apply hnot
  have ha : Agree ((1 : ℕ) : ℝ) T (translate t T) :=
    agree_of_dist_lt (n := 1) (by simpa [dist_comm] using hdist)
  simpa using ha

/-- The same orbit is continuous in the ordinary local presentation. -/
theorem continuous_local_orbit (T : S.Hull) :
    Continuous (fun t : ℝ => PeriodicPartnerLocalTopology.translate S t
      (PeriodicPartnerLocalTopology.ofExact S T)) :=
  (PeriodicPartnerLocalTopology.continuous_translate S).comp
    (continuous_id.prodMk continuous_const)

/-- When the hull is inhabited, the identity of carriers back to the exact
presentation is not continuous.  The two topology instances are distinct. -/
theorem not_continuous_toHull (T : S.Hull) :
    ¬ Continuous (fun U : PeriodicPartnerLocalTopology.LocalHull S => U.toHull) := by
  intro hc
  have horbit := hc.comp (continuous_local_orbit T)
  change Continuous (fun t : ℝ => translate t T) at horbit
  exact not_continuousAt_exact_orbit T horbit.continuousAt

end Psc.PeriodicPartnerLocalTopologyControls
