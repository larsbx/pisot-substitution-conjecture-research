/-
# The ordinary local hull is Hausdorff

Gap 1 of `docs/c4-ordinary-hull-topology-2026-11-19.md` lists Hausdorffness of `LocalHull` as
unproved.  This module proves `T2Space (LocalHull S)` for every length substitution.  No
recognizability, primitivity, Pisot, compactness or finite-local-complexity hypothesis enters.

Argument.  If every ordinary neighbourhood of `T` meets the corresponding one of `U`, then `U`
agrees with translates of `T` by arbitrarily small `r` on arbitrarily large windows
(`approx_of_patches`).  A tile `(a, x)` of either tiling then has copies `(a, x + r)` with
`|r|` arbitrarily small in the other.  Two such copies at offsets closer than `ℓ a` overlap,
so tiling uniqueness forces every small offset to equal one fixed `r₀`, and hence `r₀ = 0`
(`mem_of_approx`).

Source decision: `docs/c4-ordinary-hull-hausdorff-stop-go-2026-11-21.md`.
-/
import PscVerif.PeriodicPartnerLocalTopology

namespace Psc.PeriodicPartnerLocalTopology

open Function Filter Set Topology Psc.PeriodicPartnerHull
open LengthSubst
open scoped Topology

variable {α : Type*} {S : LengthSubst α}

/-- A tile whose label recurs at arbitrarily small offsets in a tiling lies in it. -/
theorem mem_of_approx {X : Set (α × ℝ)} (hX : S.IsTiling X) {a : α} {x : ℝ}
    (h : ∀ ε > 0, ∃ r, |r| < ε ∧ (a, x + r) ∈ X) : (a, x) ∈ X := by
  have hℓ := S.ℓ_pos a
  obtain ⟨r₀, hr₀, hm₀⟩ := h (S.ℓ a / 2) (by linarith)
  by_cases hzero : r₀ = 0
  · simpa [hzero] using hm₀
  exfalso
  obtain ⟨r, hr, hm⟩ := h (min |r₀| (S.ℓ a / 2)) (lt_min (abs_pos.mpr hzero) (by linarith))
  have hr1 := lt_of_lt_of_le hr (min_le_left _ _)
  have hr2 := lt_of_lt_of_le hr (min_le_right _ _)
  obtain ⟨h1, h2⟩ := abs_lt.mp hr2
  obtain ⟨h3, h4⟩ := abs_lt.mp hr₀
  have hz : ∀ s, x + s ≤ max (x + r) (x + r₀) → -(S.ℓ a / 2) < s →
      max (x + r) (x + r₀) ∈ S.supp (a, x + s) := fun s hle hs =>
    ⟨hle, max_lt (by dsimp only; linarith) (by dsimp only; linarith)⟩
  have heq := (hX (max (x + r) (x + r₀))).unique
    ⟨hm, hz r (le_max_left _ _) h1⟩ ⟨hm₀, hz r₀ (le_max_right _ _) h3⟩
  have : r = r₀ := by simpa using heq
  rw [this] at hr1
  exact lt_irrefl _ hr1

/-- Two exact tilings that agree with arbitrarily small translates of each other on
arbitrarily large windows are equal. -/
theorem eq_of_approx {T U : S.Hull}
    (h : ∀ ε > 0, ∀ R : ℝ, ∃ r, |r| < ε ∧ Agree R T (LengthSubst.translate r U)) : T = U := by
  apply Subtype.ext
  ext ⟨a, x⟩
  have hℓ := S.ℓ_pos a
  constructor
  · intro hp
    refine mem_of_approx U.2.1 fun ε hε => ?_
    obtain ⟨r, hr, hA⟩ := h (min ε 1) (lt_min hε one_pos) (|x| + 1)
    refine ⟨r, lt_of_lt_of_le hr (min_le_left _ _), ?_⟩
    have hW : (S.supp (a, x) ∩ Ioo (-(|x| + 1)) (|x| + 1)).Nonempty :=
      ⟨x, ⟨le_rfl, by dsimp only; linarith⟩, by
        constructor <;> linarith [neg_abs_le x, le_abs_self x]⟩
    exact (hA (a, x) hW).mp hp
  · intro hq
    refine mem_of_approx T.2.1 fun ε hε => ?_
    obtain ⟨r, hr, hA⟩ := h (min ε 1) (lt_min hε one_pos) (|x| + 2)
    have hr1 := lt_of_lt_of_le hr (min_le_right _ _)
    obtain ⟨hr1a, hr1b⟩ := abs_lt.mp hr1
    refine ⟨-r, by rw [abs_neg]; exact lt_of_lt_of_le hr (min_le_left _ _), ?_⟩
    have hW : (S.supp (a, x + -r) ∩ Ioo (-(|x| + 2)) (|x| + 2)).Nonempty :=
      ⟨x + -r, ⟨le_rfl, by dsimp only; linarith⟩, by
        constructor <;> linarith [neg_abs_le x, le_abs_self x]⟩
    have hmem : (a, x + -r) ∈ (LengthSubst.translate r U).1 := by
      change (a, x + -r + r) ∈ U.1
      simpa using hq
    exact (hA (a, x + -r) hW).mpr hmem

theorem mem_patch_self (T : LocalHull S) {ε : ℝ} (hε : 0 < ε) (n : ℕ) : T ∈ patch S T ε n :=
  ⟨0, by simpa using hε, by simpa using Agree.refl (n : ℝ) T.toHull⟩

/-- Meeting ordinary neighbourhoods give agreement up to arbitrarily small translations. -/
theorem approx_of_patches {T U : LocalHull S}
    (h : ∀ ε > 0, ∀ n : ℕ, (patch S T ε n ∩ patch S U ε n).Nonempty) :
    ∀ ε > 0, ∀ R : ℝ, ∃ r, |r| < ε ∧ Agree R T.toHull (LengthSubst.translate r U.toHull) := by
  intro ε hε R
  obtain ⟨n, hn⟩ := exists_nat_gt (R + 2)
  set ε' := min (ε / 2) 1
  have hε' : 0 < ε' := lt_min (by linarith) one_pos
  obtain ⟨V, ⟨t, ht, hT⟩, ⟨s, hs, hU⟩⟩ := h ε' hε' n
  have ht1 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 := lt_of_lt_of_le ht (min_le_right _ _)
  have hs1 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 := lt_of_lt_of_le hs (min_le_right _ _)
  have habs : |s - t| ≤ |s| + |t| := abs_sub _ _
  refine ⟨s - t, by linarith, ?_⟩
  -- carry `U`'s agreement through the translation by `s - t`
  have hU' : Agree (n - |s - t|) (LengthSubst.translate (s - t) U.toHull)
      (LengthSubst.translate (-t) V.toHull) := by
    have := agree_translate_of_agree (R := n - |s - t|) (s - t)
      (by simpa using hU)
    rw [LengthSubst.translate_translate, show s - t + -s = -t by ring] at this
    exact this
  have hT' : Agree (n - |s - t|) T.toHull (LengthSubst.translate (-t) V.toHull) :=
    agree_mono hT (by linarith [abs_nonneg (s - t)])
  exact agree_mono (hT'.trans hU'.symm) (by linarith)

/-- **The ordinary local hull is Hausdorff.** -/
instance : T2Space (LocalHull S) := by
  refine ⟨fun T U hne => ?_⟩
  by_contra hcon
  apply hne
  have hpatch : ∀ ε > 0, ∀ n : ℕ, (patch S T ε n ∩ patch S U ε n).Nonempty := by
    intro ε hε n
    by_contra hempty
    exact hcon ⟨_, _, isOpen_patch S T ε n, isOpen_patch S U ε n, mem_patch_self T hε n,
      mem_patch_self U hε n, Set.disjoint_iff_inter_eq_empty.mpr
        (Set.not_nonempty_iff_eq_empty.mp hempty)⟩
  exact LocalHull.ext (eq_of_approx (approx_of_patches hpatch))

end Psc.PeriodicPartnerLocalTopology
