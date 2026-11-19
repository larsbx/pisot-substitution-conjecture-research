/-
# The legal two-sided substitution tiling hull

This module constructs, for a substitution with a positive length eigenvector, the space of
legal two-sided tilings of the line by labelled half-open intervals.  It defines translation,
inflation, the endpoint and ray-agreement predicates, centred agreement, and an
exact-agreement metric on the hull.  It then proves, for this concrete instance, every local
contract consumed by `PeriodicPartnerDynamics`, `PeriodicPartnerCollapse`,
`PeriodicPartnerAsymptotic` and `PeriodicPartnerDichotomy`:

* `rightBranchLaws`: translation/inflation transport, endpoint uniqueness and the
  ray-to-endpoint rule;
* `agreementData`: restriction, one-step inflation of radius and the metric modulus;
* `window_of_ray` and `common_patch`: the ray-window and positive-common-tile facts;
* `rightAsymptotic_iff_translationRightAsymptotic`: on this metric, metric
  translation-asymptoticity and exact right-ray agreement coincide.

Conventions.  A tile `(a, x)` occupies `[x, x + ℓ a)`.  `shift t T` is `T - t`.  The tiles of a
patch are those meeting an **open** window, as in the companion note.  Legality: every patch
of a bounded window is a translate of a set of tiles of some level-`n` supertile.

The metric is the exact-agreement ultrametric `(1/2)^N`, where `N` is the first natural radius
of disagreement.  It dominates the usual translation-tolerant tiling metric but induces a finer
topology, in which translation is not continuous.  Compactness is neither claimed nor used.

Not constructed here: the geometric-realization map, and proofs of inflation injectivity
(recognizability), of the Barge--Diamond--Swanson periodicization theorem, of finite fibres
and of (R4).  `ExternalInputs` names these published inputs for this hull; the consumers at the
end of the module use them only through those named fields.

See `docs/c4-tiling-hull-realization-stop-go-2026-11-19.md` for the pre-code source decision.
-/
import PscVerif.PeriodicPartnerAsymptotic
import PscVerif.PeriodicPartnerDichotomy
import Mathlib.Topology.MetricSpace.PiNat

namespace Psc.PeriodicPartnerHull

open Function Filter Set Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerCollapse
  Psc.PeriodicPartnerAsymptotic
open scoped Topology

/-! ## Substitutions with a length eigenvector -/

/-- A substitution with nonempty images and positive tile lengths forming an eigenvector:
the image of `a` has total length `β * ℓ a`.  No Pisot or primitivity hypothesis is used by
the local contracts; they enter only through the named external inputs. -/
structure LengthSubst (α : Type*) where
  σ : α → List α
  ne_nil : ∀ a, σ a ≠ []
  ℓ : α → ℝ
  ℓ_pos : ∀ a, 0 < ℓ a
  β : ℝ
  eigen : ∀ a, ((σ a).map ℓ).sum = β * ℓ a

namespace LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-- The right endpoint map `g_R`: the last letter of each image. -/
def lastLetter (a : α) : α := (S.σ a).getLast (S.ne_nil a)

theorem sum_nonneg (w : List α) : 0 ≤ (w.map S.ℓ).sum :=
  List.sum_nonneg (by simpa using fun a _ => (S.ℓ_pos a).le)

theorem sum_pos {w : List α} (hw : w ≠ []) : 0 < (w.map S.ℓ).sum := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simpa using add_pos_of_pos_of_nonneg (S.ℓ_pos a) (S.sum_nonneg w)

theorem β_pos [Nonempty α] : 0 < S.β := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have h := S.sum_pos (S.ne_nil a)
  rw [S.eigen a] at h
  exact pos_of_mul_pos_left h (S.ℓ_pos a).le

/-! ## Tiles and their placement -/

/-- The half-open support `[x, x + ℓ a)` of the tile `(a, x)`. -/
def supp (p : α × ℝ) : Set ℝ := Ico p.2 (p.2 + S.ℓ p.1)

/-- Lay the word `w` out from `x`, left to right. -/
def place : List α → ℝ → List (α × ℝ)
  | [], _ => []
  | a :: w, x => (a, x) :: place w (x + S.ℓ a)

theorem place_mem_bounds {w : List α} {x : ℝ} {q : α × ℝ} (hq : q ∈ S.place w x) :
    x ≤ q.2 ∧ q.2 + S.ℓ q.1 ≤ x + (w.map S.ℓ).sum := by
  induction w generalizing x with
  | nil => simp [place] at hq
  | cons a w ih =>
    simp only [place, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simpa using S.sum_nonneg w
    · obtain ⟨h1, h2⟩ := ih hq
      refine ⟨by linarith [S.ℓ_pos a], ?_⟩
      simp only [List.map_cons, List.sum_cons]
      linarith

theorem supp_subset_of_mem_place {w : List α} {x : ℝ} {q : α × ℝ} (hq : q ∈ S.place w x) :
    S.supp q ⊆ Ico x (x + (w.map S.ℓ).sum) := by
  obtain ⟨h1, h2⟩ := S.place_mem_bounds hq
  intro z hz
  exact ⟨h1.trans hz.1, hz.2.trans_le h2⟩

theorem place_cover {w : List α} {x z : ℝ} (hz : z ∈ Ico x (x + (w.map S.ℓ).sum)) :
    ∃ q ∈ S.place w x, z ∈ S.supp q := by
  induction w generalizing x with
  | nil => simp at hz
  | cons a w ih =>
    by_cases hlt : z < x + S.ℓ a
    · exact ⟨(a, x), by simp [place], hz.1, hlt⟩
    · have hz' : z ∈ Ico (x + S.ℓ a) (x + S.ℓ a + (w.map S.ℓ).sum) := by
        refine ⟨not_lt.mp hlt, ?_⟩
        have := hz.2
        simp only [List.map_cons, List.sum_cons] at this
        linarith
      obtain ⟨q, hq, hzq⟩ := ih hz'
      exact ⟨q, by simp [place, hq], hzq⟩

theorem place_unique {w : List α} {x z : ℝ} {q q' : α × ℝ}
    (hq : q ∈ S.place w x) (hq' : q' ∈ S.place w x)
    (hz : z ∈ S.supp q) (hz' : z ∈ S.supp q') : q = q' := by
  induction w generalizing x with
  | nil => simp [place] at hq
  | cons a w ih =>
    simp only [place, List.mem_cons] at hq hq'
    rcases hq with rfl | hq <;> rcases hq' with rfl | hq'
    · rfl
    · have := (S.place_mem_bounds hq').1
      exact absurd (hz'.1.trans' this) (not_le.mpr hz.2)
    · have := (S.place_mem_bounds hq).1
      exact absurd (hz.1.trans' this) (not_le.mpr hz'.2)
    · exact ih hq hq'

theorem place_last {w : List α} (hw : w ≠ []) (x : ℝ) :
    (w.getLast hw, x + (w.map S.ℓ).sum - S.ℓ (w.getLast hw)) ∈ S.place w x := by
  induction w generalizing x with
  | nil => exact absurd rfl hw
  | cons a w ih =>
    cases w with
    | nil => simp [place]
    | cons b w =>
      have h := ih (List.cons_ne_nil b w) (x + S.ℓ a)
      rw [List.getLast_cons (List.cons_ne_nil b w)]
      refine List.mem_cons_of_mem _ ?_
      convert h using 3
      simp only [List.map_cons, List.sum_cons]
      ring

theorem place_add (w : List α) (x c : ℝ) :
    S.place w (x + c) = (S.place w x).map (fun q => (q.1, q.2 + c)) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    simp only [place, List.map_cons]
    rw [show x + c + S.ℓ a = (x + S.ℓ a) + c by ring, ih]

/-! ## Tile sets: translation, inflation, tilings and legality -/

/-- Translation in the convention `shift t T = T - t`. -/
def shift (t : ℝ) (T : Set (α × ℝ)) : Set (α × ℝ) := {q | (q.1, q.2 + t) ∈ T}

/-- Inflation: every tile is replaced by its image laid out on the `β`-scaled support. -/
def inflate (T : Set (α × ℝ)) : Set (α × ℝ) :=
  {q | ∃ p ∈ T, q ∈ S.place (S.σ p.1) (S.β * p.2)}

/-- The singleton supertile of level zero. -/
def supertile (a : α) (n : ℕ) : Set (α × ℝ) := S.inflate^[n] {(a, 0)}

/-- A tiling: every point of the line lies in exactly one tile. -/
def IsTiling (T : Set (α × ℝ)) : Prop := ∀ z : ℝ, ∃! p, p ∈ T ∧ z ∈ S.supp p

/-- Agreement of two tile sets on all tiles meeting the window `W`. -/
def AgreeOn (W : Set ℝ) (T U : Set (α × ℝ)) : Prop :=
  ∀ p : α × ℝ, (S.supp p ∩ W).Nonempty → (p ∈ T ↔ p ∈ U)

/-- Legality: every bounded patch is a translate of a set of tiles of one supertile. -/
def Legal (T : Set (α × ℝ)) : Prop :=
  ∀ R : ℝ, ∃ a n t, ∀ p ∈ T, (S.supp p ∩ Ioo (-R) R).Nonempty →
    (p.1, p.2 + t) ∈ S.supertile a n

theorem supp_shift (t : ℝ) (p : α × ℝ) :
    S.supp (p.1, p.2 + t) = (· + t) '' S.supp p := by
  ext z
  simp only [supp, mem_Ico, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨z - t, ⟨by linarith, by linarith⟩, by ring⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩

theorem mem_supp_shift {t z : ℝ} {p : α × ℝ} :
    z + t ∈ S.supp (p.1, p.2 + t) ↔ z ∈ S.supp p := by
  simp only [supp, mem_Ico]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem shift_zero (T : Set (α × ℝ)) : shift 0 T = T := by
  ext q
  simp [shift]

theorem shift_shift (s t : ℝ) (T : Set (α × ℝ)) : shift s (shift t T) = shift (s + t) T := by
  ext q
  change (q.1, q.2 + s + t) ∈ T ↔ (q.1, q.2 + (s + t)) ∈ T
  rw [add_assoc]

theorem shift_injective (t : ℝ) : Injective (shift (α := α) t) := by
  intro T U h
  have := congrArg (shift (-t)) h
  simpa only [shift_shift, neg_add_cancel, shift_zero] using this

/-- A placed tile lies in the `β`-scaled support of its parent. -/
theorem mem_supp_parent [Nonempty α] {p q : α × ℝ} {z : ℝ}
    (hq : q ∈ S.place (S.σ p.1) (S.β * p.2)) (hz : z ∈ S.supp q) :
    z / S.β ∈ S.supp p := by
  have hβ := S.β_pos
  have h := S.supp_subset_of_mem_place hq hz
  rw [S.eigen] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [le_div_iff₀ hβ]; linarith
  · rw [div_lt_iff₀ hβ]; linarith

theorem inflate_shift (t : ℝ) (T : Set (α × ℝ)) :
    S.inflate (shift t T) = shift (S.β * t) (S.inflate T) := by
  ext q
  simp only [inflate, shift]
  constructor
  · rintro ⟨p, hp, hq⟩
    refine ⟨(p.1, p.2 + t), hp, ?_⟩
    rw [mul_add, S.place_add, List.mem_map]
    exact ⟨q, hq, rfl⟩
  · rintro ⟨p, hp, hq⟩
    refine ⟨(p.1, p.2 - t), by simpa using hp, ?_⟩
    have hp' : S.β * p.2 = S.β * (p.2 - t) + S.β * t := by ring
    rw [hp', S.place_add, List.mem_map] at hq
    obtain ⟨q', hq', heq⟩ := hq
    have : q = q' := by
      rcases q with ⟨a, x⟩
      rcases q' with ⟨b, y⟩
      simp only [Prod.mk.injEq] at heq ⊢
      exact ⟨heq.1.symm, by linarith [heq.2]⟩
    exact this ▸ hq'

theorem isTiling_shift {T : Set (α × ℝ)} (hT : S.IsTiling T) (t : ℝ) :
    S.IsTiling (shift t T) := by
  intro z
  obtain ⟨p, ⟨hp, hz⟩, huniq⟩ := hT (z + t)
  refine ⟨(p.1, p.2 - t), ⟨by simpa [shift] using hp, ?_⟩, ?_⟩
  · rw [← S.mem_supp_shift (t := t)]
    simpa using hz
  · rintro q ⟨hq, hzq⟩
    have := huniq (q.1, q.2 + t) ⟨hq, S.mem_supp_shift.mpr hzq⟩
    subst this
    simp

/-- Inflation turns a unique tile at `z / β` into a unique tile at `z`. -/
theorem unique_inflate [Nonempty α] {T : Set (α × ℝ)} {z : ℝ}
    (h : ∃! p, p ∈ T ∧ z / S.β ∈ S.supp p) : ∃! q, q ∈ S.inflate T ∧ z ∈ S.supp q := by
  have hβ := S.β_pos
  obtain ⟨p, ⟨hp, hz⟩, huniq⟩ := h
  have hz' : z ∈ Ico (S.β * p.2) (S.β * p.2 + ((S.σ p.1).map S.ℓ).sum) := by
    rw [S.eigen]
    obtain ⟨h1, h2⟩ := hz
    constructor
    · rw [le_div_iff₀ hβ] at h1; linarith
    · rw [div_lt_iff₀ hβ] at h2; linarith
  obtain ⟨q, hq, hzq⟩ := S.place_cover hz'
  refine ⟨q, ⟨⟨p, hp, hq⟩, hzq⟩, ?_⟩
  rintro q' ⟨⟨p', hp', hq'⟩, hzq'⟩
  have hpp : p' = p := huniq p' ⟨hp', S.mem_supp_parent hq' hzq'⟩
  subst hpp
  exact S.place_unique hq' hq hzq' hzq

theorem isTiling_inflate [Nonempty α] {T : Set (α × ℝ)} (hT : S.IsTiling T) :
    S.IsTiling (S.inflate T) := fun z => S.unique_inflate (hT (z / S.β))

theorem legal_shift {T : Set (α × ℝ)} (hT : S.Legal T) (t : ℝ) : S.Legal (shift t T) := by
  intro R
  obtain ⟨a, n, s, h⟩ := hT (R + |t|)
  refine ⟨a, n, t + s, fun p hp hW => ?_⟩
  obtain ⟨z, hz, hzW⟩ := hW
  have := h (p.1, p.2 + t) hp ⟨z + t, S.mem_supp_shift.mpr hz, ?_⟩
  · simpa [add_assoc] using this
  · obtain ⟨h1, h2⟩ := hzW
    constructor <;> cases abs_cases t <;> linarith

theorem legal_inflate [Nonempty α] {T : Set (α × ℝ)} (hT : S.Legal T) :
    S.Legal (S.inflate T) := by
  have hβ := S.β_pos
  intro R
  obtain ⟨a, n, t, h⟩ := hT (R / S.β)
  refine ⟨a, n + 1, S.β * t, ?_⟩
  rintro q ⟨p, hp, hq⟩ ⟨z, hz, hzW⟩
  have hpW : (S.supp p ∩ Ioo (-(R / S.β)) (R / S.β)).Nonempty := by
    refine ⟨z / S.β, S.mem_supp_parent hq hz, ?_⟩
    obtain ⟨h1, h2⟩ := hzW
    constructor
    · rw [neg_div', div_lt_div_iff_of_pos_right hβ]; linarith
    · exact div_lt_div_of_pos_right h2 hβ
  have hparent := h p hp hpW
  rw [supertile, iterate_succ_apply']
  refine ⟨(p.1, p.2 + t), hparent, ?_⟩
  rw [mul_add, S.place_add, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-! ## The hull -/

/-- The legal two-sided hull: legal tilings of the line. -/
def Hull : Type _ := {T : Set (α × ℝ) // S.IsTiling T ∧ S.Legal T}

variable {S}

/-- Translation on the hull, `translate t T = T - t`. -/
def translate (t : ℝ) (T : S.Hull) : S.Hull :=
  ⟨shift t T.1, S.isTiling_shift T.2.1 t, S.legal_shift T.2.2 t⟩

/-- Inflation on the hull. -/
def inflateH [Nonempty α] (T : S.Hull) : S.Hull :=
  ⟨S.inflate T.1, S.isTiling_inflate T.2.1, S.legal_inflate T.2.2⟩

theorem translate_injective (t : ℝ) : Injective (translate (S := S) t) := by
  intro T U h
  exact Subtype.ext (shift_injective t (congrArg Subtype.val h))

theorem translate_translate (s t : ℝ) (T : S.Hull) :
    translate s (translate t T) = translate (s + t) T :=
  Subtype.ext (shift_shift s t T.1)

theorem inflateH_translate [Nonempty α] (t : ℝ) (T : S.Hull) :
    inflateH (translate t T) = translate (S.β * t) (inflateH T) :=
  Subtype.ext (S.inflate_shift t T.1)

/-- Exact agreement on the open right ray `(y, ∞)`. -/
def AgreeRight (T U : S.Hull) (y : ℝ) : Prop := S.AgreeOn (Ioi y) T.1 U.1

/-- The tile labelled `b` ends at `y`. -/
def EndsAt (T : S.Hull) (y : ℝ) (b : α) : Prop := (b, y - S.ℓ b) ∈ T.1

/-- Exact agreement on the open centred window `(-R, R)`. -/
def Agree (R : ℝ) (T U : S.Hull) : Prop := S.AgreeOn (Ioo (-R) R) T.1 U.1


/-! ## Local laws of agreement and endpoints -/

theorem supp_inter_Ioi {p : α × ℝ} {r : ℝ} (h : r < p.2 + S.ℓ p.1) :
    (S.supp p ∩ Ioi r).Nonempty := by
  have hℓ := S.ℓ_pos p.1
  refine ⟨max ((r + (p.2 + S.ℓ p.1)) / 2) p.2, ⟨le_max_right _ _, ?_⟩, ?_⟩
  · exact max_lt (by linarith) (by linarith)
  · exact lt_of_lt_of_le (show r < (r + (p.2 + S.ℓ p.1)) / 2 by linarith) (le_max_left _ _)

theorem AgreeOn.mono {W W' : Set ℝ} {T U : Set (α × ℝ)} (h : S.AgreeOn W T U)
    (hW : W' ⊆ W) : S.AgreeOn W' T U := fun p ⟨z, hz, hzW⟩ => h p ⟨z, hz, hW hzW⟩

theorem AgreeOn.shift {W W' : Set ℝ} {T U : Set (α × ℝ)} {t : ℝ} (h : S.AgreeOn W T U)
    (hW : ∀ z ∈ W', z + t ∈ W) : S.AgreeOn W' (shift t T) (shift t U) :=
  fun p ⟨z, hz, hzW⟩ => h (p.1, p.2 + t) ⟨z + t, S.mem_supp_shift.mpr hz, hW z hzW⟩

theorem AgreeOn.inflate [Nonempty α] {W W' : Set ℝ} {T U : Set (α × ℝ)}
    (h : S.AgreeOn W T U) (hW : ∀ z ∈ W', z / S.β ∈ W) :
    S.AgreeOn W' (S.inflate T) (S.inflate U) := by
  have key : ∀ {T U : Set (α × ℝ)}, S.AgreeOn W T U → ∀ q : α × ℝ,
      (S.supp q ∩ W').Nonempty → q ∈ S.inflate T → q ∈ S.inflate U := by
    rintro T U h q ⟨z, hz, hzW⟩ ⟨p, hp, hq⟩
    exact ⟨p, (h p ⟨z / S.β, S.mem_supp_parent hq hz, hW z hzW⟩).mp hp, hq⟩
  have hsymm : S.AgreeOn W U T := fun p hp => (h p hp).symm
  exact fun q hq => ⟨key h q hq, key hsymm q hq⟩

/-- An endpoint tile `(b, y - ℓ b)` contains every point just left of `y`. -/
theorem mem_supp_endpoint {y z : ℝ} {b : α} (h1 : y - S.ℓ b ≤ z) (h2 : z < y) :
    z ∈ S.supp (b, y - S.ℓ b) := ⟨h1, by simpa using h2⟩

theorem endsAt_unique {T : S.Hull} {y : ℝ} {b c : α}
    (hb : EndsAt T y b) (hc : EndsAt T y c) : b = c := by
  have hm := lt_min (S.ℓ_pos b) (S.ℓ_pos c)
  have hz := fun d (hd : min (S.ℓ b) (S.ℓ c) ≤ S.ℓ d) =>
    S.mem_supp_endpoint (b := d) (y := y) (z := y - min (S.ℓ b) (S.ℓ c))
      (by linarith) (by linarith)
  have := (T.2.1 (y - min (S.ℓ b) (S.ℓ c))).unique
    ⟨hb, hz b (min_le_left _ _)⟩ ⟨hc, hz c (min_le_right _ _)⟩
  exact congrArg Prod.fst this

theorem agree_endpoint {T U : S.Hull} {r y : ℝ} {b c : α} (h : AgreeRight T U r)
    (hr : r < y) (hb : EndsAt T y b) (hc : EndsAt U y c) : b = c := by
  have hb' : EndsAt U y b :=
    (h _ (S.supp_inter_Ioi (by simpa using hr))).mp hb
  exact endsAt_unique hb' hc

/-- The right branch contract of `PeriodicPartnerDynamics`, proved for the hull. -/
theorem rightBranchLaws [Nonempty α] :
    RightBranchLaws (inflateH (S := S)) translate S.β S.lastLetter AgreeRight EndsAt where
  translate_zero T := Subtype.ext (shift_zero T.1)
  endpoint_unique := endsAt_unique
  agree_endpoint := agree_endpoint
  agree_translate t h := h.shift (by intro z hz; simp only [mem_Ioi] at hz ⊢; linarith)
  endpoint_translate {T y b} t h := by
    have h' : (b, y - S.ℓ b) ∈ T.1 := h
    change (b, y - t - S.ℓ b + t) ∈ T.1
    convert h' using 2
    ring
  agree_inflate {T U y} h := by
    have hβ := S.β_pos
    refine AgreeOn.inflate h ?_
    intro z hz
    simp only [mem_Ioi] at hz ⊢
    rw [lt_div_iff₀ hβ]
    linarith
  endpoint_inflate {T y b} h := by
    refine ⟨(b, y - S.ℓ b), h, ?_⟩
    have := S.place_last (S.ne_nil b) (S.β * (y - S.ℓ b))
    rw [S.eigen] at this
    unfold lastLetter
    convert this using 2
    ring

/-! ## The exact-agreement metric -/

/-- The patch of tiles meeting `(-n, n)`. -/
def window (T : S.Hull) (n : ℕ) : Set (α × ℝ) :=
  {p | p ∈ T.1 ∧ (S.supp p ∩ Ioo (-(n : ℝ)) n).Nonempty}

theorem agree_iff_window {T U : S.Hull} {n : ℕ} :
    Agree (n : ℝ) T U ↔ window T n = window U n := by
  constructor
  · intro h
    ext p
    exact ⟨fun hp => ⟨(h p hp.2).mp hp.1, hp.2⟩, fun hp => ⟨(h p hp.2).mpr hp.1, hp.2⟩⟩
  · intro h p hp
    have := congrArg (p ∈ ·) h
    simp only [window, eq_iff_iff] at this
    exact ⟨fun hT => (this.mp ⟨hT, hp⟩).1, fun hU => (this.mpr ⟨hU, hp⟩).1⟩

theorem window_injective : Injective (window (S := S)) := by
  intro T U h
  apply Subtype.ext
  ext p
  obtain ⟨n, hn⟩ := exists_nat_gt |p.2|
  have hp : (S.supp p ∩ Ioo (-(n : ℝ)) n).Nonempty :=
    ⟨p.2, ⟨le_rfl, by simpa using S.ℓ_pos p.1⟩, by
      constructor <;> cases abs_cases p.2 <;> linarith⟩
  exact agree_iff_window.mpr (congrFun h n) p hp

attribute [local instance] PiNat.dist

/-- The exact-agreement ultrametric: `(1/2)^N` for the first disagreeing natural radius. -/
noncomputable instance : MetricSpace S.Hull where
  dist T U := dist (window T) (window U)
  dist_self T := PiNat.dist_self _
  dist_comm T U := PiNat.dist_comm _ _
  dist_triangle T U V := PiNat.dist_triangle _ _ _
  eq_of_dist_eq_zero h := window_injective (PiNat.eq_of_dist_eq_zero _ _ h)

theorem hull_dist_def (T U : S.Hull) : dist T U = dist (window T) (window U) := rfl

theorem agree_mono {r R : ℝ} {T U : S.Hull} (h : Agree R T U) (hr : r ≤ R) : Agree r T U :=
  AgreeOn.mono h (Ioo_subset_Ioo (by linarith) hr)

theorem dist_le_of_agree {T U : S.Hull} {n : ℕ} (h : Agree (n : ℝ) T U) :
    dist T U ≤ (1 / 2) ^ n := by
  rw [hull_dist_def, ← PiNat.mem_cylinder_iff_dist_le, PiNat.mem_cylinder_iff]
  intro i hi
  exact agree_iff_window.mp (agree_mono h (by exact_mod_cast hi.le))

theorem agree_of_dist_lt {T U : S.Hull} {n : ℕ} (h : dist T U < (1 / 2) ^ n) :
    Agree (n : ℝ) T U :=
  agree_iff_window.mpr (PiNat.apply_eq_of_dist_lt h le_rfl)

/-- The agreement contract of `PeriodicPartnerCollapse`, proved for the hull. -/
def agreementData [Nonempty α] : AgreementData S.Hull inflateH S.β where
  Agree := Agree
  restrict _ hrR h := agree_mono h hrR
  inflate {R T U} _ h := by
    have hβ := S.β_pos
    refine AgreeOn.inflate h ?_
    rintro z ⟨h1, h2⟩
    constructor
    · rw [lt_div_iff₀ hβ]; linarith
    · rw [div_lt_iff₀ hβ]; linarith
  controls_dist ε hε := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n + 1, by positivity, fun T U h => ?_⟩
    exact (dist_le_of_agree (agree_mono h (by linarith))).trans_lt hn

/-- A right ray beginning at or before `-R` covers the centred window of radius `R`. -/
theorem window_of_ray {R r : ℝ} {T U : S.Hull} (_hR : 0 < R) (hr : r ≤ -R)
    (h : AgreeRight T U r) : Agree R T U :=
  AgreeOn.mono h (fun _ hz => lt_of_le_of_lt hr hz.1)

/-- A common right ray at the origin and a common origin endpoint label `a` give a common
centred patch of the full radius `ℓ a`. -/
theorem common_patch {T U : S.Hull} {a : α} (hray : AgreeRight T U 0)
    (hT : EndsAt T 0 a) (hU : EndsAt U 0 a) : Agree (S.ℓ a) T U := by
  intro p ⟨z, hz, hzW⟩
  by_cases hright : (S.supp p ∩ Ioi 0).Nonempty
  · exact hray p hright
  have hend : p.2 + S.ℓ p.1 ≤ 0 :=
    not_lt.mp fun h => hright (S.supp_inter_Ioi h)
  have hz0 : z < 0 := lt_of_lt_of_le hz.2 hend
  have hza : z ∈ S.supp (a, 0 - S.ℓ a) :=
    S.mem_supp_endpoint (by linarith [hzW.1]) hz0
  have side : ∀ V : S.Hull, EndsAt V 0 a → (p ∈ V.1 ↔ p = (a, 0 - S.ℓ a)) := by
    intro V hV
    exact ⟨fun hp => (V.2.1 z).unique ⟨hp, hz⟩ ⟨hV, hza⟩, fun h => h ▸ hV⟩
  rw [side T hT, side U hU]

/-! ## Exact right rays and metric translation-asymptoticity coincide -/

theorem rightAsymptotic_iff_translationRightAsymptotic [Nonempty α] {T U : S.Hull} :
    RightAsymptotic AgreeRight T U ↔ TranslationRightAsymptotic translate T U := by
  constructor
  · exact translationRightAsymptotic_of_rightAsymptotic agreementData
      (rightBranchLaws (S := S)).agree_translate window_of_ray
  · intro h
    obtain ⟨t₀, ht₀⟩ := Metric.tendsto_atTop.mp h ((1 / 2) ^ 1) (by norm_num)
    refine ⟨t₀, fun p ⟨z, hz, hzt⟩ => ?_⟩
    have hd : dist (translate z T) (translate z U) < (1 / 2) ^ 1 := by
      have := ht₀ z (le_of_lt hzt)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at this
    have h0 : (0 : ℝ) ∈ S.supp (p.1, p.2 - z) := by
      have := S.mem_supp_shift (t := z) (z := 0) (p := (p.1, p.2 - z))
      simp only [zero_add, sub_add_cancel] at this
      exact this.mp hz
    have hagree := agree_of_dist_lt hd (p.1, p.2 - z) ⟨0, h0, by norm_num⟩
    change (p.1, p.2 - z + z) ∈ T.1 ↔ (p.1, p.2 - z + z) ∈ U.1 at hagree
    simpa using hagree

/-- On this hull the metric and exact-ray forms of the BDS input are the same statement. -/
theorem bds_ray_iff_metric [Nonempty α] :
    BDSPeriodicization (inflateH (S := S)) translate (RightAsymptotic AgreeRight) ↔
      BDSPeriodicization (inflateH (S := S)) translate (TranslationRightAsymptotic translate) := by
  constructor
  · intro h T U hne hasym
    exact h hne (rightAsymptotic_iff_translationRightAsymptotic.mpr hasym)
  · intro h T U hne hasym
    exact h hne (rightAsymptotic_iff_translationRightAsymptotic.mp hasym)


/-! ## Unconditional consequences on the hull -/

/-- Lemma M on the actual hull, with every local input discharged: a common right ray at the
origin and endpoint labels merging after `m` substitutions force collapse of the unshifted
inflations.  No external theorem enters. -/
theorem distance_tendsto_zero_of_endpoint_merge [Nonempty α] (hβ : 1 < S.β)
    {T U : S.Hull} {a b : α} (hray : AgreeRight T U 0) (hT : EndsAt T 0 a)
    (hU : EndsAt U 0 b) (m : ℕ) (hmerge : S.lastLetter^[m] a = S.lastLetter^[m] b) :
    Tendsto (fun n : ℕ => dist (inflateH^[n] T) (inflateH^[n] U)) atTop (𝓝 0) :=
  (Psc.PeriodicPartnerDichotomy.endpointDataOfBranch rightBranchLaws agreementData S.ℓ
    S.ℓ_pos common_patch).distance_tendsto_zero_of_endpoint_merge hβ hray hT hU m hmerge

/-- Distinct periodic tilings sharing a right ray at a common origin endpoint never have
merging endpoint labels.  No external theorem enters. -/
theorem endpoint_persistent_of_periodic [Nonempty α] (hβ : 1 < S.β)
    {T U : S.Hull} {a b : α} (hray : AgreeRight T U 0) (hT : EndsAt T 0 a)
    (hU : EndsAt U 0 b) (hne : T ≠ U) (hpT : T ∈ periodicPts inflateH)
    (hpU : U ∈ periodicPts inflateH) : ∀ m : ℕ, S.lastLetter^[m] a ≠ S.lastLetter^[m] b :=
  (Psc.PeriodicPartnerDichotomy.endpointDataOfBranch rightBranchLaws agreementData S.ℓ
    S.ℓ_pos common_patch).endpoint_persistent_of_periodic hβ hray hT hU hne hpT hpU

end LengthSubst

/-! ## Published inputs for this hull -/

open LengthSubst

/-- The published theorems that the periodic-partner consumers import, stated for this
concrete hull.  None is proved here and none is a Lean axiom; each is a field to be supplied.

* `inflate_injective`: recognizability (Mossé 1992; Solomyak 1998);
* `bds`: Barge--Diamond--Swanson asymptotic periodicization, in metric form; on this hull it
  is equivalent to the exact-ray form (`bds_ray_iff_metric`);
* `realize`, `A`, `semiconj`, `finite_fibres`: the Baker--Barge--Kwapisz geometric
  realization and its finite fibres.  The realization map is **not constructed** here;
* `q₀`, `q₀_fixed`, `r4`: the distinguished fibre and the origin/fibre input (R4). -/
structure PublishedInputs {α : Type*} [Nonempty α] (S : LengthSubst α) (Y : Type*) where
  inflate_injective : Injective (inflateH (S := S))
  bds : BDSPeriodicization (inflateH (S := S)) translate (TranslationRightAsymptotic translate)
  A : Y → Y
  realize : S.Hull → Y
  semiconj : Semiconj realize inflateH A
  finite_fibres : ∀ q, {T | realize T = q}.Finite
  q₀ : Y
  q₀_fixed : A q₀ = q₀
  r4 : R4ZeroFibre inflateH realize q₀ EndsAt

section Ternary

variable {S : LengthSubst (Fin 3)} {Y : Type*}

/-- On the actual hull, branch-origin endpoint merging after two steps is exactly metric
collapse.  The only external input is BDS periodicization. -/
theorem hull_endpoint_merge_iff_collapse (hβ : 1 < S.β)
    (hBDS : BDSPeriodicization (inflateH (S := S)) translate
      (TranslationRightAsymptotic translate))
    {T U : S.Hull} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt T U 0 b c) :
    S.lastLetter^[2] b = S.lastLetter^[2] c ↔
      Tendsto (fun n : ℕ => dist (inflateH^[n] T) (inflateH^[n] U)) atTop (𝓝 0) :=
  Psc.PeriodicPartnerDichotomy.ternary_endpoint_merge_iff_collapse rightBranchLaws hβ
    (bds_ray_iff_metric.mpr hBDS) agreementData S.ℓ S.ℓ_pos common_patch hbranch

/-- On the actual hull, the two-step endpoint test is exactly common periodicity of the
branch-normalized pair.  The only external input is BDS periodicization. -/
theorem hull_two_step_iff_pairPeriodic (hβ : 1 < S.β)
    (hBDS : BDSPeriodicization (inflateH (S := S)) translate
      (TranslationRightAsymptotic translate))
    {T U : S.Hull} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt T U 0 b c) :
    S.lastLetter^[2] b ≠ S.lastLetter^[2] c ↔ PairPeriodic inflateH T U :=
  ternary_two_step_iff_pairPeriodic_of_metric_BDS rightBranchLaws hβ agreementData
    window_of_ray hBDS hbranch

/-- Lemma E on the actual hull, with every local input discharged. -/
theorem hull_two_step_iff_zero_fibre (hβ : 1 < S.β) (P : PublishedInputs S Y)
    {T U : S.Hull} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt T U 0 b c) :
    S.lastLetter^[2] b ≠ S.lastLetter^[2] c ↔ P.realize T = P.q₀ ∧ P.realize U = P.q₀ :=
  ternary_two_step_iff_zero_fibre_of_metric_BDS rightBranchLaws hβ agreementData
    window_of_ray P.bds P.A P.realize P.q₀ P.inflate_injective P.semiconj
    (P.finite_fibres P.q₀) P.q₀_fixed P.r4 hbranch

/-- The branch-origin triple dichotomy on the actual hull.  Every local contract is
discharged; only the fields of `PublishedInputs` remain. -/
theorem hull_branch_triple_dichotomy (hβ : 1 < S.β) (P : PublishedInputs S Y)
    {T₀ T U : S.Hull} {b c : Fin 3} (hbranch : BranchAt AgreeRight EndsAt T U 0 b c)
    (hT₀T : P.realize T₀ = P.realize T) (hT₀U : P.realize T₀ = P.realize U) :
    (S.lastLetter^[2] b ≠ S.lastLetter^[2] c ∧ P.realize T₀ = P.q₀ ∧ P.realize T = P.q₀ ∧
      P.realize U = P.q₀ ∧
      ∃ n > 0, inflateH^[n] T₀ = T₀ ∧ inflateH^[n] T = T ∧ inflateH^[n] U = U) ∨
    (S.lastLetter^[2] b = S.lastLetter^[2] c ∧ P.realize T₀ ≠ P.q₀ ∧ P.realize T ≠ P.q₀ ∧
      P.realize U ≠ P.q₀ ∧ ¬ PairPeriodic inflateH T U ∧
      Tendsto (fun n : ℕ => dist (inflateH^[n] T) (inflateH^[n] U)) atTop (𝓝 0)) :=
  Psc.PeriodicPartnerDichotomy.ternary_branch_triple_dichotomy rightBranchLaws hβ
    (bds_ray_iff_metric.mpr P.bds) agreementData S.ℓ S.ℓ_pos common_patch P.A P.realize
    P.q₀ P.inflate_injective P.semiconj (P.finite_fibres P.q₀) P.q₀_fixed P.r4 hbranch
    hT₀T hT₀U

end Ternary

/-! ## Nonemptiness from a growing legal seed -/

namespace LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-- `P` tiles exactly the set `I`. -/
def TilesOn (I : Set ℝ) (P : Set (α × ℝ)) : Prop :=
  (∀ p ∈ P, S.supp p ⊆ I) ∧ ∀ z ∈ I, ∃! p, p ∈ P ∧ z ∈ S.supp p

theorem inflate_mono {P Q : Set (α × ℝ)} (h : P ⊆ Q) : S.inflate P ⊆ S.inflate Q :=
  fun _ ⟨p, hp, hq⟩ => ⟨p, h hp, hq⟩

theorem inflate_iterate_mono {P Q : Set (α × ℝ)} (h : P ⊆ Q) (n : ℕ) :
    S.inflate^[n] P ⊆ S.inflate^[n] Q := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iterate_succ_apply'] using S.inflate_mono ih

theorem inflate_iterate_shift (t : ℝ) (P : Set (α × ℝ)) (n : ℕ) :
    S.inflate^[n] (shift t P) = shift (S.β ^ n * t) (S.inflate^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, S.inflate_shift, pow_succ', mul_assoc]

theorem tilesOn_inflate [Nonempty α] {x y : ℝ} {P : Set (α × ℝ)}
    (h : S.TilesOn (Ico x y) P) : S.TilesOn (Ico (S.β * x) (S.β * y)) (S.inflate P) := by
  have hβ := S.β_pos
  have hdiv : ∀ z, z ∈ Ico (S.β * x) (S.β * y) ↔ z / S.β ∈ Ico x y := by
    intro z
    simp only [mem_Ico, le_div_iff₀ hβ, div_lt_iff₀ hβ, mul_comm x, mul_comm y]
  refine ⟨fun q ⟨p, hp, hq⟩ z hz => (hdiv z).mpr (h.1 p hp (S.mem_supp_parent hq hz)),
    fun z hz => S.unique_inflate (h.2 _ ((hdiv z).mp hz))⟩

theorem tilesOn_inflate_iterate [Nonempty α] {x y : ℝ} {P : Set (α × ℝ)}
    (h : S.TilesOn (Ico x y) P) (n : ℕ) :
    S.TilesOn (Ico (S.β ^ n * x) (S.β ^ n * y)) (S.inflate^[n] P) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iterate_succ_apply', pow_succ', mul_assoc] using S.tilesOn_inflate ih

/-- A seed tiling an interval around the origin, contained in its own `k`-fold inflation and
legal as a whole, generates a legal two-sided tiling: the hull is nonempty. -/
theorem hull_nonempty_of_seed [Nonempty α] (hβ : 1 < S.β) {k : ℕ} (hk : 0 < k)
    {P : Set (α × ℝ)} {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (htiles : S.TilesOn (Ico x y) P) (hgrow : P ⊆ S.inflate^[k] P)
    (hlegal : ∃ c m t, P ⊆ shift t (S.supertile c m)) : Nonempty S.Hull := by
  set F : ℕ → Set (α × ℝ) := fun n => S.inflate^[k * n] P with hF
  have hmono : Monotone F := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [hF, Nat.mul_succ, iterate_add_apply]
    exact S.inflate_iterate_mono hgrow (k * n)
  have htile : ∀ n, S.TilesOn (Ico (S.β ^ (k * n) * x) (S.β ^ (k * n) * y)) (F n) :=
    fun n => S.tilesOn_inflate_iterate htiles (k * n)
  -- the tiled intervals exhaust the line
  have hexhaust : ∀ R : ℝ, ∃ n, Icc (-R) R ⊆ Ico (S.β ^ (k * n) * x) (S.β ^ (k * n) * y) := by
    intro R
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max (R / -x) (R / y) + 1) hβ
    refine ⟨N, fun z ⟨h1, h2⟩ => ?_⟩
    have hpow : S.β ^ N ≤ S.β ^ (k * N) :=
      pow_le_pow_right₀ hβ.le (Nat.le_mul_of_pos_left N hk)
    have h1' : R / -x < S.β ^ (k * N) := by linarith [le_max_left (R / -x) (R / y)]
    have h2' : R / y < S.β ^ (k * N) := by linarith [le_max_right (R / -x) (R / y)]
    rw [div_lt_iff₀ (by linarith)] at h1'
    rw [div_lt_iff₀ hy] at h2'
    constructor <;> nlinarith
  let T : Set (α × ℝ) := ⋃ n, F n
  have huniq : ∀ {z p q}, p ∈ T → q ∈ T → z ∈ S.supp p → z ∈ S.supp q → p = q := by
    intro z p q hp hq hzp hzq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    have hpi := hmono (le_max_left i j) hi
    have hqj := hmono (le_max_right i j) hj
    exact ((htile _).2 z ((htile _).1 p hpi hzp)).unique ⟨hpi, hzp⟩ ⟨hqj, hzq⟩
  have hcover : ∀ {R : ℝ} {n : ℕ}, Icc (-R) R ⊆ Ico (S.β ^ (k * n) * x) (S.β ^ (k * n) * y) →
      ∀ p ∈ T, ∀ z ∈ S.supp p, z ∈ Icc (-R) R → p ∈ F n := by
    intro R n hn p hp z hz hzR
    obtain ⟨q, ⟨hq, hzq⟩, _⟩ := (htile n).2 z (hn hzR)
    exact (huniq hp (mem_iUnion.mpr ⟨n, hq⟩) hz hzq) ▸ hq
  have hT : S.IsTiling T := by
    intro z
    obtain ⟨n, hn⟩ := hexhaust |z|
    have hz : z ∈ Icc (-|z|) |z| := ⟨neg_abs_le z, le_abs_self z⟩
    obtain ⟨q, ⟨hq, hzq⟩, _⟩ := (htile n).2 z (hn hz)
    exact ⟨q, ⟨mem_iUnion.mpr ⟨n, hq⟩, hzq⟩, fun p hp => huniq hp.1 (mem_iUnion.mpr ⟨n, hq⟩) hp.2 hzq⟩
  have hL : S.Legal T := by
    obtain ⟨c, m, t, hPt⟩ := hlegal
    intro R
    obtain ⟨n, hn⟩ := hexhaust R
    refine ⟨c, m + k * n, S.β ^ (k * n) * t, fun p hp ⟨z, hz, hzW⟩ => ?_⟩
    have hpn := hcover hn p hp z hz ⟨hzW.1.le, hzW.2.le⟩
    have hsub := S.inflate_iterate_mono hPt (k * n)
    rw [S.inflate_iterate_shift, supertile, ← iterate_add_apply, add_comm] at hsub
    exact hsub hpn
  exact ⟨⟨T, hT, hL⟩⟩

end LengthSubst

/-! ## Control: the Thue--Morse hull is nonempty -/

/-- Thue--Morse, `0 ↦ 01`, `1 ↦ 10`, with unit tiles and `β = 2`.  An aperiodic primitive
substitution, used only to show that the construction is not vacuous.  It is not an
irreducible Pisot substitution and realizes no periodic-partner configuration. -/
def thueMorse : LengthSubst (Fin 2) where
  σ := ![[0, 1], [1, 0]]
  ne_nil a := by fin_cases a <;> simp
  ℓ _ := 1
  ℓ_pos _ := one_pos
  β := 2
  eigen a := by fin_cases a <;> norm_num

/-- The seed `1.0`: the tile `1` on `[-1, 0)` and the tile `0` on `[0, 1)`. -/
def thueMorseSeed : Set (Fin 2 × ℝ) := {(1, -1), (0, 0)}

/-- Membership of one placed tile in the inflation of a set, by an explicit parent. -/
theorem thueMorse_mem_inflate {P : Set (Fin 2 × ℝ)} {p q : Fin 2 × ℝ} (hp : p ∈ P)
    (hq : q ∈ thueMorse.place (thueMorse.σ p.1) (2 * p.2)) : q ∈ thueMorse.inflate P :=
  ⟨p, hp, hq⟩

theorem thueMorse_hull_nonempty : Nonempty thueMorse.Hull := by
  have hσ0 : thueMorse.σ 0 = [0, 1] := rfl
  have hσ1 : thueMorse.σ 1 = [1, 0] := rfl
  have hℓ : ∀ a, thueMorse.ℓ a = 1 := fun _ => rfl
  have hplace : ∀ (a b : Fin 2) (x : ℝ), thueMorse.place [a, b] x = [(a, x), (b, x + 1)] := by
    intro a b x
    simp [LengthSubst.place, hℓ]
  refine thueMorse.hull_nonempty_of_seed (by norm_num [thueMorse]) (k := 2) (by norm_num)
    (P := thueMorseSeed) (x := -1) (y := 1) (by norm_num) (by norm_num) ?_ ?_ ?_
  · refine ⟨?_, fun z hz => ?_⟩
    · rintro p (rfl | rfl) z ⟨h1, h2⟩ <;> simp only [hℓ] at h1 h2 <;>
        exact ⟨by linarith, by linarith⟩
    · by_cases hneg : z < 0
      · refine ⟨(1, -1), ⟨Or.inl rfl, ⟨hz.1, by simp [hℓ, hneg]⟩⟩, ?_⟩
        rintro p ⟨hp | hp, hzp⟩
        · exact hp
        · subst hp; exact absurd hzp.1 (by simpa using hneg)
      · refine ⟨(0, 0), ⟨Or.inr rfl, ⟨not_lt.mp hneg, by simpa [hℓ] using hz.2⟩⟩, ?_⟩
        rintro p ⟨hp | hp, hzp⟩
        · subst hp; exact absurd hzp.2 (by simpa [hℓ] using hneg)
        · exact hp
  · rintro p (rfl | rfl)
    · refine thueMorse_mem_inflate (p := (0, -1))
        (thueMorse_mem_inflate (p := (1, -1)) (Or.inl rfl) ?_) ?_
      · simp only [hσ1, hplace]; norm_num
      · simp only [hσ0, hplace]; norm_num
    · refine thueMorse_mem_inflate (p := (0, 0))
        (thueMorse_mem_inflate (p := (0, 0)) (Or.inr rfl) ?_) ?_
      · simp only [hσ0, hplace]; norm_num
      · simp only [hσ0, hplace]; norm_num
  · refine ⟨0, 2, 3, ?_⟩
    have h11 : ((1 : Fin 2), (1 : ℝ)) ∈ thueMorse.inflate {((0 : Fin 2), (0 : ℝ))} :=
      thueMorse_mem_inflate (p := (0, 0)) rfl (by simp only [hσ0, hplace]; norm_num)
    rintro p (rfl | rfl)
    · exact thueMorse_mem_inflate (p := (1, 1)) h11 (by simp only [hσ1, hplace]; norm_num)
    · exact thueMorse_mem_inflate (p := (1, 1)) h11 (by simp only [hσ1, hplace]; norm_num)

end Psc.PeriodicPartnerHull
