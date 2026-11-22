/-
# Compact exact origin fibres of the legal hull

Fixing the exact tile containing zero removes the continuous position
parameter. A finite alphabet then leaves finitely many exact windows at
each radius. The proof follows adjacent tiles in both directions: each
step changes the start by one tile length, and every length is bounded
below by the positive minimum. No recognition radius, compact hull or
continuous inverse is assumed.

Source decision: `docs/c4-realization-continuity-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerHullComplete
import PscVerif.PeriodicPartnerRealization
import PscVerif.PeriodicPartnerOriginContinuity
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace Psc.PeriodicPartnerHullCompact

open Function Filter Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
  Psc.PeriodicPartnerRealization
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α}

/-- Tiles reached by repeatedly crossing the right endpoint of the preceding tile. -/
noncomputable def rightTile (T : S.Hull) : ℕ → α × ℝ
  | 0 => origin T
  | n + 1 => tileAt T ((rightTile T n).2 + S.ℓ (rightTile T n).1)

/-- Tiles reached by repeatedly moving to the tile immediately to the left. -/
noncomputable def leftTile (T : S.Hull) : ℕ → α × ℝ
  | 0 => origin T
  | n + 1 => tileAt T ((leftTile T n).2 - minLen S)

omit [Nonempty α] in
theorem rightTile_mem (T : S.Hull) (n : ℕ) : rightTile T n ∈ T.1 := by
  cases n with
  | zero => exact (tileAt_spec T 0).1
  | succ n => exact (tileAt_spec T _).1

theorem leftTile_mem (T : S.Hull) (n : ℕ) : leftTile T n ∈ T.1 := by
  cases n with
  | zero => exact (tileAt_spec T 0).1
  | succ n => exact (tileAt_spec T _).1

omit [Nonempty α] in
theorem rightTile_start_succ (T : S.Hull) (n : ℕ) :
    (rightTile T (n + 1)).2 = (rightTile T n).2 + S.ℓ (rightTile T n).1 :=
  tileAt_next (rightTile_mem T n)

/-- The point one minimum length left of a tile start lies in its immediate predecessor. -/
theorem tileAt_prev_end {T : S.Hull} {q : α × ℝ} (hq : q ∈ T.1) :
    (tileAt T (q.2 - minLen S)).2 + S.ℓ (tileAt T (q.2 - minLen S)).1 = q.2 := by
  obtain ⟨b, hb⟩ := exists_prev hq
  have he : tileAt T (q.2 - minLen S) = (b, q.2 - S.ℓ b) := by
    apply tileAt_eq hb
    change q.2 - S.ℓ b ≤ q.2 - minLen S ∧ q.2 - minLen S < q.2 - S.ℓ b + S.ℓ b
    constructor
    · linarith [minLen_le (S := S) b]
    · linarith [minLen_pos (S := S)]
  rw [he]
  dsimp
  ring

theorem leftTile_end_succ (T : S.Hull) (n : ℕ) :
    (leftTile T (n + 1)).2 + S.ℓ (leftTile T (n + 1)).1 = (leftTile T n).2 :=
  tileAt_prev_end (leftTile_mem T n)

theorem leftTile_start_succ (T : S.Hull) (n : ℕ) :
    (leftTile T (n + 1)).2 = (leftTile T n).2 - S.ℓ (leftTile T (n + 1)).1 := by
  linarith [leftTile_end_succ T n]

theorem rightTile_start_lower (T : S.Hull) (n : ℕ) :
    (origin T).2 + n * minLen S ≤ (rightTile T n).2 := by
  induction n with
  | zero => simp [rightTile]
  | succ n ih =>
    rw [rightTile_start_succ]
    push_cast
    nlinarith [minLen_le (S := S) (rightTile T n).1]

theorem leftTile_start_upper (T : S.Hull) (n : ℕ) :
    (leftTile T n).2 ≤ (origin T).2 - n * minLen S := by
  induction n with
  | zero => simp [leftTile]
  | succ n ih =>
    rw [leftTile_start_succ]
    push_cast
    nlinarith [minLen_le (S := S) (leftTile T (n + 1)).1]

omit [Nonempty α] in
/-- The first `n` right tiles cover the interval up to the next start. -/
theorem rightTile_cover (T : S.Hull) (n : ℕ) {z : ℝ}
    (hlo : (origin T).2 ≤ z) (hhi : z < (rightTile T n).2) :
    ∃ i < n, z ∈ S.supp (rightTile T i) := by
  induction n with
  | zero => simp only [rightTile] at hhi; linarith
  | succ n ih =>
    by_cases h : z < (rightTile T n).2
    · obtain ⟨i, hi, hz⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hz⟩
    · refine ⟨n, Nat.lt_succ_self n, le_of_not_gt h, ?_⟩
      exact (rightTile_start_succ T n) ▸ hhi

/-- The first `n` left tiles cover the interval from the outer start to the origin tile. -/
theorem leftTile_cover (T : S.Hull) (n : ℕ) {z : ℝ}
    (hlo : (leftTile T n).2 ≤ z) (hhi : z < (origin T).2) :
    ∃ i ≤ n, z ∈ S.supp (leftTile T i) := by
  induction n with
  | zero => simp only [leftTile] at hlo; linarith
  | succ n ih =>
    by_cases h : (leftTile T n).2 ≤ z
    · obtain ⟨i, hi, hz⟩ := ih h
      exact ⟨i, Nat.le_succ_of_le hi, hz⟩
    · refine ⟨n + 1, le_rfl, hlo, ?_⟩
      rw [leftTile_end_succ]
      exact lt_of_not_ge h

omit [Nonempty α] in
theorem finite_range_rightTile (p : α × ℝ) (n : ℕ) :
    (range (fun T : {T : S.Hull // origin T = p} => rightTile T.1 n)).Finite := by
  induction n with
  | zero =>
    apply (finite_singleton p).subset
    rintro q ⟨T, rfl⟩
    exact T.2
  | succ n ih =>
    have hf : (⋃ q ∈ range (fun T : {T : S.Hull // origin T = p} => rightTile T.1 n),
        range (fun a : α => (a, q.2 + S.ℓ q.1))).Finite :=
      ih.biUnion (fun q _ => finite_range _)
    apply hf.subset
    rintro q ⟨T, rfl⟩
    refine mem_iUnion.mpr ⟨rightTile T.1 n, mem_iUnion.mpr ⟨⟨T, rfl⟩, ?_⟩⟩
    exact ⟨(rightTile T.1 (n + 1)).1, Prod.ext rfl (rightTile_start_succ T.1 n).symm⟩

theorem finite_range_leftTile (p : α × ℝ) (n : ℕ) :
    (range (fun T : {T : S.Hull // origin T = p} => leftTile T.1 n)).Finite := by
  induction n with
  | zero =>
    apply (finite_singleton p).subset
    rintro q ⟨T, rfl⟩
    exact T.2
  | succ n ih =>
    have hf : (⋃ q ∈ range (fun T : {T : S.Hull // origin T = p} => leftTile T.1 n),
        range (fun a : α => (a, q.2 - S.ℓ a))).Finite :=
      ih.biUnion (fun q _ => finite_range _)
    apply hf.subset
    rintro q ⟨T, rfl⟩
    refine mem_iUnion.mpr ⟨leftTile T.1 n, mem_iUnion.mpr ⟨⟨T, rfl⟩, ?_⟩⟩
    exact ⟨(leftTile T.1 (n + 1)).1, Prod.ext rfl (leftTile_start_succ T.1 n).symm⟩

/-- Uniformly in the tiling, an anchored bounded window uses a finite set of exact tiles. -/
theorem exists_finite_window_container (p : α × ℝ) (n : ℕ) :
    ∃ A : Set (α × ℝ), A.Finite ∧
      ∀ T : S.Hull, origin T = p → window T n ⊆ A := by
  obtain ⟨N, hN⟩ := exists_nat_gt (((n : ℝ) + |p.2|) / minLen S)
  have hNm : (n : ℝ) + |p.2| < N * minLen S := (div_lt_iff₀ (minLen_pos (S := S))).mp hN
  let A : Set (α × ℝ) :=
    (⋃ i : Fin (N + 1), range (fun T : {T : S.Hull // origin T = p} => rightTile T.1 i.1)) ∪
    (⋃ i : Fin (N + 1), range (fun T : {T : S.Hull // origin T = p} => leftTile T.1 i.1))
  refine ⟨A, (finite_iUnion (fun i : Fin (N + 1) => finite_range_rightTile p i.1)).union
    (finite_iUnion (fun i : Fin (N + 1) => finite_range_leftTile p i.1)), ?_⟩
  intro T hT q hq
  obtain ⟨z, hzq, hzlo, hzhi⟩ := hq.2
  have hright : (n : ℝ) < (rightTile T N).2 := by
    have hb := rightTile_start_lower T N
    rw [hT] at hb
    linarith [neg_abs_le p.2]
  have hleft : (leftTile T N).2 < -(n : ℝ) := by
    have hb := leftTile_start_upper T N
    rw [hT] at hb
    linarith [le_abs_self p.2]
  by_cases hside : (origin T).2 ≤ z
  · obtain ⟨i, hi, hzi⟩ := rightTile_cover T N hside (hzhi.trans hright)
    have heq : q = rightTile T i := (T.2.1 z).unique ⟨hq.1, hzq⟩ ⟨rightTile_mem T i, hzi⟩
    exact Or.inl (mem_iUnion.mpr ⟨⟨i, Nat.lt_succ_of_lt hi⟩, ⟨⟨T, hT⟩, heq.symm⟩⟩)
  · obtain ⟨i, hi, hzi⟩ := leftTile_cover T N (hleft.trans hzlo).le (lt_of_not_ge hside)
    have heq : q = leftTile T i := (T.2.1 z).unique ⟨hq.1, hzq⟩ ⟨leftTile_mem T i, hzi⟩
    exact Or.inr (mem_iUnion.mpr ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, ⟨⟨T, hT⟩, heq.symm⟩⟩)

/-- There are finitely many exact windows of any fixed radius with a fixed origin tile. -/
theorem finite_range_window (p : α × ℝ) (n : ℕ) :
    (range (fun T : {T : S.Hull // origin T = p} => window T.1 n)).Finite := by
  obtain ⟨A, hA, hcover⟩ := exists_finite_window_container (S := S) p n
  apply hA.powerset.subset
  rintro W ⟨T, rfl⟩
  exact hcover T.1 T.2

/-- Finite anchored windows give total boundedness in the exact-agreement metric. -/
theorem totallyBounded_origin_fibre (p : α × ℝ) :
    TotallyBounded {T : S.Hull | origin T = p} := by
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let W := range (fun T : {T : S.Hull // origin T = p} => window T.1 n)
  let : Fintype W := (finite_range_window (S := S) p n).fintype
  refine ⟨W, inferInstance, (fun T => ⟨window T.1 n, ⟨T, rfl⟩⟩), ?_⟩
  intro T U hTU
  have heq : window T.1 n = window U.1 n := congrArg Subtype.val hTU
  exact (dist_le_of_agree (agree_iff_window.mpr heq)).trans_lt hn

/-- A fixed exact origin tile has a compact fibre, including the empty fibre. -/
theorem isCompact_origin_fibre (p : α × ℝ) :
    IsCompact {T : S.Hull | origin T = p} :=
  (totallyBounded_origin_fibre p).isCompact_of_isClosed
    (Psc.PeriodicPartnerOriginContinuity.isClosed_origin_fibre p)

end Psc.PeriodicPartnerHullCompact
