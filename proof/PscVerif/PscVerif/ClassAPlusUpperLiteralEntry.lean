/-
# Literal upper plus-Class-A entry

The arithmetic selector is bound to the original words, their actual marks,
and the full integral packet. The target is the central y/y region, not a
coincidence. Orientation exchanges complete tracks and adds no edge.

This formalizes the existing contract and source decision in
`docs/class-a-plus-upper-all-source-entry-2026-11-16.md` and
`docs/bh-class-a-plus-upper-entry-stop-go-2026-11-16.md`.
-/
import PscVerif.ClassAPlusUpperNoHalfTies
import PscVerif.ClassAPlusUpperEntryTransport

namespace Psc.ClassAPlusUpperLiteralEntry

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.OccurrenceSuccessor
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusPrefixAssembly
open Psc.ClassAPlusUpperCycles Psc.ClassAPlusUpperRecurrence
open Psc.ClassAPlusUpperEntryTransport Matrix

namespace Arithmetic
abbrev length := ClassAPlusUpperEntry.length
noncomputable abbrev threshold := ClassAPlusUpperEntry.threshold
end Arithmetic

noncomputable def xLength (n : ℕ) (β : ℝ) : ℝ := β-(n : ℝ)-2+1/β
noncomputable def cLength (β : ℝ) : ℝ := 1-1/β
noncomputable def lengths (n : ℕ) (β : ℝ) : Fin 3 → ℝ :=
  Arithmetic.length (xLength n β) (cLength β)

@[simp] theorem lengths_x (n : ℕ) (β : ℝ) : lengths n β 0 = xLength n β := rfl
@[simp] theorem lengths_c (n : ℕ) (β : ℝ) : lengths n β 1 = cLength β := rfl
@[simp] theorem lengths_y (n : ℕ) (β : ℝ) : lengths n β 2 = 1 := rfl

theorem length_bounds {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    2 < xLength n β ∧ xLength n β < 10/3 ∧
    10/11 < cLength β ∧ cLength β < 1 := by
  have hinv : 0 < 1/β := div_pos (by norm_num) hp.beta_pos
  have hinvhi : 1/β < 1/11 := (div_lt_div_iff_of_pos_left (by norm_num)
    hp.beta_pos (by norm_num)).2 hp.beta_gt_eleven
  have hrep : xLength n β = 3+3/β-V n β := by
    simp only [xLength, V, A, C]
    ring
  constructor
  · dsimp [xLength]
    linarith [hp.root_lower]
  constructor
  · rw [hrep]
    have hthree : 3/β < 3/11 := (div_lt_div_iff_of_pos_left (by norm_num)
      hp.beta_pos (by norm_num)).2 hp.beta_gt_eleven
    linarith [hp.V_pos]
  constructor <;> dsimp [cLength] <;> linarith

theorem lengths_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    ∀ a, 0 < lengths n β a := by
  intro a
  obtain ⟨hX, _, hK, _⟩ := length_bounds hp
  fin_cases a <;> simp <;> linarith

theorem lengths_lt_four {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    ∀ a, lengths n β a < 4 := by
  intro a
  obtain ⟨_, hX, _, hK⟩ := length_bounds hp
  fin_cases a <;> simp <;> linarith

theorem lengths_first_lt {n J : ℕ} {β : ℝ} (hp : Family n J β) (a : Fin 3) :
    lengths n β (first a) < 10/3 := by
  obtain ⟨_, hX, _, hK⟩ := length_bounds hp
  unfold first
  split <;> simp <;> linarith

theorem run_length_lower {n J : ℕ} {β : ℝ} (hp : Family n J β) (a : Fin 3) :
    7 ≤ plusRunLength n (2*n+12-J) a := by
  have hn := hp.n_lower
  fin_cases a <;> simp [plusRunLength, ClassAPlusConstantRecurrence.runLength] <;> omega

theorem physical_replicate_y (n : ℕ) (β : ℝ) (r : ℕ) :
    physicalLength (lengths n β) (List.replicate r 2) = r := by
  simp [physicalLength, dotProduct, List.count_replicate]

theorem literal_length_formula (n J : ℕ) (β : ℝ) (a : Fin 3) :
    physicalLength (lengths n β) (upperSigma n J a) =
      lengths n β (first a) + (plusRunLength n (2*n+12-J) a : ℝ) +
        lengths n β (last a) := by
  simp [upperSigma, plusSigma, ClassAPlusConstantRecurrence.sigma,
    physical_replicate_y, plusRunLength, add_assoc]

theorem literal_scaling {n J : ℕ} {β : ℝ} (hp : Family n J β) (a : Fin 3) :
    physicalLength (lengths n β) (upperSigma n J a) = β*lengths n β a := by
  rw [literal_length_formula]
  have hsub : J ≤ 2*n+12 := by have := hp.J_upper; omega
  have hb : β ≠ 0 := ne_of_gt hp.beta_pos
  have hc := hp.root_eq
  fin_cases a <;>
    simp [first, last, plusRunLength, ClassAPlusConstantRecurrence.runLength,
      Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul, xLength, cLength]
  all_goals field_simp
  all_goals nlinarith [hc]

/-- Prose displacement: the complete stored packet uses the opposite sign. -/
noncomputable def shift (n : ℕ) (β : ℝ) (p : Packet) : ℝ :=
  -offset (lengths n β) p.delta

@[simp] theorem shift_swap (n : ℕ) (β : ℝ) (p : Packet) :
    shift n β p.swap = -shift n β p := by
  simp [shift, Packet.swap, offset_neg]

theorem shift_no_half {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) (z : ℤ) : shift n β p ≠ (z : ℝ)+1/2 := by
  have hh := ClassAPlusUpperNoHalfTies.vector_shift_ne_half_integer n J β hp
    (-p.delta) z
  simpa [shift, offset, dotProduct, Fin.sum_univ_three, xLength, cLength,
    neg_add_rev, mul_neg, add_comm, add_left_comm, add_assoc] using hh

theorem interior_iff {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet) :
    p.Interior (lengths n β) ↔
      -lengths n β p.bottom < shift n β p ∧ shift n β p < lengths n β p.top := by
  rw [Packet.interior_iff_bounds _ (lengths_pos hp)]
  dsimp [shift]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Every child is formed from complete literal marks, not a projected scalar. -/
def markedChild (n J : ℕ) (p : Packet)
    (dt : Mark (upperSigma n J p.top)) (db : Mark (upperSigma n J p.bottom)) : Packet :=
  ⟨dt.letter, db.letter, incidenceZ (upperSigma n J) *ᵥ p.delta +
    residual dt.before db.before⟩

theorem marked_edge (n J : ℕ) (p : Packet)
    (dt : Mark (upperSigma n J p.top)) (db : Mark (upperSigma n J p.bottom)) :
    IndexedDigitStep (upperSigma n J) p dt.index db.index (markedChild n J p dt db) :=
  ⟨dt, db, rfl, rfl, rfl⟩

theorem marked_shift {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet)
    (dt : Mark (upperSigma n J p.top)) (db : Mark (upperSigma n J p.bottom)) :
    shift n β (markedChild n J p dt db) = β*shift n β p +
      physicalLength (lengths n β) db.before - physicalLength (lengths n β) dt.before := by
  dsimp [shift, markedChild]
  rw [offset_affine _ _ β (literal_scaling hp)]
  ring

def Central (n : ℕ) (β : ℝ) (p : Packet) : Prop :=
  p.top = 2 ∧ p.bottom = 2 ∧ |shift n β p| < 1/2

theorem central_swap {n : ℕ} {β : ℝ} {p : Packet} (hc : Central n β p) :
    Central n β p.swap := by
  obtain ⟨ht, hb, hs⟩ := hc
  exact ⟨hb, ht, by simpa using hs⟩

theorem central_interior {n J : ℕ} {β : ℝ} (hp : Family n J β)
    {p : Packet} (hc : Central n β p) : p.Interior (lengths n β) := by
  apply (interior_iff hp p).2
  obtain ⟨ht, hb, hs⟩ := hc
  rw [ht, hb]
  simp only [lengths_y]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hs
  constructor <;> linarith

noncomputable def entryThreshold (n : ℕ) (β : ℝ) (a b : Fin 3) : ℝ :=
  Arithmetic.threshold β (xLength n β) (cLength β) a b

theorem threshold_formula (n : ℕ) (β : ℝ) (a b : Fin 3) :
    entryThreshold n β a b =
      (lengths n β (last a) + lengths n β (first b) + 1/2)/β := rfl

theorem run_prefix_length (n J : ℕ) (β : ℝ) (a : Fin 3) (i : ℕ)
    (hi : i < plusRunLength n (2*n+12-J) a) :
    physicalLength (lengths n β) (plusRunMark n (2*n+12-J) a i hi).before =
      lengths n β (first a) + (i : ℝ) := by
  simp [plusRunMark, ClassAPlusConstantRecurrence.runMark, physical_replicate_y]

theorem last_prefix_length (n J : ℕ) (β : ℝ) (a : Fin 3) :
    physicalLength (lengths n β) (ClassAPlusUpperCycles.lastMark n (2*n+12-J) a).before =
      lengths n β (first a) + (plusRunLength n (2*n+12-J) a : ℝ) := by
  simp [ClassAPlusUpperCycles.lastMark, physical_replicate_y]

/-- The scalar nearest integer is realized by two genuine original RUN marks.
Half ties are discharged for the full inflated integral packet. -/
theorem direct_entry {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet)
    (hu : 0 ≤ shift n β p)
    (hentry : entryThreshold n β p.top p.bottom < lengths n β p.top - shift n β p) :
    ∃ i j q, IndexedDigitStep (upperSigma n J) p i j q ∧ Central n β q := by
  let Rt := plusRunLength n (2*n+12-J) p.top
  let Rb := plusRunLength n (2*n+12-J) p.bottom
  have hRt : 7 ≤ Rt := run_length_lower hp p.top
  have hRb : 7 ≤ Rb := run_length_lower hp p.bottom
  let s := β*shift n β p + lengths n β (first p.bottom) - lengths n β (first p.top)
  let D := β*(lengths n β p.top - shift n β p)
  have hlen := literal_scaling hp p.top
  rw [literal_length_formula] at hlen
  have hid : s = (Rt : ℝ) +
      (lengths n β (last p.top)+lengths n β (first p.bottom)) - D := by
    dsimp [s, D, Rt]
    nlinarith [hlen]
  have hD : lengths n β (last p.top)+lengths n β (first p.bottom)+1/2 < D := by
    rw [threshold_formula] at hentry
    have hh := (div_lt_iff₀ hp.beta_pos).1 hentry
    dsimp [D]
    nlinarith
  obtain ⟨hlo, hhi⟩ := ClassAPlusUpperEntry.direct_gap_window hu hp.beta_pos.le
    (lengths_first_lt hp p.top) (lengths_pos hp (first p.bottom)) hRb hid hD
  have hno : ∀ z : ℤ, s ≠ (z : ℝ)+1/2 := by
    let dt : Mark (upperSigma n J p.top) :=
      plusRunMark n (2*n+12-J) p.top 0 (by change 0 < Rt; omega)
    let db : Mark (upperSigma n J p.bottom) :=
      plusRunMark n (2*n+12-J) p.bottom 0 (by change 0 < Rb; omega)
    have hvalue : shift n β (markedChild n J p dt db) = s := by
      rw [marked_shift hp]
      simp only [dt, db, run_prefix_length, Nat.cast_zero, add_zero]
      rfl
    intro z
    rw [← hvalue]
    exact shift_no_half hp _ z
  obtain ⟨i, j, hi0, hi, hj0, hj, hnear⟩ :=
    ClassAPlusUpperEntry.ordered_run_indices s Rt Rb (by omega) (by omega) hlo hhi hno
  let dt : Mark (upperSigma n J p.top) :=
    plusRunMark n (2*n+12-J) p.top (i-1) (by change i-1 < Rt; omega)
  let db : Mark (upperSigma n J p.bottom) :=
    plusRunMark n (2*n+12-J) p.bottom (j-1) (by change j-1 < Rb; omega)
  have hiidx : dt.index = i := by
    simp [dt, ClassAPlusConstantRecurrence.runMark, Mark.index]
    omega
  have hjidx : db.index = j := by
    simp [db, ClassAPlusConstantRecurrence.runMark, Mark.index]
    omega
  have hs : shift n β (markedChild n J p dt db) = s+(j : ℝ)-(i : ℝ) := by
    rw [marked_shift hp]
    simp only [dt, db, run_prefix_length, Nat.cast_sub hi0, Nat.cast_sub hj0, Nat.cast_one]
    dsimp [s]
    ring
  refine ⟨i, j, markedChild n J p dt db, ?_, rfl, rfl, ?_⟩
  · simpa only [hiidx, hjidx] using marked_edge n J p dt db
  · simpa only [hs] using hnear

theorem direct_path {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet)
    (hu : 0 ≤ shift n β p)
    (hentry : entryThreshold n β p.top p.bottom < lengths n β p.top - shift n β p) :
    ∃ xs q, xs.length = 1 ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) p xs q ∧ Central n β q := by
  obtain ⟨i, j, q, he, hc⟩ := direct_entry hp p hu hentry
  have hop := OrderedPath.snoc (OrderedPath.nil p) i j he
  exact ⟨[(i,j)], q, rfl,
    ordered_path_indexed_interior _ _ β (lengths_pos hp) hp.beta_pos
      (literal_scaling hp) hop (central_interior hp hc), hc⟩

theorem reversed_direct_path {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet)
    (hu : shift n β p ≤ 0)
    (hentry : entryThreshold n β p.bottom p.top < lengths n β p.bottom + shift n β p) :
    ∃ xs q, xs.length = 1 ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) p xs q ∧ Central n β q := by
  have hs : 0 ≤ shift n β p.swap := by rw [shift_swap]; linarith
  have hm : entryThreshold n β p.swap.top p.swap.bottom <
      lengths n β p.swap.top - shift n β p.swap := by
    rw [shift_swap]
    simpa only [Packet.swap, sub_neg_eq_add] using hentry
  obtain ⟨xs, q, hlen, hpath, hc⟩ := direct_path hp p.swap hs hm
  refine ⟨xs.map Prod.swap, q.swap, by simpa using hlen, ?_, central_swap hc⟩
  have hswap : p.swap.swap = p := by cases p; simp [Packet.swap]
  simpa only [hswap] using ordered_interior_path_swap hpath

theorem prepend_direct {n J : ℕ} {β : ℝ} (hp : Family n J β)
    {p q : Packet} {i j : ℕ} (he : IndexedDigitStep (upperSigma n J) p i j q)
    (hpath : ∃ xs r, xs.length = 1 ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) q xs r ∧ Central n β r) :
    ∃ xs r, xs.length ≤ 2 ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) p xs r ∧ Central n β r := by
  obtain ⟨xs, r, hlen, hxs, hc⟩ := hpath
  have hop := (OrderedPath.snoc (.nil p) i j he).trans hxs.orderedPath
  refine ⟨[(i,j)] ++ xs, r, by simp [hlen], ?_, hc⟩
  exact ordered_path_indexed_interior _ _ β (lengths_pos hp) hp.beta_pos
    (literal_scaling hp) hop (central_interior hp hc)

theorem last_first_child {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet) :
    ∃ q, IndexedDigitStep (upperSigma n J) p
        (plusRunLength n (2*n+12-J) p.top+1) 0 q ∧
      q.top = last p.top ∧ q.bottom = first p.bottom ∧
      shift n β q = lengths n β (last p.top) - β*(lengths n β p.top-shift n β p) := by
  let dt : Mark (upperSigma n J p.top) := ClassAPlusUpperCycles.lastMark n (2*n+12-J) p.top
  let db : Mark (upperSigma n J p.bottom) := ClassAPlusUpperCycles.firstMark n (2*n+12-J) p.bottom
  refine ⟨markedChild n J p dt db, ?_, rfl, rfl, ?_⟩
  · convert marked_edge n J p dt db using 1 <;>
      simp [dt, db, ClassAPlusUpperCycles.lastMark, ClassAPlusUpperCycles.firstMark,
        Mark.index, Nat.add_comm]
  · rw [marked_shift hp]
    simp only [dt, db, last_prefix_length, ClassAPlusUpperCycles.firstMark, physicalLength_nil]
    have hl := literal_scaling hp p.top
    rw [literal_length_formula] at hl
    nlinarith

theorem runlast_first_child {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet) :
    ∃ q, IndexedDigitStep (upperSigma n J) p
        (plusRunLength n (2*n+12-J) p.top) 0 q ∧
      q.top = 2 ∧ q.bottom = first p.bottom ∧
      shift n β q = lengths n β (last p.top)+1 - β*(lengths n β p.top-shift n β p) := by
  let R := plusRunLength n (2*n+12-J) p.top
  have hR : 7 ≤ R := run_length_lower hp p.top
  let dt : Mark (upperSigma n J p.top) := plusRunMark n (2*n+12-J) p.top
    (R-1) (by change R-1 < R; omega)
  let db : Mark (upperSigma n J p.bottom) := ClassAPlusUpperCycles.firstMark n (2*n+12-J) p.bottom
  refine ⟨markedChild n J p dt db, ?_, rfl, rfl, ?_⟩
  · convert marked_edge n J p dt db using 1 <;>
      simp [dt, db, ClassAPlusConstantRecurrence.runMark,
        ClassAPlusUpperCycles.firstMark, Mark.index]
    change R = R-1+1
    omega
  · rw [marked_shift hp]
    simp only [dt, db, run_prefix_length, ClassAPlusUpperCycles.firstMark, physicalLength_nil,
      Nat.cast_sub (show 1 ≤ R by omega), Nat.cast_one]
    have hl := literal_scaling hp p.top
    rw [literal_length_formula] at hl
    dsimp [R]
    nlinarith

theorem last_runfirst_child {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet) :
    ∃ q, IndexedDigitStep (upperSigma n J) p
        (plusRunLength n (2*n+12-J) p.top+1) 1 q ∧
      q.top = last p.top ∧ q.bottom = 2 ∧
      shift n β q = lengths n β (last p.top)+lengths n β (first p.bottom) -
        β*(lengths n β p.top-shift n β p) := by
  have hRb := run_length_lower hp p.bottom
  let dt : Mark (upperSigma n J p.top) := ClassAPlusUpperCycles.lastMark n (2*n+12-J) p.top
  let db : Mark (upperSigma n J p.bottom) := plusRunMark n (2*n+12-J) p.bottom 0
    (by change 0 < plusRunLength n (2*n+12-J) p.bottom; omega)
  refine ⟨markedChild n J p dt db, ?_, rfl, rfl, ?_⟩
  · convert marked_edge n J p dt db using 1 <;>
      simp [dt, db, ClassAPlusUpperCycles.lastMark,
        ClassAPlusConstantRecurrence.runMark, Mark.index, Nat.add_comm]
  · rw [marked_shift hp]
    simp only [dt, db, last_prefix_length, run_prefix_length, Nat.cast_zero, add_zero]
    have hl := literal_scaling hp p.top
    rw [literal_length_formula] at hl
    nlinarith

/-- The existing arithmetic boundary split is now a literal ordered-occurrence
alternative. Only the first branch grows the oriented distance; every other
branch has one or two actual substitution edges to the central region. -/
theorem oriented_alternative {n J : ℕ} {β : ℝ} (hp : Family n J β) (p : Packet)
    (hu : 0 ≤ shift n β p) (hi : p.Interior (lengths n β)) :
    (∃ xs q, xs.length ≤ 2 ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) p xs q ∧ Central n β q) ∨
    ∃ i j q, IndexedDigitStep (upperSigma n J) p i j q ∧
      0 ≤ shift n β q ∧ q.Interior (lengths n β) ∧
      lengths n β q.top - shift n β q = β*(lengths n β p.top-shift n β p) := by
  by_cases hc : Central n β p
  · exact Or.inl ⟨[], p, by simp, .nil p hi, hc⟩
  by_cases hd : entryThreshold n β p.top p.bottom < lengths n β p.top-shift n β p
  · obtain ⟨xs, q, hlen, hp', hc'⟩ := direct_path hp p hu hd
    exact Or.inl ⟨xs, q, by omega, hp', hc'⟩
  let A := last p.top
  let B := first p.bottom
  let G := lengths n β A
  let F := lengths n β B
  let E := G+F
  let D := β*(lengths n β p.top-shift n β p)
  have hD : 0 < D := mul_pos hp.beta_pos
    (sub_pos.mpr ((interior_iff hp p).1 hi).2)
  have hwall : D ≤ G+F+1/2 := by
    have hh : lengths n β p.top-shift n β p ≤ entryThreshold n β p.top p.bottom := le_of_not_gt hd
    rw [threshold_formula] at hh
    have hmult := (le_div_iff₀ hp.beta_pos).1 hh
    dsimp [D, G, F, A, B]
    nlinarith
  obtain ⟨hXlo, hXhi, hKlo, hKhi⟩ := length_bounds hp
  have hcases := ClassAPlusUpperEntry.boundary_cases β (xLength n β) (cLength β) D
    hp.beta_gt_eleven hXlo hXhi hKlo hKhi p.top p.bottom hD hwall
  change
    (0 ≤ G-D ∧ G-D < G ∧ G-(G-D) = D) ∨
    (-F < G-D ∧ G-D < 0 ∧ entryThreshold n β B A < E-D) ∨
    (0 ≤ G+1-D ∧ G+1-D < 1 ∧ entryThreshold n β 2 B < D-G) ∨
    (-F < G+1-D ∧ G+1-D < 0 ∧ entryThreshold n β B 2 < E+1-D) ∨
    (-1 < E-D ∧ E-D ≤ 0 ∧ entryThreshold n β 2 A < 1+(E-D)) at hcases
  obtain ⟨qlf, elf, hlt, hlb, hls⟩ := last_first_child hp p
  change shift n β qlf = G-D at hls
  change qlf.top = A at hlt
  change qlf.bottom = B at hlb
  rcases hcases with hg | hrev | hrun | hrunrev | hfinal
  · refine Or.inr ⟨_, _, qlf, elf, by rw [hls]; exact hg.1, ?_, ?_⟩
    · apply (interior_iff hp qlf).2
      rw [hlt, hlb, hls]
      have hF : 0 < F := lengths_pos hp B
      exact ⟨by dsimp [F] at hF; linarith [hg.1], hg.2.1⟩
    · rw [hlt, hls]
      change G-(G-D) = D
      ring
  · apply Or.inl
    apply prepend_direct hp elf
    apply reversed_direct_path hp qlf
    · rw [hls]; linarith [hrev.2.1]
    · rw [hlt, hlb, hls]
      change entryThreshold n β B A < F+(G-D)
      dsimp [E] at hrev
      linarith [hrev.2.2]
  · obtain ⟨q, he, ht, hb, hs⟩ := runlast_first_child hp p
    change q.bottom = B at hb
    change shift n β q = G+1-D at hs
    apply Or.inl
    apply prepend_direct hp he
    apply direct_path hp q
    · rw [hs]; exact hrun.1
    · rw [ht, hb, hs, lengths_y]
      linarith [hrun.2.2]
  · obtain ⟨q, he, ht, hb, hs⟩ := runlast_first_child hp p
    change q.bottom = B at hb
    change shift n β q = G+1-D at hs
    apply Or.inl
    apply prepend_direct hp he
    apply reversed_direct_path hp q
    · rw [hs]; linarith [hrunrev.2.1]
    · rw [ht, hb, hs]
      change entryThreshold n β B 2 < F+(G+1-D)
      dsimp [E] at hrunrev
      linarith [hrunrev.2.2]
  · obtain ⟨q, he, ht, hb, hs⟩ := last_runfirst_child hp p
    change q.top = A at ht
    change shift n β q = E-D at hs
    apply Or.inl
    apply prepend_direct hp he
    apply reversed_direct_path hp q
    · rw [hs]; exact hfinal.2.1
    · rw [ht, hb, hs, lengths_y]
      exact hfinal.2.2

end Psc.ClassAPlusUpperLiteralEntry
