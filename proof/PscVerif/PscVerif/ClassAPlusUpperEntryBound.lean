/-
# Literal upper entry with its least-power depth bound

The bounded-growth state retains an oriented full packet and an independent
frame bit. Reorienting a source never counts as an edge: all state edges
project to a literal ordered occurrence edge on the original tracks. The
same frame bit is retained by a boundary-growth edge, including at zero
shift, so its positive boundary margin is multiplied by exactly beta.

The endpoint is the central y/y region with its complete possibly nonzero
offset. No central-source coincidence theorem is assumed or concluded.
-/
import PscVerif.ClassAPlusUpperLiteralEntry

namespace Psc.ClassAPlusUpperEntryBound

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry
open Psc.ClassAPlusUpperEntryTransport Matrix

/-- The frame bit is independent of the sign of the current displacement.
It remembers which complete original track is represented by each side. -/
structure State (n : ℕ) (β : ℝ) where
  oriented : Packet
  nonnegative : 0 ≤ shift n β oriented
  interior : oriented.Interior (lengths n β)
  reversed : Bool

/-- Recover the complete packet in the original source orientation. -/
def actual {n : ℕ} {β : ℝ} (a : State n β) : Packet :=
  if a.reversed then a.oriented.swap else a.oriented

noncomputable def margin {n : ℕ} {β : ℝ} (a : State n β) : ℝ :=
  lengths n β a.oriented.top - shift n β a.oriented

private theorem swap_swap (p : Packet) : p.swap.swap = p := by
  cases p
  simp [Packet.swap]

/-- The initial orientation is chosen once, without consuming a digit. -/
noncomputable def orient (n : ℕ) (β : ℝ) (p : Packet)
    (hi : p.Interior (lengths n β)) : State n β := by
  classical
  exact if hu : 0 ≤ shift n β p then
    ⟨p, hu, hi, false⟩
  else ⟨p.swap, by rw [shift_swap]; linarith, hi.swap, true⟩

theorem actual_orient (n : ℕ) (β : ℝ) (p : Packet)
    (hi : p.Interior (lengths n β)) : actual (orient n β p hi) = p := by
  classical
  unfold orient
  split <;> simp [actual, swap_swap]

theorem actual_interior {n : ℕ} {β : ℝ} (a : State n β) :
    (actual a).Interior (lengths n β) := by
  unfold actual
  split
  · exact a.interior.swap
  · exact a.interior

theorem margin_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) (a : State n β) :
    0 < margin a := by
  have hi := ((interior_iff hp a.oriented).mp a.interior).2
  dsimp [margin]
  linarith

theorem margin_lt_four {n J : ℕ} {β : ℝ} (hp : Family n J β) (a : State n β) :
    margin a < 4 := by
  have hlen := lengths_lt_four hp a.oriented.top
  have hu := a.nonnegative
  dsimp [margin]
  linarith

/-- Every edge in the growth carrier is an actual substitution edge on the
original tracks, with both selected zero-based indices. -/
def Edge (n J : ℕ) (β : ℝ) (a b : State n β) : Prop :=
  LiteralEdge (upperSigma n J) (actual a) (actual b)

def Ready (n : ℕ) (β : ℝ) (a : State n β) : Prop := Central n β (actual a)

theorem state_alternative {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (a : State n β) (_hm : 0 < margin a) :
    (∃ j target, j ≤ 2 ∧ ClassAPlusUpperEntry.Steps (Edge n J β) j a target ∧
      Ready n β target) ∨
    ∃ child, Edge n J β a child ∧ 0 < margin child ∧ margin child = β*margin a := by
  rcases oriented_alternative hp a.oriented a.nonnegative a.interior with
    ⟨xs, q, hlen, hpath, hc⟩ | ⟨i, j, q, he, hu, hi, hm⟩
  · let ys := if a.reversed then xs.map Prod.swap else xs
    let target := if a.reversed then q.swap else q
    have hactual : OrderedInteriorPath (upperSigma n J) (lengths n β)
        (actual a) ys target := by
      cases hr : a.reversed
      · simpa [actual, ys, target, hr] using hpath
      · simpa [actual, ys, target, hr] using ordered_interior_path_swap hpath
    have hcentral : Central n β target := by
      cases hr : a.reversed
      · simpa [target, hr] using hc
      · simpa [target, hr] using central_swap hc
    have hlength : ys.length ≤ 2 := by
      cases hr : a.reversed <;> simpa [ys, hr] using hlen
    obtain ⟨b, hb, hs⟩ := ordered_interior_to_steps actual
      (fun p hi => ⟨orient n β p hi, actual_orient n β p hi⟩)
      (fun _ _ h => h) hactual a rfl
    exact Or.inl ⟨ys.length, b, hlength, hs, by simpa [Ready, hb] using hcentral⟩
  · let child : State n β := ⟨q, hu, hi, a.reversed⟩
    have hedge : Edge n J β a child := by
      cases hr : a.reversed
      · exact ⟨i, j, by simpa [actual, child, hr] using he⟩
      · exact ⟨j, i, by simpa [actual, child, hr] using indexed_step_swap he⟩
    exact Or.inr ⟨child, hedge, margin_pos hp child, hm⟩

/-- For any witnessing power, the output transcript has at most k+1 actual
edges. Both original marks and all terminal offset coordinates are kept. -/
theorem state_entry_for_power {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : State n β) (k : ℕ) (hk : 4 ≤ β^k * margin source) :
    ∃ xs target, xs.length ≤ k+1 ∧ Central n β target ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) (actual source) xs target ∧
      OriginalTraces (upperSigma n J) (actual source) xs target := by
  obtain ⟨j, target, hj, hs, hc⟩ := ClassAPlusUpperEntry.bounded_entry_of_growth
    (Edge n J β) (Ready n β) margin β (state_alternative hp) (margin_lt_four hp)
    k source (margin_pos hp source) hk
  obtain ⟨xs, hlen, hpath, htraces⟩ := steps_traced_interior actual
    (fun _ _ h => h) (lengths n β) β (lengths_pos hp) hp.beta_pos
    (literal_scaling hp) hs (central_interior hp hc)
  exact ⟨xs, actual target, by omega, hc, hpath, htraces⟩

/-- The positive distance to the upper boundary after the initial complete
track reversal, if needed. The zero-shift case retains the source order. -/
noncomputable def sourceMargin (n : ℕ) (β : ℝ) (source : Packet) : ℝ :=
  if 0 ≤ shift n β source then lengths n β source.top - shift n β source
  else lengths n β source.bottom + shift n β source

theorem margin_orient (n : ℕ) (β : ℝ) (p : Packet)
    (hi : p.Interior (lengths n β)) :
    margin (orient n β p hi) = sourceMargin n β p := by
  classical
  unfold orient sourceMargin
  split
  · simp_all [margin]
  · simp_all [margin, shift_swap]
    rfl

theorem source_margin_pos {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) (hi : p.Interior (lengths n β)) : 0 < sourceMargin n β p := by
  rw [← margin_orient n β p hi]
  exact margin_pos hp _

theorem entry_for_power {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hi : source.Interior (lengths n β))
    (k : ℕ) (hk : 4 ≤ β^k * sourceMargin n β source) :
    ∃ xs target, xs.length ≤ k+1 ∧ Central n β target ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) source xs target ∧
      OriginalTraces (upperSigma n J) source xs target := by
  have hk' : 4 ≤ β^k * margin (orient n β source hi) := by
    simpa only [margin_orient] using hk
  simpa only [actual_orient] using state_entry_for_power hp (orient n β source hi) k hk'

/-- The least natural power at which this source's positive oriented
boundary margin reaches the common wall 4. -/
noncomputable def leastEntryPower {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hi : source.Interior (lengths n β)) : ℕ :=
  Nat.find (ClassAPlusUpperEntry.exists_entry_power β (sourceMargin n β source)
    (by linarith [hp.beta_gt_eleven]) (source_margin_pos hp source hi))

theorem least_entry_power_spec {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hi : source.Interior (lengths n β)) :
    4 ≤ β^(leastEntryPower hp source hi) * sourceMargin n β source ∧
    ∀ j < leastEntryPower hp source hi, β^j * sourceMargin n β source < 4 := by
  let hex : ∃ k : ℕ, 4 ≤ β^k * sourceMargin n β source :=
    ClassAPlusUpperEntry.exists_entry_power β (sourceMargin n β source)
      (by linarith [hp.beta_gt_eleven]) (source_margin_pos hp source hi)
  change 4 ≤ β^(Nat.find hex) * sourceMargin n β source ∧
    ∀ j < Nat.find hex, β^j * sourceMargin n β source < 4
  exact ⟨Nat.find_spec hex, fun j hj => lt_of_not_ge (Nat.find_min hex hj)⟩

/-- Every strict integral source enters central y/y, with the documented
least-power bound and complete original occurrence witnesses. -/
theorem all_source_entry {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hi : source.Interior (lengths n β)) :
    ∃ xs target, xs.length ≤ leastEntryPower hp source hi + 1 ∧ Central n β target ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) source xs target ∧
      OriginalTraces (upperSigma n J) source xs target :=
  entry_for_power hp source hi (leastEntryPower hp source hi)
    (least_entry_power_spec hp source hi).1

/-- A source already central uses the empty literal transcript. -/
theorem central_empty_entry {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) :
    OrderedInteriorPath (upperSigma n J) (lengths n β) source [] source ∧
    OriginalTraces (upperSigma n J) source [] source :=
  ⟨.nil source (central_interior hp hc), original_traces_of_ordered (.nil source)⟩

/-- Convert the manuscript's n,d chamber to the existing n,J family without
truncated subtraction or a change in the substitution words. -/
theorem family_of_nd (n d : ℕ) (β : ℝ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hlo : (n : ℝ)+4 < β) (hhi : β < (n : ℝ)+6)
    (hroot : β^3 - ((n : ℝ)+4)*β^2 + ((n : ℝ)+5-(d : ℝ))*β - 2 = 0) :
    Family n (2*n+12-d) β := by
  apply ClassAPlusUpperNoHalfTies.family_of_parameters n d β hn hdlo hdhi hlo hhi
  nlinarith [hroot]

theorem upper_sigma_original (n d : ℕ) (hdhi : d ≤ 2*n+12) :
    upperSigma n (2*n+12-d) = plusSigma n d := by
  simp [upperSigma, Nat.sub_sub_self hdhi]

/-- The same counted theorem for the original literal n,d words. -/
theorem entry_for_power_nd (n d : ℕ) (β : ℝ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hlo : (n : ℝ)+4 < β) (hhi : β < (n : ℝ)+6)
    (hroot : β^3 - ((n : ℝ)+4)*β^2 + ((n : ℝ)+5-(d : ℝ))*β - 2 = 0)
    (source : Packet) (hi : source.Interior (lengths n β))
    (k : ℕ) (hk : 4 ≤ β^k * sourceMargin n β source) :
    ∃ xs target, xs.length ≤ k+1 ∧ Central n β target ∧
      OrderedInteriorPath (plusSigma n d) (lengths n β) source xs target ∧
      OriginalTraces (plusSigma n d) source xs target := by
  have hp := family_of_nd n d β hn hdlo hdhi hlo hhi hroot
  simpa only [upper_sigma_original n d (by omega)] using
    entry_for_power hp source hi k hk

/-- The manuscript statement, including the leastness of its source-
dependent power and both original prefix tracks. -/
theorem all_source_entry_nd (n d : ℕ) (β : ℝ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hlo : (n : ℝ)+4 < β) (hhi : β < (n : ℝ)+6)
    (hroot : β^3 - ((n : ℝ)+4)*β^2 + ((n : ℝ)+5-(d : ℝ))*β - 2 = 0)
    (source : Packet) (hi : source.Interior (lengths n β)) :
    ∃ (k : ℕ) (xs : List (ℕ × ℕ)) (target : Packet),
      4 ≤ β^k * sourceMargin n β source ∧
      (∀ j < k, β^j * sourceMargin n β source < 4) ∧
      xs.length ≤ k+1 ∧ Central n β target ∧
      OrderedInteriorPath (plusSigma n d) (lengths n β) source xs target ∧
      OriginalTraces (plusSigma n d) source xs target := by
  have hp := family_of_nd n d β hn hdlo hdhi hlo hhi hroot
  obtain ⟨hk, hmin⟩ := least_entry_power_spec hp source hi
  obtain ⟨xs, target, hlen, hc, hpath, htraces⟩ := all_source_entry hp source hi
  refine ⟨leastEntryPower hp source hi, xs, target, hk, hmin, hlen, hc, ?_, ?_⟩
  · simpa only [upper_sigma_original n d (by omega)] using hpath
  · simpa only [upper_sigma_original n d (by omega)] using htraces

/-- Every parameter pair in the documented chamber has an actual bracketed
cubic root and positive literal eigenlengths for which all strict integral
sources enter central y/y with the source-dependent least-power bound.
No root-existence premise is supplied by the caller. -/
theorem exists_root_all_source_entry (n d : ℕ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11) :
    ∃ β : ℝ, (n : ℝ)+4 < β ∧ β < (n : ℝ)+6 ∧
      β^3 - ((n : ℝ)+4)*β^2 + ((n : ℝ)+5-(d : ℝ))*β - 2 = 0 ∧
      (∀ a, 0 < lengths n β a) ∧
      (∀ a, physicalLength (lengths n β) (plusSigma n d a) = β*lengths n β a) ∧
      ∀ source : Packet, source.Interior (lengths n β) →
        ∃ (k : ℕ) (xs : List (ℕ × ℕ)) (target : Packet),
          4 ≤ β^k * sourceMargin n β source ∧
          (∀ j < k, β^j * sourceMargin n β source < 4) ∧
          xs.length ≤ k+1 ∧ Central n β target ∧
          OrderedInteriorPath (plusSigma n d) (lengths n β) source xs target ∧
          OriginalTraces (plusSigma n d) source xs target := by
  obtain ⟨β, hp⟩ := ClassAPlusUpperNoHalfTies.family_root_exists n (2*n+12-d)
    hn (by omega) (by omega)
  have hroot : β^3 - ((n : ℝ)+4)*β^2 + ((n : ℝ)+5-(d : ℝ))*β - 2 = 0 := by
    have hh := hp.root_eq
    rw [Nat.cast_sub (show d ≤ 2*n+12 by omega)] at hh
    push_cast at hh
    nlinarith [hh]
  refine ⟨β, hp.root_lower, hp.root_upper, hroot, lengths_pos hp, ?_, ?_⟩
  · intro a
    simpa only [upper_sigma_original n d (by omega)] using literal_scaling hp a
  · intro source hi
    exact all_source_entry_nd n d β hn hdlo hdhi hp.root_lower hp.root_upper hroot source hi

end Psc.ClassAPlusUpperEntryBound
