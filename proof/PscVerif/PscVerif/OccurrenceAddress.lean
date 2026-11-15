/-
# Global positions, actual factor occurrences and substitution addresses

`docs/c4-address-transport-literature-2026-11-10.md` records the targeted
stop/go review. This module resolves a literal in-range letter position in
an ordered concatenation to its unique factor ordinal and local position.
The executable lookup handles empty chunks and preserves selected letters,
word prefixes and physical starts. Specialization to the complete
`Reduction.red` removes the prelocated-occurrence premise from the common
factor theorem. A second specialization resolves substitution descendants
to actual source indices and within-image digits.

No packet-edge completeness, multistep lifting or uniform productivity
claim is made here. Physical common-factor identification still requires
strictly intersecting tile interiors; mere endpoint contact is insufficient.
-/
import PscVerif.OccurrenceNewborn

namespace Psc.OccurrenceAddress

open Psc.Binomial Psc.Reduction Psc.OccurrenceNewborn

variable {α : Type*}

/-- Number of letters in the chunks strictly before ordinal `j`. -/
def prefixLength (ws : List (List α)) (j : ℕ) : ℕ :=
  ((ws.take j).map List.length).sum

/-- Resolve a global position to a chunk ordinal and local position.
Empty chunks are skipped; an exterior position returns `none`. -/
def locate : List (List α) → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | w :: ws, n =>
      if n < w.length then some (0, n)
      else (locate ws (n - w.length)).map (fun p => (p.1 + 1, p.2))

theorem locate_sound {ws : List (List α)} {n j k : ℕ}
    (h : locate ws n = some (j, k)) :
    ∃ w, ws[j]? = some w ∧ k < w.length ∧ n = prefixLength ws j + k := by
  induction ws generalizing n j k with
  | nil => simp [locate] at h
  | cons w ws ih =>
      by_cases hn : n < w.length
      · have hp : (0, n) = (j, k) := by simpa [locate, hn] using h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        exact ⟨w, by simp, hn, by simp [prefixLength]⟩
      · simp only [locate, hn, ↓reduceIte] at h
        cases ht : locate ws (n - w.length) with
        | none => simp [ht] at h
        | some p =>
            obtain ⟨a, b⟩ := p
            have hp : (a + 1, b) = (j, k) := by simpa [ht] using h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
            obtain ⟨v, hv, hb, he⟩ := ih ht
            refine ⟨v, by simpa using hv, hb, ?_⟩
            simp only [prefixLength, List.take_succ_cons, List.map_cons, List.sum_cons]
            unfold prefixLength at he
            omega

theorem locate_complete {ws : List (List α)} {n j k : ℕ} {w : List α}
    (hw : ws[j]? = some w) (hk : k < w.length)
    (hn : n = prefixLength ws j + k) : locate ws n = some (j, k) := by
  induction ws generalizing n j with
  | nil => simp at hw
  | cons v ws ih =>
      cases j with
      | zero =>
          have hv : v = w := by simpa using hw
          subst v
          have hnk : n = k := by simpa [prefixLength] using hn
          rw [hnk]
          simp [locate, hk]
      | succ j =>
          have hw' : ws[j]? = some w := by simpa using hw
          have hn' : n = v.length + prefixLength ws j + k := by
            simpa [prefixLength, Nat.add_assoc] using hn
          have hnot : ¬ n < v.length := by omega
          have hsub : n - v.length = prefixLength ws j + k := by omega
          simp [locate, hnot, ih hw' hsub]

theorem locate_eq_some_iff {ws : List (List α)} {n j k : ℕ} :
    locate ws n = some (j, k) ↔
      ∃ w, ws[j]? = some w ∧ k < w.length ∧ n = prefixLength ws j + k := by
  constructor
  · exact locate_sound
  · rintro ⟨w, hw, hk, hn⟩
    exact locate_complete hw hk hn

theorem locate_eq_none_iff {ws : List (List α)} {n : ℕ} :
    locate ws n = none ↔ ws.flatten.length ≤ n := by
  induction ws generalizing n with
  | nil => simp [locate]
  | cons w ws ih =>
      by_cases hn : n < w.length
      · constructor
        · intro h
          simp [locate, hn] at h
        · intro h
          have he : w.length + ws.flatten.length ≤ n := by
            simpa only [List.flatten_cons, List.length_append] using h
          omega
      · simp only [locate, hn, ↓reduceIte, Option.map_eq_none_iff, ih,
          List.flatten_cons, List.length_append]
        omega

theorem locate_isSome {ws : List (List α)} {n : ℕ}
    (hn : n < ws.flatten.length) : (locate ws n).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  intro he
  have := locate_eq_none_iff.mp he
  omega

/-- The total, executable lookup on an in-range global position. -/
def lookup (ws : List (List α)) (n : ℕ) (hn : n < ws.flatten.length) : ℕ × ℕ :=
  (locate ws n).get (locate_isSome hn)

theorem lookup_eq (ws : List (List α)) (n : ℕ) (hn : n < ws.flatten.length) :
    locate ws n = some (lookup ws n hn) :=
  (Option.some_get _).symm

theorem lookup_spec (ws : List (List α)) (n : ℕ) (hn : n < ws.flatten.length) :
    ∃ w, ws[(lookup ws n hn).1]? = some w ∧
      (lookup ws n hn).2 < w.length ∧
      n = prefixLength ws (lookup ws n hn).1 + (lookup ws n hn).2 :=
  locate_sound (lookup_eq ws n hn)

theorem locate_unique {ws : List (List α)} {n j k j' k' : ℕ} {w w' : List α}
    (hw : ws[j]? = some w) (hk : k < w.length)
    (hn : n = prefixLength ws j + k)
    (hw' : ws[j']? = some w') (hk' : k' < w'.length)
    (hn' : n = prefixLength ws j' + k') : j = j' ∧ k = k' := by
  have h := (locate_complete hw hk hn).symm.trans (locate_complete hw' hk' hn')
  exact Prod.mk.inj (Option.some.inj h)

theorem chunk_split {ws : List (List α)} {j : ℕ} {w : List α}
    (hw : ws[j]? = some w) : ws = ws.take j ++ w :: ws.drop (j + 1) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hw
  rw [← hget, List.getElem_cons_drop hj, List.take_append_drop]

theorem locate_prefix {ws : List (List α)} {n j k : ℕ} {w : List α}
    (hw : ws[j]? = some w) (hk : k < w.length)
    (hn : n = prefixLength ws j + k) :
    ws.flatten.take n = (ws.take j).flatten ++ w.take k := by
  have hs : ws.flatten = (ws.take j).flatten ++ w ++ (ws.drop (j + 1)).flatten := by
    conv_lhs => rw [chunk_split hw]
    simp
  rw [hs, hn]
  have hp : prefixLength ws j = (ws.take j).flatten.length := by
    simp [prefixLength]
  rw [hp, List.append_assoc, List.take_length_add_append,
    List.take_append_of_le_length (Nat.le_of_lt hk)]

theorem locate_letter {ws : List (List α)} {n j k : ℕ} {w : List α}
    (hw : ws[j]? = some w) (hk : k < w.length)
    (hn : n = prefixLength ws j + k) : ws.flatten[n]? = w[k]? := by
  have hs : ws.flatten = (ws.take j).flatten ++ w ++ (ws.drop (j + 1)).flatten := by
    conv_lhs => rw [chunk_split hw]
    simp
  have hp : prefixLength ws j = (ws.take j).flatten.length := by
    simp [prefixLength]
  rw [hs, hn, hp, List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

/-- A numerical address of a literal selected letter in one track of an
ordered list of objects. The object at the ordinal is retained. -/
structure TrackAddress {β : Type*} (bs : List β) (track : β → List α) (n : ℕ) where
  ordinal : ℕ
  localIndex : ℕ
  factor : β
  atOrdinal : bs[ordinal]? = some factor
  localValid : localIndex < (track factor).length
  index_eq : n = prefixLength (bs.map track) ordinal + localIndex

variable {β : Type*}

/-- An in-range global letter has a computably selected track address. -/
def lookupTrack (bs : List β) (track : β → List α) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) : TrackAddress bs track n := by
  let p := lookup (bs.map track) n hn
  have hj : p.1 < bs.length := by
    obtain ⟨w, hw, _, _⟩ := lookup_spec (bs.map track) n hn
    obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hw
    simpa only [List.length_map] using hj
  let f := bs[p.1]
  have hf : bs[p.1]? = some f := List.getElem?_eq_getElem hj
  have hword : (bs.map track)[p.1]? = some (track f) := by
    simp [List.getElem?_map, hf]
  have hs : p.2 < (track f).length ∧ n = prefixLength (bs.map track) p.1 + p.2 := by
    obtain ⟨w, hw, hk, he⟩ := lookup_spec (bs.map track) n hn
    have hwf : w = track f := Option.some.inj (hw.symm.trans hword)
    exact ⟨hwf ▸ hk, he⟩
  exact ⟨p.1, p.2, f, hf, hs.1, hs.2⟩

namespace TrackAddress

variable {bs : List β} {track : β → List α} {n : ℕ}

def before (o : TrackAddress bs track n) : List α :=
  (track o.factor).take o.localIndex

def letter (o : TrackAddress bs track n) : α :=
  (track o.factor)[o.localIndex]'o.localValid

def after (o : TrackAddress bs track n) : List α :=
  (track o.factor).drop (o.localIndex + 1)

theorem split (o : TrackAddress bs track n) :
    track o.factor = o.before ++ o.letter :: o.after := by
  unfold before letter after
  rw [List.getElem_cons_drop o.localValid, List.take_append_drop]

theorem atWord (o : TrackAddress bs track n) :
    (bs.map track)[o.ordinal]? = some (track o.factor) := by
  simp [List.getElem?_map, o.atOrdinal]

theorem prefix_eq (o : TrackAddress bs track n) :
    (bs.map track).flatten.take n =
      ((bs.take o.ordinal).map track).flatten ++ o.before := by
  simpa only [List.map_take, before] using
    locate_prefix o.atWord o.localValid o.index_eq

theorem selected (o : TrackAddress bs track n) :
    (bs.map track).flatten[n]? = some o.letter := by
  rw [locate_letter o.atWord o.localValid o.index_eq,
    List.getElem?_eq_getElem o.localValid]
  rfl

theorem local_length (o : TrackAddress bs track n) : o.before.length = o.localIndex := by
  simp [before, Nat.min_eq_left (Nat.le_of_lt o.localValid)]

theorem unique (o o' : TrackAddress bs track n) :
    o.ordinal = o'.ordinal ∧ o.localIndex = o'.localIndex ∧ o.factor = o'.factor := by
  obtain ⟨hj, hk⟩ := locate_unique o.atWord o.localValid o.index_eq
    o'.atWord o'.localValid o'.index_eq
  refine ⟨hj, hk, ?_⟩
  exact Option.some.inj (o.atOrdinal.symm.trans (hj.symm ▸ o'.atOrdinal))

end TrackAddress

/-- Convert a numerical address into the existing concrete occurrence
structure, preserving the factor ordinal and its selected literal letter. -/
def TrackAddress.toFactorOccurrence
    {bs : List (List (Fin 3) × List (Fin 3))}
    {track : List (Fin 3) × List (Fin 3) → List (Fin 3)} {n : ℕ}
    (o : TrackAddress bs track n) : FactorOccurrence bs track where
  ordinal := o.ordinal
  factor := o.factor
  atOrdinal := o.atOrdinal
  before := o.before
  letter := o.letter
  after := o.after
  split := o.split

/-- Total lookup of an actual tile occurrence from a valid global index. -/
def locateTrack (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) : FactorOccurrence bs track :=
  (lookupTrack bs track n hn).toFactorOccurrence

theorem locateTrack_index (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    n = prefixLength (bs.map track) (locateTrack bs track n hn).ordinal +
      (locateTrack bs track n hn).before.length := by
  change n = prefixLength (bs.map track) (lookupTrack bs track n hn).ordinal +
    (lookupTrack bs track n hn).before.length
  rw [TrackAddress.local_length]
  exact (lookupTrack bs track n hn).index_eq

theorem locateTrack_prefix (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    (bs.map track).flatten.take n =
      ((bs.take (locateTrack bs track n hn).ordinal).map track).flatten ++
        (locateTrack bs track n hn).before :=
  (lookupTrack bs track n hn).prefix_eq

theorem locateTrack_selected (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    (bs.map track).flatten[n]? = some (locateTrack bs track n hn).letter :=
  (lookupTrack bs track n hn).selected

theorem locateTrack_letter (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    (locateTrack bs track n hn).letter = (bs.map track).flatten[n] := by
  have h := locateTrack_selected bs track n hn
  rw [List.getElem?_eq_getElem hn] at h
  exact (Option.some.inj h).symm

/-- Lookup preserves the actual physical position, for any length row. -/
theorem locateTrack_start (ℓ : Fin 3 → ℝ)
    (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    (locateTrack bs track n hn).start ℓ =
      physicalLength ℓ ((bs.map track).flatten.take n) := by
  rw [locateTrack_prefix bs track n hn, physicalLength_append]
  rfl

theorem locateTrack_finish (ℓ : Fin 3 → ℝ)
    (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) (n : ℕ)
    (hn : n < (bs.map track).flatten.length) :
    (locateTrack bs track n hn).finish ℓ =
      physicalLength ℓ ((bs.map track).flatten.take n) + ℓ (bs.map track).flatten[n] := by
  rw [FactorOccurrence.finish, locateTrack_start, locateTrack_letter]

/-- Lookup in the complete top track of the literal balanced reduction. -/
def redTop {u v : List (Fin 3)} (hbal : Equiv1 u v) (n : ℕ) (hn : n < u.length) :
    FactorOccurrence (red u v) Prod.fst :=
  locateTrack (red u v) Prod.fst n (by rw [red_top hbal.length_eq]; exact hn)

/-- Lookup in the complete bottom track of the literal balanced reduction. -/
def redBot {u v : List (Fin 3)} (hbal : Equiv1 u v) (n : ℕ) (hn : n < v.length) :
    FactorOccurrence (red u v) Prod.snd :=
  locateTrack (red u v) Prod.snd n (by rw [red_bot hbal.length_eq]; exact hn)

theorem redTop_prefix {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < u.length) :
    u.take n = (((red u v).take (redTop hbal n hn).ordinal).map Prod.fst).flatten ++
      (redTop hbal n hn).before := by
  calc
    u.take n = ((red u v).map Prod.fst).flatten.take n := by rw [red_top hbal.length_eq]
    _ = _ := locateTrack_prefix (red u v) Prod.fst n
      (by rw [red_top hbal.length_eq]; exact hn)

theorem redBot_prefix {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < v.length) :
    v.take n = (((red u v).take (redBot hbal n hn).ordinal).map Prod.snd).flatten ++
      (redBot hbal n hn).before := by
  calc
    v.take n = ((red u v).map Prod.snd).flatten.take n := by rw [red_bot hbal.length_eq]
    _ = _ := locateTrack_prefix (red u v) Prod.snd n
      (by rw [red_bot hbal.length_eq]; exact hn)

theorem redTop_letter {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < u.length) : (redTop hbal n hn).letter = u[n] := by
  apply Option.some.inj
  calc
    some (redTop hbal n hn).letter = ((red u v).map Prod.fst).flatten[n]? :=
      (locateTrack_selected (red u v) Prod.fst n
        (by rw [red_top hbal.length_eq]; exact hn)).symm
    _ = u[n]? := by rw [red_top hbal.length_eq]
    _ = some u[n] := List.getElem?_eq_getElem hn

theorem redBot_letter {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < v.length) : (redBot hbal n hn).letter = v[n] := by
  apply Option.some.inj
  calc
    some (redBot hbal n hn).letter = ((red u v).map Prod.snd).flatten[n]? :=
      (locateTrack_selected (red u v) Prod.snd n
        (by rw [red_bot hbal.length_eq]; exact hn)).symm
    _ = v[n]? := by rw [red_bot hbal.length_eq]
    _ = some v[n] := List.getElem?_eq_getElem hn

theorem redTop_start (ℓ : Fin 3 → ℝ) {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < u.length) :
    (redTop hbal n hn).start ℓ = physicalLength ℓ (u.take n) := by
  calc
    (redTop hbal n hn).start ℓ =
        physicalLength ℓ (((red u v).map Prod.fst).flatten.take n) :=
      locateTrack_start ℓ (red u v) Prod.fst n (by rw [red_top hbal.length_eq]; exact hn)
    _ = physicalLength ℓ (u.take n) := by rw [red_top hbal.length_eq]

theorem redBot_start (ℓ : Fin 3 → ℝ) {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (n : ℕ) (hn : n < v.length) :
    (redBot hbal n hn).start ℓ = physicalLength ℓ (v.take n) := by
  calc
    (redBot hbal n hn).start ℓ =
        physicalLength ℓ (((red u v).map Prod.snd).flatten.take n) :=
      locateTrack_start ℓ (red u v) Prod.snd n (by rw [red_bot hbal.length_eq]; exact hn)
    _ = physicalLength ℓ (v.take n) := by rw [red_bot hbal.length_eq]

/-- Valid global positions with strictly overlapping interiors resolve to
one actual reduced factor ordinal. No prelocated occurrence is assumed. -/
theorem red_common_factor_lookup (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (i j : ℕ) (hi : i < u.length) (hj : j < v.length)
    (hoverlap : ∃ x, physicalLength ℓ (u.take i) < x ∧
      x < physicalLength ℓ (u.take i) + ℓ u[i] ∧
      physicalLength ℓ (v.take j) < x ∧
      x < physicalLength ℓ (v.take j) + ℓ v[j]) :
    (redTop hbal i hi).ordinal = (redBot hbal j hj).ordinal ∧
      (redTop hbal i hi).factor = (redBot hbal j hj).factor := by
  apply red_common_factor ℓ hℓ hbal (redTop hbal i hi) (redBot hbal j hj)
  simpa only [FactorOccurrence.finish, redTop_start, redBot_start,
    redTop_letter, redBot_letter] using hoverlap

/-- Resolve a selected letter of a substituted word to its actual source
ordinal and within-image digit. Valid selected images suffice; erasing
images elsewhere are allowed. -/
def locateSubst (s : α → List α) (w : List α) (n : ℕ)
    (hn : n < (subst s w).length) : TrackAddress w s n :=
  lookupTrack w s n hn

theorem locateSubst_index (s : α → List α) (w : List α) (n : ℕ)
    (hn : n < (subst s w).length) :
    n = (subst s (w.take (locateSubst s w n hn).ordinal)).length +
      (locateSubst s w n hn).localIndex := by
  simpa only [prefixLength, subst, List.map_take, List.length_flatten] using
    (locateSubst s w n hn).index_eq

theorem locateSubst_prefix (s : α → List α) (w : List α) (n : ℕ)
    (hn : n < (subst s w).length) :
    (subst s w).take n = subst s (w.take (locateSubst s w n hn).ordinal) ++
      (s (locateSubst s w n hn).factor).take (locateSubst s w n hn).localIndex :=
  (locateSubst s w n hn).prefix_eq

theorem locateSubst_selected (s : α → List α) (w : List α) (n : ℕ)
    (hn : n < (subst s w).length) :
    (subst s w)[n]? = some (locateSubst s w n hn).letter :=
  (locateSubst s w n hn).selected

/-- Forward source/digit addressing and inverse lookup agree exactly. -/
theorem locate_subst_position (s : α → List α) (w : List α)
    (i p : ℕ) (hi : i < w.length) (hp : p < (s w[i]).length) :
    locate (w.map s) ((subst s (w.take i)).length + p) = some (i, p) := by
  apply locate_complete (w := s w[i])
  · simp [List.getElem?_map, List.getElem?_eq_getElem hi]
  · exact hp
  · simp [subst, prefixLength, List.map_take]

/-- Repeated chunk values keep different occurrence ordinals. -/
theorem control_repeated_chunk :
    locate ([[0, 1], [0, 1]] : List (List ℕ)) 2 = some (1, 0) := by decide

/-- An empty chunk does not capture a valid letter. -/
theorem control_empty_chunk :
    locate ([[], [7], [], [8, 9]] : List (List ℕ)) 1 = some (3, 0) := by decide

/-- The last valid index and the exterior endpoint have different results. -/
theorem control_last_and_exterior :
    locate ([[0, 1], [0, 1]] : List (List ℕ)) 3 = some (1, 1) ∧
      locate ([[0, 1], [0, 1]] : List (List ℕ)) 4 = none := by decide

end Psc.OccurrenceAddress
