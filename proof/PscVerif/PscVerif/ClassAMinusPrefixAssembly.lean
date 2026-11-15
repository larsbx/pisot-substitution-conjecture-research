/-
# Original ordered prefixes along finite literal occurrence paths

The endpoint identity is proved first with its full, possibly nonzero,
terminal packet.  The zero specialization follows only afterwards.
Every selected mark is in the original iterated image of its source
letter; the path keeps both original zero-based occurrence ordinals.

Pre-code source gate: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusConstantRecurrence

namespace Psc.ClassAMinusPrefixAssembly

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape Matrix

/-- Literal finite substitution iteration, starting at one source letter. -/
def image (s : Fin 3 → Word) (k : ℕ) (a : Fin 3) : Word :=
  (subst s)^[k] [a]

theorem image_eq_iterate (s : Fin 3 → Word) (k : ℕ) (a : Fin 3) :
    image s k a = (subst s)^[k] [a] := rfl

theorem image_succ (s : Fin 3 → Word) (k : ℕ) (a : Fin 3) :
    image s (k+1) a = subst s (image s k a) :=
  Function.iterate_succ_apply' _ _ _

/-- Inflation preserves every prefix word, selected letter, and suffix. -/
def inflateImageMark (s : Fin 3 → Word) {k : ℕ} {a : Fin 3}
    (top : Mark (image s k a)) (digit : Mark (s top.letter)) :
    Mark (image s (k+1) a) where
  before := subst s top.before ++ digit.before
  letter := digit.letter
  after := digit.after ++ subst s top.after
  split := by rw [image_succ]; exact (top.inflate s digit).split

theorem inflateImageMark_index (s : Fin 3 → Word) {k : ℕ} {a : Fin 3}
    (top : Mark (image s k a)) (digit : Mark (s top.letter)) :
    (inflateImageMark s top digit).index =
      (subst s top.before).length + digit.index := by
  simp [inflateImageMark, Mark.index]

def rootMark (a : Fin 3) : Mark [a] where
  before := []
  letter := a
  after := []
  split := rfl

/-- Original top and bottom ordinals are retained in their physical order.
The source of the next edge is the exact preceding packet, not an equal
projection or an independently selected label. -/
inductive OrderedPath (s : Fin 3 → Word) :
    Packet → List (ℕ × ℕ) → Packet → Prop
  | nil (p : Packet) : OrderedPath s p [] p
  | snoc {p r q : Packet} {xs : List (ℕ × ℕ)}
      (path : OrderedPath s p xs r) (i j : ℕ)
      (edge : IndexedDigitStep s r i j q) :
      OrderedPath s p (xs ++ [(i,j)]) q

/-- Strictness at the source and every intermediate packet is attached
to the same original ordinal transcript. Even the empty path has a strict
source, so it cannot provide a vacuous overlap certificate. -/
inductive OrderedInteriorPath (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) :
    Packet → List (ℕ × ℕ) → Packet → Prop
  | nil (p : Packet) (interior : p.Interior ℓ) : OrderedInteriorPath s ℓ p [] p
  | snoc {p r q : Packet} {xs : List (ℕ × ℕ)}
      (path : OrderedInteriorPath s ℓ p xs r) (i j : ℕ)
      (edge : IndexedDigitStep s r i j q) (interior : q.Interior ℓ) :
      OrderedInteriorPath s ℓ p (xs ++ [(i,j)]) q

theorem OrderedInteriorPath.orderedPath {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {p q : Packet} {xs : List (ℕ × ℕ)} (hp : OrderedInteriorPath s ℓ p xs q) :
    OrderedPath s p xs q := by
  induction hp with
  | nil => exact .nil _
  | snoc _ i j he _ ih => exact .snoc ih i j he

theorem OrderedInteriorPath.source_interior {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {p q : Packet} {xs : List (ℕ × ℕ)} (hp : OrderedInteriorPath s ℓ p xs q) :
    p.Interior ℓ := by
  induction hp with
  | nil hi => exact hi
  | snoc _ _ _ _ _ ih => exact ih

theorem OrderedInteriorPath.interiorPath {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {p q : Packet} {xs : List (ℕ × ℕ)} (hp : OrderedInteriorPath s ℓ p xs q) :
    Relation.ReflTransGen (InteriorStep s ℓ) p q := by
  induction hp with
  | nil => exact .refl
  | snoc _ _ _ he hi ih => exact ih.tail ⟨he.digitStep, hi⟩

theorem OrderedPath.digitPath {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    Relation.ReflTransGen (DigitStep s) p q := by
  induction hp with
  | nil => exact .refl
  | snoc _ _ _ he ih => exact ih.tail he.digitStep

/-- Concatenation requires the identical full middle packet and preserves
the complete order of both ordinal transcripts. -/
theorem OrderedPath.trans {s : Fin 3 → Word} {p q r : Packet}
    {xs ys : List (ℕ × ℕ)} (hp : OrderedPath s p xs q)
    (hq : OrderedPath s q ys r) : OrderedPath s p (xs ++ ys) r := by
  induction hq with
  | nil => simpa using hp
  | snoc _ i j he ih =>
    simpa only [List.append_assoc] using OrderedPath.snoc ih i j he

/-- Extract a complete ordinal transcript from any finite actual-digit path. -/
theorem digit_path_has_ordered_path {s : Fin 3 → Word} {p q : Packet}
    (hp : Relation.ReflTransGen (DigitStep s) p q) :
    ∃ xs, OrderedPath s p xs q := by
  induction hp with
  | refl => exact ⟨[], .nil _⟩
  | tail _ he ih =>
    obtain ⟨xs, hx⟩ := ih
    obtain ⟨dt, db, hq⟩ := he
    exact ⟨xs ++ [(dt.index, db.index)],
      .snoc hx dt.index db.index ⟨dt, db, rfl, rfl, hq⟩⟩

/-- The full affine packet computed from genuine original depth-k marks. -/
def assembledPacket (s : Fin 3 → Word) (p : Packet) (k : ℕ)
    (top : Mark (image s k p.top)) (bottom : Mark (image s k p.bottom)) : Packet :=
  ⟨top.letter, bottom.letter,
    incidenceZ s ^ k *ᵥ p.delta + residual top.before bottom.before⟩

/-- One original track, including every local ordinal and the complete
accumulated prefix, current letter and suffix. The next local mark is in
the image of this exact current letter. -/
inductive MarkTrace (s : Fin 3 → Word) (source : Fin 3) :
    List ℕ → Word → Fin 3 → Word → Prop
  | root : MarkTrace s source [] [] source []
  | snoc {xs : List ℕ} {pre post : Word} {a : Fin 3}
      (trace : MarkTrace s source xs pre a post) (digit : Mark (s a)) :
      MarkTrace s source (xs ++ [digit.index])
        (subst s pre ++ digit.before) digit.letter (digit.after ++ subst s post)

/-- The nested original-image marks and both ordinal tracks are constructed
together from the supplied ordered path. Thus the final marks are tied to
every recorded ordinal, not merely to the transcript's length. -/
theorem ordered_path_traced_affine {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    ∃ (top : Mark (image s xs.length p.top))
      (bottom : Mark (image s xs.length p.bottom)),
      MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
      MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
      q = assembledPacket s p xs.length top bottom := by
  induction hp with
  | nil =>
    refine ⟨rootMark p.top, rootMark p.bottom, .root, .root, ?_⟩
    simp [assembledPacket, rootMark, OccurrenceTransport.residual]
  | @snoc r q xs path i j he ih =>
    obtain ⟨top, bottom, htop, hbottom, rfl⟩ := ih
    obtain ⟨dt, db, hi, hj, rfl⟩ := he
    have hlen : (xs ++ [(i,j)]).length = xs.length+1 := by simp
    rw [hlen]
    refine ⟨inflateImageMark s top dt, inflateImageMark s bottom db, ?_, ?_, ?_⟩
    · have ht := MarkTrace.snoc htop dt
      have hi' : @Mark.index (s top.letter) dt = i := hi
      rw [hi'] at ht
      simpa only [List.map_append, List.map_cons, List.map_nil,
        inflateImageMark] using ht
    · have hb := MarkTrace.snoc hbottom db
      have hj' : @Mark.index (s bottom.letter) db = j := hj
      rw [hj'] at hb
      simpa only [List.map_append, List.map_cons, List.map_nil,
        inflateImageMark] using hb
    · apply congrArg (Packet.mk dt.letter db.letter)
      change incidenceZ s *ᵥ
          (incidenceZ s ^ xs.length *ᵥ p.delta + residual top.before bottom.before) +
          residual dt.before db.before =
        incidenceZ s ^ (xs.length+1) *ᵥ p.delta +
          residual (subst s top.before ++ dt.before) (subst s bottom.before ++ db.before)
      rw [residual_inflate, Matrix.mulVec_add, pow_succ', Matrix.mulVec_mulVec]
      abel

/-- Every ordered path has genuine nested marks in the original images.
The complete terminal offset is retained; no zero-endpoint premise enters
this statement and no projection replaces the integral vector identity. -/
theorem ordered_path_affine {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    ∃ (top : Mark (image s xs.length p.top))
      (bottom : Mark (image s xs.length p.bottom)),
      q = assembledPacket s p xs.length top bottom := by
  obtain ⟨top, bottom, _, _, hq⟩ := ordered_path_traced_affine hp
  exact ⟨top, bottom, hq⟩

/-- Full original-image assembly with type-level correspondence to both
ordered ordinal tracks. The complete affine equation is retained even when
the terminal offset is nonzero. -/
theorem ordered_path_traced_original_prefixes {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
      (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
      MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
      MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter = q.top ∧ bottom.letter = q.bottom ∧
      q.delta = incidenceZ s ^ xs.length *ᵥ p.delta +
        (parikhZ top.before - parikhZ bottom.before) := by
  obtain ⟨top, bottom, htop, hbottom, hq⟩ := ordered_path_traced_affine hp
  exact ⟨top, bottom, htop, hbottom, (congrArg Packet.top hq).symm,
    (congrArg Packet.bottom hq).symm, congrArg Packet.delta hq⟩

/-- Only the terminal zero premise changes the affine equation to the
manuscript's source identity. Both original ordinal tracks remain attached
to the same full prefix/letter/suffix marks. -/
theorem ordered_path_traced_zero_original_prefixes {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) (hq : q.delta = 0) :
    ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
      (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
      MarkTrace s p.top (xs.map Prod.fst) top.before top.letter top.after ∧
      MarkTrace s p.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter = q.top ∧ bottom.letter = q.bottom ∧
      incidenceZ s ^ xs.length *ᵥ (-p.delta) =
        parikhZ top.before - parikhZ bottom.before := by
  obtain ⟨top, bottom, htop, hbottom, ht, hb, he⟩ :=
    ordered_path_traced_original_prefixes hp
  refine ⟨top, bottom, htop, hbottom, ht, hb, ?_⟩
  rw [hq] at he
  have hh := congrArg (fun v : Fin 3 → ℤ => -(incidenceZ s ^ xs.length *ᵥ p.delta) + v) he
  simpa only [add_zero, neg_add_cancel_left, Matrix.mulVec_neg] using hh

/-- The exact terminal identity written in terms of the original source
offset, both original prefix words and both original selected letters. -/
theorem ordered_path_original_prefixes {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
      (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
      top.letter = q.top ∧ bottom.letter = q.bottom ∧
      q.delta = incidenceZ s ^ xs.length *ᵥ p.delta +
        (parikhZ top.before - parikhZ bottom.before) := by
  have hx : ∃ (top : Mark (image s xs.length p.top))
      (bottom : Mark (image s xs.length p.bottom)),
      top.letter = q.top ∧ bottom.letter = q.bottom ∧
      q.delta = incidenceZ s ^ xs.length *ᵥ p.delta +
        (parikhZ top.before - parikhZ bottom.before) := by
    obtain ⟨top, bottom, hq⟩ := ordered_path_affine hp
    exact ⟨top, bottom, (congrArg Packet.top hq).symm,
      (congrArg Packet.bottom hq).symm, congrArg Packet.delta hq⟩
  exact hx

/-- Zero is used only here.  The source sign is converted back to the
bottom-minus-top convention of the Class-A manuscript.  Unequal terminal
letters are retained; integral zero alone does not identify them. -/
theorem ordered_path_zero_original_prefixes {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) (hq : q.delta = 0) :
    ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
      (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
      top.letter = q.top ∧ bottom.letter = q.bottom ∧
      incidenceZ s ^ xs.length *ᵥ (-p.delta) =
        parikhZ top.before - parikhZ bottom.before := by
  obtain ⟨top, bottom, ht, hb, he⟩ := ordered_path_original_prefixes hp
  refine ⟨top, bottom, ht, hb, ?_⟩
  rw [hq] at he
  have hh := congrArg (fun v : Fin 3 → ℤ => -(incidenceZ s ^ xs.length *ᵥ p.delta) + v) he
  simpa only [add_zero, neg_add_cancel_left, Matrix.mulVec_neg] using hh

/-- A supplied digit path yields both an explicit ordinal transcript and
the full original-image affine identity for that transcript. -/
theorem digit_path_original_prefixes {s : Fin 3 → Word} {p q : Packet}
    (hp : Relation.ReflTransGen (DigitStep s) p q) :
    ∃ xs, OrderedPath s p xs q ∧
      ∃ (top : Mark ((subst s)^[xs.length] [p.top]))
        (bottom : Mark ((subst s)^[xs.length] [p.bottom])),
        top.letter = q.top ∧ bottom.letter = q.bottom ∧
        q.delta = incidenceZ s ^ xs.length *ᵥ p.delta +
          (parikhZ top.before - parikhZ bottom.before) := by
  obtain ⟨xs, hx⟩ := digit_path_has_ordered_path hp
  exact ⟨xs, hx, ordered_path_original_prefixes hx⟩

/-- The lower-chamber signed constant descent now carries original depth-m
prefix witnesses. Its arithmetic run-range premise is unchanged. -/
theorem constant_original_prefixes (n d : ℕ) (hd : 5 ≤ d) (H : ℤ)
    (hn : 2*(d : ℤ)*|H| ≤ (n : ℤ)) :
    ∃ xs, OrderedPath (sigma n d) (packet 2 2 H (-H) 0) xs (packet 2 2 0 0 0) ∧
      ∃ (top : Mark ((subst (sigma n d))^[xs.length] [2]))
        (bottom : Mark ((subst (sigma n d))^[xs.length] [2])),
        top.letter = 2 ∧ bottom.letter = 2 ∧
        incidenceZ (sigma n d) ^ xs.length *ᵥ ![H, -H, 0] =
          parikhZ top.before - parikhZ bottom.before := by
  obtain ⟨xs, hx⟩ := digit_path_has_ordered_path
    (ClassAMinusConstantRecurrence.constant_digit_path n d hd H hn)
  have hz : (packet 2 2 0 0 0).delta = 0 := by
    funext a
    fin_cases a <;> rfl
  obtain ⟨top, bottom, ht, hb, he⟩ := ordered_path_zero_original_prefixes hx hz
  refine ⟨xs, hx, top, bottom, ht, hb, ?_⟩
  have hs : -(packet 2 2 H (-H) 0).delta = ![H, -H, 0] := by
    funext a
    fin_cases a <;> simp [packet]
  simpa only [hs] using he

/-- A strict final occurrence pulls back along the very same ordered
transcript. No independently supplied strict source or finite carrier is
needed for this conversion. -/
theorem ordered_path_interior (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    {p q : Packet} {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q)
    (hq : q.Interior ℓ) :
    p.Interior ℓ ∧ Relation.ReflTransGen (InteriorStep s ℓ) p q :=
  ClassAMinusConstantRecurrence.digit_path_interior
    s ℓ β hpos hβ hscale hp.digitPath hq

/-- Backward strictness is proved at every step of the original ordered
transcript. This produces an indexed interior path rather than an
independent unindexed existence claim with only the same endpoints. -/
theorem ordered_path_indexed_interior (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    {p q : Packet} {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q)
    (hq : q.Interior ℓ) : OrderedInteriorPath s ℓ p xs q := by
  revert hq
  induction hp with
  | nil => exact fun hq => .nil _ hq
  | snoc _ i j he ih =>
    intro hq
    have hr := interior_source_of_digitStep s ℓ β hpos hβ hscale he.digitStep hq
    exact .snoc (ih hr) i j he hq

/-! ## Independent controls for weakened path contracts -/

/-- Equal prefix word lengths and equal terminal letters do not
establish equality of the full integral prefix vectors. Both marks here
are genuine occurrences, so the failure is not a malformed-word artifact. -/
theorem incomplete_prefix_control :
    ∃ (top : Mark ([0,2] : Word)) (bottom : Mark ([1,2] : Word)),
      top.letter = bottom.letter ∧ top.before.length = bottom.before.length ∧
      parikhZ top.before - parikhZ bottom.before ≠ 0 := by
  refine ⟨⟨[0], 2, [], rfl⟩, ⟨[1], 2, [], rfl⟩, rfl, rfl, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [parikhZ] at hh

def identitySubstitution (a : Fin 3) : Word := [a]

theorem singleton_mark (a : Fin 3) (m : Mark [a]) :
    m.before = [] ∧ m.letter = a ∧ m.after = [] := by
  have hlen := congrArg List.length m.split
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have ht : m.before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hb : m.after = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hl := m.split
  rw [ht, hb] at hl
  have ha : m.letter = a := by simpa using hl.symm
  exact ⟨ht, ha, hb⟩

/-- Every original local index of the identity substitution is zero. -/
theorem identity_mark_trace_indices {a b : Fin 3} {xs : List ℕ} {pre post : Word}
    (htrace : MarkTrace identitySubstitution a xs pre b post) :
    ∀ i ∈ xs, i = 0 := by
  induction htrace with
  | root => simp
  | snoc _ digit ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ih i hi
    · have he : i = digit.index := List.mem_singleton.mp hi
      have ht := (singleton_mark _ digit).1
      simp only [he, Mark.index, ht, List.length_nil]

theorem identity_incidence : incidenceZ identitySubstitution = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [incidenceZ, identitySubstitution, inc, Matrix.one_apply]

theorem identity_digit_step_eq {p q : Packet}
    (he : DigitStep identitySubstitution p q) : q = p := by
  obtain ⟨dt, db, hq⟩ := he
  obtain ⟨ht, htl, _⟩ := singleton_mark p.top dt
  obtain ⟨hb, hbl, _⟩ := singleton_mark p.bottom db
  simpa [ht, hb, htl, hbl, identity_incidence, OccurrenceTransport.residual] using hq

theorem identity_ordered_path_eq {p q : Packet} {xs : List (ℕ × ℕ)}
    (hp : OrderedPath identitySubstitution p xs q) : q = p := by
  induction hp with
  | nil => rfl
  | snoc _ _ _ he ih => exact (identity_digit_step_eq he.digitStep).trans ih

theorem identity_indexed_step (p : Packet) :
    IndexedDigitStep identitySubstitution p 0 0 p := by
  refine ⟨rootMark p.top, rootMark p.bottom, rfl, rfl, ?_⟩
  simp [rootMark, identity_incidence, OccurrenceTransport.residual]

/-- A genuine one-step original mark has the full zero-prefix identity.
Changing its ordinal transcript to a different list of the same length
is rejected, even while leaving the final prefix, letter and suffix fixed. -/
theorem wrong_transcript_control :
    MarkTrace identitySubstitution 2 [0] [] 2 [] ∧
    incidenceZ identitySubstitution^1 *ᵥ (0 : Fin 3 → ℤ) = parikhZ []-parikhZ [] ∧
    ([0] : List ℕ).length = ([1] : List ℕ).length ∧
    ¬ MarkTrace identitySubstitution 2 [1] [] 2 [] := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · have hroot : MarkTrace identitySubstitution 2 [] [] 2 [] := .root
    simpa [rootMark, Mark.index, subst] using MarkTrace.snoc hroot (rootMark 2)
  · simp
  · intro htrace
    have hh := identity_mark_trace_indices htrace 1 (by simp)
    omega

/-- Both edges are valid, with the same original ordinals and the same
tile types. Their integral middle packets differ, so no concatenation is
accepted even though a coordinate-dropping view could splice the labels. -/
theorem noncomposable_paths_control :
    IndexedDigitStep identitySubstitution (packet 2 2 0 0 0) 0 0
      (packet 2 2 0 0 0) ∧
    IndexedDigitStep identitySubstitution (packet 2 2 0 1 (-1)) 0 0
      (packet 2 2 0 1 (-1)) ∧
    ¬ OrderedPath identitySubstitution (packet 2 2 0 0 0) [(0,0),(0,0)]
      (packet 2 2 0 1 (-1)) := by
  refine ⟨identity_indexed_step _, identity_indexed_step _, ?_⟩
  intro hp
  have he := identity_ordered_path_eq hp
  have hh := congrArg (fun p : Packet => p.delta 1) he
  norm_num [packet] at hh

/-- An empty transcript cannot erase a nonzero full source offset. -/
theorem empty_transcript_control (s : Fin 3 → Word) :
    ¬ OrderedPath s (packet 2 2 0 1 (-1)) [] (packet 2 2 0 0 0) := by
  intro hp
  obtain ⟨top, bottom, he⟩ := ordered_path_affine hp
  obtain ⟨ht, _, _⟩ := singleton_mark 2 top
  obtain ⟨hb, _, _⟩ := singleton_mark 2 bottom
  have hh := congrArg (fun p : Packet => p.delta 1) he
  norm_num [assembledPacket, packet, ht, hb, OccurrenceTransport.residual] at hh

theorem mixed_letter_zero_control :
    (packet 0 1 0 0 0).delta = 0 ∧ ¬ (packet 0 1 0 0 0).Diagonal := by
  constructor
  · funext a
    fin_cases a <;> rfl
  · intro h
    have hletter := h.1
    norm_num [packet] at hletter

end Psc.ClassAMinusPrefixAssembly
