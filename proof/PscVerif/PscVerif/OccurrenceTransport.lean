/-
# Literal occurrence transport and affine packet paths

The residual convention is top-prefix minus bottom-prefix, matching
`kernel/psc/target_packets.mojo`.  A packet digit edge is defined by source
letters, actual positions in their substitution images, and the incidence
formula; it does not contain a realization premise.

The converse lifting theorem starts from an actual marked balanced pair.
Strict overlap of the selected descendant interiors identifies a unique
factor occurrence in the complete reduction.  Balanced-prefix cancellation
then identifies its local residual with the independently computed packet.

Literature stop/go: `docs/c4-address-transport-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceAddress

namespace Psc.OccurrenceTransport

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceAddress Matrix
open scoped BigOperators

abbrev Word := List (Fin 3)
abbrev WordPair := Word × Word

/-- An actual selected letter, with both parts of its occurrence address. -/
structure Mark (w : Word) where
  before : Word
  letter : Fin 3
  after : Word
  split : w = before ++ letter :: after

/-- The numeric source occurrence is determined by the literal prefix. -/
def Mark.index {w : Word} (m : Mark w) : ℕ := m.before.length

theorem Mark.index_lt {w : Word} (m : Mark w) : m.index < w.length := by
  calc
    m.index < (m.before ++ m.letter :: m.after).length := by simp [Mark.index]
    _ = w.length := (congrArg List.length m.split).symm

theorem Mark.take_index {w : Word} (m : Mark w) : w.take m.index = m.before := by
  simpa [Mark.index] using congrArg (List.take m.index) m.split

theorem Mark.selected {w : Word} (m : Mark w) : w[m.index]'m.index_lt = m.letter := by
  have h : w[m.index]? = some m.letter := by
    simpa [Mark.index] using congrArg (fun x : Word => x[m.index]?) m.split
  rw [List.getElem?_eq_getElem m.index_lt] at h
  exact Option.some.inj h

/-- Valid source and digit occurrences construct the actual inflated mark. -/
def Mark.inflate (s : Fin 3 → Word) {w : Word} (m : Mark w)
    (d : Mark (s m.letter)) : Mark (subst s w) where
  before := subst s m.before ++ d.before
  letter := d.letter
  after := d.after ++ subst s m.after
  split := by
    calc
      subst s w = subst s (m.before ++ m.letter :: m.after) := congrArg (subst s) m.split
      _ = subst s m.before ++ (s m.letter ++ subst s m.after) := by
        rw [subst_append, subst_cons]
      _ = subst s m.before ++ ((d.before ++ d.letter :: d.after) ++ subst s m.after) :=
        congrArg (fun x => subst s m.before ++ (x ++ subst s m.after)) d.split
      _ = _ := by simp [List.append_assoc]

theorem Mark.inflate_index (s : Fin 3 → Word) {w : Word} (m : Mark w)
    (d : Mark (s m.letter)) :
    (m.inflate s d).index = (subst s (w.take m.index)).length + d.index := by
  rw [m.take_index]
  simp [Mark.inflate, Mark.index]

/-- The integral Parikh column, with no machine-integer bound. -/
def parikhZ (w : Word) : Fin 3 → ℤ := fun a => w.count a

theorem parikhZ_append (u v : Word) : parikhZ (u ++ v) = parikhZ u + parikhZ v := by
  funext a
  simp [parikhZ]

theorem parikhZ_eq_of_equiv1 {u v : Word} (h : Equiv1 u v) : parikhZ u = parikhZ v := by
  funext a
  simp only [parikhZ, h a]

theorem equiv1_of_parikhZ_eq {u v : Word} (h : parikhZ u = parikhZ v) : Equiv1 u v := by
  intro a
  have ha := congrFun h a
  change (u.count a : ℤ) = (v.count a : ℤ) at ha
  exact_mod_cast ha

def incidenceZ (s : Fin 3 → Word) : Matrix (Fin 3) (Fin 3) ℤ :=
  (inc s).map (Nat.castRingHom ℤ)

theorem parikhZ_subst (s : Fin 3 → Word) (w : Word) :
    parikhZ (subst s w) = incidenceZ s *ᵥ parikhZ w := by
  funext a
  simp [parikhZ, incidenceZ, count_subst, Matrix.mulVec, dotProduct]

/-- Physical track order is retained: top minus bottom, before any
normalization of the containing word pair. -/
def residual (u v : Word) : Fin 3 → ℤ := parikhZ u - parikhZ v

theorem residual_swap (u v : Word) : residual v u = -residual u v := by
  simp [residual, neg_sub]

theorem residual_subst (s : Fin 3 → Word) (u v : Word) :
    residual (subst s u) (subst s v) = incidenceZ s *ᵥ residual u v := by
  simp [residual, parikhZ_subst, Matrix.mulVec_sub]

/-- The affine formula is proved from literal word prefixes. -/
theorem residual_inflate (s : Fin 3 → Word) (u v p q : Word) :
    residual (subst s u ++ p) (subst s v ++ q) =
      incidenceZ s *ᵥ residual u v + residual p q := by
  rw [← residual_subst]
  simp only [residual, parikhZ_append]
  abel

/-- Trimming a whole balanced prefix preserves the physical residual. -/
theorem residual_trim {pu pv : Word} (h : Equiv1 pu pv) (u v : Word) :
    residual (pu ++ u) (pv ++ v) = residual u v := by
  simp only [residual, parikhZ_append, parikhZ_eq_of_equiv1 h]
  abel

structure MarkedPair where
  words : WordPair
  top : Mark words.1
  bottom : Mark words.2

structure Packet where
  top : Fin 3
  bottom : Fin 3
  delta : Fin 3 → ℤ

def MarkedPair.packet (m : MarkedPair) : Packet :=
  ⟨m.top.letter, m.bottom.letter, residual m.top.before m.bottom.before⟩

def Packet.swap (p : Packet) : Packet := ⟨p.bottom, p.top, -p.delta⟩

def MarkedPair.swap (m : MarkedPair) : MarkedPair :=
  ⟨m.words.swap, m.bottom, m.top⟩

theorem MarkedPair.packet_swap (m : MarkedPair) : m.swap.packet = m.packet.swap := by
  simp only [MarkedPair.swap, MarkedPair.packet, Packet.swap]
  rw [residual_swap]

/-- A digit transition contains no actual-parent or graph-realization
premise.  Its two digit marks are valid literal source-image occurrences. -/
def DigitStep (s : Fin 3 → Word) (p q : Packet) : Prop :=
  ∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    q = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ p.delta + residual dt.before db.before⟩

def MarkedPair.inflate (s : Fin 3 → Word) (m : MarkedPair)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter)) : MarkedPair :=
  ⟨(subst s m.words.1, subst s m.words.2), m.top.inflate s dt, m.bottom.inflate s db⟩

/-- Forward projection to the independently defined affine digit relation. -/
theorem MarkedPair.inflate_packet (s : Fin 3 → Word) (m : MarkedPair)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter)) :
    (m.inflate s dt db).packet =
      ⟨dt.letter, db.letter,
        incidenceZ s *ᵥ m.packet.delta + residual dt.before db.before⟩ := by
  simp only [MarkedPair.inflate, MarkedPair.packet, Mark.inflate]
  rw [residual_inflate]

theorem MarkedPair.inflate_digitStep (s : Fin 3 → Word) (m : MarkedPair)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter)) :
    DigitStep s m.packet (m.inflate s dt db).packet :=
  ⟨dt, db, m.inflate_packet s dt db⟩

/-- Swapping physical tracks swaps both digits and negates the residual. -/
theorem DigitStep.swap {s : Fin 3 → Word} {p q : Packet} (h : DigitStep s p q) :
    DigitStep s p.swap q.swap := by
  obtain ⟨dt, db, rfl⟩ := h
  refine ⟨db, dt, ?_⟩
  simp only [Packet.swap, Matrix.mulVec_neg]
  rw [residual_swap dt.before db.before]
  congr 1
  abel

/-! ## Exact physical meaning and normalization signs -/

def offset (ℓ : Fin 3 → ℝ) (r : Fin 3 → ℤ) : ℝ :=
  ℓ ⬝ᵥ (fun a => (r a : ℝ))

theorem offset_residual (ℓ : Fin 3 → ℝ) (u v : Word) :
    offset ℓ (residual u v) = physicalLength ℓ u - physicalLength ℓ v := by
  simp [offset, residual, parikhZ, physicalLength, dotProduct, mul_sub,
    Finset.sum_sub_distrib]

theorem offset_neg (ℓ : Fin 3 → ℝ) (r : Fin 3 → ℤ) :
    offset ℓ (-r) = -offset ℓ r := by
  simp [offset, dotProduct, Finset.sum_neg_distrib]

/-- A strict common interior in relative coordinates.  Since the residual
is top minus bottom, a point at top-relative coordinate `x` has
bottom-relative coordinate `x + offset ℓ p.delta`. -/
def Packet.Interior (ℓ : Fin 3 → ℝ) (p : Packet) : Prop :=
  ∃ x, 0 < x ∧ x < ℓ p.top ∧
    0 < x + offset ℓ p.delta ∧ x + offset ℓ p.delta < ℓ p.bottom

theorem Packet.interior_iff_bounds (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (p : Packet) : p.Interior ℓ ↔ -ℓ p.top < offset ℓ p.delta ∧
      offset ℓ p.delta < ℓ p.bottom := by
  constructor
  · rintro ⟨x, hx, hxt, hxb, hxbe⟩
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    have hinterval : max 0 (-offset ℓ p.delta) <
        min (ℓ p.top) (ℓ p.bottom - offset ℓ p.delta) := by
      rw [max_lt_iff]
      constructor <;> rw [lt_min_iff]
      · exact ⟨hpos p.top, by linarith⟩
      · exact ⟨by linarith, by linarith [hpos p.bottom]⟩
    obtain ⟨x, hlo, hhi⟩ := exists_between hinterval
    have h0 := (max_lt_iff.mp hlo).1
    have hδ := (max_lt_iff.mp hlo).2
    have ht := (lt_min_iff.mp hhi).1
    have hb := (lt_min_iff.mp hhi).2
    exact ⟨x, h0, ht, by linarith, by linarith⟩

theorem Packet.Interior.swap {ℓ : Fin 3 → ℝ} {p : Packet} (h : p.Interior ℓ) :
    p.swap.Interior ℓ := by
  obtain ⟨x, hx, hxt, hxb, hxbe⟩ := h
  refine ⟨x + offset ℓ p.delta, hxb, hxbe, ?_, ?_⟩
  · simp only [Packet.swap, offset_neg]
    linarith
  · simp only [Packet.swap, offset_neg]
    linarith

def MarkedPair.Overlaps (ℓ : Fin 3 → ℝ) (m : MarkedPair) : Prop :=
  ∃ x, physicalLength ℓ m.top.before < x ∧
    x < physicalLength ℓ m.top.before + ℓ m.top.letter ∧
    physicalLength ℓ m.bottom.before < x ∧
    x < physicalLength ℓ m.bottom.before + ℓ m.bottom.letter

/-- Relative packet overlap is equivalent to overlap of these actual
literal occurrences; no Perron independence premise is used here. -/
theorem MarkedPair.overlaps_iff (ℓ : Fin 3 → ℝ) (m : MarkedPair) :
    m.Overlaps ℓ ↔ m.packet.Interior ℓ := by
  unfold MarkedPair.Overlaps Packet.Interior MarkedPair.packet
  rw [offset_residual]
  constructor
  · rintro ⟨x, ht, hte, hb, hbe⟩
    refine ⟨x - physicalLength ℓ m.top.before, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨x, ht, hte, hb, hbe⟩
    refine ⟨x + physicalLength ℓ m.top.before, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `false` retains a representative's order and `true` swaps it. -/
def orient (flipped : Bool) (T : WordPair) : WordPair :=
  if flipped then T.swap else T

def orientationSign (flipped : Bool) : ℤ := if flipped then -1 else 1

theorem orient_comp (e f : Bool) (T : WordPair) :
    orient e (orient f T) = orient (Bool.xor e f) T := by
  cases e <;> cases f <;> rfl

theorem orientationSign_comp (e f : Bool) :
    orientationSign (Bool.xor e f) = orientationSign e * orientationSign f := by
  cases e <;> cases f <;> decide

/-- Swapping a parent preserves the selected child ordinal and swaps that
actual child.  Equal labels at distinct ordinals are never identified. -/
theorem child_ordinal_orient (s : Fin 3 → Word) (e : Bool)
    {T U : WordPair} {j : ℕ}
    (h : (red (subst s T.1) (subst s T.2))[j]? = some U) :
    (red (subst s (orient e T).1) (subst s (orient e T).2))[j]? =
      some (orient e U) := by
  cases e with
  | false => exact h
  | true =>
    change (red (subst s T.2) (subst s T.1))[j]? = some U.swap
    rw [red_swap, List.getElem?_map, h]
    rfl

/-- The parent orientation and raw-child normalization orientation compose
by multiplication of signs, as in the canonical target-packet transition. -/
theorem normalized_child_orientation (s : Fin 3 → Word) (e f : Bool)
    {T U : WordPair} {j : ℕ}
    (h : (red (subst s T.1) (subst s T.2))[j]? = some (orient f U)) :
    (red (subst s (orient e T).1) (subst s (orient e T).2))[j]? =
      some (orient (Bool.xor e f) U) ∧
      orientationSign (Bool.xor e f) = orientationSign e * orientationSign f := by
  exact ⟨by simpa only [orient_comp] using child_ordinal_orient s e h,
    orientationSign_comp e f⟩

/-! ## Constructive common-factor refinement -/

/-- Concrete lookup output: a single actual factor ordinal and the literal
prefix decompositions on both physical tracks.  Residual equality is a
derived theorem, not a field of this structure. -/
structure Localization (m : MarkedPair) where
  ordinal : ℕ
  target : MarkedPair
  atOrdinal : (red m.words.1 m.words.2)[ordinal]? = some target.words
  top_prefix : m.top.before =
    (((red m.words.1 m.words.2).take ordinal).map Prod.fst).flatten ++ target.top.before
  bottom_prefix : m.bottom.before =
    (((red m.words.1 m.words.2).take ordinal).map Prod.snd).flatten ++ target.bottom.before
  top_letter : target.top.letter = m.top.letter
  bottom_letter : target.bottom.letter = m.bottom.letter

/-- Actual global positions and strict overlap construct the common factor;
neither a common-factor membership nor a localization is assumed. -/
def MarkedPair.localize (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (m : MarkedPair) (hbal : Equiv1 m.words.1 m.words.2)
    (hoverlap : m.Overlaps ℓ) : Localization m := by
  let t := redTop hbal m.top.index m.top.index_lt
  let b := redBot hbal m.bottom.index m.bottom.index_lt
  have hcommon : t.ordinal = b.ordinal ∧ t.factor = b.factor := by
    apply red_common_factor_lookup ℓ hpos hbal m.top.index m.bottom.index
      m.top.index_lt m.bottom.index_lt
    simpa only [MarkedPair.Overlaps, m.top.take_index, m.bottom.take_index,
      m.top.selected, m.bottom.selected] using hoverlap
  let target : MarkedPair :=
    ⟨t.factor, ⟨t.before, t.letter, t.after, t.split⟩,
      ⟨b.before, b.letter, b.after, (congrArg Prod.snd hcommon.2).trans b.split⟩⟩
  refine ⟨t.ordinal, target, t.atOrdinal, ?_, ?_, ?_, ?_⟩
  · have h := redTop_prefix hbal m.top.index m.top.index_lt
    rw [m.top.take_index] at h
    exact h
  · have h := redBot_prefix hbal m.bottom.index m.bottom.index_lt
    rw [m.bottom.take_index] at h
    change m.bottom.before =
      (((red m.words.1 m.words.2).take b.ordinal).map Prod.snd).flatten ++ b.before at h
    rw [← hcommon.1] at h
    exact h
  · exact (redTop_letter hbal m.top.index m.top.index_lt).trans m.top.selected
  · exact (redBot_letter hbal m.bottom.index m.bottom.index_lt).trans m.bottom.selected

theorem Localization.packet_eq {m : MarkedPair} (L : Localization m)
    (hbal : Equiv1 m.words.1 m.words.2) : L.target.packet = m.packet := by
  have hp : Equiv1
      (((red m.words.1 m.words.2).take L.ordinal).map Prod.fst).flatten
      (((red m.words.1 m.words.2).take L.ordinal).map Prod.snd).flatten :=
    equiv1_join _ (fun T hT => (red_isBlock hbal T (List.mem_of_mem_take hT)).2.1)
  have hr : residual m.top.before m.bottom.before =
      residual L.target.top.before L.target.bottom.before := by
    rw [L.top_prefix, L.bottom_prefix]
    exact residual_trim hp _ _
  unfold MarkedPair.packet
  rw [L.top_letter, L.bottom_letter, hr]

/-- Full one-step witness: source and digit occurrences, common child
ordinal, local marks and the unchanged physical packet. -/
structure LiftedStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (m : MarkedPair) (q : Packet) where
  source_block : IsBlock m.words
  topDigit : Mark (s m.top.letter)
  bottomDigit : Mark (s m.bottom.letter)
  localization : Localization (m.inflate s topDigit bottomDigit)
  packet_eq : localization.target.packet = q
  interior : q.Interior ℓ

def LiftedStep.target {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {m : MarkedPair} {q : Packet}
    (e : LiftedStep s ℓ m q) : MarkedPair := e.localization.target

theorem LiftedStep.child {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {m : MarkedPair} {q : Packet}
    (e : LiftedStep s ℓ m q) : Child s m.words e.target.words :=
  List.mem_of_getElem? e.localization.atOrdinal

theorem LiftedStep.target_block {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} {q : Packet} (e : LiftedStep s ℓ m q) : IsBlock e.target.words :=
  red_isBlock (equiv1_subst s e.source_block.2.1) _ e.child

/-- The numeric address square commutes on the top track. -/
theorem LiftedStep.top_address {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} {q : Packet} (e : LiftedStep s ℓ m q) :
    (subst s (m.words.1.take m.top.index)).length + e.topDigit.index =
      (((red (subst s m.words.1) (subst s m.words.2)).take e.localization.ordinal).map
        Prod.fst).flatten.length + e.target.top.index := by
  rw [← m.top.inflate_index s e.topDigit]
  simpa only [Mark.index, MarkedPair.inflate, LiftedStep.target, List.length_append]
    using congrArg List.length e.localization.top_prefix

/-- The same square retains the independent bottom source/digit address. -/
theorem LiftedStep.bottom_address {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} {q : Packet} (e : LiftedStep s ℓ m q) :
    (subst s (m.words.2.take m.bottom.index)).length + e.bottomDigit.index =
      (((red (subst s m.words.1) (subst s m.words.2)).take e.localization.ordinal).map
        Prod.snd).flatten.length + e.target.bottom.index := by
  rw [← m.bottom.inflate_index s e.bottomDigit]
  simpa only [Mark.index, MarkedPair.inflate, LiftedStep.target, List.length_append]
    using congrArg List.length e.localization.bottom_prefix

/-- Soundness of a literal localized step against the affine digit relation. -/
theorem LiftedStep.digitStep {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} {q : Packet} (e : LiftedStep s ℓ m q) : DigitStep s m.packet q := by
  refine ⟨e.topDigit, e.bottomDigit, ?_⟩
  calc
    q = e.localization.target.packet := e.packet_eq.symm
    _ = (m.inflate s e.topDigit e.bottomDigit).packet :=
      e.localization.packet_eq (equiv1_subst s e.source_block.2.1)
    _ = _ := m.inflate_packet s e.topDigit e.bottomDigit

/-- Apply representative orientations to this actual addressed step.  The
source frame and the selected representative child are checked as literal
word equalities; the target frame is then a conclusion. -/
theorem LiftedStep.normalized_target {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} {q : Packet} (edge : LiftedStep s ℓ m q)
    (e f : Bool) (R U : WordPair) (hsource : m.words = orient e R)
    (hchild : (red (subst s R.1) (subst s R.2))[edge.localization.ordinal]? =
      some (orient f U)) :
    edge.target.words = orient (Bool.xor e f) U ∧
      orientationSign (Bool.xor e f) = orientationSign e * orientationSign f := by
  have hraw := edge.localization.atOrdinal
  change (red (subst s m.words.1) (subst s m.words.2))[edge.localization.ordinal]? =
    some edge.target.words at hraw
  rw [hsource] at hraw
  obtain ⟨hframe, hsign⟩ := normalized_child_orientation s e f hchild
  exact ⟨Option.some.inj (hraw.symm.trans hframe), hsign⟩

/-- Fixed-digit lifting.  Both supplied valid digit marks are retained
definitionally; this is stronger than choosing witnesses for `DigitStep`. -/
def lift_digits (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (m : MarkedPair) (hblock : IsBlock m.words)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter))
    (hinterior : (m.inflate s dt db).packet.Interior ℓ) :
    LiftedStep s ℓ m (m.inflate s dt db).packet := by
  have ho : (m.inflate s dt db).Overlaps ℓ :=
    ((m.inflate s dt db).overlaps_iff ℓ).mpr hinterior
  let L := (m.inflate s dt db).localize ℓ hpos (equiv1_subst s hblock.2.1) ho
  exact ⟨hblock, dt, db, L, L.packet_eq (equiv1_subst s hblock.2.1), hinterior⟩

theorem lift_digits_top (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (m : MarkedPair) (hblock : IsBlock m.words)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter))
    (hinterior : (m.inflate s dt db).packet.Interior ℓ) :
    (lift_digits s ℓ hpos m hblock dt db hinterior).topDigit = dt := rfl

theorem lift_digits_bottom (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (m : MarkedPair) (hblock : IsBlock m.words)
    (dt : Mark (s m.top.letter)) (db : Mark (s m.bottom.letter))
    (hinterior : (m.inflate s dt db).packet.Interior ℓ) :
    (lift_digits s ℓ hpos m hblock dt db hinterior).bottomDigit = db := rfl

/-- Completeness relative to an actual source occurrence.  Every affine
digit edge with a strict descendant interior constructs the literal child
and both addresses; no realizability premise is hidden in `DigitStep`. -/
theorem lift_digitStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (m : MarkedPair) (hblock : IsBlock m.words) {q : Packet}
    (hedge : DigitStep s m.packet q) (hinterior : q.Interior ℓ) :
    Nonempty (LiftedStep s ℓ m q) := by
  obtain ⟨dt, db, hq⟩ := hedge
  have hp : (m.inflate s dt db).packet = q := (m.inflate_packet s dt db).trans hq.symm
  have ho : (m.inflate s dt db).Overlaps ℓ := by
    apply ((m.inflate s dt db).overlaps_iff ℓ).mpr
    rw [hp]
    exact hinterior
  let L := (m.inflate s dt db).localize ℓ hpos (equiv1_subst s hblock.2.1) ho
  exact ⟨⟨hblock, dt, db, L,
    (L.packet_eq (equiv1_subst s hblock.2.1)).trans hp, hinterior⟩⟩

/-! ## Finite address histories and diagonal targets -/

def InteriorStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (p q : Packet) : Prop :=
  DigitStep s p q ∧ q.Interior ℓ

/-- Each constructor retains its source words, both source/digit addresses,
actual factor ordinal and local target marks.  The tail starts at that exact
marked target, preventing a splice based only on equal packet labels. -/
inductive AddressedPath (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) :
    MarkedPair → MarkedPair → Prop
  | refl (m : MarkedPair) : AddressedPath s ℓ m m
  | cons {m : MarkedPair} {q : Packet} {n : MarkedPair}
      (edge : LiftedStep s ℓ m q) (tail : AddressedPath s ℓ edge.target n) :
      AddressedPath s ℓ m n

theorem AddressedPath.child_path {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m n : MarkedPair} (p : AddressedPath s ℓ m n) :
    Relation.ReflTransGen (Child s) m.words n.words := by
  induction p with
  | refl => exact .refl
  | cons e _ ih => exact .head e.child ih

theorem AddressedPath.packet_path {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {m n : MarkedPair} (p : AddressedPath s ℓ m n) :
    Relation.ReflTransGen (InteriorStep s ℓ) m.packet n.packet := by
  induction p with
  | refl => exact .refl
  | cons e _ ih =>
    refine .head ?_ ih
    have hp : e.target.packet = _ := e.packet_eq
    change DigitStep s _ e.target.packet ∧ e.target.packet.Interior ℓ
    rw [hp]
    exact ⟨e.digitStep, e.interior⟩

/-- Finite-path completeness from any actual source realization.  It
constructs a coherent literal address history for the supplied independent
affine/interior path.  No graph finiteness or universal productivity is
assumed or concluded. -/
theorem packet_path_lift (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    {p q : Packet} (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q)
    (m : MarkedPair) (hp : m.packet = p) (hblock : IsBlock m.words) :
    ∃ n : MarkedPair, AddressedPath s ℓ m n ∧ IsBlock n.words ∧ n.packet = q := by
  revert m hp hblock
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro m hp hblock
    exact ⟨m, .refl m, hblock, hp⟩
  | @head p r hedge _ ih =>
    intro m hp hblock
    have hstep : DigitStep s m.packet r := by rw [hp]; exact hedge.1
    obtain ⟨e⟩ := lift_digitStep s ℓ hpos m hblock hstep hedge.2
    obtain ⟨n, hmn, hn, hnq⟩ := ih e.target e.packet_eq e.target_block
    exact ⟨n, .cons e hmn, hn, hnq⟩

def Packet.Diagonal (p : Packet) : Prop := p.top = p.bottom ∧ p.delta = 0

/-- A diagonal packet realized inside an irreducible balanced pair forces
that pair to be a singleton coincidence.  Coincidence of the containing
pair is a conclusion, not an endpoint realization premise. -/
theorem MarkedPair.diagonal_coincident (m : MarkedPair) (hblock : IsBlock m.words)
    (hdiag : m.packet.Diagonal) : m.words.1 = m.words.2 := by
  have hl : m.top.letter = m.bottom.letter := hdiag.1
  have hr : parikhZ m.top.before - parikhZ m.bottom.before = 0 := hdiag.2
  have hp : Equiv1 m.top.before m.bottom.before :=
    equiv1_of_parikhZ_eq (sub_eq_zero.mp hr)
  have hw := hblock.2.1
  rw [m.top.split, m.bottom.split, ← hl] at hw
  have hd : ([m.top.letter], [m.top.letter]) ∈ red m.words.1 m.words.2 := by
    have he : red m.words.1 m.words.2 =
        red (m.top.before ++ m.top.letter :: m.top.after)
          (m.bottom.before ++ m.top.letter :: m.bottom.after) := by
      calc
        red m.words.1 m.words.2 =
            red (m.top.before ++ m.top.letter :: m.top.after)
              (m.bottom.before ++ m.bottom.letter :: m.bottom.after) :=
          congrArg₂ red m.top.split m.bottom.split
        _ = _ := by rw [← hl]
    rw [he, red_split_at_diagonal hp hw]
    simp
  rw [red_of_isBlock hblock] at hd
  have heq := List.mem_singleton.mp hd
  exact (congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq)

/-- The abstract finite diagonal route yields an actual literal child path
to a coincident irreducible pair. -/
theorem packet_path_literal_target (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) (m : MarkedPair) (hblock : IsBlock m.words) {q : Packet}
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) m.packet q)
    (hdiag : q.Diagonal) :
    ∃ U : WordPair, Relation.ReflTransGen (Child s) m.words U ∧
      IsBlock U ∧ U.1 = U.2 := by
  obtain ⟨n, hnpath, hnblock, hnq⟩ := packet_path_lift s ℓ hpos hpath m rfl hblock
  refine ⟨n.words, hnpath.child_path, hnblock, n.diagonal_coincident hnblock ?_⟩
  rw [hnq]
  exact hdiag

/-- Compose the concrete finite lift with first-diagonal newborn extraction.
Nonerasure is needed for the interior newborn, not for affine transport or
common-factor lookup. -/
theorem packet_path_newborn (s : Fin 3 → Word) (hs : ∀ a, s a ≠ [])
    (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a) (m : MarkedPair)
    (hblock : IsBlock m.words) (hne : m.words.1 ≠ m.words.2) {q : Packet}
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) m.packet q)
    (hdiag : q.Diagonal) :
    ∃ P D k, Relation.ReflTransGen (Child s) m.words P ∧ IsBlock P ∧ P.1 ≠ P.2 ∧
      Child s P D ∧ D.1 = D.2 ∧ NewbornCut s P.1 P.2 k ∧
      (SyncPlus (subst s P.1) (subst s P.2) k ∨
        SyncMinus (subst s P.1) (subst s P.2) k) := by
  obtain ⟨U, hchild, _, hco⟩ := packet_path_literal_target s ℓ hpos m hblock hpath hdiag
  exact child_path_newborn s hs hchild hco hblock hne

end Psc.OccurrenceTransport
