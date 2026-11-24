/-
# Count-preserving literal entry paths and complete original tracks

The arithmetic entry argument counts only actual substitution edges. This
module extracts the same number of original ordered occurrence pairs and
reuses the existing prefix assembly to retain both complete tracks and
all three terminal offset coordinates. Reversal maps every pair of indices,
swaps the two original marks, and negates the complete offset; it adds no edge.
-/
import PscVerif.ClassAPlusUpperEntry
import PscVerif.ClassAPlusUpperCycles

namespace Psc.ClassAPlusUpperEntryTransport

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles Matrix

/-- An edge carries the actual ordered local indices. -/
def LiteralEdge (s : Fin 3 → Word) (p q : Packet) : Prop :=
  ∃ i j : ℕ, IndexedDigitStep s p i j q

/-- Append one genuine edge without adding any frame-change step. -/
theorem steps_snoc {α : Type} {edge : α → α → Prop}
    {k : ℕ} {source middle target : α}
    (hp : ClassAPlusUpperEntry.Steps edge k source middle)
    (he : edge middle target) :
    ClassAPlusUpperEntry.Steps edge (k+1) source target := by
  induction hp with
  | nil => exact .cons he (.nil _)
  | cons h _ ih => exact .cons h (ih he)

/-- Lift a strict original-occurrence transcript to any covering carrier.
The supplied initial carrier state is retained, and each subsequently
chosen state projects to the identical complete packet. -/
theorem ordered_interior_to_steps {α : Type} {edge : α → α → Prop}
    {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} (packet : α → Packet)
    (cover : ∀ p, p.Interior ℓ → ∃ a, packet a = p)
    (realize : ∀ a b, LiteralEdge s (packet a) (packet b) → edge a b)
    {p q : Packet} {xs : List (ℕ × ℕ)}
    (hp : OrderedInteriorPath s ℓ p xs q)
    (source : α) (hsource : packet source = p) :
    ∃ target : α, packet target = q ∧
      ClassAPlusUpperEntry.Steps edge xs.length source target := by
  induction hp with
  | nil => exact ⟨source, hsource, .nil _⟩
  | @snoc middle q xs hp i j he hi ih =>
    obtain ⟨mid, hmid, hpath⟩ := ih
    obtain ⟨target, htarget⟩ := cover q hi
    refine ⟨target, htarget, ?_⟩
    have hedge : edge mid target := realize mid target (by
      rw [hmid, htarget]
      exact ⟨i, j, he⟩)
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      using steps_snoc hpath hedge

/-- Extraction preserves the exact number of actual substitution edges.
The optional carrier projection permits the growth argument to work with
strict, oriented packets without changing the meaning of an edge. -/
theorem steps_ordered_path {α : Type} {edge : α → α → Prop}
    {s : Fin 3 → Word} (packet : α → Packet)
    (literal : ∀ a b, edge a b → LiteralEdge s (packet a) (packet b))
    {k : ℕ} {source target : α}
    (hp : ClassAPlusUpperEntry.Steps edge k source target) :
    ∃ xs : List (ℕ × ℕ), xs.length = k ∧
      OrderedPath s (packet source) xs (packet target) := by
  induction hp with
  | nil => exact ⟨[], rfl, .nil _⟩
  | @cons k source middle target he hp ih =>
    obtain ⟨i, j, hij⟩ := literal source middle he
    obtain ⟨xs, hlen, hxs⟩ := ih
    refine ⟨[(i,j)] ++ xs, ?_, ?_⟩
    · simp [hlen, Nat.add_comm]
    · exact (OrderedPath.snoc (.nil (packet source)) i j hij).trans hxs

/-- The original prefix words, chosen letters, suffixes, and full terminal
offset are tied to every local ordinal of this precise transcript. -/
def OriginalTraces (s : Fin 3 → Word) (source : Packet)
    (xs : List (ℕ × ℕ)) (target : Packet) : Prop :=
  ∃ (top : Mark ((subst s)^[xs.length] [source.top]))
    (bottom : Mark ((subst s)^[xs.length] [source.bottom])),
    MarkTrace s source.top (xs.map Prod.fst) top.before top.letter top.after ∧
    MarkTrace s source.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
    top.letter = target.top ∧ bottom.letter = target.bottom ∧
    target.delta = incidenceZ s ^ xs.length *ᵥ source.delta +
      (parikhZ top.before - parikhZ bottom.before)

theorem original_traces_of_ordered {s : Fin 3 → Word} {source target : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s source xs target) :
    OriginalTraces s source xs target :=
  ordered_path_traced_original_prefixes hp

/-- Final strictness pulls back along the same counted literal transcript.
A central endpoint may have a nonzero full offset, which is preserved. -/
theorem steps_traced_interior {α : Type} {edge : α → α → Prop}
    {s : Fin 3 → Word} (packet : α → Packet)
    (literal : ∀ a b, edge a b → LiteralEdge s (packet a) (packet b))
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    {k : ℕ} {source target : α}
    (hp : ClassAPlusUpperEntry.Steps edge k source target)
    (htarget : (packet target).Interior ℓ) :
    ∃ xs : List (ℕ × ℕ), xs.length = k ∧
      OrderedInteriorPath s ℓ (packet source) xs (packet target) ∧
      OriginalTraces s (packet source) xs (packet target) := by
  obtain ⟨xs, hlen, hxs⟩ := steps_ordered_path packet literal hp
  exact ⟨xs, hlen,
    ordered_path_indexed_interior s ℓ β hpos hβ hscale hxs htarget,
    original_traces_of_ordered hxs⟩

/-- Reversal is a map of complete ordered strict paths. It is not a
substitution edge, and no ordinal is inserted into the transcript. -/
theorem ordered_interior_path_swap {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {source target : Packet} {xs : List (ℕ × ℕ)}
    (hp : OrderedInteriorPath s ℓ source xs target) :
    OrderedInteriorPath s ℓ source.swap (xs.map Prod.swap) target.swap := by
  induction hp with
  | nil hi => exact .nil _ hi.swap
  | snoc _ i j he hi ih =>
    simpa only [List.map_append, List.map_cons, List.map_nil, Prod.swap_prod_mk] using
      OrderedInteriorPath.snoc ih j i (indexed_step_swap he) hi.swap

/-- The full original tracks are exchanged, including their prefix words,
suffixes and indices. The terminal complete offset is negated. -/
theorem original_traces_swap {s : Fin 3 → Word} {source target : Packet}
    {xs : List (ℕ × ℕ)} (ht : OriginalTraces s source xs target) :
    OriginalTraces s source.swap (xs.map Prod.swap) target.swap := by
  obtain ⟨top, bottom, htop, hbottom, ht, hb, hdelta⟩ := ht
  unfold OriginalTraces
  rw [List.length_map]
  simp only [Packet.swap]
  refine ⟨bottom, top, ?_, ?_, hb, ht, ?_⟩
  · simpa only [List.map_map, Function.comp_def, Prod.fst_swap] using hbottom
  · simpa only [List.map_map, Function.comp_def, Prod.snd_swap] using htop
  · rw [hdelta, Matrix.mulVec_neg]
    abel

/-- Exact edge count and both full tracks survive orientation reversal. -/
theorem swap_preserves_count_and_tracks {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {source target : Packet} {xs : List (ℕ × ℕ)}
    (hp : OrderedInteriorPath s ℓ source xs target)
    (ht : OriginalTraces s source xs target) :
    (xs.map Prod.swap).length = xs.length ∧
    OrderedInteriorPath s ℓ source.swap (xs.map Prod.swap) target.swap ∧
    OriginalTraces s source.swap (xs.map Prod.swap) target.swap :=
  ⟨List.length_map _, ordered_interior_path_swap hp, original_traces_swap ht⟩

/-- The manuscript's bottom-minus-top convention retains the nonzero
terminal vector; central entry alone never supplies terminal zero. -/
theorem original_traces_bottom_minus_top {s : Fin 3 → Word}
    {source target : Packet} {xs : List (ℕ × ℕ)}
    (ht : OriginalTraces s source xs target) :
    ∃ (top : Mark ((subst s)^[xs.length] [source.top]))
      (bottom : Mark ((subst s)^[xs.length] [source.bottom])),
      MarkTrace s source.top (xs.map Prod.fst) top.before top.letter top.after ∧
      MarkTrace s source.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter = target.top ∧ bottom.letter = target.bottom ∧
      -target.delta = incidenceZ s ^ xs.length *ᵥ (-source.delta) +
        (parikhZ bottom.before - parikhZ top.before) := by
  obtain ⟨top, bottom, htop, hbottom, ht, hb, hdelta⟩ := ht
  refine ⟨top, bottom, htop, hbottom, ht, hb, ?_⟩
  rw [hdelta, Matrix.mulVec_neg]
  abel

end Psc.ClassAPlusUpperEntryTransport
