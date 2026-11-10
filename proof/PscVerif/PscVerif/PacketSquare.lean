/-
# The packet square: absolute occurrence pairs, literal occurrence pairs, packet rows

The composite layer of the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`; `README.llm.txt`, 2026-11-09 addendum "P0
OCCURRENCE REFINEMENT").  It joins two committed squares over the literal occurrence graph
`occGraph s` of `Psc.OccurrenceGraph`:

* the top square ρ (`Psc.OccurrenceRealisation`): the reading `reading s T₀` of an absolute
  occurrence pair of the iterates `σⁿ(T₀)` is a refinement onto `occGraph s`
  (`reading_refines`; on the declared universe `Universe s T₀`, `universe_refines`);
* the certificate square D (`Psc.PacketCertificate`): on an accepted table
  (`t.check = true`) the decoding `t.occAt` sends every listed edge to a literal edge
  (`Table.graph_sound`), lists every literal child of a row (`Table.graph_complete`), has the
  same targets (`Table.targets`), satisfies the star equation, children and splits
  (`Table.Accepted.star_eq`, no order hypothesis), and is injective over a linearly ordered
  alphabet (`Table.check_sound`).

Apart from the Fibonacci calibration and the `weird` control, which evaluate listed states,
rows, stars and edges of those two tables by `decide`, `decide +kernel` and `rfl`, nothing here
re-derives a row, a star, an edge or a reading: every statement is assembled from those
theorems and the generic layer `Psc.GraphRefinement` (`PscVerif.GraphRefinement`,
`PscVerif.GraphEmbedding`).

## Which word points which way

With the predicates named as in `docs/packet-square-stop-go-2026-11-10.md` §1 (`Complete`, the
forward condition; `SoundEvery`, the backward condition), the absolute pairs as the actual side
and the packet rows as the quotient, "completeness" of the composite is `Complete` (every
retained absolute edge is a listed packet edge) and "soundness" is `SoundEvery` (every listed
edge out of the packet of an absolute pair is the packet of a retained absolute edge out of
**that** pair, at any level and offset).  At layer D the table is the source side and the words
swap: `Table.embeds` bundles "every listed edge is literal" (`Embeds.sound`, i.e. `Complete`
with the table as source) and "full child stars" (`Embeds.complete`, i.e. `SoundEvery` with the
table as source).

## Contents

* `Table.embeds`: the two `Psc.GraphRefinement.Embeds` bundles of an accepted table, for the
  coincidence target (`t.graph` into `occGraph t.s`) and the success target (`t.graphSuccess`
  into `occGraphFor t.s t.target`).  No order hypothesis.  It is declared in the namespace
  `Psc.PacketCertificate` of `Table`, so `t.embeds h` resolves by dot notation; its full name is
  `Psc.PacketCertificate.Table.embeds`, and its module is this one.
* Graph logic.  `refines_of_embeds`: a refinement `ρ` onto an actual graph factors through an
  **injective** embedding `e` along any `π` with `e ∘ π = ρ`.  Injectivity is used twice, once
  for `Complete` and once for `SoundEvery`, to identify the listed row an edge arrives at.
  `refines_precomp`: a refinement survives a change of source along a surjection that preserves
  and reflects edges and targets.
* **The general carrier.**  `Covered t T₀`: the anchored pairs (`Anchored t.s T₀`, absolute
  pair together with one reading) whose reading is the decoded pair of some row;
  `coveredGraph t T₀`, `coveredGraphFor t T₀` (the retained edges; coincidence and success
  targets); `packetOf t T₀` (a row over the reading, by choice) and `packetOf_spec` (**the
  square commutes**: `t.occAt (packetOf t T₀ a) = reading t.s T₀ a.1`); `packetOf_congr`: the
  packet depends only on the reading.  `covered_closed`: the covered set is closed under
  retained edges (`Table.closed_range`); `covered_refines`: the reading is a refinement of the
  covered graph onto `occGraph t.s` (both targets); `covered_acyclic`: levels increase, so the
  covered graph has no cycle.
  `packet_square_covered` (`[LinearOrder α]`): `packetOf t T₀` is a refinement of the covered
  graph onto the packet graph, both targets; `packet_square_covered_readings`,
  `packet_square_covered_readings_for`: (E), (AE), (A), (A⁺) agree, (AE°) pulls back.  No
  hypothesis on `T₀`.  `packetOf_eq_iff` (`[LinearOrder α]`): `packetOf t T₀ a` is the only
  row over the reading.  `packet_fields`: the letters of the packet row of a covered pair are
  the letters at its two absolute positions in the iterates, its residual (over `t.letters`)
  is the absolute prefix defect there, and its two addresses and its `interior` and `success`
  bits are those of the reading (block-local data, by `packetOf_spec`).
* **The declared universe.**  `covered_level_zero`: every root reading of a noncoincident listed
  state is covered (`Table.roots`).  `universe_covered`: for a noncoincident listed state `T₀`,
  every element of `Universe t.s T₀` is covered (`universe_reading_mem_of_closed` with the
  range of `t.occAt`, child-closed by `Table.closed_range` and holding the root pairs by
  `Table.roots`).  Since `Universe` is defined by reachability from the root readings, this is
  close to definitional; the intrinsic form is `packet_of_red` (no order hypothesis): every
  absolute pair of the iterates whose two positions lie in one noncoincident block of
  `red (σⁿ T₀.1) (σⁿ T₀.2)` is the absolute pair of exactly one element of the universe, and the
  packet of that element decodes to that block at the local positions (`anchored_cover_red`,
  `universe_reading_unique`, `universePacket_spec`).  `seed_universe_covered`
  (`[LinearOrder α]`): for every seed `(ab, ba)` of `Psc.Descendants.seeds`, either it is listed
  and its universe is covered, or its swap is listed and every element of its universe is read,
  side-swapped, by a row (`seedsOK`, `Table.seeds_listed`, `universe_swap`).  `toCovered`,
  `toCovered_graph`: the universe graph is the covered graph pulled back along the inclusion,
  both targets included.  `universe_step`: a listed edge out of the row over the reading of an
  element of the universe lifts to a retained edge out of that element (no order hypothesis).
  `row_realised`: every row of an accepted table is read in the universe of some noncoincident
  listed state (the state of a root row it is reachable from; no order hypothesis).
* **The headline square, on the declared universe** (`[LinearOrder α]`; `T₀` a noncoincident
  listed state, no other hypothesis on `T₀` or on `t.s`): `universePacket t h hT₀ hnc` sends
  an element of `Universe t.s T₀` to the row over its reading, and it is the only such row
  (`universePacket_spec`, `universePacket_eq_iff`); the absolute pair determines the element
  (`universe_refines`).  `packet_square`: the composite from the actual graph induced on the
  universe (`universeGraph`, `universeGraphFor`) to the packet rows is `Complete` and
  `SoundEvery`, with targets preserved and reflected (`Refines`), for the coincidence target
  and for the success target.  `packet_square_range`: its image is exactly the set of rows
  reachable in the packet graph from the root rows of `T₀`.  `packet_square_readings`,
  `packet_square_readings_for`: hence (E), (AE), (A), (A⁺) agree between an element of the
  universe and its packet, and (AE°) pulls back from the packet.  `universe_acyclic`: the
  universe graph has no cycle, so (AE°) holds on the absolute side vacuously, and no transfer
  of (AE°) from the absolute side to the packet is claimed (a refinement does not push (AE°)
  forward, `unroll_cyclicProductive`).  `packet_path_lift`: every infinite path of the packet
  graph from the packet of an element of the universe is the packet image of an infinite path
  of the universe graph from it, whose level rises by exactly one per step.
* **Children and splits through the composite.**  `universe_star` (`[LinearOrder α]`): every
  absolute child of an element of the universe (with a noncoincident reading) is either the
  absolute pair of a retained child, whose packet is the destination of the `.child` entry of
  the packet star with the same digits, or `Separated`, with a `.split` entry of the packet
  star at those digits; conversely every `.child` entry is the packet of a retained child along
  its digits, and every `.split` entry names a `Separated` absolute child along its digits.
* **The mirrored frame.**  `successFor_swap`; `universeSwap`, `universeSwap_surjective`,
  `universeSwap_graph`: the side swap is an isomorphism from the universe graph of `T` onto that
  of `T.swap`, both targets included (`anchoredGraph_child_swap`, `universe_swap_iff`; no
  hypothesis).  `packet_square_swap` (`[LinearOrder α]`): if `T.swap` is a noncoincident listed
  state, the side swap followed by `universePacket` is a refinement of the universe graph of `T`
  onto the packet graph, both targets, and the row reached is the only row over the
  side-swapped reading (`universeSwap_packet_eq_iff`).  `seed_square` (`[LinearOrder α]`): every
  seed `(ab, ba)`, in its own frame, has such a square, through `packet_square` when it is
  listed and through `packet_square_swap` when its swap is.

## Negative control

`weird_square_fails`: on the accepted table `Psc.PacketCertificate.weird` (Fibonacci over a
two-letter type whose `<` is empty, so both orientations of the seed are listed), over the
universe of its listed seed `(ab, ba)` (`weirdSeed`), the composite `universePacket` is neither
`SoundEvery` nor `Complete`.  `weird_square_rows` (by `decide +kernel` and `rfl`) gives the row
and edge facts: rows 1 and 3 decode to the root pairs `(0, 1)` and `(1, 1)` of `weirdSeed`, rows
9 and 18 decode to one occurrence pair and no other row does, rows 1 and 16 are the only rows
over their pairs, the edges `1 → 9`, `3 → 12`, `12 → 16`, `16 → 18` are listed and `1 → 18`,
`16 → 9` are not.  `weird_square_fails` derives the universe membership: the root elements at
`(0, 1)` and `(1, 1)` and their retained descendants along those edges (`universe_step`) are
elements of the universe whose packets are rows 1 and 16 (`universePacket_spec`), and
`universePacket` sends the elements over the pair of rows 9 and 18 to only one of them.  The
injectivity hypothesis of `packet_square` therefore cannot be dropped.

## Calibration

`fib_seed_listed`, `fib_universe_covered`: the Fibonacci seed `(01, 10)` (`tmPair`) is a
noncoincident listed state of `fibTable` (`fib_accepted`), and its universe is covered.
`fib_dead_packet`: the element `fibRoot10` of that universe, at level 0 and positions
`(1, 0)`, has packet 2 (the row that decodes to the dead end `fibDead`, `fib_rows`),
and its non-productivity, a statement about the absolute side, transfers to packet 2 through
`packet_square_readings` (the source of the fact is `fib_block_readings`, read through
`universe_readings`).

## Hypotheses

`t.check = true` for every statement that uses a row's content; `packetOf_spec` and
`packetOf_congr` need only that the pair is covered, and `covered_acyclic`, `universe_acyclic`,
`refines_of_embeds`, `refines_precomp`, `successFor_swap` and the `universeSwap` lemmas need no
table.  `[LinearOrder α]` where injectivity of `t.occAt` (`Table.check_sound`) is used:
`packetOf_eq_iff`, `universePacket_eq_iff`, `packet_square_covered`, `packet_square`, their
readings, `packet_square_range`, `packet_path_lift`, `universe_star`, `packet_square_swap`,
`universeSwap_packet_eq_iff` and `seed_square`; and in `seed_universe_covered`, whose
`Table.seeds_listed` needs a total order to place a seed in normalised orientation.  With an
arbitrary `LT` injectivity is false: an accepted table may list two rows over one occurrence
pair (`Psc.PacketCertificate.weird_not_injective`), `packetOf` names only one of them, and the
square fails (`weird_square_fails`).  No hypothesis is placed on `t.s`: no primitivity, no
irreducibility of the incidence matrix, no Pisot property, no nonerasing assumption.

## Not proved here

No cycle realisation: a cycle of the packet graph lifts only to an infinite absolute lineage
graded by level (`packet_path_lift`, `universe_acyclic`, `covered_acyclic`), never to an
absolute cycle.  No legal context and no hull point: an absolute lineage lives in the iterates
`σⁿ(T₀)` of a listed state `T₀`; nothing makes `T₀` legal, gives a point of `X_σ`, a pair of
tilings, or one infinite desubstitution history (backward compactness).  No statement about a
specific substitution other than `t.s` of a checked table (the Fibonacci calibration and the
`weird` control are two such tables); the acyclicity lemmas, the frame change and the graph
logic are generic.  That a given exported table is accepted is decided by its own data module,
and the Mojo exporter is not proved correct.  Not that every row is read in the universe of a
seed: a row is read in the universe of the listed state of a root row (`row_realised`), and the
checker does not tie the listed states to the seed closure (`fibExtra_accepted`).  Splits are
accounted for one digit step at a time (`universe_star`); about the absolute descendants of a
split child nothing is said beyond what `Separated.lineage` and `Separated.not_anchor` give (no
irreducible reading containing both positions, at any depth).  Nothing about descendants of
coincidence blocks (the universe holds only retained children, `anchored_cover_needs_hnc`),
absolute pairs off the universe of a listed state or of the mirror of one, or a frame other than
a listed state and its side swap.  No productive, hereditarily productive, inevitable or
realised reading of any specific packet is claimed beyond the Fibonacci calibration.  Nothing
here advances, proves or closes C4, G1, #84, #138, #139 or the Pisot substitution conjecture.
-/
import PscVerif.PacketCertificate
import PscVerif.OccurrenceRealisation
import PscVerif.GraphEmbedding

/-! ### Layer D as two embeddings

`Table.embeds` is declared in the namespace of `Table` (`Psc.PacketCertificate`), so that
`t.embeds h` resolves by dot notation; it belongs to this module because the bundle
`Psc.GraphRefinement.Embeds` is not imported by `PscVerif.PacketCertificate`. -/

namespace Psc.PacketCertificate

open Psc.OccurrenceGraph Psc.GraphRefinement

variable {α : Type} [DecidableEq α] [Fintype α] [LT α] [DecidableLT α]

/-- **An accepted table embeds into the literal occurrence graph**, for the coincidence target
and for the success target: every listed edge is literal (`Table.graph_sound`), every literal
child of a row is listed (`Table.graph_complete`), and the targets agree (`Table.targets`).  No
order hypothesis; injectivity of `t.occAt` is not part of `Embeds`. -/
theorem Table.embeds (t : Table α) (h : t.check = true) :
    Embeds t.graph (occGraph t.s) t.occAt ∧
      Embeds t.graphSuccess (occGraphFor t.s t.target) t.occAt :=
  ⟨⟨fun _ _ hij => Table.graph_sound t h hij, fun i _ hy => Table.graph_complete t h i hy,
      fun i => (Table.targets t h i).1⟩,
    ⟨fun _ _ hij => Table.graph_sound t h hij, fun i _ hy => Table.graph_complete t h i hy,
      fun i => (Table.targets t h i).2⟩⟩

end Psc.PacketCertificate

namespace Psc.PacketSquare

open Psc.Binomial Psc.Reduction Psc.Descendants
open Psc.QuantifierInterface Psc.QuantifierBinding
open Psc.OccurrenceAddress Psc.OccurrenceGraph Psc.OccurrenceRealisation Psc.GraphRefinement
open Psc.PacketCertificate

/-! ### Graph logic: factoring through an injective embedding, changing the source -/

section Generic

universe u v w u'

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u'}

/-- **A refinement onto an actual graph factors through an injective embedding.**  If `ρ`
refines `G` onto `Q`, the table `P` embeds into `Q` by an injective `e` (sound, full child
stars, same targets), and `π` commutes the square (`e ∘ π = ρ`), then `π` refines `G` onto
`P`.  `Complete`: an edge `x → x'` reads as a `Q`-edge out of `e (π x)`, which full child stars
list as `π x → y'` with `e y' = e (π x')`, and injectivity gives `y' = π x'`.  `SoundEvery`: a
listed edge `π x → y'` is the `Q`-edge `ρ x → e y'`, which lifts to `x → x'` with
`ρ x' = e y'`, and injectivity gives `π x' = y'`.  Targets go through `Embeds.target_iff`. -/
theorem refines_of_embeds {G : ChildGraph X} {Q : ChildGraph Z} {P : ChildGraph Y}
    {ρ : X → Z} {e : Y → Z} {π : X → Y} (hρ : Refines G Q ρ) (he : Embeds P Q e)
    (hinj : Function.Injective e) (hπ : ∀ x, e (π x) = ρ x) : Refines G P π where
  complete := fun x x' hxx' => by
    have hq := hρ.complete hxx'
    rw [← hπ x, ← hπ x'] at hq
    obtain ⟨y', hy', hey'⟩ := he.complete (π x) hq
    rwa [hinj hey'] at hy'
  soundEvery := fun x y' hy' => by
    have hq := he.sound hy'
    rw [hπ x] at hq
    obtain ⟨x', hxx', hx'⟩ := hρ.soundEvery x hq
    exact ⟨x', hxx', hinj ((hπ x').trans hx')⟩
  targetDown := fun x hx => (he.target_iff (π x)).2 ((hπ x).symm ▸ hρ.targetDown x hx)
  targetUp := fun x hx => hρ.targetUp x ((hπ x) ▸ (he.target_iff (π x)).1 hx)

/-- **A refinement survives a change of source along a surjection that preserves and reflects
edges and targets.**  If `π` refines `G` onto `P`, and `f : W → X` is surjective with
`G'.child a b ↔ G.child (f a) (f b)` and `G'.target a ↔ G.target (f a)`, then `π ∘ f` refines
`G'` onto `P`.  Surjectivity is used once, for `SoundEvery`: the lift of a listed edge out of
`π (f a)` is an `f`-image.  Used for the mirrored frame (`packet_square_swap`, `f` the side
swap). -/
theorem refines_precomp {G' : ChildGraph W} {G : ChildGraph X} {P : ChildGraph Y}
    {π : X → Y} {f : W → X} (hR : Refines G P π) (hf : Function.Surjective f)
    (hchild : ∀ a b, G'.child a b ↔ G.child (f a) (f b))
    (htarget : ∀ a, G'.target a ↔ G.target (f a)) : Refines G' P (fun a => π (f a)) where
  complete := fun a b hab => hR.complete ((hchild a b).1 hab)
  soundEvery := fun a y hy => by
    obtain ⟨x, hx, rfl⟩ := hR.soundEvery (f a) hy
    obtain ⟨b, rfl⟩ := hf x
    exact ⟨b, (hchild a b).2 hx, rfl⟩
  targetDown := fun a ha => hR.targetDown (f a) ((htarget a).1 ha)
  targetUp := fun a ha => (htarget a).2 (hR.targetUp (f a) ha)

end Generic

variable {α : Type} [DecidableEq α]

/-! ### The general carrier: covered anchored pairs -/

/-- **Covered pairs**: the anchored pairs of the iterates of `T₀` (absolute pair together with
one reading, `Anchored`) whose reading is the decoded occurrence pair of a row of `t`. -/
def Covered (t : Table α) (T₀ : List α × List α) : Type :=
  {a : Anchored t.s T₀ // ∃ i, t.occAt i = reading t.s T₀ a}

/-- The actual graph on the covered pairs: the retained edges of `anchoredGraph t.s T₀`;
targets: a coincidence block. -/
def coveredGraph (t : Table α) (T₀ : List α × List α) : ChildGraph (Covered t T₀) where
  child a b := (anchoredGraph t.s T₀).child a.1 b.1
  target a := (anchoredGraph t.s T₀).target a.1

/-- The actual graph on the covered pairs for the table's packet target: the retained edges,
targets the packet successes `Occ.SuccessFor t.target` of the reading. -/
def coveredGraphFor (t : Table α) (T₀ : List α × List α) : ChildGraph (Covered t T₀) where
  child := (coveredGraph t T₀).child
  target a := (anchoredGraphFor t.s T₀ t.target).target a.1

/-- The packet of a covered pair: a row whose decoded pair is its reading (chosen; it is the
only one over a linearly ordered alphabet, `packetOf_eq_iff`). -/
noncomputable def packetOf (t : Table α) (T₀ : List α × List α) (a : Covered t T₀) :
    Fin t.packets.length :=
  a.2.choose

/-- **The square commutes**: the decoded pair of the packet of a covered pair is its reading. -/
theorem packetOf_spec (t : Table α) (T₀ : List α × List α) (a : Covered t T₀) :
    t.occAt (packetOf t T₀ a) = reading t.s T₀ a.1 :=
  a.2.choose_spec

/-- The packet of a covered pair depends only on its reading (no order hypothesis). -/
theorem packetOf_congr (t : Table α) (T₀ : List α × List α) {a b : Covered t T₀}
    (hab : reading t.s T₀ a.1 = reading t.s T₀ b.1) : packetOf t T₀ a = packetOf t T₀ b := by
  have key : ∀ (r r' : Occ α) (hr : ∃ i, t.occAt i = r) (hr' : ∃ i, t.occAt i = r'), r = r' →
      hr.choose = hr'.choose := by
    rintro r _ hr hr' rfl
    rfl
  exact key _ _ a.2 b.2 hab

/-- Levels increase along the retained edges: **the covered graph has no cycle**.  A cycle of
the packet graph is therefore never the packet image of a cycle of covered pairs. -/
theorem covered_acyclic (t : Table α) (T₀ : List α × List α) (a : Covered t T₀) :
    ¬ Relation.TransGen (coveredGraph t T₀).child a a := by
  intro hc
  have key : ∀ {b c : Covered t T₀}, Relation.TransGen (coveredGraph t T₀).child b c →
      Relation.TransGen (anchoredGraph t.s T₀).child b.1 c.1 := by
    intro b c hbc
    induction hbc with
    | single h => exact .single h
    | tail _ h ih => exact ih.tail h
  exact anchored_no_cycle t.s T₀ a.1 (key hc)

section Order

variable [Fintype α] [LT α] [DecidableLT α]

/-- **The covered set is closed under retained edges**: the reading of a retained child of a
covered pair is a literal child of a decoded row (`reading_complete`), hence a decoded row
(`Table.closed_range`). -/
theorem covered_closed (t : Table α) (h : t.check = true) (T₀ : List α × List α) :
    (anchoredGraph t.s T₀).Closed {a | ∃ i, t.occAt i = reading t.s T₀ a} := by
  rintro a b ⟨i, hi⟩ hab
  obtain ⟨j, hj⟩ := Table.closed_range t h ⟨i, hi⟩ (reading_complete t.s T₀ hab)
  exact ⟨j, hj⟩

/-- The top square restricted to the covered pairs: the reading is a refinement of the covered
graph onto `occGraph t.s`, and of its success variant onto `occGraphFor t.s t.target`.  The
lift of an edge out of a covered pair (`reading_soundEvery`) is covered by `covered_closed`. -/
theorem covered_refines (t : Table α) (h : t.check = true) (T₀ : List α × List α) :
    Refines (coveredGraph t T₀) (occGraph t.s) (fun a => reading t.s T₀ a.1) ∧
      Refines (coveredGraphFor t T₀) (occGraphFor t.s t.target) (fun a => reading t.s T₀ a.1) := by
  have hS : SoundEvery (coveredGraph t T₀) (occGraph t.s) (fun a => reading t.s T₀ a.1) := by
    intro a y' hy
    obtain ⟨b, hab, rfl⟩ := reading_soundEvery t.s T₀ a.1 hy
    exact ⟨⟨b, covered_closed t h T₀ a.2 hab⟩, hab, rfl⟩
  exact ⟨⟨fun _ _ hab => reading_complete t.s T₀ hab, hS, fun _ h => h, fun _ h => h⟩,
    ⟨fun _ _ hab => reading_complete t.s T₀ hab, hS, fun _ h => h, fun _ h => h⟩⟩

/-- **The carried fields of the packet of a covered pair are literal at the absolute pair.**
The letters at the two absolute positions in the iterates are the packet's letters, the
absolute prefix defect (over `t.letters`) is the packet's residual, and both addresses, the
`interior` bit and the `success` bit are those of the reading.  From `Table.Accepted.fields`
and `Anchor.letters`, `Anchor.residual`; no order hypothesis. -/
theorem packet_fields (t : Table α) (h : t.check = true) (T₀ : List α × List α)
    (a : Covered t T₀) :
    ((subst t.s)^[a.1.1.1.level] T₀.1)[a.1.1.1.top]? =
        some (t.packets[packetOf t T₀ a]).letters.1 ∧
      ((subst t.s)^[a.1.1.1.level] T₀.2)[a.1.1.1.bot]? =
        some (t.packets[packetOf t T₀ a]).letters.2 ∧
      (t.packets[packetOf t T₀ a]).residual = t.letters.map (fun c =>
        ((((subst t.s)^[a.1.1.1.level] T₀.1).take a.1.1.1.top).count c : ℤ) -
          ((((subst t.s)^[a.1.1.1.level] T₀.2).take a.1.1.1.bot).count c : ℤ)) ∧
      (t.packets[packetOf t T₀ a]).topAddr = (reading t.s T₀ a.1).topAddr t.s ∧
      (t.packets[packetOf t T₀ a]).botAddr = (reading t.s T₀ a.1).botAddr t.s ∧
      ((t.packets[packetOf t T₀ a]).interior = true ↔ (reading t.s T₀ a.1).Interior) ∧
      ((t.packets[packetOf t T₀ a]).success = true ↔
        (reading t.s T₀ a.1).SuccessFor t.target) := by
  obtain ⟨hv, hta, hba, hl1, hl2, hres, hint, hsuc⟩ :=
    ((Table.check_iff t).1 h).fields (packetOf t T₀ a)
  rw [packetOf_spec] at hv hta hba hl1 hl2 hres hint hsuc
  obtain ⟨off, ha⟩ := a.1.2
  obtain ⟨-, hP, hQ, -⟩ := hv
  have hlet := ha.letters hP hQ
  refine ⟨hlet.1.trans hl1, hlet.2.trans hl2, ?_, hta, hba, hint, hsuc⟩
  rw [hres]
  exact List.map_congr_left fun c _ => (ha.residual hP.le hQ.le c).symm

/-! ### The declared universe is covered -/

/-- **Level 0 of a noncoincident listed state is covered**: the root reading at every position
pair is the decoded pair of a root row (`Table.roots`). -/
theorem covered_level_zero (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (hbal : Equiv1 T₀.1 T₀.2) {P Q : ℕ}
    (hP : P < T₀.1.length) (hQ : Q < T₀.2.length) :
    ∃ i, t.occAt i = reading t.s T₀ (rootAnchored t.s hbal P Q) := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT₀
  exact Table.roots t h hk hnc hP hQ

/-- **The universe of a noncoincident listed state is covered**: every element of
`Universe t.s T₀` reads as the decoded pair of a row.  The range of `t.occAt` is child-closed
(`Table.closed_range`) and holds every root pair of `T₀` (`Table.roots`), so it holds every
reading of the universe (`universe_reading_mem_of_closed`).  No balance or irreducibility
hypothesis on `T₀` is used; noncoincidence is needed for the root rows (`rootsOK` lists none
under a coincidence state). -/
theorem universe_covered (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) :
    Universe t.s T₀ ⊆ {a | ∃ i, t.occAt i = reading t.s T₀ a} := by
  intro a ha
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT₀
  obtain ⟨i, hi⟩ := universe_reading_mem_of_closed (S := Set.range t.occAt)
    (fun _ _ hP hQ => Table.roots t h hk hnc hP hQ) (Table.closed_range t h) ha
  exact ⟨i, hi⟩

/-- An element of the universe of a noncoincident listed state, as a covered pair. -/
def toCovered (t : Table α) (h : t.check = true) {T₀ : List α × List α} (hT₀ : T₀ ∈ t.states)
    (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) : Covered t T₀ :=
  ⟨a.1, universe_covered t h hT₀ hnc a.2⟩

/-- **The packet of an element of the universe** of a noncoincident listed state: the packet of
it as a covered pair.  `packet_fields t h T₀ (toCovered t h hT₀ hnc a)` gives its carried
fields. -/
noncomputable def universePacket (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) : Fin t.packets.length :=
  packetOf t T₀ (toCovered t h hT₀ hnc a)

/-- The square commutes on the universe. -/
theorem universePacket_spec (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) :
    t.occAt (universePacket t h hT₀ hnc a) = reading t.s T₀ a.1 :=
  packetOf_spec t T₀ _

/-- The universe graph is the covered graph pulled back along `toCovered`: the same edges and
both targets (definitional), and `universePacket` is `packetOf` after `toCovered`. -/
theorem toCovered_graph (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a b : Universe t.s T₀) :
    ((coveredGraph t T₀).child (toCovered t h hT₀ hnc a) (toCovered t h hT₀ hnc b) ↔
        (universeGraph t.s T₀).child a b) ∧
      ((coveredGraph t T₀).target (toCovered t h hT₀ hnc a) ↔ (universeGraph t.s T₀).target a) ∧
      ((coveredGraphFor t T₀).target (toCovered t h hT₀ hnc a) ↔
        (universeGraphFor t.s T₀ t.target).target a) ∧
      universePacket t h hT₀ hnc a = packetOf t T₀ (toCovered t h hT₀ hnc a) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, rfl⟩

/-- A listed edge out of the packet row over the reading of an element of the universe lifts to
a retained edge out of that element (`Table.graph_sound`, then `universe_refines`); no order
hypothesis. -/
theorem universe_step (t : Table α) (h : t.check = true) (T₀ : List α × List α)
    {u : Universe t.s T₀} {i j : Fin t.packets.length} (hu : reading t.s T₀ u.1 = t.occAt i)
    (hij : t.graph.child i j) :
    ∃ u', (universeGraph t.s T₀).child u u' ∧ reading t.s T₀ u'.1 = t.occAt j := by
  have hc := Table.graph_sound t h hij
  rw [← hu] at hc
  exact (universe_refines t.s T₀).1.soundEvery u hc

/-- **Completeness relative to the declared universe, at the composite level** (intrinsic
form).  For a noncoincident listed state `T₀`, every absolute pair `x` of the iterates whose two
positions lie in one noncoincident block `red (σⁿ T₀.1) (σⁿ T₀.2)[j]` (`n = x.level`) is the
absolute pair of exactly one element `a` of the universe, and the packet of `a` decodes to that
block at the local positions `x.top - blockStart … j`, `x.bot - blockStart … j`.  From
`anchored_cover_red` (with `IsBlock T₀` from `statesOK`), `universe_reading_unique` and
`universePacket_spec`.  At a coincidence block of that reduction the statement fails
(`fib_lvl2_not_universe`). -/
theorem packet_of_red (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) {x : AbsOcc} {j : ℕ}
    (hj : j < (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)).length)
    (h1 : blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j ≤ x.top)
    (h2 : x.top < blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j +
      (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2))[j].1.length)
    (h3 : blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j ≤ x.bot)
    (h4 : x.bot < blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j +
      (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2))[j].1.length)
    (hncj : (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2))[j].1 ≠
      (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2))[j].2) :
    ∃ a : Universe t.s T₀, a.1.1.1 = x ∧ (∀ b : Universe t.s T₀, b.1.1.1 = x → b = a) ∧
      (t.occAt (universePacket t h hT₀ hnc a)).block =
        (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2))[j] ∧
      (t.occAt (universePacket t h hT₀ hnc a)).top =
        x.top - blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j ∧
      (t.occAt (universePacket t h hT₀ hnc a)).bot =
        x.bot - blockStart (red ((subst t.s)^[x.level] T₀.1) ((subst t.s)^[x.level] T₀.2)) j := by
  have hblk := (((Table.check_iff t).1 h).state_spec hT₀).1
  obtain ⟨a, ha, hx, hb, ht, hq⟩ := anchored_cover_red hblk hj h1 h2 h3 h4 hncj
  refine ⟨⟨a, ha⟩, hx,
    fun b hb' => Subtype.ext (universe_reading_unique b.2 ha (hb'.trans hx.symm)), ?_⟩
  rw [universePacket_spec]
  exact ⟨hb, ht, hq⟩

/-- **Every row is realised.**  The decoded pair of every row of an accepted table is the reading
of an element of the universe of some noncoincident listed state: the state of a root row the
row is reachable from (`Table.range_eq_reach`, then `reading_image_universe`, with the balance
of a listed state from `statesOK`).  No order hypothesis.  It does not say that this state is
reachable from a seed (`fibExtra_accepted`). -/
theorem row_realised (t : Table α) (h : t.check = true) (i : Fin t.packets.length) :
    ∃ T ∈ t.states, T.1 ≠ T.2 ∧ ∃ a ∈ Universe t.s T, reading t.s T a = t.occAt i := by
  have hi : t.occAt i ∈ Set.range t.occAt := ⟨i, rfl⟩
  rw [Table.range_eq_reach t h] at hi
  obtain ⟨T, hT, hnc, P, Q, hP, hQ, hreach⟩ := hi
  have hbal := (((Table.check_iff t).1 h).state_spec hT).1.2.1
  have hy : t.occAt i ∈ reading t.s T '' Universe t.s T := by
    rw [reading_image_universe hbal]
    exact ⟨P, Q, hP, hQ, hreach⟩
  obtain ⟨a, ha, hai⟩ := hy
  exact ⟨T, hT, hnc, a, ha, hai⟩

end Order

/-- Levels increase along the edges of the universe graph: **it has no cycle**, so (AE°)
holds at every element of the universe vacuously. -/
theorem universe_acyclic (s : α → List α) (T₀ : List α × List α) (a : Universe s T₀) :
    ¬ Relation.TransGen (universeGraph s T₀).child a a := by
  intro hc
  have key : ∀ {b c : Universe s T₀}, Relation.TransGen (universeGraph s T₀).child b c →
      Relation.TransGen (anchoredGraph s T₀).child b.1 c.1 := by
    intro b c hbc
    induction hbc with
    | single h => exact .single h
    | tail _ h ih => exact ih.tail h
  exact anchored_no_cycle s T₀ a.1 (key hc)

/-! ### Frame change of the universe graph -/

/-- The packet success of an occurrence pair is invariant under the side swap (`Interior` and
`Coincident` are, `Occ.interior_swap`, `Occ.coincident_swap`; at a coincidence block both
tracks have the same first letter). -/
theorem successFor_swap (target : Option α) (x : Occ α) :
    x.swap.SuccessFor target ↔ x.SuccessFor target := by
  have hc : x.swap.Coincident ↔ x.Coincident := Occ.coincident_swap x
  unfold Occ.SuccessFor
  rw [Occ.interior_swap, hc]
  refine and_congr_right fun _ => and_congr_right fun hco => ?_
  have hco' : x.block.1 = x.block.2 := hco
  show (target.all fun c => decide (x.block.2[0]? = some c)) = true ↔ _
  rw [hco']

/-- The side swap of an element of the universe of `T`, as an element of the universe of
`T.swap` (`universe_swap`). -/
def universeSwap {s : α → List α} {T : List α × List α} (a : Universe s T) :
    Universe s T.swap :=
  ⟨a.1.swap, universe_swap a.2⟩

/-- Every element of the universe of `T.swap` is the side swap of an element of the universe of
`T` (`universe_swap_iff`, `Occ.swap_swap`). -/
theorem universeSwap_surjective {s : α → List α} {T : List α × List α} :
    Function.Surjective (universeSwap (s := s) (T := T)) := fun b =>
  ⟨⟨b.1.swap, (universe_swap_iff b.1).2 b.2⟩, Subtype.ext (Subtype.ext
    (Prod.ext rfl (Occ.swap_swap _)))⟩

/-- **The side swap is an isomorphism of universe graphs**: it preserves and reflects retained
edges (`anchoredGraph_child_swap`, applied in the frames `T` and `T.swap`), coincidence targets
(`Occ.coincident_swap`) and packet-success targets (`successFor_swap`). -/
theorem universeSwap_graph {s : α → List α} {T : List α × List α} (target : Option α)
    (a b : Universe s T) :
    ((universeGraph s T).child a b ↔
        (universeGraph s T.swap).child (universeSwap a) (universeSwap b)) ∧
      ((universeGraph s T).target a ↔ (universeGraph s T.swap).target (universeSwap a)) ∧
      ((universeGraphFor s T target).target a ↔
        (universeGraphFor s T.swap target).target (universeSwap a)) := by
  refine ⟨⟨fun hab => anchoredGraph_child_swap hab, fun hab => ?_⟩,
    (Occ.coincident_swap a.1.1.2).symm, (successFor_swap target a.1.1.2).symm⟩
  have h2 : (anchoredGraph s T.swap.swap).child a.1.swap.swap b.1.swap.swap :=
    anchoredGraph_child_swap hab
  have ea : a.1.swap.swap = a.1 := Subtype.ext (Prod.ext rfl (Occ.swap_swap _))
  have eb : b.1.swap.swap = b.1 := Subtype.ext (Prod.ext rfl (Occ.swap_swap _))
  rw [ea, eb] at h2
  exact h2

/-! ### The square, over a linearly ordered alphabet -/

section Linear

variable [Fintype α] [LinearOrder α]

/-- The packet of a covered pair is the only row over its reading. -/
theorem packetOf_eq_iff (t : Table α) (h : t.check = true) (T₀ : List α × List α)
    (a : Covered t T₀) (i : Fin t.packets.length) :
    packetOf t T₀ a = i ↔ t.occAt i = reading t.s T₀ a.1 :=
  ⟨fun hi => hi ▸ packetOf_spec t T₀ a,
    fun hi => (Table.check_sound t h).2.1 ((packetOf_spec t T₀ a).trans hi.symm)⟩

/-- **The packet square on the general carrier**: on an accepted table over a linearly ordered
alphabet, the packet of a covered pair is a refinement of the covered graph onto the packet
graph (`Complete`, `SoundEvery`, targets preserved and reflected), for the coincidence target
and for the success target.  No hypothesis on `T₀`.  From `covered_refines`, `Table.embeds`,
injectivity of `t.occAt` (`Table.check_sound`) and `packetOf_spec`, by `refines_of_embeds`. -/
theorem packet_square_covered (t : Table α) (h : t.check = true) (T₀ : List α × List α) :
    Refines (coveredGraph t T₀) t.graph (packetOf t T₀) ∧
      Refines (coveredGraphFor t T₀) t.graphSuccess (packetOf t T₀) :=
  ⟨refines_of_embeds (covered_refines t h T₀).1 (Table.embeds t h).1 (Table.check_sound t h).2.1
      (packetOf_spec t T₀),
    refines_of_embeds (covered_refines t h T₀).2 (Table.embeds t h).2 (Table.check_sound t h).2.1
      (packetOf_spec t T₀)⟩

/-- The readings agree between a covered pair and its packet (coincidence target): (E), (AE),
(A), (A⁺) both ways, and (AE°) from the packet to the covered pair. -/
theorem packet_square_covered_readings (t : Table α) (h : t.check = true)
    (T₀ : List α × List α) (a : Covered t T₀) :
    ((coveredGraph t T₀).Productive a ↔ t.graph.Productive (packetOf t T₀ a)) ∧
      ((coveredGraph t T₀).HereditarilyProductive a ↔
        t.graph.HereditarilyProductive (packetOf t T₀ a)) ∧
      ((coveredGraph t T₀).Inevitable a ↔ t.graph.Inevitable (packetOf t T₀ a)) ∧
      ((coveredGraph t T₀).InevMax a ↔ t.graph.InevMax (packetOf t T₀ a)) ∧
      (t.graph.CyclicProductive (packetOf t T₀ a) → (coveredGraph t T₀).CyclicProductive a) :=
  let hR := (packet_square_covered t h T₀).1
  ⟨hR.productive_iff, hR.hereditarilyProductive_iff, hR.inevitable_iff, hR.inevMax_iff,
    hR.cyclicProductive_of_quotient⟩

/-- The readings agree between a covered pair and its packet (success target). -/
theorem packet_square_covered_readings_for (t : Table α) (h : t.check = true)
    (T₀ : List α × List α) (a : Covered t T₀) :
    ((coveredGraphFor t T₀).Productive a ↔ t.graphSuccess.Productive (packetOf t T₀ a)) ∧
      ((coveredGraphFor t T₀).HereditarilyProductive a ↔
        t.graphSuccess.HereditarilyProductive (packetOf t T₀ a)) ∧
      ((coveredGraphFor t T₀).Inevitable a ↔ t.graphSuccess.Inevitable (packetOf t T₀ a)) ∧
      ((coveredGraphFor t T₀).InevMax a ↔ t.graphSuccess.InevMax (packetOf t T₀ a)) ∧
      (t.graphSuccess.CyclicProductive (packetOf t T₀ a) →
        (coveredGraphFor t T₀).CyclicProductive a) :=
  let hR := (packet_square_covered t h T₀).2
  ⟨hR.productive_iff, hR.hereditarilyProductive_iff, hR.inevitable_iff, hR.inevMax_iff,
    hR.cyclicProductive_of_quotient⟩

/-- The packet of an element of the universe is the only row over its reading. -/
theorem universePacket_eq_iff (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) (i : Fin t.packets.length) :
    universePacket t h hT₀ hnc a = i ↔ t.occAt i = reading t.s T₀ a.1 :=
  packetOf_eq_iff t h T₀ _ i

/-- **The packet square** (headline, on the declared universe).  For an accepted table over a
linearly ordered alphabet and a noncoincident listed state `T₀`, the composite
`universePacket` from the actual graph induced on `Universe t.s T₀` to the packet rows is
`Complete` (every retained absolute edge is a listed edge between the packets) and
`SoundEvery` (every listed edge out of the packet of an element of the universe is the packet
image of a retained absolute edge out of that element), with targets preserved and reflected:
for the coincidence target (`t.graph`) and for the success target (`t.graphSuccess`).  It
commutes with the two committed squares (`universePacket_spec`), and the absolute pair
determines the element of the universe (`universe_refines`).  No hypothesis on `t.s`, and none
on `T₀` beyond being a noncoincident listed state. -/
theorem packet_square (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) :
    Refines (universeGraph t.s T₀) t.graph (universePacket t h hT₀ hnc) ∧
      Refines (universeGraphFor t.s T₀ t.target) t.graphSuccess (universePacket t h hT₀ hnc) :=
  ⟨refines_of_embeds (universe_refines t.s T₀).1 (Table.embeds t h).1
      (Table.check_sound t h).2.1 (universePacket_spec t h hT₀ hnc),
    refines_of_embeds (universe_refines_for t.s T₀ t.target) (Table.embeds t h).2
      (Table.check_sound t h).2.1 (universePacket_spec t h hT₀ hnc)⟩

/-- **The readings agree** between an element of the universe and its packet (coincidence
target): (E), (AE), (A), (A⁺) both ways, and (AE°) pulls back from the packet (it holds on the
absolute side vacuously, `universe_acyclic`). -/
theorem packet_square_readings (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) :
    ((universeGraph t.s T₀).Productive a ↔
        t.graph.Productive (universePacket t h hT₀ hnc a)) ∧
      ((universeGraph t.s T₀).HereditarilyProductive a ↔
        t.graph.HereditarilyProductive (universePacket t h hT₀ hnc a)) ∧
      ((universeGraph t.s T₀).Inevitable a ↔
        t.graph.Inevitable (universePacket t h hT₀ hnc a)) ∧
      ((universeGraph t.s T₀).InevMax a ↔ t.graph.InevMax (universePacket t h hT₀ hnc a)) ∧
      (t.graph.CyclicProductive (universePacket t h hT₀ hnc a) →
        (universeGraph t.s T₀).CyclicProductive a) :=
  let hR := (packet_square t h hT₀ hnc).1
  ⟨hR.productive_iff, hR.hereditarilyProductive_iff, hR.inevitable_iff, hR.inevMax_iff,
    hR.cyclicProductive_of_quotient⟩

/-- **The readings agree** between an element of the universe and its packet (success
target). -/
theorem packet_square_readings_for (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) :
    ((universeGraphFor t.s T₀ t.target).Productive a ↔
        t.graphSuccess.Productive (universePacket t h hT₀ hnc a)) ∧
      ((universeGraphFor t.s T₀ t.target).HereditarilyProductive a ↔
        t.graphSuccess.HereditarilyProductive (universePacket t h hT₀ hnc a)) ∧
      ((universeGraphFor t.s T₀ t.target).Inevitable a ↔
        t.graphSuccess.Inevitable (universePacket t h hT₀ hnc a)) ∧
      ((universeGraphFor t.s T₀ t.target).InevMax a ↔
        t.graphSuccess.InevMax (universePacket t h hT₀ hnc a)) ∧
      (t.graphSuccess.CyclicProductive (universePacket t h hT₀ hnc a) →
        (universeGraphFor t.s T₀ t.target).CyclicProductive a) :=
  let hR := (packet_square t h hT₀ hnc).2
  ⟨hR.productive_iff, hR.hereditarilyProductive_iff, hR.inevitable_iff, hR.inevMax_iff,
    hR.cyclicProductive_of_quotient⟩

/-- **The image of the composite** is exactly the set of rows reachable in the packet graph from
the root rows of `T₀`.  `⊆`: an element of the universe is reached from a root reading, whose
literal path lifts through the full child stars of the table (`Embeds.refines`,
`SoundEvery.reach_lift`) to a packet path from the root row, ending at the packet by
injectivity.  `⊇`: a packet path from the row over a root reading lifts from the root element of
the universe (`packet_square`, `SoundEvery.reach_lift`).  So every packet reachable from a root
of `T₀` is the packet of an absolute occurrence pair of the iterates of `T₀`. -/
theorem packet_square_range (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) :
    Set.range (universePacket t h hT₀ hnc) =
      {j | ∃ r : Fin t.packets.length, ∃ P Q, P < T₀.1.length ∧ Q < T₀.2.length ∧
        t.occAt r = ⟨T₀, P, Q, none⟩ ∧ t.graph.Reach r j} := by
  have hinj := (Table.check_sound t h).2.1
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT₀
  ext j
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, -, h1, h2, h3, hb⟩ := a.2
    have hreach := (reading_complete t.s T₀).reach hb
    obtain ⟨r, hr⟩ := Table.roots t h hk hnc h2 h3
    have hr' : reading t.s T₀ b = t.occAt r := h1.trans hr.symm
    rw [hr'] at hreach
    obtain ⟨j', hj', hjj⟩ := (Table.embeds t h).1.refines.soundEvery.reach_lift hreach
    have hj : j' = universePacket t h hT₀ hnc a :=
      hinj (hjj.trans (universePacket_spec t h hT₀ hnc a).symm)
    exact ⟨r, _, _, h2, h3, hr, hj ▸ hj'⟩
  · rintro ⟨r, P, Q, hP, hQ, hr, hj⟩
    have hbal := (((Table.check_iff t).1 h).state_spec hT₀).1.2.1
    let u : Universe t.s T₀ := ⟨rootAnchored t.s hbal P Q, rootAnchored_mem t.s hbal hP hQ⟩
    have hu : universePacket t h hT₀ hnc u = r :=
      (universePacket_eq_iff t h hT₀ hnc u r).2 hr
    rw [← hu] at hj
    obtain ⟨u', -, hu'⟩ := (packet_square t h hT₀ hnc).1.soundEvery.reach_lift hj
    exact ⟨u', hu'⟩

/-- **Infinite packet paths lift to absolute lineages graded by level.**  Every infinite path of
the packet graph from the packet of an element `a` of the universe is the packet image of an
infinite path of the universe graph from `a` (`SoundEvery.liftsPaths`, by dependent choice), and
the level of its `n`-th element is the level of `a` plus `n`.  A cycle of the packet graph is
therefore read off an infinite absolute lineage, never off an absolute cycle
(`universe_acyclic`). -/
theorem packet_path_lift (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀)
    (q : ℕ → Fin t.packets.length) (hq0 : q 0 = universePacket t h hT₀ hnc a)
    (hq : t.graph.IsPath q) :
    ∃ p : ℕ → Universe t.s T₀, p 0 = a ∧ (universeGraph t.s T₀).IsPath p ∧
      (∀ n, universePacket t h hT₀ hnc (p n) = q n) ∧
      ∀ n, (p n).1.1.1.level = a.1.1.1.level + n := by
  obtain ⟨p, hp0, hp, hpq⟩ := (packet_square t h hT₀ hnc).1.liftsPaths a q hq0 hq
  refine ⟨p, hp0, hp, hpq, fun n => ?_⟩
  induction n with
  | zero => rw [hp0]; rfl
  | succ n ih => rw [anchoredGraph_level (hp n), ih]; rfl

/-- **Every seed is covered, up to orientation.**  For a seed `(ab, ba)` of
`Psc.Descendants.seeds`, either it is a listed state and its universe is covered, or its swap is
a listed state and every element of its universe is read, side-swapped, by a row of `t`
(`Table.seeds_listed`, `universe_swap`, `reading_swap`, `universe_covered`). -/
theorem seed_universe_covered (t : Table α) (h : t.check = true) {T : List α × List α}
    (hT : T ∈ seeds) :
    (T ∈ t.states ∧ Universe t.s T ⊆ {a | ∃ i, t.occAt i = reading t.s T a}) ∨
      (T.swap ∈ t.states ∧
        ∀ a ∈ Universe t.s T, ∃ i, t.occAt i = (reading t.s T a).swap) := by
  obtain ⟨x, y, hxy, rfl⟩ := mem_seeds.1 hT
  have hnc : [x, y] ≠ [y, x] := fun he => hxy (List.cons.inj he).1
  rcases Table.seeds_listed t h hT with hl | hl
  · exact Or.inl ⟨hl, universe_covered t h hl hnc⟩
  · refine Or.inr ⟨hl, fun a ha => ?_⟩
    exact universe_covered t h hl (fun he => hnc he.symm) (universe_swap ha)

/-- **The packet square in the mirrored frame.**  For a frame `T` whose swap is a noncoincident
listed state, the side swap followed by the packet of the universe of `T.swap` is a refinement
of the universe graph of `T` onto the packet graph, for the coincidence target and for the
success target (`packet_square` at `T.swap`, then `refines_precomp` along the isomorphism
`universeSwap_graph`, which is onto by `universeSwap_surjective`).  The row reached reads the
element side-swapped (`universeSwap_packet_eq_iff`). -/
theorem packet_square_swap (t : Table α) (h : t.check = true) {T : List α × List α}
    (hT : T.swap ∈ t.states) (hnc : T.swap.1 ≠ T.swap.2) :
    Refines (universeGraph t.s T) t.graph (fun a => universePacket t h hT hnc (universeSwap a)) ∧
      Refines (universeGraphFor t.s T t.target) t.graphSuccess
        (fun a => universePacket t h hT hnc (universeSwap a)) :=
  ⟨refines_precomp (packet_square t h hT hnc).1 universeSwap_surjective
      (fun a b => (universeSwap_graph t.target a b).1)
      (fun a => (universeSwap_graph t.target a a).2.1),
    refines_precomp (packet_square t h hT hnc).2 universeSwap_surjective
      (fun a b => (universeSwap_graph t.target a b).1)
      (fun a => (universeSwap_graph t.target a a).2.2)⟩

/-- In the mirrored frame, the row reached from an element of the universe of `T` is the only
row over its side-swapped reading. -/
theorem universeSwap_packet_eq_iff (t : Table α) (h : t.check = true) {T : List α × List α}
    (hT : T.swap ∈ t.states) (hnc : T.swap.1 ≠ T.swap.2) (a : Universe t.s T)
    (i : Fin t.packets.length) :
    universePacket t h hT hnc (universeSwap a) = i ↔ t.occAt i = (reading t.s T a.1).swap :=
  universePacket_eq_iff t h hT hnc (universeSwap a) i

/-- **The packet square for every seed, in its own frame.**  For every seed `(ab, ba)` of
`Psc.Descendants.seeds` there is a map from its universe to the rows that is a refinement of the
universe graph onto the packet graph, for both targets; it is `universePacket` when the seed is
listed (`packet_square`), and the side swap followed by `universePacket` of the mirrored seed
when its swap is listed (`packet_square_swap`), and the row reached is the only row over the
reading, resp. over the side-swapped reading (`Table.seeds_listed`). -/
theorem seed_square (t : Table α) (h : t.check = true) {T : List α × List α} (hT : T ∈ seeds) :
    ∃ π : Universe t.s T → Fin t.packets.length,
      Refines (universeGraph t.s T) t.graph π ∧
        Refines (universeGraphFor t.s T t.target) t.graphSuccess π ∧
        ((T ∈ t.states ∧ ∀ a i, π a = i ↔ t.occAt i = reading t.s T a.1) ∨
          (T.swap ∈ t.states ∧ ∀ a i, π a = i ↔ t.occAt i = (reading t.s T a.1).swap)) := by
  obtain ⟨x, y, hxy, rfl⟩ := mem_seeds.1 hT
  have hnc : [x, y] ≠ [y, x] := fun he => hxy (List.cons.inj he).1
  rcases Table.seeds_listed t h hT with hl | hl
  · exact ⟨_, (packet_square t h hl hnc).1, (packet_square t h hl hnc).2,
      Or.inl ⟨hl, universePacket_eq_iff t h hl hnc⟩⟩
  · have hnc' : ([x, y], [y, x]).swap.1 ≠ ([x, y], [y, x]).swap.2 := fun he => hnc he.symm
    exact ⟨_, (packet_square_swap t h hl hnc').1, (packet_square_swap t h hl hnc').2,
      Or.inr ⟨hl, universeSwap_packet_eq_iff t h hl hnc'⟩⟩

/-- **The full digit star commutes through the composite: children and splits.**  For an
element `a` of the universe of a noncoincident listed state `T₀`, with packet `p` (its row):

1. every absolute child `x'` of `a` along `(d, e)` (`absStep`), when the reading of `a` is not
   a coincidence, is either the absolute pair of a retained child `b` of `a` in the universe,
   and then `.child d e (packet of b)` is in the star of `p`, or it is `Separated`, and then
   some `.split d e k k'` is in the star of `p`;
2. every `.child d e j` in the star of `p` is the packet of a retained child `b` of `a` whose
   absolute pair is the absolute child of `a` along `(d, e)`;
3. every `.split d e k k'` in the star of `p` names an absolute child of `a` along `(d, e)` that
   is `Separated`.

From `universe_valid` (with `IsBlock T₀` from `statesOK`), `occStep_isSome`, `anchor_step`,
`Anchor.split_separated`, the star equation (`Table.Accepted.star_eq`,
`Table.Accepted.child_entry_iff`) at the packet, `universePacket_spec` and, for the child
destinations, `universePacket_eq_iff`.  A separated absolute pair stays separated along every
absolute lineage, and no absolute descendant of it has an irreducible reading containing both
positions (`Separated.lineage`, `Separated.not_anchor`; `universe_absStep`). -/
theorem universe_star (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀) :
    (∀ {d e : ℕ} {x' : AbsOcc}, (reading t.s T₀ a.1).block.1 ≠ (reading t.s T₀ a.1).block.2 →
      absStep t.s T₀ a.1.1.1 d e = some x' →
      (∃ b : Universe t.s T₀, b.1.1.1 = x' ∧ (universeGraph t.s T₀).child a b ∧
          StarRow.child d e (universePacket t h hT₀ hnc b).val ∈
            t.stars.getD (universePacket t h hT₀ hnc a).val []) ∨
        (∃ k k', StarRow.split d e k k' ∈ t.stars.getD (universePacket t h hT₀ hnc a).val [] ∧
          Separated t.s T₀ x')) ∧
    (∀ {d e j : ℕ}, StarRow.child d e j ∈ t.stars.getD (universePacket t h hT₀ hnc a).val [] →
      ∃ b : Universe t.s T₀, absStep t.s T₀ a.1.1.1 d e = some b.1.1.1 ∧
        (universeGraph t.s T₀).child a b ∧ (universePacket t h hT₀ hnc b).val = j) ∧
    (∀ {d e k k' : ℕ},
      StarRow.split d e k k' ∈ t.stars.getD (universePacket t h hT₀ hnc a).val [] →
      ∃ x', absStep t.s T₀ a.1.1.1 d e = some x' ∧ Separated t.s T₀ x') := by
  have hA := (Table.check_iff t).1 h
  have hblk : IsBlock T₀ := (hA.state_spec hT₀).1
  have hspec := universePacket_spec t h hT₀ hnc a
  have hstar := hA.star_eq (universePacket t h hT₀ hnc a)
  rw [hspec] at hstar
  obtain ⟨off, hAnc⟩ := a.1.2
  refine ⟨fun {d e x'} hna hx => ?_, fun {d e j} hm => ?_, fun {d e k k'} hm => ?_⟩
  · obtain ⟨-, hP, hQ, -⟩ := universe_valid hblk a.2
    change a.1.1.2.top < a.1.1.2.block.1.length at hP
    change a.1.1.2.bot < a.1.1.2.block.2.length at hQ
    obtain ⟨hPx, hQx, hd, he, -⟩ := absStep_some hx
    obtain ⟨hlt, hlb⟩ := hAnc.letters hP hQ
    rw [List.getElem?_eq_getElem hPx, List.getElem?_eq_getElem hP] at hlt
    rw [List.getElem?_eq_getElem hQx, List.getElem?_eq_getElem hQ] at hlb
    have hd' : d < (t.s a.1.1.2.block.1[a.1.1.2.top]).length := Option.some.inj hlt ▸ hd
    have he' : e < (t.s a.1.1.2.block.2[a.1.1.2.bot]).length := Option.some.inj hlb ▸ he
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (occStep_isSome hAnc.balanced hP hQ hd' he')
    cases o with
    | child y' =>
      obtain ⟨x'', off'', hx'', hA''⟩ := anchor_step hAnc ho
      rw [hx] at hx''
      obtain rfl := Option.some.inj hx''
      have hedge : (anchoredGraph t.s T₀).child a.1 ⟨(x', y'), off'', hA''⟩ :=
        ⟨hna, d, e, hx, ho⟩
      let b : Universe t.s T₀ := ⟨_, universe_closed t.s T₀ a.2 hedge⟩
      refine Or.inl ⟨b, rfl, hedge, ?_⟩
      have hm : (d, e, Outcome.child y') ∈
          occStar t.s (t.occAt (universePacket t h hT₀ hnc a)) := by
        rw [hspec]
        exact mem_occStar.2 ⟨hna, ho⟩
      obtain ⟨dst, hdst, hdec⟩ := (hA.child_entry_iff _ d e y').2 hm
      obtain ⟨k, rfl, hk⟩ := hA.decodeAt_some hdec
      rw [← (universePacket_eq_iff t h hT₀ hnc b k).2 hk] at hdst
      exact hdst
    | split k k' =>
      obtain ⟨x'', hx'', hsep⟩ := hAnc.split_separated ho
      rw [hx] at hx''
      obtain rfl := Option.some.inj hx''
      refine Or.inr ⟨k, k', ?_, hsep⟩
      have hm : (d, e, some (Outcome.split k k')) ∈
          (t.stars.getD (universePacket t h hT₀ hnc a).val []).map t.decodeEntry := by
        rw [hstar]
        exact mem_map_some.2 (mem_occStar.2 ⟨hna, ho⟩)
      obtain ⟨r, hr, hre⟩ := List.mem_map.1 hm
      cases r with
      | child d₁ e₁ dst => simp [Table.decodeEntry] at hre
      | split d₁ e₁ k₁ k₁' =>
        simp only [Table.decodeEntry, Prod.mk.injEq, Option.some.injEq,
          Outcome.split.injEq] at hre
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hre
        exact hr
  · have hj : j < t.packets.length := by
      have hm' := List.mem_map_of_mem (f := t.decodeEntry) hm
      rw [hstar] at hm'
      obtain ⟨r, -, hr⟩ := List.mem_map.1 hm'
      simp only [Table.decodeEntry, Prod.mk.injEq] at hr
      obtain ⟨-, -, hr⟩ := hr
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hr.symm
      exact Table.lt_of_decodeAt hy
    have hc := (hA.child_entry_iff (universePacket t h hT₀ hnc a) d e
      (t.occAt ⟨j, hj⟩)).1 ⟨j, hm, hA.decodeAt_eq ⟨j, hj⟩⟩
    rw [hspec] at hc
    obtain ⟨hna, ho⟩ := mem_occStar.1 hc
    obtain ⟨x', off', hx', hA'⟩ := anchor_step hAnc ho
    have hedge : (anchoredGraph t.s T₀).child a.1 ⟨(x', t.occAt ⟨j, hj⟩), off', hA'⟩ :=
      ⟨hna, d, e, hx', ho⟩
    let b : Universe t.s T₀ := ⟨_, universe_closed t.s T₀ a.2 hedge⟩
    exact ⟨b, hx', hedge, congrArg Fin.val ((universePacket_eq_iff t h hT₀ hnc b ⟨j, hj⟩).2 rfl)⟩
  · have hm' : (d, e, some (Outcome.split k k')) ∈
        (t.stars.getD (universePacket t h hT₀ hnc a).val []).map t.decodeEntry :=
      List.mem_map_of_mem (f := t.decodeEntry) hm
    rw [hstar] at hm'
    obtain ⟨-, ho⟩ := mem_occStar.1 (mem_map_some.1 hm')
    exact hAnc.split_separated ho

end Linear

/-! ### Calibration: Fibonacci -/

/-- The seed `(01, 10)` of Fibonacci is a noncoincident listed state of `fibTable`. -/
theorem fib_seed_listed : tmPair ∈ fibTable.states ∧ tmPair.1 ≠ tmPair.2 := by decide

/-- The universe of the Fibonacci seed `(01, 10)` is covered by `fibTable`. -/
theorem fib_universe_covered :
    Universe fibSubst tmPair ⊆ {a | ∃ i, fibTable.occAt i = reading fibSubst tmPair a} :=
  universe_covered fibTable fib_accepted fib_seed_listed.1 fib_seed_listed.2

/-- The root element of the Fibonacci universe at positions `(1, 0)`. -/
def fibRoot10 : Universe fibSubst tmPair :=
  ⟨rootAnchored fibSubst fib_root_isBlock.2.1 1 0,
    rootAnchored_mem fibSubst fib_root_isBlock.2.1 (by decide) (by decide)⟩

/-- **A reading transferred through the square.**  The element of the Fibonacci universe at
level 0 and positions `(1, 0)` reads as `fibDead`; its packet is row 2 (`fib_rows`); it is not
productive in the universe graph (`fib_block_readings`, through `universe_readings`), and
`packet_square_readings` carries that to row 2 of the packet graph. -/
theorem fib_dead_packet :
    universePacket fibTable fib_accepted fib_seed_listed.1 fib_seed_listed.2 fibRoot10 =
        ⟨2, by decide⟩ ∧
      ¬ (universeGraph fibSubst tmPair).Productive fibRoot10 ∧
      ¬ fibTable.graph.Productive ⟨2, by decide⟩ := by
  have h2 : fibTable.occAt ⟨2, by decide⟩ = fibDead := by
    have := (fib_rows).1
    unfold Table.occAt
    rw [this]
    rfl
  have hp : universePacket fibTable fib_accepted fib_seed_listed.1 fib_seed_listed.2 fibRoot10 =
      ⟨2, by decide⟩ :=
    (universePacket_eq_iff fibTable fib_accepted _ _ fibRoot10 _).2 h2
  have hu : ¬ (universeGraph fibSubst tmPair).Productive fibRoot10 := fun hpr =>
    fib_block_readings.2.2.1 ((universe_readings fibSubst tmPair fibRoot10).1.1 hpr)
  refine ⟨hp, hu, fun hpr => hu ?_⟩
  rw [← hp] at hpr
  exact (packet_square_readings fibTable fib_accepted _ _ fibRoot10).1.2 hpr

/-! ### Negative control: the square fails without a linear order -/

/-- The seed `(ab, ba)` of the `weird` table (`Psc.PacketCertificate.weird`: Fibonacci over a
two-letter type with the empty `<`). -/
def weirdSeed : List EmptyOrderLetter × List EmptyOrderLetter := ([.a, .b], [.b, .a])

/-- `weirdSeed` is a noncoincident listed state of `weird`. -/
theorem weirdSeed_listed : weirdSeed ∈ weird.states ∧ weirdSeed.1 ≠ weirdSeed.2 := by decide

/-- The rows of `weird` the control reads: the decoded pairs of rows 1 and 3 are the root pairs
`(0, 1)` and `(1, 1)` of `weirdSeed`; rows 9 and 18 decode to one pair, and no other row does;
rows 1 and 16 are the only rows over their pairs; the edges `1 → 9`, `3 → 12`,
`12 → 16`, `16 → 18` are listed and `1 → 18`, `16 → 9` are not. -/
theorem weird_square_rows :
    weird.occAt ⟨1, by decide⟩ = ⟨weirdSeed, 0, 1, none⟩ ∧
      weird.occAt ⟨3, by decide⟩ = ⟨weirdSeed, 1, 1, none⟩ ∧
      weird.occAt ⟨18, by decide⟩ = weird.occAt ⟨9, by decide⟩ ∧
      (∀ i, weird.occAt i = weird.occAt ⟨9, by decide⟩ → i.val = 9 ∨ i.val = 18) ∧
      (∀ i, weird.occAt i = weird.occAt ⟨1, by decide⟩ → i.val = 1) ∧
      (∀ i, weird.occAt i = weird.occAt ⟨16, by decide⟩ → i.val = 16) ∧
      weird.graph.child ⟨1, by decide⟩ ⟨9, by decide⟩ ∧
      weird.graph.child ⟨3, by decide⟩ ⟨12, by decide⟩ ∧
      weird.graph.child ⟨12, by decide⟩ ⟨16, by decide⟩ ∧
      weird.graph.child ⟨16, by decide⟩ ⟨18, by decide⟩ ∧
      ¬ weird.graph.child ⟨1, by decide⟩ ⟨18, by decide⟩ ∧
      ¬ weird.graph.child ⟨16, by decide⟩ ⟨9, by decide⟩ := by
  have h1 : weird.stars.getD 1 [] =
      [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 9, .child 1 1 10] := rfl
  have h16 : weird.stars.getD 16 [] =
      [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 18, .child 1 1 10] := rfl
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ⟨1, 0, by decide⟩, ⟨0, 1, by decide⟩,
    ⟨0, 0, by decide⟩, ⟨1, 0, by decide⟩, ?_, ?_⟩
  · rintro ⟨d, e, hde⟩
    rw [h1] at hde
    simp at hde
  · rintro ⟨d, e, hde⟩
    rw [h16] at hde
    simp at hde

/-- **The packet square fails without a linear order.**  On the accepted table `weird` (empty
`<`, `weird_accepted`), over the universe of its listed seed `(ab, ba)`, the composite
`universePacket` is neither sound from every source nor complete.  Rows 9 and 18 decode to one
occurrence pair `x` (`weird_not_injective`), and `universePacket` sends every element of the
universe over `x` to one row `k`.  `x` is reached in the universe from the root pair `(0, 1)`
(row 1, listed edge `1 → 9`) and from the root pair `(1, 1)` along rows `3 → 12 → 16`, then the
listed edge `16 → 18`.  If `k = 18`, the listed edge `1 → 9` has no lift out of the root
element and the retained edge into `x` lands on the unlisted `1 → 18`; if `k = 9`, the same
holds at the element over row 16 with `16 → 18` and `16 → 9`.  So the injectivity of
`t.occAt`, which `[LinearOrder α]` supplies, cannot be dropped from `packet_square` (or from
`packet_square_covered`, whose carrier contains these elements). -/
theorem weird_square_fails :
    ¬ SoundEvery (universeGraph weird.s weirdSeed) weird.graph
        (universePacket weird weird_accepted weirdSeed_listed.1 weirdSeed_listed.2) ∧
      ¬ Complete (universeGraph weird.s weirdSeed) weird.graph
        (universePacket weird weird_accepted weirdSeed_listed.1 weirdSeed_listed.2) := by
  obtain ⟨r1, r3, r18, u9, u1, u16, e19, e312, e1216, e1618, n118, n169⟩ := weird_square_rows
  set π := universePacket weird weird_accepted weirdSeed_listed.1 weirdSeed_listed.2
  have hspec := universePacket_spec weird weird_accepted weirdSeed_listed.1 weirdSeed_listed.2
  have hcongr : ∀ {u v : Universe weird.s weirdSeed},
      reading weird.s weirdSeed u.1 = reading weird.s weirdSeed v.1 → π u = π v :=
    fun huv => packetOf_congr weird weirdSeed huv
  have hbal : Equiv1 weirdSeed.1 weirdSeed.2 :=
    (seed_isBlock (by decide : EmptyOrderLetter.a ≠ .b)).2.1
  let w1 : Universe weird.s weirdSeed :=
    ⟨rootAnchored weird.s hbal 0 1, rootAnchored_mem weird.s hbal (by decide) (by decide)⟩
  let w3 : Universe weird.s weirdSeed :=
    ⟨rootAnchored weird.s hbal 1 1, rootAnchored_mem weird.s hbal (by decide) (by decide)⟩
  have hw1 : reading weird.s weirdSeed w1.1 = weird.occAt ⟨1, by decide⟩ := r1.symm
  have hw3 : reading weird.s weirdSeed w3.1 = weird.occAt ⟨3, by decide⟩ := r3.symm
  obtain ⟨wx, h1x, hwx⟩ := universe_step weird weird_accepted weirdSeed hw1 e19
  obtain ⟨w12, -, hw12⟩ := universe_step weird weird_accepted weirdSeed hw3 e312
  obtain ⟨w16, -, hw16⟩ := universe_step weird weird_accepted weirdSeed hw12 e1216
  obtain ⟨wy, h16y, hwy⟩ := universe_step weird weird_accepted weirdSeed hw16 e1618
  have hp1 : π w1 = ⟨1, by decide⟩ := Fin.ext (u1 _ ((hspec w1).trans hw1))
  have hp16 : π w16 = ⟨16, by decide⟩ := Fin.ext (u16 _ ((hspec w16).trans hw16))
  have hxy : π wy = π wx := hcongr (hwy.trans (r18.trans hwx.symm))
  have hk := u9 _ ((hspec wx).trans hwx)
  -- every element over the pair `x` has the packet `π wx`
  have hover : ∀ v : Universe weird.s weirdSeed,
      reading weird.s weirdSeed v.1 = weird.occAt ⟨9, by decide⟩ → π v = π wx :=
    fun v hv => hcongr (hv.trans hwx.symm)
  constructor
  · intro hS
    rcases hk with hk | hk
    · -- `π wx = 9`: the listed edge `16 → 18` has no lift out of `w16`
      obtain ⟨v, -, hv⟩ := hS w16 (y' := ⟨18, by decide⟩) (hp16 ▸ e1618)
      have hvx : π v = π wx :=
        hover v ((hspec v).symm.trans ((congrArg weird.occAt hv).trans r18))
      rw [hv] at hvx
      exact absurd (congrArg Fin.val hvx) (by rw [hk]; decide)
    · -- `π wx = 18`: the listed edge `1 → 9` has no lift out of `w1`
      obtain ⟨v, -, hv⟩ := hS w1 (y' := ⟨9, by decide⟩) (hp1 ▸ e19)
      have hvx : π v = π wx := hover v ((hspec v).symm.trans (congrArg weird.occAt hv))
      rw [hv] at hvx
      exact absurd (congrArg Fin.val hvx) (by rw [hk]; decide)
  · intro hC
    rcases hk with hk | hk
    · have he := hC h16y
      rw [hp16, hxy, show π wx = ⟨9, by decide⟩ from Fin.ext hk] at he
      exact n169 he
    · have he := hC h1x
      rw [hp1, show π wx = ⟨18, by decide⟩ from Fin.ext hk] at he
      exact n118 he

end Psc.PacketSquare
