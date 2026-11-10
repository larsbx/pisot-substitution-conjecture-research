# Packet square: actual occurrence edges, literal occurrence pairs, checked packet rows — 2026-11-10

**Status:** research result. It has two parts: graph logic in Lean, and four literal finite
tables checked by the Lean kernel, produced by a Mojo exporter and recomputed by an
independent Python oracle. No governed claim moves and no ledger claim is added; the tests
declare contracts only. The result is mechanically checked at its stated scope. Independent
human review is pending (non-blocking validation debt). The receipts are local until the hosted
`packet-square.yml` and `ci.yml` runs on the integrating revision exist. Nothing here concerns
C4, G1, #84, #138, #139 or PSC (see [Non-claims](#non-claims--remaining-gaps)).

This note records the second item of the immediate sequence in
[the research roadmap](research-roadmap-2026-09-21.md) ("(2) realization-preserving packet
square"; P0 row "Literal packet realization/refinement") and the item "P0 OCCURRENCE
REFINEMENT" of the 2026-11-09 priority addendum in [`README.llm.txt`](../README.llm.txt). The
literature stop/go gate for it is [packet-square-stop-go-2026-11-10.md](packet-square-stop-go-2026-11-10.md),
with the decision "Proceed, narrowed". The predicate names below follow its §1.

## 1. The problem and the three obligations

The addendum asks for "commutation of actual substitution-child occurrence edges with certified
packet transitions". Every packet should carry both source occurrence addresses, the chosen
indices, the ordered parent/ordinal/child, the orientation, the residual Parikh vector, the
strict interior/boundary bit and the target. It also says that "soundness, completeness and
infinite-path lifting are DIFFERENT proof obligations". The roadmap row adds that completeness
is to be stated *relative to the declared occurrence universe*, and that no obligation may be
inferred from another.

The three obligations, as Lean predicates on a projection `π : X → Y` from an actual child
graph `G` to a quotient `P` (`Psc.GraphRefinement`):

* **completeness** `Complete G P π`: every actual edge has its quotient edge (the forward
  condition);
* **soundness** `SoundEvery G P π`: every quotient edge out of `π x` is the image of an actual
  edge out of **that** `x` (the backward condition, from every source). The weaker
  `SoundSome` asks this only for some source of the fibre;
* **infinite-path lifting** `LiftsPaths G P π x`: every infinite quotient path from `π x` is
  the image of an actual path from `x`.

Targets are preserved (`TargetDown`) and reflected (`TargetUp`) separately. `Refines G P π`
bundles `Complete`, `SoundEvery`, `TargetDown` and `TargetUp` (`Psc.GraphRefinement.Refines`,
in `PscVerif.GraphEmbedding`). Several hypotheses have a named countermodel, each a theorem
that drops one hypothesis of one transfer. Those of `PscVerif.GraphRefinement` are labelled
`dropped`, `undrawn`, `overdrawn`, `overdrawnFork`, `broken`, `unroll`, `tail` and `fan` in
its docstring; `PscVerif.GraphEmbedding` adds `brokenLoop_no_lift`, `dropped_inevitable`,
`fan_inevitable`, `unroll_embeds`, the four (A⁺) countermodels and the two finite-source
ones. They do not cover every hypothesis of every transfer: in particular `TargetDown` and
`TargetUp` have no separate countermodel (the list is under
[Negative controls](#negative-controls)).

The readings are those of `Psc.QuantifierInterface`:

* (E) `Productive`: some path reaches a target;
* (AE) `HereditarilyProductive`: every reachable state is productive;
* (A) `Inevitable`: every infinite path meets a target;
* (A⁺) `InevMax`: every maximal path meets a target, dead ends included;
* (AE°) `CyclicProductive`: every reachable state on a cycle is productive.

### Which word means which predicate on which arrow

The same English word names opposite directions on different arrows. This is the confusion
the addendum warns against, so every statement below is cited by its predicate. The actual side
is always written first.

| Arrow (actual `X` → quotient `Y`) | "every abstract transition is real" | "nothing real is missing" |
| --- | --- | --- |
| composite: universe element → packet row (`universePacket`) | `SoundEvery (universeGraph t.s T₀) t.graph (universePacket …)` (`packet_square`) | `Complete …` (`packet_square`); relative to the declared universe: `packet_of_red` |
| ρ: anchored absolute pair → literal occurrence pair (`reading s T₀`) | `SoundEvery (anchoredGraph s T₀) (occGraph s) (reading s T₀)` (`reading_soundEvery`) | `Complete …` (`reading_complete`, definitional); relative to the declared universe: `anchored_cover_universe` |
| D: packet row → literal occurrence pair (`t.occAt`). Here the **table is the source side** | `Complete t.graph (occGraph t.s) t.occAt` = `Table.graph_sound` = `Embeds.sound` ("every listed edge is literal") | `SoundEvery t.graph (occGraph t.s) t.occAt` = `Table.graph_complete` = `Embeds.complete` ("full child stars"); relative to the declared universe: `Table.range_eq_reach` |
| β: literal occurrence pair → balanced-pair state (`Occ.block`) | `SoundSome` from irreducible sources only (`block_soundSome_at`); **not** `SoundEvery` (`fib_block_readings`) | `Complete` (`block_complete`) |

At layer D, then, the export's "soundness" (every listed edge is literal) is `Complete`. Its
"completeness" (no child is missing from a star) is `SoundEvery`. On the composite, "soundness" of
the packet abstraction is `SoundEvery` with the absolute pairs as the actual side.

## 2. The four graphs and the three maps

```text
  A  universeGraph s T₀      absolute pairs (level, top, bot) in σⁿ(T₀.1), σⁿ(T₀.2), each with its reading
        │ ρ = reading s T₀                 Refines, both targets (universe_refines, universe_refines_for)
        ▼
  O  occGraph s              literal occurrence pairs Occ: ordered block, top, bot, birth (oriented parent, ordinal)
        ▲ D = t.occAt                     Embeds, both targets (Table.embeds); injective over a linear order
        │
  P  t.graph                 rows of an accepted packet table, Fin t.packets.length

  O ── β = Occ.block ──▶ B  bpaGraph s     Complete, targets; SoundSome from irreducible sources; not SoundEvery

  composite  universePacket t h hT₀ hnc : A → P,  t.occAt ∘ universePacket = ρ  (universePacket_spec)
             Refines, both targets (packet_square)
```

| Object | Lean name | Module |
| --- | --- | --- |
| obligations, transfers, countermodels | `Complete`, `SoundSome`, `SoundEvery`, `TargetDown`, `TargetUp`, `LiftsPaths`, `SoundEvery.liftsPaths`, `quotientDistance_iff` | `PscVerif.GraphRefinement` |
| bundles and the transfers added for the square | `Refines`, `Embeds`, `embeds_iff_refines`, `Refines.productive_iff` / `hereditarilyProductive_iff` / `inevitable_iff` / `inevMax_iff`, `Refines.cyclicProductive_of_quotient`, `Embeds.cyclicProductive_iff`, `brokenLoop_no_lift`, `broken_liftsPaths_vacuous`, `unroll_embeds` | `PscVerif.GraphEmbedding` |
| addresses and the transport law at a cut | `cutAddr`, `cutAddr_spec`, `blockStart`, `getElem_red`, `residual_transport`, `cut_residual_zero` | `PscVerif.OccurrenceAddress` |
| **O**, the literal occurrence graph | `Occ`, `occStep`, `occStar`, `mem_occStar`, `occStep_child_iff`, `occStep_split_iff`, `length_occStar`, `occGraph`, `occGraphFor`, `occChild.childNC`, `residual_step` | `PscVerif.OccurrenceGraph` |
| **A**, ρ and β | `AbsOcc`, `absStep`, `Anchor`, `Anchored`, `anchoredGraph`, `reading`, `Universe`, `universeGraph`, `universeGraphFor`, `universe_refines`, `universe_readings`, `universe_reading_unique`, `anchored_cover_universe`, `absLineage_anchor`, `block_complete`, `block_soundSome_at`, `fib_block_readings` | `PscVerif.OccurrenceRealisation` |
| **P**, the record and its checker | `Table`, `Table.check`, `Table.clauses`, `Table.check_sound`, `Table.iso`, `Table.range_eq_reach`, `Table.graph`, `Table.graphSuccess` | `PscVerif.PacketCertificate` |
| the composite | `Psc.PacketCertificate.Table.embeds`, `Covered`, `coveredGraph`, `packetOf`, `packetOf_spec`, `universePacket`, `packet_square`, `packet_square_covered`, `packet_square_readings`, `packet_path_lift`, `packet_of_red`, `universe_star`, `seed_square` | `PscVerif.PacketSquare` |
| the four checked tables | `table`, `accepted : table.check = true` (one `decide +kernel` each) | `PscVerif.PacketSquareData.{Tribonacci, RealSecondary, NonPisot, GfActual}` |
| the controls on the exported tables | `trib_*`, `rs_*`, `np_*`, `gf_*` (§7) | `PscVerif.PacketSquareControls` |

The sources are `proof/PscVerif/PscVerif/` + module path + `.lean`. For example the composite is
[`PacketSquare.lean`](../proof/PscVerif/PscVerif/PacketSquare.lean) and the controls are
[`PacketSquareControls.lean`](../proof/PscVerif/PscVerif/PacketSquareControls.lean). Each module
docstring lists what it does and does not prove. The proof bank lists the named theorems (43,
42, 12, 65, 95, 91, 41 for the first seven modules; one per data module), with the controls
module added at integration.

### The addendum's fields

The fields are definitions on `Occ` (`PscVerif.OccurrenceGraph`). An accepted table carries each
of them in a row field or in its star, and the checker re-derives all of them except the `birth`
field, which `birthOK` checks only to name an earlier parent (§5):

| Field | Definition | On every literal edge |
| --- | --- | --- |
| both source occurrence addresses | `Occ.topAddr`, `Occ.botAddr`: (source position, digit, global position, local position) | `occStep_addr` |
| chosen indices | the digit pair `(d, e)` of the edge | `occStep_digits_unique` |
| ordered parent / ordinal / child | `birth = (oriented parent, ordinal)`; `Occ.Valid` | `occChild.valid` |
| orientation | ordered blocks, no side-swap normalisation; `Occ.swap` | `occStep_swap`, `Occ.residual_swap` |
| residual Parikh | `Occ.residual`, the prefix defect inside the block | `residual_step` (§4) |
| strict interior / boundary | `Occ.Interior`, `Occ.Boundary` (decidable) | `Occ.atStart_iff` |
| target | `Occ.Coincident` (`occGraph`), `Occ.SuccessFor` (`occGraphFor`) | targets of both graphs |

## 3. What each arrow transfers

| Arrow | Obligations | (E) | (AE) | (A) | (A⁺) | (AE°) |
| --- | --- | --- | --- | --- | --- | --- |
| ρ on the universe (`universe_readings`; success target `universe_refines_for`) | `Refines`, no hypothesis on `s`, `T₀` | ⇔ | ⇔ | ⇔ | ⇔ | O ⇒ A only |
| D on an accepted table | `Embeds` (`Table.embeds`), hence `Refines` with the table as source (`Embeds.refines`); no order hypothesis | ⇔ | ⇔ | ⇔ | ⇔ | ⇔ only with injectivity (`Embeds.cyclicProductive_iff`, injectivity from `Table.check_sound` over a linear order) |
| composite on the universe (`packet_square_readings`, `packet_square_readings_for`) | `Refines`, `[LinearOrder α]` | ⇔ | ⇔ | ⇔ | ⇔ | P ⇒ A only; the absolute side has no cycle (`universe_acyclic`) |
| β (`block_productive`, `block_inevitable`, `fib_block_readings`) | `Complete`, targets; `SoundSome` from irreducible sources | O ⇒ B; B ⇏ O | B ⇏ O | B ⇒ O; O ⇏ B | none established | none established |

"⇏" means that a literal countermodel exists (Fibonacci `fibDead`, §7 item 1′); "none
established" means that no transfer is claimed. The D row is the composition
`(Table.embeds t h).1.refines` with `Refines.productive_iff` and its siblings. It is not a
separately named theorem.

**The headline statement** (`Psc.PacketSquare.packet_square`). Let `t : Table α` with
`h : t.check = true` over `[Fintype α] [LinearOrder α]`, and let `T₀` be a noncoincident listed
state (`hT₀ : T₀ ∈ t.states`, `hnc : T₀.1 ≠ T₀.2`). Then

```lean
Refines (universeGraph t.s T₀) t.graph (universePacket t h hT₀ hnc) ∧
  Refines (universeGraphFor t.s T₀ t.target) t.graphSuccess (universePacket t h hT₀ hnc)
```

There is no hypothesis on `t.s`. Around it:

* `universePacket_eq_iff`: the row reached is the only row over the reading.
* `packet_square_range`: its image is the set of rows reachable from the root rows of `T₀`.
* `packet_square_covered`: the same square on the general carrier `Covered t T₀` (the anchored
  pairs whose reading is the decoded pair of some row), with `packetOf` chosen by choice;
  `packetOf_spec` (`t.occAt (packetOf t T₀ a) = reading t.s T₀ a.1`) is the commuting square.
* `packet_square_swap`, `seed_square`: the mirrored frame. Every seed `(ab, ba)` has such a
  square in its own frame, through its listed orientation or its listed swap.
* `packet_fields` (no order hypothesis): the letters of the packet row of a covered pair are the
  letters at its two absolute positions in `σⁿ(T₀)`. Its residual is the absolute prefix defect
  there, and its addresses and its `interior` and `success` bits are those of the reading.

**Completeness relative to the declared universe.** The declared universe `Universe s T₀` is the
set of anchored pairs reached by retained edges from the level-0 root readings `⟨T₀, P, Q, none⟩`.
It is a set of absolute pairs, not of pairs with arbitrary readings: on it the reading, birth
record included, is a function of the absolute pair (`universe_reading_unique`). It holds every
absolute pair whose two positions lie in one **noncoincident** irreducible block of
`red (σⁿ T₀.1) (σⁿ T₀.2)`. For a root that is an irreducible block this is
`anchored_cover_universe` and `anchored_cover_red`, and through the table `packet_of_red` (no
order hypothesis): such a pair is the absolute pair of exactly one element of the universe, whose
packet decodes to that block at the local positions. At layer D the statement is
`Table.range_eq_reach`: the decoded rows are exactly the literal occurrence pairs reachable in
`occGraph t.s` from the root pairs of the noncoincident listed states. `universe_covered` places
the universe of a noncoincident listed state inside the decoded rows. `seed_universe_covered`
does the same for every seed, read in its listed orientation or side-swapped (`seedsOK`).

**Children and splits.** `universe_star`: every absolute child of a universe element with a
noncoincident reading is one of two things. It is either a retained child, whose packet is the
destination of the `.child d e` entry of the packet star, or `Separated`, with a `.split d e k k'`
entry at the same digits. Conversely every `.child` and `.split` entry is realised in this way.
`split_never_rejoins`: no absolute descendant of a split child has an irreducible reading, at any
depth.

**Infinite-path lifting** is a corollary of `SoundEvery` and needs no further hypothesis. It
holds along ρ (`reading_liftsPaths`, and choice-free through `absLineage_anchor`) and along the
composite (`packet_path_lift`): every infinite path of the packet graph from the packet of a
universe element is the image of an infinite path of the universe graph from that element. On
that path the level rises by exactly one per step. It is **not** cycle realisation: the universe
graph has no cycle (`universe_acyclic`, `covered_acyclic`, `anchored_no_cycle`), so a packet
cycle is read off an infinite absolute lineage of `σⁿ(T₀)`, never off an absolute cycle.
Lifting from prefixes would need finite branching and a finite set of sources
(`exists_lift_of_finite_sources`, with both hypotheses shown necessary). The set of universe
elements over one packet row can be infinite. Row 209 of `1/02/202` lies on a packet cycle and
is the packet of the universe element `rsU3` (`rs_cycle_packets`); by `rs_cycle_realised`
(through `packet_path_lift`) the lifted path from `rsU3` returns to row 209 at every even step,
at a new level each time. So prefix lifting from finitely many sources is unavailable in
general, and the design uses `SoundEvery` instead. Not every such set is infinite: a root row
decodes with birth `none` (`Table.decode`), and a universe element above level 0 has a birth
record (`universe_birth`), so by `universePacket_spec` only level-0 elements have a root row as
their packet. This is a composition of those statements, not a named theorem.

## 4. The derived transport law

The packet update `r' = M r + λ` (`docs/c4-ordered-word-completion-interface-2026-11-02.md` §1)
is derived in Lean from literal prefixes. It is not assumed by the export.

1. `Psc.OccurrenceAddress.residual_transport`: select letters `u[i]`, `v[j]` and digits `d`, `e`
   of their images, and take a balanced cut `lo` of `(σ u, σ v)` at or before both inflated
   positions. Measured from `lo`, the Parikh difference of the two prefixes is
   `M · (u.take i − v.take j) + ((σ u[i]).take d − (σ v[j]).take e)`. No hypothesis says that the
   two positions fall in one child.
2. `Psc.OccurrenceGraph.residual_step`: take a balanced block and a literal edge
   `occStep s x d e = some (.child y)`, and put the cut at the start of the child block. Then
   `y.residual = M · x.residual + forcing s x d e`. Its forms are `residual_step_vec`,
   `residual_atStart` (`M r + λ = 0` at a child start), `residual_iterate_lt` (along a finite path,
   which may end at a dead end or a coincidence) and `residual_iterate`
   (`r_n = Mⁿ r_0 + Σ_{t<n} M^{n−1−t} λ_t` along an infinite literal lineage).
3. On the absolute side: `Anchor.residual` says that the absolute prefix defect of
   `σⁿ(T₀.1)`, `σⁿ(T₀.2)` at an anchored pair is the residual of its reading.
   `Psc.PacketSquare.packet_fields` says that the residual of the packet row of a covered pair is
   that absolute prefix defect.

Since `packetOK` re-derives every row's residual from the definitions (§5), the law holds along
every listed edge of an accepted table, by `Table.check_sound`, `Table.graph_sound` and
`residual_step`. This is a composition, not a separately stated theorem. The Python oracle
checks it executably on every child entry (185 / 948 / 82 / 235). It also checks the
asynchronous form `Parikh(σ(T)[:ti]) − Parikh(σ(B)[:bi]) = M r + λ` on every digit pair, split
or not (379 / 2,222 / 164 / 455 digit pairs).

## 5. The certificate

**Record** (`packet-square-v1`; `PscVerif.PacketCertificate`). `Table α` has the fields `letters`,
`s`, `target`, `states`, `factors`, `packets` (with `state`, `sign`, `top`, `bot`, `factor`,
`topAddr`, `botAddr`, `letters`, `residual`, `interior`, `success` and `birth`), `stars` (the
full digit star of each row, children and splits with both ordinals), `keyOrder` and `hubs`.
`Table.decode` / `Table.occAt` read a row as a literal occurrence pair.

**Checker.** `Table.check` is the conjunction of eleven `Bool` clauses, evaluated by one
`decide +kernel` per table. `Table.clauses` lists them in order, and `Table.check_eq_clauses`
lets a control state the refusing clause:

| Clause | Decides | Layer |
| --- | --- | --- |
| `lettersOK` | every letter once (the residual coordinate order) | — |
| `statesOK` | each state an irreducible block in normalised orientation, no repetition | L2 |
| `seedsOK` | every normalised seed `([a, b], [b, a])`, `a < b`, is listed | L2 |
| `factorsOK` | for each noncoincident state, its factor rows are the blocks of `red (σ T.1) (σ T.2)` in order, with ordinal, orientation, bounds and image length | L3 |
| `keysOK` | `keyOrder` lists the rows by strictly increasing `Table.keyCode` | L6 |
| `rootsOK` | the root rows are `(i, +, P, Q)` for the noncoincident states in order, positions row-major | L6 |
| `birthOK` | each non-root row names an incoming `.child` entry from an **earlier** row | L6 |
| star count | `stars.length = packets.length` | L5 |
| `packetOK` (every row) | addresses, letters, residual, `interior`, `success` re-derived from the decoded pair | L4 |
| `starOK` (every row) | the star is the literal `occStar` of the decoded pair, in order: every child and every split | L5 |
| `hubsOK` | each listed hub row: state in range and noncoincident, hub a listed letter, `(state, hub)` unique, bits equal to `factorHub` slot by slot, `none` exactly where undefined | L7 |

**What an accepted table yields.** `Table.check_sound` (`[LinearOrder α]`) says that every row
decodes, and that `occAt` is injective. Every decoded pair is `Occ.Valid`, every star is the
literal `occStar`, every carried field has its literal value, and every row is reachable from a
root row. `Table.iso` (`[LinearOrder α]`) gives an isomorphism of `t.graph` onto the subgraph of
`occGraph t.s` induced on the child-closed set `Set.range t.occAt`, for both targets.
`Table.range_eq_reach` (no order hypothesis) is the completeness statement of §3. `Table.roots`,
`Table.hubs_sound`, `Table.hubs_rows`, `Table.seeds_listed` and `Table.bpaStatesNC_listed` (one
inclusion only) complete the list.

**Fail-closed behaviour.** Every gate is in the refuse-to-proceed column of the `AGENTS.md`
fail-closed table. None deletes or overwrites a committed file.

* The checker refuses rather than repairs. An out-of-range destination decodes to `none` and
  fails `starOK`; it is never reduced modulo the row count. Missing roots fail `rootsOK`. A
  coerced undefined hub bit fails `hubsOK`.
* The exporter refuses on an exhausted state, length, packet or edge cap, and on
  `--target sync-right`, and then emits no table and no Lean module. An exhausted budget is
  reported as inconclusive, never as a verdict.
* `kernel/check_packet_square.sh` refuses in three cases: a missing committed data module, any
  other file or directory under the data-module prefix, and any byte difference.
* The Python oracle raises `InvalidPacketSquare` naming the layer, or `BudgetExhausted`
  (inconclusive).

**The four checked tables.** Generated by the exporter with `--target any --hub-rows` and the
default caps (state 20,000, length 10,000, packets 200,000, edges 2,000,000):

| Module | σ | States | Factor rows | Rows | Child entries | Split entries | Roots | Hub rows | Successes | PIP (recorded) | Single-file time, peak RSS |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `Tribonacci` | `01/02/0` | 6 | 12 | 132 | 185 | 194 | 37 | 15 | 0 | true | 11.0 s, 7,194 MiB |
| `RealSecondary` | `1/02/202` | 10 | 26 | 507 | 948 | 1,274 | 118 | 24 | 23 | true | 36.9 s, 9,760 MiB (9.5 GiB) |
| `NonPisot` | `1/012/1` | 4 | 6 | 46 | 82 | 82 | 12 | 9 | 1 | false | 7.5 s, 6,881 MiB |
| `GfActual` | `1/2/021` | 8 | 12 | 153 | 235 | 220 | 39 | 18 | 6 | true | 11.9 s, 7,272 MiB |

How the cost column was measured: one run each of `lake env lean` on this container. Importing
`PscVerif.PacketCertificate` alone takes 5.7 s and 6,718 MiB, mostly mapped Mathlib and Lean
object files. In one parallel `lake build` they took 18 s (`NonPisot`), 24 s (`Tribonacci`),
25 s (`GfActual`) and 55 s (`RealSecondary`).
`PscVerif.PacketSquareControls` takes 87.6 s single-file. These are local measurements, not
hosted-runner figures. The checker does not read the PIP field.

## 6. The exporter, the evidence and the oracle

* **Canonical Mojo exporter.**
  [`kernel/psc/packet_square_export.mojo`](../kernel/psc/packet_square_export.mojo), with the
  driver [`kernel/packet_square_export.mojo`](../kernel/packet_square_export.mojo). It reads the
  packet graph of `psc.target_packets.build_packets`, which is unchanged. The archived
  `target-aware-bpa-v1` bytes still reproduce. To that graph it adds:
  * the full digit star of every packet, with each split's two ordinals, recomputed and refused
    unless the split count equals `split_count`;
  * the birth (first incoming edge);
  * a key order equal to the numeric order of `Table.keyCode`;
  * hub rows, with undefined bits printed as `null` / `none`;
  * the PIP status, recorded and never a filter;
  * `verify_packet_square`, a second literal computation of every row, star, birth, key and hub
    bit.

  It emits JSONL and the Lean data modules.
* **Hidden dependencies.** The driver takes `parse_sigma` and `parse_positive` from
  `kernel/target_aware_bpa.mojo`, and the module takes `ints_json` from
  `kernel/psc/target_packet_report.mojo`. The Mojo import closure of the driver and the test is
  46 files: the driver, the test, the archived driver, 18 files under `kernel/psc/`, and 25
  files of the vendored `finite_exact`, `finite_graph`, `finite_linear_algebra`, `mojo_smoke`
  and `substitution_dynamics`.
* **Regression test.** [`kernel/tests/test_packet_square_export.mojo`](../kernel/tests/test_packet_square_export.mojo)
  pins the four fixtures' counts (`test_fixture_counts`), the mutation controls at their layers
  and the caps. It also renders the Lean module line by line from the committed JSONL alone. It
  ends with `require_contract("packet-square-v1 export: …")`, a contract and not a ledger claim.
* **Regenerate and compare.** [`kernel/check_packet_square.sh`](../kernel/check_packet_square.sh)
  rebuilds the four JSONL files and the four Lean data modules and compares them byte for byte.
  It also checks the checksums, the cap, `sync-right` and malformed-input refusals, and that no
  other entry sits under `PscVerif.PacketSquareData.`.
* **Evidence.** [`evidence/packet-square-2026-11-10/`](../evidence/packet-square-2026-11-10/)
  holds four JSONL files and `SHA256SUMS`.
* **Independent oracle.** [`oracles/python/packet_square_oracle.py`](../oracles/python/packet_square_oracle.py)
  imports nothing from `kernel/` and uses Python `int` only. It:
  * rebuilds every JSONL file from σ and compares the bytes;
  * audits each table clause by clause at least as strictly as `Table.check`;
  * checks the transport law and the split account;
  * compares with the archived `target-aware-bpa-v1` dumps;
  * replays absolute occurrences of the swap seeds and their swaps to a stated level;
  * compares the committed Lean modules field by field and against a template.

  Its tests are [`tests/test_packet_square_oracle.py`](../tests/test_packet_square_oracle.py).
* **CI.** [`.github/workflows/packet-square.yml`](../.github/workflows/packet-square.yml) has
  four jobs, each bound to the exact head revision with `test "$(git rev-parse HEAD)" =
  "$EXPECTED_HEAD"`:
  * a path-filter guard. It recomputes from the sources the Lean, Mojo and Python import
    closures of the packet-square files, and the Python import closure of
    `tools/make_proof_bank.py`, which `tools/setup_lean.sh` runs when it provisions the Lean
    job (with `tools/` on `sys.path`: `tools/make_ledger.py`, `tools/proof_records/`,
    `tools/claim_governance/`). It adds a hand-written list of inputs that are read rather
    than imported: the three Lean pins, `tools/setup_lean.sh`, `kernel/pixi.toml` and
    `kernel/pixi.lock`, the evidence `SHA256SUMS`, `pyproject.toml` and the archived
    `real-secondary.jsonl`. It refuses any of these files that the filter misses, an import it
    cannot resolve, and a push filter that differs from the pull-request filter. It traces no
    other input;
  * a Lean job: `tools/setup_lean.sh`, `lake build` of the packet-square modules with one data
    module per invocation, and an axiom audit of every declaration those twelve modules own;
    each step clears `LEAN_*`, `LAKE_*` and `MATHLIB_CACHE_*` and disables Lake's caches, as
    `tools/setup_lean.sh` and `tools/check_lean.sh` do;
  * a Mojo job: pinned `prefix-dev/setup-pixi@v0.9.1` with `pixi-version: v0.81.0` and
    `locked: true`, then the regression test with its receipt and `check_packet_square.sh` with
    its `PASS` line;
  * a Python job: the oracle tests, `tests/test_target_packet_evidence.py`, and the oracle
    command line with its pass line.

  Each job uploads its receipts with `if-no-files-found: error`. `ci.yml` (`lean-proofs`) still
  builds the whole package and replays `ProofBankAudit.lean` on every push.

## 7. Controls and their rejection layers

Layers: **L0** input, **L1** PIP record, **L2** states and caps, **L3** literal ordered
factorisation, **L4** row fields, **L5** full child stars, **L6** identity and reachability,
**L7** hub bits, **L8** graph logic, **L9** premises outside the square (Pisot, strict
child-closed support). A control is filed under the first layer at which it stops being
evidence for the tempting conclusion. In the Evidence column a bare Lean name is in the
namespace `Psc.PacketSquareControls`, unless a namespace followed by a colon precedes it in the
same cell (`Psc.PacketCertificate`: `fib_side_swapped`); such a prefix holds until the next one
or the end of the cell. Other names are written in full.

| # | Control | Outcome | Layer | Evidence |
| --- | --- | --- | --- | --- |
| 1 | Tribonacci `01/02/0` (positive) | accepted. 38 noncoincident and 9 coincidence rows have no child entry. No row is a success. Every universe element is unproductive for the success target. The lineage `(0,0,0) → (1,1,1) → (2,2,2)` of seed `(01, 10)` has packets `0 → 38 → 57` | none for the square; L8: (A) ≠ (A⁺) for both targets | `PscVerif.PacketSquareData.Tribonacci.accepted`; `trib_shape`, `trib_universe_no_success`, `trib_inevitable_ne_inevMax`, `trib_universe_inevitable_ne_inevMax`, `trib_lineage` |
| 1′ | Fibonacci `0 ↦ 01, 1 ↦ 0` (Lean only; binary). The repository records it inside the standing class (`Psc.QuantifierBinding.fib_lasso`) and outside the three-letter corpus | β complete and not `SoundEvery`. (AE) at the block while (E) fails at the pair; (A) at the pair while it fails at the block | L8 (β) | `Psc.OccurrenceRealisation.fib_block_readings`, `Psc.OccurrenceGraph.fibDead_star`, `Psc.PacketSquare.fib_dead_packet` |
| 2 | packet cycle `209 -(0,0)-> 429 -(0,2)-> 209` of `1/02/202` | accepted. Both rows and stars are literal. It is realised by an infinite absolute lineage with level rising by one per step, never by an absolute cycle. States 7 and 8 lie in no strict closed set | L8 (realisation); L9 (support not strict) | `rs_cycle_rows`, `rs_cycle_literal`, `rs_cycle_packets`, `rs_cycle_realised`, `rs_support_not_strict`; `Psc.OccurrenceRealisation`: `rs_cycle_lineage`, `rs_infinite_lineage` |
| 3 | non-Pisot strict `1/012/1` (`x³ − x² − 2x`) | accepted; the headline square applies unchanged | L1 / L9: rejected only at the PIP hypothesis (reducible incidence polynomial `x(x − 2)(x + 1)`; eigenvalue −1 on the unit circle); the square is PIP-blind by design | `PscVerif.PacketSquareData.NonPisot.accepted`; `np_incidence_eigen` (eigenvalues 2, −1, 0), `np_rows`, `np_square_blind` |
| 4 | strong G/F template of `1/2/021` | actual closure accepted. The template states have 1, 2, 5 literal blocks (the template proposes 1, 1, 3), and the third has a diagonal `2/2` | L3 | `gf_actual_shape`, `gf_template_literal`, `gf_template_refused`, `gf_template_states_refused`, `gf_template_table_refused`; Mojo test |
| 5 | seed `(01, 10)` of `1/02/202`, "second letter / depth one" | no depth-one success. Success at depth two, `2 -(1,1)-> 124 -(0,2)-> 346`. Row 154 has letters `(2, 2)` at residual `(−1, 1, 0)` and is not a success | L4 | `rs_seed_rows`, `rs_depth_one_no_success`, `rs_depth_two_success`, `rs_matching_letters_refused` |
| 6 | dropped split entry | refused by the star clause only | L5 | `np_dropped_split`; `Psc.PacketCertificate`: `fib_dropped_split` |
| 7 | side-swapped row | refused. The row clause refuses the letters, the swapped row collides with the key of row 30, and four stars fail | L4, L5, L6 | `np_side_swapped`, `fib_side_swapped_collision`; `Psc.PacketCertificate`: `fib_side_swapped` (keys, rows and stars) |
| 8 | coerced undefined hub bit; other hub-row faults | refused by the hub clause only | L7 | `np_hub_coerced`; `Psc.PacketCertificate`: `fib_hub_coerced`, `fib_hub_undefined`, `fib_hub_state_oob`, `fib_hub_coincident`, `fib_hub_duplicate` |
| 9 | duplicated row | refused by the key clause alone; without that clause `occAt` is not injective | L6 | `np_duplicate_isolated`, `np_duplicate_not_injective`; `Psc.PacketCertificate`: `fib_duplicate_isolated`, `fib_duplicate_not_injective`; and a non-isolated variant, `Psc.PacketCertificate`: `fib_duplicate_key`, refused by the key and birth clauses together |
| 10 | wrong global position | refused by the row clause only | L4 | `np_wrong_global`; `Psc.PacketCertificate`: `fib_wrong_global` |
| 11 | forged root-unreachable mirror of success row 147, with literal fields and star | refused by the birth clause for every birth record; with the sibling's birth `(10, 0, 2)` (`1/02/202`) and with three birth records (Fibonacci) every other clause accepts | L6 | `rs_forged_outside`, `rs_forged_not_reached`, `rs_forged_refused`; `Psc.PacketCertificate`: `fibExtra_forged_outside`, `fibExtra_forged_not_reached`, `fibExtra_forged_unreachable`; oracle `forged_mirror` |
| 12 | naive letter-pair quotient, 2-cycle `(0,1) -(1,0)-> (1,0) -(0,1)-> (0,1)` (Tribonacci) | no packet walk of length 4 over it, hence no packet cycle | L5 | `trib_letterpair_cycle`, `trib_letterpair_cycle_unrealised` |
| 13 | empty order (forged normalisation): Fibonacci over `EmptyOrderLetter` | accepted. Rows 9 and 18 decode to one pair, `occAt` is not injective, and the square fails. Over `Fin 2` the same rows are refused | L6, which is sound only together with a strict total order | `Psc.PacketCertificate`: `weird_accepted`, `weird_rows_collide`, `weird_not_injective`, `weirdFin_refused`; `Psc.PacketSquare`: `weird_square_fails` |
| 14 | the other mutations on `fibTable` | refused at their clauses | L2–L5 | `Psc.PacketCertificate`: `fib_no_seed` (seeds, L2); `fib_wrong_stop` (factors, L3); `fib_wrong_ordinal` (factors, rows and stars, L3–L5); `fib_wrong_residual`, `fib_wrong_interior` (rows, L4); `fib_dropped_child`, `fib_wrong_split`, `fib_bad_destination`, `fib_truncated` (stars, L5) |
| 15 | quotient cycle without an actual cycle (generic) | — | L8 | `Psc.GraphRefinement`: `unroll_cycle`, `tail_not_cyclic`, `unroll_cyclicProductive`, `unroll_embeds` (the last in the module `PscVerif.GraphEmbedding`); `Psc.PacketSquare`: `universe_acyclic`, `covered_acyclic`; `Psc.OccurrenceRealisation`: `anchored_no_cycle` |
| 16 | caps, `sync-right`, malformed input; missing or extra data module | refused, no table | L0 / L2; gate | `check_packet_square.sh`; Mojo `test_caps_and_synchronize_mode_refuse`; oracle `BudgetExhausted`, `InvalidPacketSquare` |

The addendum's control list (`README.llm.txt`, "The known controls include …") maps onto the
table as follows:

* second-letter, depth-one: row 5;
* naive six-state: row 12;
* strong G/F: row 4;
* productive packet cycles: row 2;
* phase-flat non-PIP strict: row 3.

"Zero source defect with different parents" is definitional in O: two pairs with equal residual
and different parent words are different `Occ`, because `birth` records the oriented parent. No
fixture is replayed for it. The binary productive-root / nonproductive-descendant example
(`Psc.QuantifierBinding.tm_fork`) is graph logic and transfers along `Refines` like any reading.
It is not replayed here. No fixture for rank-three delayed PIP synchronization was located.

Further observations come from the Python oracle on the four committed tables (finite, pinned
in `tests/test_packet_square_oracle.py`; they are not theorems):

| Fixture | Noncoincident dead-end rows | Roots reaching a coincidence row | Rows read from the seed roots (level ≤ 9) | Non-seed root rows never read from a seed |
| --- | ---: | ---: | ---: | ---: |
| `01/02/0` | 38 | 21 of 37 | 107 | 25 |
| `1/02/202` | 208 | 48 of 118 | 389 | 106, plus non-root rows 150–161 |
| `1/012/1` | 12 | 2 of 12 | 46 | 0 |
| `1/2/021` | 42 | 24 of 39 | 126 | 27 |

## 8. Corrections found during the work

Items 1–4 and 6, the hub-row strictness of item 5, and the oracle and packet-154 corrections of
item 7 are already in [the side-notes ledger](side-notes-ledger.md) (entries of 2026-11-10). The
archived hub-row count of item 5 and the Tribonacci root count of item 7 are first recorded here;
the integrating commit adds their ledger line.

1. **The order hypothesis for injectivity.** Suppose the checker keys orientation on `isNormal`
   under an arbitrary `<`. Then an accepted table may list a state and its swap, and two rows
   with distinct keys decode to one occurrence pair (`weird`, §7 row 13). Injectivity of
   `occAt`, `Table.iso` and `packet_square` therefore carry `[LinearOrder α]`. The (AE°)
   equivalence along D (§3) is `Embeds.cyclicProductive_iff` composed with that injectivity, so
   it is available under `[LinearOrder α]`; it is not a separately named theorem. A `Fin 3`
   data module with the default instances is covered (`fin3_occAt_injective`). The statements
   that need no injectivity stay under `[LT α] [DecidableLT α]`: `Table.range_eq_reach`,
   `Table.embeds`, `packet_of_red`, `packet_fields`. A clause refusing a listed state whose swap
   is listed would have been the alternative; it was not taken.
2. **The declared universe is not the pair type, and it differs at coincidence blocks.**
   `Anchored s T₀` (absolute pair with some reading) constrains neither irreducibility, nor the
   positions, nor the birth record. One absolute pair can carry two readings there, so the
   headline statements live on `Universe s T₀`, and `Covered` is kept as the general carrier.
   An earlier draft described the universe as "every absolute pair inside an irreducible block
   of `red (σⁿ T₀.1) (σⁿ T₀.2)`"; that description is false at coincidence blocks. Fibonacci,
   root `(01, 10)`: the pair `(2, 0, 0)` lies in the coincidence block `(0, 0)` of
   `red (01001) (01010)` and is in no universe element (`fib_lvl2_not_universe`,
   `anchored_cover_needs_hnc`). The noncoincidence hypothesis of `anchored_cover_universe` is
   necessary.
3. **`broken` separates `SoundSome` from `SoundEvery` only along finite paths.** Its quotient
   has no infinite path, so `LiftsPaths` holds there vacuously (`broken_liftsPaths_vacuous`).
   The countermodel for infinite lifting is `brokenLoop_no_lift` (`step2` onto `loop`).
4. **Birth.** The checker accepts any earlier parent whose star holds the child
   (`fibExtra_birth_not_first`). The exporter, the oracle and the archive use the first incoming
   edge. No theorem depends on which incoming edge is recorded: the `birth` field is used only
   to give reachability from a root row. A birth that is not the first edge is accepted, and one
   from a later row is refused.
5. **Hub-row strictness.** `hubsOK` checks:
   * state range and noncoincidence;
   * that the hub is a listed letter;
   * uniqueness of `(state, hub)`;
   * the bits, slot by slot.

   An earlier draft of the clause compared only the bits of each listed hub row with
   `factorHub`; the committed clause also checks the first three items. The export lists one
   row per (noncoincident state, letter): 15 / 24 / 9 / 18 rows. The archived `ordered_hub_row` records
   (`evidence/ordered-hub-packets-2026-10-06/`) list the support states of each recurrent SCC,
   once per SCC: 27 records for `1/02/202` are 15 distinct `(state, hub)` pairs. That listing
   would fail `hubsOK`, so no repository file should repeat it as a hub-row count. The checker
   accepts a table whose hub rows are dropped, because only listed hub rows are re-derived. The
   oracle requires none or all of them.
6. **Exporter interface.** An earlier draft of the interface had
   `emit_packet_square_lean(sq, module, hub_rows)` and no hub rows in `PacketSquare`. The
   committed `emit_packet_square_lean` and `packet_square_lean` take a further `command`
   argument (the regeneration command printed in the module header), and `PacketSquare`
   carries the hub rows `hubs`.
7. **Smaller corrections.**
   * The expectation that every Tribonacci root packet is productive for the coincidence target
     is false: 21 of 37 reach a coincidence row (oracle observation). For Tribonacci, (A) and
     (A⁺) differ for both targets (`trib_inevitable_ne_inevMax`; for the success target the
     witness is the coincidence row 37, a dead end of `graphSuccess`). The other three fixtures
     also have noncoincident dead-end rows (`1/02/202` 208, `1/012/1` 12, `1/2/021` 42; oracle
     observation, §7). By `graph_deadEnd` and `deadEnd_inevitable_not_inevMax`, (A) and (A⁺)
     then differ there for the coincidence target, but no Lean statement names such a row for
     these three tables, and none compares (A) with (A⁺) for their success target.
   * The target-packet Python oracle was a fixed-point check. It now checks reachability from the
     roots (`2868ce4`).
   * The Mojo test comment on packet 154 of `1/02/202` now says that the packet is the mirror of
     packet 341, a seed descendant, and not a seed descendant itself.
   * The data-module docstring states exactly what `Table.check` decides, including that
     `birth` is not re-derived.

## Work shown

### Assumptions and hypotheses

* **Lean.** Every statement carries its own hypotheses:
  * `t.check = true` wherever a row's content is used;
  * `[Fintype α] [DecidableEq α]`, and `[LinearOrder α]` exactly where injectivity of
    `t.occAt` is used: `Table.check_sound`, `Table.iso`, `packetOf_eq_iff`,
    `universePacket_eq_iff`, `packet_square_covered`, `packet_square` and their readings,
    `packet_square_range`, `packet_path_lift`, `universe_star`, `packet_square_swap`,
    `universeSwap_packet_eq_iff`, `seed_square`, and `seed_universe_covered` (whose
    `Table.seeds_listed` needs a total order);
  * `T₀ ∈ t.states` and `T₀.1 ≠ T₀.2` for the headline square;
  * `IsBlock T₀`, an irreducible reading with noncoincident block, and positions inside it, for
    `anchored_cover_universe`.

  **No hypothesis is placed on the substitution:** no primitivity, no irreducibility of the
  incidence matrix, no Pisot or unimodularity property, no nonerasing assumption. The axioms are
  `propext`, `Classical.choice` and `Quot.sound` only. There is no `sorry`, no `native_decide`
  and no local axiom.
* **Executable.** Alphabet 3, the four σ above, `--target any`, the default caps. The PIP field
  is recorded and never a filter. The Python oracle uses exact integers and no randomness.
* **Derived, not assumed:** the transport law (§4), the star equation, the uniqueness of the
  reading on the universe, and the birth record of a universe element (`universe_birth`).

### Derivation / reduction

1. **ρ.** The digit star of an occurrence pair depends on `(block, top, bot)` only (`occStep`
   does not read `birth`). So every literal edge out of the reading of an anchored pair is the
   reading of an absolute edge out of that pair, at any level and offset (`anchor_step`, hence
   `reading_soundEvery`). `Complete` and the two target conditions are definitional
   (`reading_refines`). On the universe the reading is a function (`universe_reading_unique`),
   so the square restricts to `universe_refines`.
2. **D.** `Table.check` re-derives every factor row, every row except its `birth` field, every
   star and every listed hub row from `Psc.Reduction.red`, and checks births, roots, seeds and
   key order. `Table.embeds` (no order hypothesis) bundles acceptance as an embedding of
   `t.graph` into `occGraph t.s` with full child stars, for both targets. `Table.check_sound`
   adds injectivity over a linear order, and `Table.iso` combines the two onto the child-closed
   range.
3. **Composite.** `refines_of_embeds`: a refinement ρ onto an actual graph factors through an
   **injective** embedding `e` along any `π` with `e ∘ π = ρ`. Injectivity is used once for
   `Complete` and once for `SoundEvery`, to identify the row an edge arrives at. With
   `π = universePacket` and `universePacket_spec` this gives `packet_square`. The readings then
   transfer by `Refines.*_iff`, and path lifting by `SoundEvery.liftsPaths`.
4. **Completeness relative to the universe.** `universe_covered` comes from
   `universe_reading_mem_of_closed`, with the range of `t.occAt`. That range is child-closed by
   `Table.closed_range` and holds the root pairs by `Table.roots`. The intrinsic form
   `packet_of_red` combines `anchored_cover_red` (induction on the level, with `anchor_parent`
   as parent closure) with `universe_reading_unique` and `universePacket_spec`.
5. **Mirrored frame.** `universeSwap` is an isomorphism of universe graphs (`absStep_swap`,
   `universe_swap_iff`), and `refines_precomp` transports a refinement along it.

### Evidence and replay

Local receipts, this container, revision `00d81cd` with the controls module of this wave in the
working tree. Nothing here is a hosted-CI receipt.

| Receipt | Command (from the repository root unless stated) | Result |
| --- | --- | --- |
| package build and full audit at `00d81cd`, before the controls module (recorded in its commit message) | `lake build`, then `lake env lean ProofBankAudit.lean`; replay with `./tools/check_lean.sh` | 5,548 declarations, 4,015 theorems, standard axioms only |
| controls module | `cd proof/PscVerif && lake env lean PscVerif/PacketSquareControls.lean` | rc 0, no output, 87.6 s; 79.5 s on a rerun with `-o` (below) |
| focused axiom audit (the heredoc of the `lean` job of `packet-square.yml`) | after the controls olean exists (precondition below): `cd proof/PscVerif && lake --no-cache env lean <audit file>` | 12 modules, 1,590 owned declarations (1,039 compiled theorem constants, generated ones included); the four `accepted`, `packet_square` and `Table.check_sound` depend on `propext`, `Classical.choice`, `Quot.sound` |
| exporter regression | `cd kernel && pixi run --locked mojo run -I . -I tests tests/test_packet_square_export.mojo` | `contract-receipt: packet-square-v1 export: …`, 6 s |
| regenerate and compare | `cd kernel && pixi run --locked bash check_packet_square.sh` | `PASS packet-square-v1: …`, 10 s; no tracked file changed |
| oracle tests | `python3 -m pytest -q -p no:cacheprovider tests/test_packet_square_oracle.py tests/test_target_packet_evidence.py` | exit 0, 96 tests (72 + 24 progress dots), 6 s. With the `addopts = "-q"` of `pyproject.toml` the command runs at `-qq` and prints no summary line; without the `-q` it ends `96 passed` |
| oracle command line | `python3 oracles/python/packet_square_oracle.py` | exit 0, `packet-square oracle: every check passed on the four committed fixtures …` |
| evidence digests | `(cd evidence/packet-square-2026-11-10 && sha256sum -c SHA256SUMS)` | four `OK` (inside the gate) |
| path-filter guard (the `path-filter` job's script) | the heredoc of `packet-square.yml`, run from the root | Lean 77 files (52 modules, 3 pins, `tools/setup_lean.sh`, and the 21 Python files of the import closure of `tools/make_proof_bank.py`), Mojo 50 (46 sources, 4 gate inputs), Python 15 (12 sources, 3 inputs); none outside the filter, `PATH_FILTER_COVERS_CLOSURES`. The 21 files are exactly the files under the repository that `import make_proof_bank` loads, with `tools/` on `sys.path` |
| one table, by hand | `cd proof/PscVerif && lake env lean PscVerif/PacketSquareData/RealSecondary.lean` | rc 0; times in §5 |
| regenerate one table | `cd kernel && pixi run --locked mojo run -I . packet_square_export.mojo --sigma 1/02/202 --target any --hub-rows` | byte-equal to `evidence/packet-square-2026-11-10/real-secondary.jsonl` |

**Precondition of the focused axiom audit.** The audit imports
`PscVerif.PacketSquareControls`. Until the integrating commit imports that module from
`PscVerif.lean`, no plain `lake build` produces its olean, and in this tree the audit refuses
with `object file '…/.lake/build/lib/lean/PscVerif/PacketSquareControls.olean' of module
PscVerif.PacketSquareControls does not exist` (rc 1). The audit reproduces after
`lake build +PscVerif.PacketSquareControls`, which the `lean` job runs before it, or after the
integrating `lake build` once `PscVerif.lean` imports the module. The local receipt above did
not run that build. It used an overlay `<overlay>` in a scratch directory:

1. compile the controls module into it, from the source whose sha256 is
   `ecb945db537451c758e3a1af81998f73dd9368ef5dfd25566ed865744f634df4`:
   `lake env lean -o <overlay>/PscVerif/PacketSquareControls.olean PscVerif/PacketSquareControls.lean`
   (rc 0, 79.5 s);
2. fill the rest of `<overlay>` with a symlink copy of `.lake/build/lib/lean` (Lean resolves
   every `PscVerif.*` module in the first search-path entry that holds a `PscVerif` directory,
   so the overlay must hold all of them);
3. run `LEAN_PATH=<overlay>:$(lake env printenv LEAN_PATH) $(lake env which lean) <audit file>`
   (rc 0, 5 s), and check the three assertions of the workflow step.

Hosted receipts still to come are the `packet-square.yml` and `ci.yml` (`lean-proofs`,
`mojo-kernel`, `python-tests`) runs on the integrating revision. The Lean job is new: it has not
yet run on a hosted runner, and its build step has not been run locally in this form.

### Negative controls

* **Mathematical.** The controls of §7 with their rejection layers. The checker refuses the
  tables of rows 4–11 and 14 at the named clause. Rows 1, 1′, 2, 3, 12, 13 and 15 bound what
  the graph logic gives; row 13 is a table the checker accepts and on which the square
  fails. The countermodels of the modules `PscVerif.GraphRefinement` and
  `PscVerif.GraphEmbedding` (namespace `Psc.GraphRefinement`) each drop one hypothesis of one
  transfer, in the direction their docstrings name:
  * `Complete` cannot be dropped from either (AE) transfer (`dropped_hereditarilyProductive`,
    `undrawn_hereditarilyProductive`), nor from (A) quotient ⇒ actual (`dropped_inevitable`);
  * `SoundEvery` cannot be dropped from (E) or (AE) quotient ⇒ actual
    (`overdrawn_productive`), nor from (AE) actual ⇒ quotient
    (`overdrawnFork_hereditarilyProductive`); without path lifting, (A) actual ⇒ quotient
    fails (`fan_inevitable`);
  * neither `Complete` nor `SoundEvery` can be dropped from either (A⁺) transfer
    (`dropped_inevMax`, `overdrawn_inevMax`, `undrawn_inevMax`, `overdrawnFork_inevMax`);
  * `SoundSome` does not replace `SoundEvery`: `broken_productive` along finite paths,
    `brokenLoop_no_lift` for infinite lifting;
  * injectivity cannot be dropped from (AE°) along an embedding (`unroll_embeds`);
  * neither finiteness hypothesis can be dropped from `exists_lift_of_finite_sources`
    (`fan_finite_sources_no_lift`, `chains_finite_sources_no_lift`).

  `TargetDown` and `TargetUp` have no separate countermodel, and the list does not cover
  every hypothesis of every row of the transfer tables (no named theorem states, for instance,
  that `Complete` is needed for (E) actual ⇒ quotient). `anchored_cover_needs_hnc` bounds the
  universe at coincidence blocks, and `weird_square_fails` bounds the order hypothesis.
* **Executable.** The exporter's mutation controls (36 of 38 mutants killed in the wave-A
  review). The cap, `sync-right` and malformed-input refusals of the gate, and its refusal of a
  missing, stale or extra data module. The oracle's forgeries (`forged_mirror`, a dropped split,
  exchanged split ordinals, a side swap, a wrong ordinal, a late birth, a coerced hub bit, a
  wrong global position, wrongly typed JSON) and its refusal of a missing Lean module.
* **CI gates of this note.**
  * The focused axiom audit was run against four substituted controls modules. It refused a
    `sorry` (`sorryAx`), a `native_decide` (its generated axiom), a local `axiom`, and a module
    owning no theorem.
  * The path-filter guard was run against five mutated filters. It refused the omission of
    `kernel/psc/**` (18 files), of `kernel/target_aware_bpa.mojo` and of
    `reference/psc_research/**` (9 files). It refused the narrowing of `proof/PscVerif/**` to
    `proof/PscVerif/*.lean` (55 files), and a push filter that differed from the pull request
    filter.
  * After the import trace of `tools/make_proof_bank.py` was added, it was run, on a scratch
    copy of the tree, against eight more mutations. It refused the omission of
    `tools/claim_governance/**` (13 files), `tools/proof_records/**` (6),
    `tools/make_ledger.py` and `tools/make_proof_bank.py`. It refused a new local package
    imported by `tools/make_proof_bank.py`, a new module imported inside a function of
    `tools/proof_records/graph.py`, a new module named in a parenthesised multi-line `from …
    import (…)`, all three outside the filter, and an import that resolves neither to the
    standard library nor under `tools/`. The five filter mutations above still refuse.

### Non-claims / remaining gaps

* **No C4, G1, #84, #138, #139 or PSC.** C4 starts from a supplied finite strict child-closed SCC
  with full word factorisation. The square takes no such input and says nothing about strictness
  or productivity of any support; the balanced-pair states under the real-secondary cycle lie in
  no strict closed set (`rs_support_not_strict`). Finiteness of the balanced-pair closure is an
  input of the exporter (`require_complete` in `build_packets`), never derived.
* **No cycle realisation, no legal context, no hull point.** A packet cycle lifts only to an
  infinite absolute lineage of `σⁿ(T₀)` for a listed state `T₀`. Nothing makes `T₀` legal, gives
  a point of `X_σ` or a pair of tilings, or produces one infinite desubstitution history
  (backward compactness).
* **No uniformity.** There are four three-letter tables (one non-Pisot) and two binary Lean
  controls. There is no census, no statement about the 4,554-member corpus, and no
  finite-to-uniform transfer. The counts of §5 and §7 are facts about the committed tables.
* **The square is PIP-blind.** No proof uses the Pisot property or unimodularity, and `1/012/1`
  is accepted by design. PIP is recorded in the header only.
* **The declared universe only.** The square says nothing about:
  * absolute descendants of a split beyond `Separated.lineage` / `Separated.not_anchor`;
  * pairs of a coincidence block that are not retained children;
  * frames other than a listed state and its swap;
  * the `sync-right` target.

  The checker does not tie the listed states to the seed closure (`fibExtra_accepted`); a row is
  read in the universe of the listed state of a root row (`row_realised`), not necessarily of a
  seed.
* **The Mojo engine is not proved correct.** Its rows are checked row by row by the Lean kernel,
  and the committed modules are regenerated and compared. That is a certificate per table, not a
  refinement proof of the program.
* **Not started:** roadmap immediate-sequence item (3), the ordered hub-word invariant. The hub
  rows here are certified only as equal to `factorHub`.
* **Review and CI.** Independent human review is pending. The receipts above are local, and the
  hosted runs of `packet-square.yml` and `ci.yml` on the integrating revision are outstanding.
  The peak memory of the `RealSecondary` module (9,760 MiB resident, single-file, local) has not
  been measured on a hosted runner. If a runner runs out of memory, the check is to be split
  into chunks, not weakened.
