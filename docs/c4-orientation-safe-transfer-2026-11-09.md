# C4 orientation-safe transfer

Research candidate for [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
The negative-control baseline is [PR #529](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/529)
at `f5539c75f245ebdec1e56ad0b15bb696472b73db`.
The canonical regression extends that revision. This research note changes no governed claim status.

## Conditional lemma

Let σ be a nonerasing primitive substitution with irreducible cubic incidence,
and use its positive left Perron lengths. Start with two specified overlapping
tile occurrences in the common interval of a noncoincident irreducible balanced
pair. Work with the actual ordered child occurrences with strictly intersecting
interiors. Fix the complementary unordered letter edge {a,b}.

Call a marked overlap an admissible endpoint if it realizes either of these
conditions, allowing either order of the two tracks.

- The tile starts agree, and in some common inflation of a and b there is
  an equal letter following prefixes with the same Parikh vector. This
  is the Barge–Diamond witness for the left-aligned edge.
- The tile ends agree, and in some common inflation of a and b there is
  an equal letter preceding suffixes with the same Parikh vector. This
  is the reflected witness, equivalently the prefix witness for the
  letterwise reversed substitution.

**If the marked overlap reaches an admissible endpoint along actual ordered
child occurrences, an actual descendant factor has a one-step interior
zero-return newborn with a coincident adjacent letter.** A direct diagonal
route suffices as well.

The proof has two steps.

1. Inflation preserves a shared endpoint. The prefix witness gives the same
   start for both copies of the common letter. The suffix witness gives the
   same end, hence also the same start. Trace those two tile occurrences
   back through the addressed inflation. Their common positive-length
   interior lies inside both ancestors at every level, so the witness
   supplies an actual ordered overlap path. Conversely, a diagonal
   descendant of an endpoint-aligned pair gives the corresponding equal
   prefix or suffix Parikh witness. Equality of Perron lengths implies
   equality of integer Parikh columns here. If ℓg=0 then ℓ annihilates
   g, Mg and M²g, which span over Q for every nonzero rational g by cubic
   irreducibility.
2. At each step, the full irreducible balanced factorization partitions
   both tracks into the same physical intervals. Each tile lies in its
   track's factor interval, so an interior overlap cannot involve two
   different factor intervals. Transport the marked overlap into the
   unique common factor and retain its occurrence ordinal. At the
   first diagonal, the equal start and end are balanced cuts by the
   same injectivity argument, so the tile pair is a singleton child.
   The parent was irreducible and noncoincident and its inflated length
   is at least two. At least one singleton boundary is interior. The
   left boundary gives a Sync₊ newborn when interior, and otherwise the
   right boundary gives a Sync₋ newborn. Every interior return here is
   new relative to that parent, whose only old returns are its endpoints.

The endpoint side, track order and newborn side are separate data. In
particular a right endpoint route can give a Sync₊ newborn. The construction
uses actual Perron lengths and applies with non-unit representations when the
marked addresses and all factor boundaries are transported exactly.

## The missing uniform premise

For a fixed marked root, an actual diagonal route exists exactly when there
is no successor-closed set of marked overlap states containing the root and
avoiding diagonals. In one direction a closed set contains every path from
its seed. In the other direction take the set of all reachable states.
The same equivalence holds with admissible endpoints as the target.
Endpoint access is a sufficient route to the diagonal. A prescribed edge
visit is unnecessary for the transfer proof.

A useful sufficient discharge would be an occurrence-level coverage result.
For example, in a completed marked graph, exhibit a certified diagonal or
admissible endpoint in a sink SCC reachable from the forced crossing. This
is a checkable sufficient condition for that root. Requiring one in every
reachable sink gives a sufficient condition for productivity from every
reachable vertex. The coverage needs to be proved on the marked graph, or
lifted from the word SCC by a separately justified transport argument.
Recurrent legal ancestry at the word level alone does not supply such a
lift. Different occurrence addresses can carry different defects even with
the same parent word and child labels.

For #461, complete strict child closure transports the crossing into
noncoincident factors forever. The first diagonal would violate strictness,
so the strict hypothesis gives a diagonal-free closed lift. The uniform
open step is to rule out that lift for a forced crossing under the genuine
Pisot hypotheses and full recurrent legal ancestry. Equivalently, prove
productivity for at least one of the forced crossings in each hypothetical
component. A proof need not show every crossing productive or require that
a path visits a named endpoint. Neither primitivity nor recurrence alone
has been shown here to prove the required coverage. The graph criterion is
an exact reduction of the obstruction and is not a substitute for ruling
it out.

[OrientationSafe.lean](../evidence/c4-orientation-safe/OrientationSafe.lean) gives the relational path composition, closed-set
obstruction and strictness contradiction. The occurrence transport and
Perron argument above are mathematical proofs in prose. The Lean source
has no admissions and awaits a native kernel check.

## Finite replay

The independent Python oracle sweeps the two exact endpoint streams rather
than forming the Cartesian product of digits. Comparisons use integer
incidence lifts and abort on exhausted sign or vertex budgets. It
independently reconstructs factors and source addresses. Absorbing
diagonals preserve noncoincident reachability since children of identical
aligned tiles can overlap only with their identical counterparts.

| Substitution | Ordered states / edges | First left good alignment | First right good alignment | First diagonal |
| --- | ---: | ---: | ---: | ---: |
| `1/02/002` | 54 / 94 | absent, both track orders | 7 | 8 |
| `1/02/220` | 39 / 80 | 3 | 3 | 3 |
| `01/12/021` | 68 / 146 | 4 | 2 | 3 |

For PR #529, the right route begins at source indices (1,2), with defect
−e₁. The depth-seven state is (1,2,e₂−e₁); digits (0,1) align a common
0 in the suffix 02. The resulting complete top and bottom addresses are
`(1,2,2,2,2,2,0,0,0)` and `(2,0,1,0,0,1,2,2,1)`.
The factor ordinal chain is `(0,0,1,0,0,0,1,3)`, giving a Sync₊
newborn at cut 15 in `(100202021,020211002)`. The other shortest
route gives cut 5 in the same parent, with ordinal chain
`(0,0,1,0,0,0,1,1)`. The unmarked full source has diagonal factors in
its second inflation. This productive tree fails strict closure.

The older `1/02/220` crossing supplies an exact negative to a
terminal-letter shortcut. Its right alignment (0,2,e₂−e₀) has marked
addresses `(8,1,0,2)` and `(9,1,1,0)`. Rightmost descent cycles
through (0,2), (1,0), (2,1) and back to (0,2). A genuine suffix-Parikh
witness still exists at depth five. The off-terminal continuation uses
digits (0,2), (1,0), (1,1), (1,0), (0,1) and gives Sync₊ at cut 3
in `(2201,1220)`. The direct depth-three diagonal route bypasses the
noncoincident endpoint targets. The `01/12/021` control reaches the
right target at depth two and uses its common terminal 1 at depth
three, giving Sync₊ at cut 11. Its earlier depth-two flat rank-three
cone remains a control against any forced exit by depth two.

The reducible strict four-state control in [PR #459](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/459)
has a genuine good edge and an invariant rational plane. It does not
exercise the irreducible-cubic transport argument. The non-unit phase-one
cone in [PR #460](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/460)
and the earlier packet and factorization controls motivate retaining exact
physical addresses and all factor occurrences. They do not furnish strict
Pisot closed counterexamples. No new counterexample to the full #461
premise was established. C4 concerns the supplied strict component;
G1 would need a separate extraction from general failure, and PSC is a
separate global conjecture.

## Commands and verification

```sh
python3 tests/test_c4_orientation_safe_oracle.py
(cd proof/PscVerif && lean ../../evidence/c4-orientation-safe/OrientationSafe.lean)
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_forced_overlap_routes.mojo)
```

The integer replay passed locally. The exact-head C4 recurrent flat exits workflow runs the canonical Mojo regression and the independent oracle. Its separate Lean job checks the standalone relational reduction using the pinned toolchain.

References: [Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/),
[Akiyama–Lee](https://arxiv.org/abs/1003.2898),
[physical crossing controls](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466).
