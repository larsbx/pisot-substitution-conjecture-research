# C4 oriented overlap carriers and terminal alignment

**Status:** Repository-proved conditional restriction and exact finite controls.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@36ac685d`, including [#471](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/471).

## Oriented enclosure

Use the signed ordered-child double cover of
[the orientation-monodromy reduction](c4-orientation-monodromy.md).
Its connectedness dichotomy is the usual
[voltage-cover argument](https://doi.org/10.1111/j.1749-6632.1979.tb32796.x).
For the overlap graph use the literal descendants of strictly
intersecting tiles, as in
[Akiyama–Lee](https://arxiv.org/abs/1003.2898).
Keep signed integer prefix offsets and keep the two tracks ordered.

**Lemma.** Under the hypotheses of
[whole-factor enclosure](c4-overlap-carrier-enclosure-2026-11-04.md),
each strongly connected component of the oriented child cover
induces one entire sink of the **ordered** overlap graph. If the
cover splits into two components exchanged by the deck involution,
their overlap sinks are either equal or disjoint. They are equal
if and only if they share an ordered first pair. Equivalently,
they are equal if and only if they share an ordered terminal pair.

The two-sheet cover of a strongly connected child support is
a union of closed strongly connected components. To lift the
enclosure proof, inflate any source overlap until it contains a
whole factor, carrying that factor's physical orientation. Follow
a path inside the same oriented child component to the desired
oriented state. Each occurrence in the target descends from the
original two tiles in their given track order. Forward closure
holds by trimming each actual child to its common balanced factor,
which leaves the relative prefix offset unchanged. This proves the
sink assertion. Two sinks that share a vertex must be equal.

A zero-offset overlap in an irreducible pair has equal prefix
Parikh vectors and hence equal source indices. The common start
must be the first position, since every other such prefix would
be an internal balanced cut. Thus the zero-offset labels of a
sink are exactly its ordered first pairs. Likewise, if the type
is `(a,b,d)` with bottom-minus-top offset `d=e_a-e_b`, its end
prefixes agree in Parikh vector, so it is exactly an ordered
terminal pair. This label is always a genuine overlap since the
two positive-length tiles end together. The offset statements
retain integer vectors even if the length map has a kernel.

## A terminal-order obstruction from prefix flatness

In phase zero, orient each state with its first hub on top.
Every child preserves this choice. The two oriented child
components therefore have disjoint sets of ordered first pairs,
since only one has hub on top. By the lemma their overlap sinks
are disjoint. In particular the hub-top states cannot contain both
`(a,b)` and `(b,a)` as ordered terminal pairs. More generally no
ordered overlap label and its swapped label can both occur in
these orientations.

Write `g(a)` for the last letter of the image of `a`. Every
iterate `(g^n(a),g^n(b))` of an ordered terminal pair is the actual
terminal pair of an ordered last-factor descendant. A return to
the reversed ordered pair therefore excludes complete strict
phase-zero closure. Equality of the two letters on this orbit
also excludes strict closure, by the terminal coincidence.
These are different finite obstructions. The reversal argument
uses the full closed recurrence of the hypothetical completion.

In particular, a ternary suffix map of type F (one two-cycle and
one transient letter) is impossible in a strict phase-zero
component. Every persistent distinct suffix pair eventually
enters the two-cycle, where the next step reverses it.
For type E (one fixed letter and one two-cycle), if a genuine
right-good edge is supplied, it must be the transposed pair.
A good edge joining the fixed letter to a cyclic letter would
rule out both fixed-to-cycle pairs by suffix iteration. The
transposed pair is already excluded by reversal. Here a
right-good edge means a left-good edge for the reversed
substitution, with its witness measured from the common end.

For phase one the oriented cover is connected when the base
support contains an odd directed cycle. If all cycles are even,
choose the path-parity coloring of the base states. A cover
component then contains the hub-top orientation at one color and
the hub-bottom orientation at the other. Its ordered overlap sink
coincides with its swapped sink exactly when some unordered first
pair occurs at both colors. This is the first-pair criterion above
applied to the two color classes. When the sinks are disjoint,
the same criterion implies that the parity-adjusted terminal
pairs cannot contain both orders of one unordered pair.

## Exact controls

For `01/12/021`, take the actual hub-top pair `(10,01)`.
Its ordered last-factor path starts at `(10,01)`, then visits
`(1201,0112)` and `(12,21)`. The terminal orbit is
`(0,1) -> (1,2) -> (2,1)`. Both complete child rows on this path
retain the hub on top. The reversal at depth two rules out a full
strict phase-zero completion already on this finite prefix.
It neither identifies a diagonal in that prefix nor relies on
there being a supplied completion.

The strict reducible `10/102/211` fixture has a suffix map that
swaps letters 1 and 2. Its represented terminal pairs in hub-1
orientation are only `(2,0)` and `(1,0)`, which map to each other
without a reversal. Thus a transposition in the suffix map alone
does not exclude a strict phase-zero component. The replay checks
actual terminal pairs and retains the earlier enclosure control.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_enclosure.mojo)
python -m pytest -q tests/test_c4_overlap_enclosure_oracle.py
```

This eliminates every strict phase-zero candidate with type F
suffix or a represented terminal reversal. The remaining compatible terminal orders and the general
productivity and C4 obligations remain open. No governed status changes.
