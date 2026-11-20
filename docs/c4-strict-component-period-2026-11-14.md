# Periods of finite strict ternary balanced-pair components

**Status:** repository-proved conditional restriction on supplied literal components; independent human review pending.

This continues [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
The [source review](c4-strict-period-stop-go-2026-11-14.md) precedes the
new controls. A period below is the gcd of directed closed-walk lengths.

**Theorem (strict-component primitivity).** Let σ have primitive irreducible
ternary Pisot incidence. In any supplied nonempty finite fully child-closed
strongly connected system of literal irreducible noncoincident balanced
pairs, the child graph modulo track swap has period one. Its overlap graph
with the same normalization has period one. Each strongly connected
component of the ordered child cover and its ordered overlap graph have
period one or two. An ordered period-two component has the complementary
hub flip on every child occurrence at **both ends**, for any genuinely
left and right eventually coincident edges.

This concerns complete strict components and both physical track orders.
It needs neither unimodularity nor a state-count bound.

## Shared overlap types identify cyclic classes

Consider one strongly connected child graph, with the chosen treatment
of track order used on both the child graph and its overlap graph. In the
ordered setting choose one closed component of the ordered cover. An
actual positive-length overlap keeps its tile letters and the integer
difference of their prefix Parikh vectors. Normalization, if used,
identifies a type with its track swap, which negates that vector.

Fix the child graph period `d`. Suppose states `T,U` contain the same
overlap type. Arrange the chosen occurrences in the same track order.
Because the relative prefix vectors agree, their two tiles, and all
their inflated subtiles, match under simultaneous translation from the
first occurrence to the second. Inflate until the scaled overlap
interval has room for a **whole** factor strictly inside it in the full
image of `T`. This uses the fixed maximum factor width of the supplied
finite component and the [whole-factor enclosure argument](c4-overlap-carrier-enclosure-2026-11-04.md).
The two endpoints of the enclosed factor transfer as balanced cuts in
the full image of `U`. In fact, the Parikh difference at any pair of
corresponding descendant positions is the common inflated source
difference plus the same difference of local prefixes. Thus both cuts
and the absence of any cut between them transfer literally. The
resulting factor belongs to both complete level-`n` reductions. In the
normalized setting use its normalized state ID. Both source classes
advance by the same `n`, so they were equal modulo `d`.

Hence the overlap types from distinct child classes are disjoint. Each
overlap edge advances that class by one: its actual occurrence lies in
one child factor after complete reduction, since a common cut on both
tracks cannot cross a positive overlap.

The overlap graph is strongly connected by [ordered enclosure](c4-oriented-alignment-2026-11-04.md)
or its normalized version. Let its period be `c`. The class map just
constructed gives `d | c`. Conversely color the overlaps by their own
cyclic classes modulo `c`. Choose one overlap and inflate until it
encloses an entire factor. Every overlap of that factor descends from
the chosen overlap at the same depth, so they share one color. This
property propagates from a parent to each child: each positive child
overlap has positive overlapping parent tiles, regardless of where its
two tiles sit in their images. A path from the enclosed factor reaches
every state by strong connectivity. Thus all the overlaps of each state
have one common color, and these state colors advance by one on every
child edge. This gives `c | d`, so the two periods agree.

The shared-overlap argument uses the **integer** prefix difference. It is
valid even for the reducible controls with rationally dependent widths.

## The only candidate for normalized period two collapses

Let `g(a)` be the first letter of σ(a). Every represented first pair is
distinct, and each iterate under `g × g` is realized by a first-factor
descendant. Translate the cyclic classes proved above to these pairs:
their aligned overlap types have zero prefix difference. Every return
of a pair to itself therefore has length divisible by the graph period.
If a pair is transient, apply this statement after it enters its cycle.

The prefix endpoint theorem excludes A, B and G. In types C, D and F,
every recurrent distinct **unordered** pair is fixed. Type E fixes a
letter `h` and transposes the other two letters `a,b`. The only
nonconstant unordered pair cycle is
`{h,a} → {h,b} → {h,a}`.
If this cycle is represented, neither cross pair can be a genuine
good edge, because it would supply a diagonal to the component.
By Barge–Diamond, `{a,b}` is then a genuine good edge.

Take actual states beginning with `(h,a)` and `(h,b)`, orienting them
with `h` on top. For an ordered component these orientations are
available together whenever an ordered cross pair is represented:
its first child preserves the track of `h`. If the hub is on the
bottom, use the same argument with the tracks interchanged. Since
`g²` fixes all three letters, the corresponding even iterates of a
letter form nested prefixes. Use an even-depth coincidence witness
for `a,b`, replacing an odd-depth witness by its one-step inflation
if necessary. The marked tile is thus retained at the same integer
prefix in both leaf images at every sufficiently large even depth.
The growing common hub image eventually covers the marked tile,
and some hub tile intersects it with positive length. That ordered
overlap has the same integer prefix difference in the two full
reductions, since the hub tile and the marked leaf tile each start
at the same prefix on their respective tracks.

The two inflated parent states have therefore reached the same
overlap at the same depth. They belong to the same cyclic class before
inflation as well. But their first pairs are consecutive on the
endpoint cycle, so that class must equal its successor. This proves
period one in the cross-pair case both with and without normalization.
All remaining normalized cases already have a fixed unordered pair.
This also removes imprimitive normalized templates satisfying the
earlier [phase-wise Parikh constraints](c4-periodic-parikh-phase-rigidity-2026-11-04.md)
from the literal ternary search.

## Ordered period two forces flips at both ends

For the ordered graph, a fixed ordered first pair gives period one.
After the cross-pair case above, the only remaining recurrent ordered
pair consists of the two transposed letters in type E or F and has
period two. Hence any ordered component with period two must have
such a prefix cycle. The same reasoning applied to reversed
substitution words and reversed states gives a transposed suffix
cycle as well. Reversal preserves every occurrence of the child
graph, in reversed row order, and preserves its period.

Fix a witnessed left good edge. It cannot be the transposed pair.
Its complementary hub is therefore one of the transposed letters,
and every represented first pair contains that hub. In type E a
good cross pair makes the other cross pair good: the first-letter
map takes the latter to the former and the witness can be lifted
through that first image. Thus only the transposed pair is
represented. In type F every represented pair maps to the
transposed pair after one step, and its hub changes track at that
step. In either case each cyclic class has a single hub side
and the two classes have opposite sides. Every child advances that
class, so the left hub flips on every actual child. The proof for
the right hub is the left-hub argument on reversed words using an
independently witnessed right good edge.

In particular, a flat phase-one component in #461 would have
primitive normalized support, ordered period exactly two, and a
right-hub flip as well. Primitivity
of the normalized graph supplies an odd closed walk. In hub-top
representatives, every edge flips the track, so the odd walk lifts
to a path from one lift to its swap and connects the ordered cover.
Every ordered closed walk has even length since it flips the hub at
each step.

## Literal controls and replay

- The reversal `01/201/112` of the known reducible strict control
  has a type-E cross-pair cycle. For both first-pair states, the
  common good-edge tile `1` at level 4 and position 7 expands over
  the literal interval `[142,164)` at level 7. The first hub image
  covers it. Both full reductions contain the block
  `(01112,20111)` at `[145,150)` inside that marked interval.
  The exact directed period is one.
- The primitive reducible source `1/012/1` has a two-state strict
  system modulo track swap. Each literal child reverses the hub
  track. The normalized graph has period one and the ordered
  graph period two. The independent replay also constructs the literal
  overlap graph for each strict control using exact positive lengths and
  keeps full integer prefix differences even for dependent widths. The
  periods agree with those of the child graphs in both track conventions.
- Exact endpoint enumeration separately retains all 42 cyclic
  viable unordered-root assignments of a first map and a good edge:
  18 have ordered and unordered period one, 18 have ordered period
  two and unordered period one, and 6 have both periods two. The
  last six are exactly the type-E cross-pair case. The endpoint
  enumeration assumes only avoidance of the supplied good edge
  and does not certify its witness. The collapse argument above
  requires the literal witness.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_strict_period.mojo)
python -m pytest tests/test_c4_strict_period_oracle.py
python tools/make_proof_bank.py --check
```

The remaining uniform phase-one problem is whether both endpoint
transpositions, the two required hub flips, and a primitive
normalized overlap carrier can coexist in a fully strict PIP
component. No general C4, BH, A1′, G1 or PSC status changes.
