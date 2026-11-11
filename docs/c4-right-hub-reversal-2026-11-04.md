# C4 right-hub orientation and reversal

**Status:** Repository-proved conditional transfer and exact finite control.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
This depends on the ordered-carrier restriction in [#472](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/472).

[Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
provide an eventual coincidence between at least two letters in
the Pisot setting. Applying the result to reversed image words gives
a right-good edge. Right-good means there is an actual same-letter
witness at equal suffix Parikh offsets in some common inflation.
The reversal below uses literal balanced factorization, as in the
[balanced-pair algorithm](https://citeseerx.ist.psu.edu/document?doi=ac6481cf41605ed271988fa1354fbf057680ba4e&repid=rep1&type=pdf).

## Right-hub rigidity

**Lemma.** Supply a finite strict child-closed balanced SCC with
positive expanding letter lengths. Suppose its oriented cover has
two components inducing disjoint ordered overlap sinks. Then for
suffix type C, or for suffix type D or E with a genuine right-good edge,
one letter is on the same track at the right end of every state
in a chosen oriented component. Reversing all words and choosing
that letter as hub gives a strict phase-zero system.

Take the actual ordered terminal pairs in one oriented component.
They form a nonempty set of distinct pairs forward invariant under the
suffix map `g` acting on both coordinates. Indeed, the terminal
pair of the last child is the image of the parent's terminal pair.
By disjointness and [#472](c4-oriented-alignment-2026-11-04.md),
the set never contains both orders of one unordered pair.
A right-good edge cannot be represented there, since its witness
would give a coincidence in a full descendant.

- **Type C.** The two fixed-letter basins have sizes two and one.
  Any same-basin pair synchronizes by iteration, so every terminal
  pair is cross-basin. All cross-basin pairs evolve to the two
  fixed letters. If the singleton-basin letter were on opposite
  tracks in different states, both orders of the fixed pair would
  be represented. Thus the singleton letter is a uniform right
  hub. The edge between the two letters in the other basin is
  itself right-good by endpoint synchronization.
- **Type E.** Let `k` be the fixed letter and let `a,b` be the
  transposed letters. The pair `{a,b}` cannot be represented
  because its next image reverses it. A witnessed right-good
  edge incident with `k` would exclude both fixed-to-cycle
  pairs by iteration, leaving no represented terminal pair.
  Hence the right-good edge must be `{a,b}`. All terminal
  pairs use `k`. A terminal pair with `k` on top forces
  both leaf choices with `k` on top. A pair with `k` on bottom
  would then give a reversal. Thus `k` is a uniform right hub.
- **Type D.** Write the right-good edge as `{a,b}` and its
  complementary letter as `h`. Every represented terminal pair
  contains `h`. Opposite hub tracks would require opposite
  orders of one pair, or the two ordered pairs `(h,a),(b,h)`
  after naming the leaves. The first case is excluded by
  disjointness. For the second, reverse the substitution and
  use its left-aligned pairs. Reversal identifies the two overlap
  graphs and commutes with track swap. On signed integer offsets
  it sends `(x,y,d)` to `(x,y,e_x-e_y-d)`, by reflecting
  both endpoint intervals.

  Let the witnessed coincidence between the reversed images of
  `a,b` occur at depth `m`. In type D each reversed image
  starts with its source letter. For every `n >= m` the two
  depth-`m` words are therefore prefixes of the depth-`n`
  words. Their witnessed tile stays at the same offset. Take
  `n` large enough that the growing depth-`n` hub image
  covers that entire tile. Choose a point in its interior that
  lies inside a hub-image tile. Both inflated aligned pairs use
  the same hub image starting at the common origin. The chosen
  point therefore gives an actual overlap between the hub-image
  tile and the witnessed tile in the first pair, and its
  track swap in the second pair. The prefix Parikh vectors
  for the witnessed tile agree on both leaf tracks, so these
  are swapped labels even when offsets are retained as vectors.
  All actual descendants lie in the chosen ordered sink.
  The two labels force that sink to intersect its swapped
  sink, contradicting disjointness. Thus the hub track is uniform.

Use a single global track swap if necessary to put the right hub
on top. Reversing a word replaces each prefix with a suffix in
the opposite order. In a balanced pair equal prefix masses are
equivalent to equal complementary suffix masses. Consequently
the reversed system has exactly the same actual ordered child
occurrences in reversed row order, with the tracks preserved.
Every reversed child starts with the chosen hub on top, giving
the stated phase-zero closure. Strong connectivity is unchanged.

The hypothesis on ordered sinks holds for a strict phase-zero
system by [#472](c4-oriented-alignment-2026-11-04.md). The transfer
also works in one chosen oriented sheet of a nonconstant signing
when the ordered sinks are disjoint. In that application the
choice is made on the oriented cover before reversal.

## Consequence for the physical crossing

For primitive irreducible Pisot incidence, reversal preserves
the matrix and letter lengths. In all three surviving suffix types above,
[#469's physical-crossing bound](c4-physical-hub-density-2026-11-04.md)
can therefore also be applied with the right hub. In the
original words, it forces an overlap in which the bottom right-hub
tile ends strictly inside a top nonhub tile, and the following
suffixes have equal right-hub counts. The positive lower
frequency applies to this right-oriented crossing separately.
Together with [#471](c4-overlap-carrier-enclosure-2026-11-04.md),
the carrier modulo track swap contains both the
original left crossing, when its hypotheses hold, and the
right crossing. Productivity of either remains open.

The endpoint signature `(1,0),(2,1)` with the identity map
and good edge `{0,2}` illustrates why the type-D argument needs
the actual witness. The endpoint conditions alone allow mixed
tracks. For the reversed constant-length substitution
`021/102/201`, the good descendants coincide at position 2.
The two marked images at that position realize the swapped
labels `(2,1,e_2-e_1)` and `(1,2,e_1-e_2)`.
This checks the local obstruction with exact words.

## Exact replay

The new strict reducible type-C control is `020/20/12` with
states `(012,120),(02,20),(02012,12020)`. Its ordered child
rows in these state IDs are `[1,2],[2],[1,0,1,2]`.
The left hub 0 and the right hub 2 are both on top. The genuine
left edge `{1,2}` has a depth-two witness at position 3 in
`12020/2012`. The right edge `{0,1}` has common last letter
0 at depth one. Its characteristic polynomial is
`(x-1)(x^2-2x-1)`. The strict type-E control is the existing
`10/102/211` example, with right hub 0 on the bottom. Its right-good edge
`{1,2}` has a depth-two witness at position 7 in the reversed
images, with equal prefixes `1120120` and `2012011` in Parikh mass.

Both replays verify all literal rows after reversal, including
the reversed child order and the physical track of the right hub.
The type-D endpoint signature and mirrored descendant labels are checked separately. No governed
status changes.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_enclosure.mojo)
python -m pytest -q tests/test_c4_overlap_enclosure_oracle.py
```
