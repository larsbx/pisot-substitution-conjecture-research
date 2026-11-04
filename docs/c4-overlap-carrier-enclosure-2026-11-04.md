# C4 whole-factor enclosure and the actual overlap carrier

**Status:** Repository-proved conditional carrier reduction and exact finite control.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@566a5615`, including [#467](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/467).

## Literature and scope

[Sirvent–Solomyak](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf)
compare balanced pairs with overlap algorithms.
[Akiyama–Lee](https://arxiv.org/abs/1003.2898) use descendants of
strict-interior overlaps to study overlap coincidence. The
[Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
witness for an aligned good edge requires an actual common prefix
position. Use these overlap and address semantics with complete
balanced-factor closure. The goal here is to determine which overlap
types can occur in the same recurrent carrier. The productivity of that
carrier is a separate condition.

## Whole-factor enclosure

**Lemma.** Let a nonerasing substitution have positive letter lengths `ell`
with `ell M = beta ell` and `beta > 1`. Supply a finite nonempty,
strictly child-closed collection `C` of literal irreducible balanced
pairs, strongly connected on normalized ordered-child support.
Let `L` be the maximum physical length of a state. Each normalized
state represents both physical orientations. Keep all occurrence
edges, including those with identical projected overlap types.

For a top and bottom tile whose interiors meet, let `J` be their
intersection interval, of length `d > 0`. At depth `n`, their
inflated source tiles both cover `beta^n J`. Take `n` with
`beta^n d > 2 L`. The complete balanced-factor cut grid has gaps at
most `L` and includes both endpoints of the inflated state. The first
cut strictly after the left endpoint of `beta^n J` is at most `L`
away. The next cut is at most another `L` away and thus strictly
before the right endpoint. They enclose a whole factor inside both
inflated source tiles.

The enclosed factor belongs to `C`. For any state `S` in `C`,
follow an ordered child path from the enclosed factor to `S`,
of length at most `|C|-1` in the normalized support. Every actual
overlap occurrence in that copy of `S` lies inside both inflated
source tiles. Its ancestor tiles at each intermediate step also
overlap, since their intervals contain the scaled-back interior of
the chosen descendant overlap. This yields a literal route from the
original source occurrence to the chosen occurrence of `S`, up to
the recorded orientation. The depth bound is `n + |C|-1`. Reaching
the target within the particular source intersection is stronger than
finding the same type somewhere else in the inflated root.

## Consequences for #461

Consider the overlap graph on all actual overlap types occurring in
the states of `C`, modulo simultaneous interchange of the two
tracks. A type retains the two letter types and their relative
offset. The offset can be kept as a prefix Parikh difference, even
when the Perron length map has a rational kernel.

- The graph is forward closed. Every strict-interior child overlap
  lies within a single ordered balanced factor, since the factor
  boundaries agree on both tracks. Its offset is preserved by
  trimming at that common boundary.
- The graph is strongly connected by whole-factor enclosure.
  Therefore the complete overlap orbit of **any one** represented
  type recovers this entire carrier. In particular, a forced
  physical crossing from #466 can reach all other represented
  types, including every left-aligned first pair of the component.
  Forward closure makes this carrier an entire sink SCC of the
  ambient formal overlap graph modulo track swap. A sink with only
  nonzero-offset vertices cannot be the carrier of such a component.
- In the hypothetical strict flat Pisot case, [#469](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/469)
  and [#466](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466)
  supply a represented physical crossing. Productivity of **any
  represented type**, for example an aligned first pair with an
  independently witnessed coincidence, now suffices. Concatenating
  the literal routes gives the witness required by #467.

In a genuinely strict component every represented type must be
nonproductive. The proof narrows the missing implication to ruling
out a single closed recurrent carrier that contains both the forced
crossing and all its represented aligned boundary types. The known
good edge need not be a represented boundary type. No general
productivity result or C4/PSC status change follows.

## Exact finite control

The primitive constant-length control `012/120/201` has a finite
strict component consisting of the three unordered pairs of its
images. Its incidence matrix has all entries equal to one. The
letter lengths are all one and the inflation factor is three.
For each of its nine literal source occurrences, the depth-two
source intersection has length nine. The middle factor lies
strictly inside, and its next child row contains all three state
types. The replays verify the actual ancestor index on each track
for every target letter position in those children. The native
checker uses the ordered derived system. The Python oracle uses
full word expansion, balanced cuts and explicit ancestor labels.
This is a reducible control for the enclosure mechanism.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_enclosure.mojo)
python -m pytest -q tests/test_c4_overlap_enclosure_oracle.py
```
