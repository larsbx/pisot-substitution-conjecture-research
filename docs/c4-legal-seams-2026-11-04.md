# C4 legal seams for bilateral phase zero

**Status:** Repository-proved conditional restrictions and exact finite controls.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
This uses the bilateral hub result in [#473](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/473), merged into #472.

The setting is literal balanced factorization as in
[Sirvent–Solomyak](https://citeseerx.ist.psu.edu/document?doi=ac6481cf41605ed271988fa1354fbf057680ba4e&repid=rep1&type=pdf).
Here the language means factors of finite inflations of single
letters. See also [Durand's language and return-word setting](https://arxiv.org/abs/0807.3322).
The repository previously established legal contexts at sufficiently
deep cuts by a counting argument. Whole-factor enclosure permits a
stronger conclusion when a complete strongly connected carrier is
supplied.

## Legality and recurrence of represented seams

**Lemma.** In a finite strict child-closed balanced SCC with positive
expanding letter lengths and phase zero, each word of each state is
a factor of an inflation of a single letter. Both words of every
literal adjacent balanced-factor pair in any iterated state are
also legal. Each represented seam occurs at least twice in the
complete ordered factorization of some iterated state.

For legality, choose an actual strict-interior overlap of two
source tiles in a state. Whole-factor enclosure in the phase-zero
oriented component gives an occurrence of any requested state
entirely within both inflated source tiles. This proves legality
of its full words, regardless of the legality of a seed used to
construct the component. An iterated state therefore has each
track contained in a further inflation of a single letter, so
adjacent factors of that iterate give legal concatenations.

For repetition, inflate any state until its complete factorization
has more factors than the number of states. This is possible because
the physical length grows and the factor lengths are uniformly
bounded. Two occurrences of one state have the same physical
orientation. Choose an ordered child path from that state to the
parent of a given seam. Inflating the whole row by the path length
preserves both occurrences of the chosen descendant. Inflating
further by the depth at which the seam occurs produces two
copies of it in the same row. The copies stay distinct because
balanced cuts persist under nonerasing inflation.

In particular, any directed graph used to model consecutive
ordered endpoint signatures must put every represented seam on a
directed cycle. Starting at one copy of the edge and stopping
at the next copy of its source gives a closed walk through it.

## Exact two-track bigram condition

For a preceding terminal pair `(a,b)` and a following first pair
`(c,d)`, the seam requires both `ac` and `bd` to be legal.
With left hub top and right hub top, this in particular requires
the single bigram `right_hub left_hub`. With the right hub on
the bottom, both opposite-track constraints are checked.

The exact set of legal bigrams is the least set containing every
internal image bigram and closed under
`(x,y) -> (last(sigma(x)), first(sigma(y)))`.
Induct on the inflation depth. Every next bigram is internal to
one letter image or straddles the images of a previous bigram.
Conversely every inherited bigram in the closure has a finite
single-letter ancestor witness.

The implementation overapproximates the possible terminal and
first pairs independently. It keeps only pairs whose full endpoint
orbit remains distinct and keeps the proposed hub on its track.
The resulting list contains exactly the compatible seams for that
track at this level of approximation. Every state can occur before
and after a seam by the same repetition argument, so an endpoint
pair absent from the appropriate projection is also excluded. An
empty list excludes the track. A surviving entry only certifies
bigram compatibility, since
the actual first and last pairs of a factor and the ordered child
rows may impose more constraints.

## Exact Pisot controls

Both specimens have left hub 0, right hub 2, left-good edge
`{1,2}` and right-good edge `{0,1}`. The positions are zero-based
in a common inflation, using reversed words for the right edge.

| Images | Left witness depth and position | Right witness depth and position | Legal bigrams | Right hub |
| --- | --- | --- | --- | --- |
| `01/20/102` | 2, 4 | 2, 3 | 00 01 02 10 11 12 20 | top only |
| `01/21/102` | 4, 27 | 1, 0 | 01 02 10 11 12 21 22 | bottom only |

For the first specimen, a bottom right hub forces a bottom
`2` followed by a nonzero left leaf. Neither `21` nor `22`
is legal. For the second, a top right hub forces top `20`,
which is absent. Its bottom-hub case also excludes the terminal
pair `(0,2)`, since its top seam would be `00`. The remaining
terminal pair is `(1,2)`. The respective incidence characteristic
polynomials are `x^3-2x^2-x+1` and `x^3-3x^2+2x-1`.

The strict reducible type-C control `020/20/12` checks actual
seams against the filter. The two Pisot rows are orientation
exclusions, with no hypothetical strict component asserted.
Productivity of the remaining overlaps stays open.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_enclosure.mojo)
python -m pytest -q tests/test_c4_overlap_enclosure_oracle.py
```
