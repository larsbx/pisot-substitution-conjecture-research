# C4 legal seams must have a newborn ancestor

**Status:** Repository-proved conditional filter and exact finite controls.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
This uses [#474](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/474)
and the [bilateral newborn exclusion](c4-bilateral-birth-rigidity-2026-11-02.md).

## Birth and inheritance

**Lemma.** In a supplied finite strict child-closed phase-zero balanced
SCC with nonsingular incidence, every represented seam lies in the
endpoint forward orbit of a legal, locally admissible newborn seam.

Start with the literal ordered factorization of an iterated
irreducible state. At any interior cut, trace it back one level
whenever it is the image of a previous balanced cut. A cut inside
the image of a single parent factor is a newborn. The backward
trace must reach one because the initial state is irreducible.
If its ordered terminal pair and first pair are `L,R`, inheritance
acts deterministically by `(L,R) -> (g(L),f(R))`, where `g` is
the suffix map and `f` the prefix map, applied coordinatewise.

At the newborn let the source letters be `a,b` with proper image
digits `r,s` measured immediately to the right of the cut. At
least one digit is positive by bilateral newborn exclusion. The
difference `q` of the two proper image prefix Parikh columns must
lie in `M Z^3`. A digit zero can take its left letter only from
the image of a legal predecessor of its source letter. This uses
the full-word legality from [#474](c4-legal-seams-2026-11-04.md).
The adjacent first and terminal pairs must respect both fixed
hub tracks and their endpoint orbits.

There are two additional exact boundary implications. If the
proper image prefix columns agree, injectivity gives equal
source prefix Parikh columns. The two source indices must then
both be zero by irreducibility. Thus `(a,b)` must be an allowed
first pair. If the two remaining image suffix Parikh columns
agree, apply the same argument to the source suffixes after
the two letters. Both source indices must be last, so `(a,b)`
must be an allowed terminal pair.

The checker enumerates this local birth superset and follows
its inherited endpoint orbits. Empty output for both tracks
excludes a strict phase-zero system with those hubs. A surviving
label is a necessary condition only. The source positions have
no full-word realization test. The executable checks images up
to length 64 with exact integer arithmetic.

## A Pisot specimen excluded by newborn residues

Take `01/121/012` on the letters 0,1,2. Its incidence matrix is
`[[1,0,1],[1,2,1],[0,1,1]]`, with determinant 2 and characteristic
polynomial `x^3-4x^2+4x-2`. The square of the matrix is positive.
The polynomial has no integer root among its possible divisors
of 2, its discriminant is −44, and its real root lies between
2 and 3. The complex conjugates therefore have squared modulus
`2/beta < 1`.

The genuine left-good edges are witnessed for `{0,2}` at depth
one, position 0, and for `{1,2}` at depth two, position 4.
Thus the only unordered first pair of a strict state can be
`{0,1}`. For phase zero orient it with 0 on top. The suffix map
is `(1,1,2)`, type C, so the right hub is 2 by the
[right-hub restriction](c4-right-hub-reversal-2026-11-04.md).
Its complementary right-good edge `{0,1}` is witnessed at
depth one, position 0 of the reversed images.

The legal seam test leaves only `L=(1,2), R=(0,1)`, with
right hub bottom. The top seam is `10`, absent from the interiors
of all three images. The top cut must be on an image boundary.
The bottom seam `21` must be internal, and its only internal
occurrence is in `121` at digit 2. The bottom proper prefix
`12` has Parikh vector `(0,1,1)`. The image lattice cannot
contain it, because row 1 minus row 0 of `M` is `(0,2,0)`.
So the sole legal seam has no possible newborn, and no
strict phase-zero component exists for this specimen.
In a common-phase component the first child preserves the
ordered pair `(0,1)`, since both letters are fixed by the
prefix map. Thus a common phase would have to be zero.

The test also checks a positive local distinction for the
same specimen under the weaker input with left hub 1, without
imposing the second good-edge exclusion. Its candidate newborn
`(21,12)` inherits to `(21,10)`, which is not itself a candidate
birth. This pins the need for forward closure. Actual newborn
seams in the strict reducible `020/20/12` control remain in
the superset.

No uniform productivity result or governed status change follows.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_enclosure.mojo)
python -m pytest -q tests/test_c4_overlap_enclosure_oracle.py
```
