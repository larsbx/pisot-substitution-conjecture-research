# Vertex asymptotes and the eventual-range cycle rank

For primitive three-letter substitutions with irreducible Pisot incidence,
`β₁(ER) ≥ 3` implies the vertex-asymptote condition (NM_V). The threshold is
sharp. The unimodular substitution `01/210/1021` has `ER = K_{2,3}`,
`β₁(ER) = 2`, and a right-asymptotic vertex/interior pair in the zero fibre.
Reflection gives a left failure with `ER = K_{3,2}`.

This follows up [PR #611](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/611)
at `aba9b8a54eb1eb9b5542130cf70c5f2d8742b8f9`, merged as
`4b75e005a6f3ec793e8c7d5c872091e1e00486f5`. The proposal is based on main
`d28af053e476f7be29f1f4f7999b8efe512a0206` (merge of #614).

## Work shown

### Assumptions and hypotheses

Let `σ` be primitive on `{0,1,2}` with irreducible incidence
characteristic polynomial and Pisot Perron root `β > 1`. Use the legal
aperiodic tiling hull with positive Perron lengths `r_i`, inflation `Φ`,
and the standard geometric realization `h` with identity fibre
`F₀ = h⁻¹(0)`, normalized as in (R4). Aperiodicity follows here because a
periodic symbolic sequence would have a rational Perron frequency vector,
forcing a rational Perron eigenvalue. A vertex-type member has a
tile boundary at 0. Left or right asymptoticity means exact agreement on
a half-line. (NM_V) requires any member of `F₀` asymptotic on one side to a
vertex member to be vertex-type with the same letter at 0 on that side.
See [round 4, §3.1–3.3](c4-round4-2026-11-17.md#31-setting) and
[round 3, §4.1](c4-round3-2026-11-16.md#41-the-solenoid-replaces-the-torus).

For a seam `xy`, its left vertex is the right end of tile `x`, and its
right vertex is the left end of tile `y`. The first- and last-letter maps
are `g_L` and `g_R`, respectively, so inflation acts on seams by
`f(x,y) = (g_R(x),g_L(y))`. The eventual-range edges are exactly the
legal bigrams with both endpoints periodic. Each edge determines a
periodic vertex member by taking nested inflations of the seam after a
common period of the two endpoints. The interior members in the census
come from the certified central-tile address cycles. [Eventual-range
and realization lemmas](c4-geometric-f-class-2026-11-16.md#5-lemma-s-and-theorem-p-a-parity-refinement-of-barge-2015-thm-22).

#### Targeted literature decision

| Input | What transfers | Source |
| --- | --- | --- |
| Eventual range and cohomology | The endpoint action on legal seams and its cohomological contribution. The graph records periodic vertex seams. | [Barge–Diamond (2008), §3 and Theorem 4](https://arxiv.org/pdf/math/0702669) |
| Normalized realization and finite fibres | The equivariant translation factor and finiteness of `F₀`. Recognizability and (R4) give periodicity of its members and put periodic seams at the origin in `F₀`. | [Baker–Barge–Kwapisz (2006), §3 and Theorem 4.2](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), [round 3, §4.1](c4-round3-2026-11-16.md#41-the-solenoid-replaces-the-torus) |
| Asymptotic tilings and overlap states | Periodic asymptotic tilings in geometric realization, exact overlap children, and persistence of a coincidence. The one-sided cycle test used here comes from #611. | [Barge–Diamond–Swanson (2008), §2](https://arxiv.org/pdf/0804.0930), [Sirvent–Solomyak (2002), §§3–5](https://doi.org/10.4153/CMB-2002-062-3), [#611 derivation](c4-unique-partner-exclusion-2026-11-18.md#scope-on-the-corpus-where-nm_v-holds) |
| Odd-norm coincidence rank two | In degree three, the bound `dim H¹ ≥ 5` requires odd norm and coincidence rank two. The connected eventual-range formula then gives `β₁(ER) ≥ 2`. | [Barge (2015), Theorem 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) |

The prior computations include 48 failures at ranks zero and one, and
#614 gives periodic interior/interior asymptotes at rank two with (NM_V).
Proceed by counting the periodic endpoint letters and testing a nested
vertex/interior pair in the complete two-by-three range. The pair below
uses the two word identities `σ(0) = 01` and `σ(2) = 10·2·1`.

### Derivation / reduction

#### An (NM_V) failure forces a small side

A distinct right-asymptotic pair in `F₀` has a first common right ray
starting at a common vertex `y`. Both tilings are fixed by a positive
power `Φ^q`. Inflation gives agreement from `β^q y`, so minimality of
`y` gives `y ≥ 0`. If `g_R` is injective, the different labels ending
at `y` remain different after inflation. Then `β^q y` is also the first
such vertex and equals `y`, hence `y = 0`. In that case both tilings have
a vertex at 0 and share their right letter. Thus a right failure forces
`g_R` to be noninjective. Reflection gives the corresponding statement
for a left failure and `g_L`. [Round-4 Lemma A](c4-round4-2026-11-17.md#33-proofs).

Write `L = Per(g_R)`, `R = Per(g_L)`. Every periodic letter has an
incident edge in `ER` because a large power of the endpoint action fixes
the letter and puts its neighbour in any incident legal bigram on a cycle.
The Barge–Diamond graph is
connected here. In its cohomology sequence a nonzero reduced component
group of `ER` would inject equivariantly into the incidence direct limit
and give an eigenvalue 1 for a power of the incidence action. The cubic
Pisot eigenvalues have moduli different from one. Consequently
`β₁(ER) = |E| − |L| − |R| + 1 ≤ (|L| − 1)(|R| − 1)`.
[Eventual-range connectivity, Lemma 7](c4-geometric-f-class-2026-11-16.md#5-lemma-s-and-theorem-p-a-parity-refinement-of-barge-2015-thm-22).

A noninjective map on three letters has at most two periodic letters.
The failing side therefore has at most two endpoint letters and the
opposite side has at most three. A failure forces `β₁ ≤ 2`. If
`β₁ = 2`, equality requires two letters on the failing side's endpoint
map, three on the other and all six edges. Thus a right failure at rank
two requires `K_{2,3}` and a left failure requires `K_{3,2}`, in the
stated side order. Only one side can fail at rank two. The weaker bound
`β₁ ≤ 1` holds when both maps have at most two periodic letters.

#### The substitution `01/210/1021`

With images as columns its incidence matrix and polynomial are
`M = [[1,1,1],[1,1,2],[0,1,1]]` and `p(x) = x³ − 3x² + 1`. Every
image contains 1 and the image of 1 contains all the letters, so
`M² > 0` entrywise. The determinant is −1. The only possible rational
roots are ±1 and neither is a root. The values at −1, 0, 1 and 3 are
−3, 1, −1 and 1. There is one root in each of `(−1,0)`, `(0,1)` and
`(1,3)`, so the third root is the Perron root and is Pisot of degree 3.

The maps on `0,1,2` are `g_R = (1,0,1)` and `g_L = (0,2,1)`.
The internal bigrams are `{01,02,10,21}`. One boundary image adds
`{00,11,12}`, and the union is closed under the seam action. Every legal
bigram is internal to an image or crosses the boundary in the image of a
shorter-level bigram, so this is the complete legal set. Its first image
under `f` is `{0,1} × {0,1,2}`, on which `f` is a permutation.
Hence `ER = K_{2,3}` and `β₁ = 6 − 5 + 1 = 2`.

Take the vertex tiling `T` from seam `1.0`. The seam is legal and the
two endpoint germs are fixed by `σ²`, so its even inflations form nested
legal patches exhausting the line. The right ray of `T` comes from the
nested words `σⁿ(0)`.

For the other tiling, let `v = e₂ − e₀` in integer strand coordinates.
The identity `(M−I)v = e₀ + e₁` is the prefix equation for the interior
occurrence of 2 in `1021`, preceded by `10` and followed by `1`. Pairing
it with the positive length vector gives
`(β−1)(r₂−r₀) = r₀+r₁ > 0`. Place the tile 2 at `x = r₀−r₂ < 0`.
It ends at `r₀ > 0`, so zero lies strictly inside the tile. Its retained
copy in the inflation starts at `βx + r₁ + r₀ = x`. The iterates of
this tile are nested and legal, with supports `[βⁿx, βⁿr₀)` exhausting
the line. They generate an interior tiling `S` fixed by `Φ`.

The initial 0 of `T` and the retained 2 of `S` both end at `r₀`.
The two word identities append the same `1` after those tiles. At depth
`n` the common suffix beginning at `r₀` is
`1 σ(1) … σⁿ⁻¹(1)`, whose length tends to infinity. Thus `T` and `S`
agree on `[r₀,∞)` and the letters just before `r₀` are 0 and 2.
The seam puts `T` in `F₀` by (R4). The continuous, translation-equivariant
factor sends the two asymptotic tilings to the same point. Their image
difference is invariant under joint translation and tends to zero along
translations into the common ray. Hence `S ∈ F₀` and this is an (NM_V)
failure. The same right ray occurs for seam `0.0`. Reversing all three
words gives `10/012/1201`, with interior address `e₂−v = e₀` and
the reflected failure on the left.

#### The necessary parity condition still permits failure

In `01/2100/10021`, the endpoint maps are the same. The additional
internal bigram `00` already belongs to the legal set above, so the
legal bigrams and the complete eventual range are unchanged. Its
incidence rows are `[[1,2,2],[1,1,2],[0,1,1]]`, with positive square and
characteristic polynomial `x³ − 3x² − x + 1`. The values at −1, 0, 1
and 4 are −2, 1, −2 and 13. This gives two roots in `(−1,1)` and one
greater than 1, and the only possible rational roots ±1 are excluded.
The same vector `v = e₂−e₀` now satisfies `(M−I)v = 2e₀+e₁`, matching
the interior prefix `100`. The retained 2 and the vertex 0 still end
at `r₀`, followed by the same right suffix. This gives another failure
at determinant −1 and rank two. Its trace and `e₂(M)` are
both odd, so it satisfies Theorem P's necessary parity test, which
excludes the shorter example at coincidence rank two. Coincidence rank
two would require further evidence. [Theorem P](c4-geometric-f-class-2026-11-16.md#5-lemma-s-and-theorem-p-a-parity-refinement-of-barge-2015-thm-22).

#### Binding to the overlap-cycle criterion

For periodic members of `F₀`, the finite periodic sequence of central
overlap states on one side of 0 supplies the side branches. A reachable
cycle of noncoincident states along a side branch produces discrepancies
arbitrarily far out, since the branch support expands by positive powers
of `β`. If the reachable noncoincident graph is acyclic, descendants
become coincidences at bounded depth and the two tilings agree on a
half-line. Coincidences persist under inflation. This is the exact
criterion of #611, with failure to finish any capped computation treated
as inconclusive. [Canonical kernel](../kernel/psc/zero_fibre_asymptotes.mojo).

In the example the right central cell `[0,r₀)` has labels 0 and 2.
Its inflation on `[0,βr₀)` contains the same central cell followed
only by the coincident tile 1 on `[r₀,βr₀)`. The central loop stays at
zero and the right side branch is a coincidence. This gives the same
verdict as the nested-word proof.

### Evidence and replay

- At #611 head, the locked Mojo census reproduces the archived log
  byte for byte. The independent Python oracle confirms all 96 reported
  pairs by at least 500 aligned consecutive tiles. That finite check
  accompanies the exact overlap decisions.
- For the 48 archived failures, counting the sixth-iterate fixed
  letters independently gives the following distribution. In every
  case the endpoint map for the failing direction has two periodic
  letters.

| `β₁(ER)` | Periodic last letters | Periodic first letters | Failures |
| ---: | ---: | ---: | ---: |
| 0 | 2 | 3 | 12 |
| 0 | 3 | 2 | 12 |
| 1 | 2 | 2 | 24 |

- The Mojo regression checks both complete eventual-range masks and
  their graph counts `(6,5,1)`, plus the zero-fibre overlap decisions.
  The two new cases and the reflection each have eight fibre members,
  two of them interior. The independent word oracle checks their
  asymptotes from the displayed literal addresses.
- Lean checks the three-letter periodic-count bound, the cycle-rank
  bound and equality shape, the example's exact legal-bigram closure
  and stable image, the incidence and interior address, and the
  common-suffix recurrence at every finite inflation. The passage to
  legal two-sided limits, the realization step and the Pisot root
  argument are written above. [Lean
  source](../proof/PscVerif/PscVerif/VertexAsymptoteRange.lean).

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_zero_fibre_asymptotes.mojo)
python3 -m pytest -q tests/test_nmv_literal_rays_oracle.py
(cd proof/PscVerif && lake build PscVerif.VertexAsymptoteRange)
python3 tools/make_proof_bank.py --check
```

For the archived census replay, in a checkout of the exact #611 head:

```sh
(cd kernel && pixi run --locked mojo run -I . nmv_census.mojo) > nmv-replay.log
cmp nmv-replay.log evidence/nmv-census-2026-11-18/nmv-census.log
python3 oracles/python/nmv_literal_rays.py nmv-replay.log
```

### Negative controls

- `1/012/21` and `01/12/021` preserve the known right failures at
  ranks zero and one. `220/01/021` preserves an earlier left failure.
  The new example and its reflection refute the proposed upper bound
  of one even in the unimodular class.
- `01/122/201` has a complete two-by-three range and satisfies (NM_V).
  In `10/200/02` the exact regression also finds the #614 right
  interior/interior asymptote while (NM_V) holds. Thus the borderline
  graph occurs with both (NM_V) outcomes, and the type of the
  asymptotic pair matters.

### Non-claims / remaining gaps

Barge's bound at odd determinant and coincidence rank two still
permits `β₁ = 2`. In that rank, (NM_V) is automatic unless `ER` is one of
the two complete graphs above, with a possible failure on its
noninjective endpoint side. To remove (NM_V) from the strict-system
argument on those graphs would require an additional geometric
implication using coincidence rank two or the strict system itself,
or an argument that bypasses (NM_V). The counterexample concerns the
implication without a coincidence-rank premise. Periodic-partner
witness selection and the remaining C4 and PSC obligations stay open.
