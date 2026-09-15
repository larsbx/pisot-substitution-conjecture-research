# P1 overlap productivity — minimal bad-overlap normal form

**Status:** proved structural reduction plus exact fail-closed extraction.  This
note does **not** prove overlap productivity, strong coincidence, or PSC.

Primary target: issue #84 / manuscript Open Problem 5.35.

## 1. Why isolate a recurrent obstruction

For a PIP substitution the seed-patch overlap graph is finite by bounded
discrepancy (manuscript Theorem 4.22).  A vertex is *productive* when some
descendant is a coincidence.  If a child of a vertex is productive, then the
parent is productive, so the set of nonproductive vertices is forward closed.

This elementary observation lets us replace an arbitrary bad overlap by a
finite recurrent object carrying all of the algebra already proved for closed
overlap sets.

## 2. Minimal bad-overlap normal form

**Proposition 2.1 (closed irreducible obstruction).**  Suppose an overlap
reachable from a swap seed is nonproductive.  Then the finite seed-patch
overlap graph contains a nonempty strongly connected set `S` such that:

1. every vertex of `S` is a noncoincidence and is nonproductive;
2. every child occurrence of every vertex of `S` is again in `S`;
3. the child-count matrix `N_S` is irreducible;
4. with `lambda(O)` the positive geometric intersection length,
   `N_S lambda = beta lambda`, hence `rho(N_S)=beta`;
5. for the intersection-vector matrix `V_S`,
   `N_S V_S = V_S M^T` and `rank_Q(V_S)=d`; consequently every Galois
   conjugate of `beta` occurs in `spec(N_S)`.

**Proof.**  Let `B` be the nonproductive vertices reachable from the bad
vertex.  `B` is nonempty and forward closed: a productive child would make
its parent productive.  Every genuine noncoincidence overlap has at least one
child occurrence because inflation partitions a nonempty intersection.
Following children forever in the finite graph enters a recurrent SCC.  Take
a sink SCC `S` of the induced graph on `B`.  Forward closedness of `B` and
the sink property imply that every child occurrence of a vertex of `S` lies
in `S`.  Strong connectivity makes `N_S` irreducible.  Items 4 and 5 are the
mass-balance and full-rank results already proved in Corollaries 5.33--5.34
(`docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`).  ∎

The point is not the graph-theoretic extraction by itself.  It means that a
counterexample to issue #84 can always be assumed simultaneously **finite,
recurrent, child-closed, PF-critical, and full-rank**.  Future arguments should
attack this normal form rather than an arbitrary nonproductive vertex.

## 3. Boundary-avoidance constraints inherited from PR #82

For a state `O=(i,j,<w,l>)`, Proposition 5.40 gives the exact boundary-hitting
criterion

```text
M^m w in P_m(i) - P_m(j)
```

iff the two level-`m` subdivisions have a common left endpoint, iff `O` has an
offset-zero descendant.

Let `EC_+` be the unordered letter pairs that are eventually coincident in the
prefix sense and `EC_-` the corresponding set for the reversed substitution.
Proposition 5.39 says left-aligned states on `EC_+` and right-aligned states on
`EC_-` are productive.  Therefore every obstruction `S` of Proposition 2.1
satisfies

```text
A_+(S) cap EC_+ = empty,
A_-(S) cap EC_- = empty,
```

where

```text
A_+(S) = {{i,j}: (i,j,0) is in S},
A_-(S) = {{i,j}: (i,j,l_i-l_j) is in S}.
```

Under two-sided strong coincidence both `EC_+` and `EC_-` contain every
letter pair, so a bad `S` contains no endpoint-aligned state at all.  More
generally, any boundary hit along a bad orbit must land on a letter pair that
is itself not eventually coincident in the corresponding direction.

This separates two possible contradiction mechanisms:

1. **boundary-hitting:** force an endpoint-aligned descendant in a good pair;
2. **interior rigidity:** rule out a finite full-rank child-closed component
   that avoids all such good boundary hits forever.

The second is the genuinely interior case left after PR #82.

## 4. Stronger subtargets worth testing

These are research targets, not claims.

### 4.1 Good-pair hitting

Barge--Diamond proves strong coincidence for two letters and a partial
higher-letter result; the live manuscript uses their general existence input
with exact scope.  A useful strengthening for the present route would be:

> every closed irreducible bad-overlap normal form contains a left- or
> right-aligned state on a pair already known to be eventually coincident.

This would kill the obstruction directly without proving all-pairs strong
coincidence first.

### 4.2 Aligned-pair coverage

A still stronger but very concrete candidate is that the aligned states of a
closed full-rank overlap component cover enough unordered letter pairs that
they must meet the Barge--Diamond good-pair set (and, after reversal, the
suffix good-pair set).  This is now an exact finite invariant of any proposed
countermodel.

### 4.3 Interior-only obstruction

If neither boundary mechanism can be forced, the remaining object is sharply
specified:

```text
finite + strongly connected + child-closed
+ no coincidence
+ PF(N_S)=beta
+ rank(V_S)=d and spec(M) subset spec(N_S)
+ avoids every productive endpoint-aligned pair at every depth.
```

Any new spectral, ordered-child, Rauzy, or recognizability argument should be
stated against exactly this object.

## 5. Executable certificate

Canonical Mojo implementation:

```text
mojo/psc/overlap_obstruction.mojo
```

The function

```text
nonproductive_sink_sccs(graph)
```

returns all closed recurrent SCCs inside the nonproductive set.  It fails
closed on capped graphs.  The regression constructs a synthetic graph with a
transient bad vertex feeding a two-state closed bad SCC and verifies that only
the recurrent core is returned.

Independent Python oracle:

```text
src/psc_research/overlap_obstruction.py
tests/test_overlap_obstruction.py
```

No corpus output changes are expected: the exact 4,554-member PIP corpus has
zero nonproductive overlap vertices, so its obstruction list is empty.  The
purpose of the extractor is countermodel retention and normalization if a
future conjectured invariant fails.

## 6. Literature alignment and provenance

The **graph-theoretic part** of Proposition 2.1 is not claimed as novel.
Potential-overlap algorithms standardly reduce failure of overlap coincidence
to recurrent noncoincidence components and compare their Perron growth with
the expansion; Akiyama--Lee (2011) is the primary algorithmic reference in the
self-affine setting.  What is specific to the present seed-patch programme is
the combination of that standard finite obstruction normalization with:

- unconditional finiteness of the swap-seed overlap graph from bounded
  discrepancy;
- the in-repository full-rank intertwiner of Corollary 5.34;
- the exact endpoint/boundary-hitting criterion of PR #82; and
- a canonical fail-closed extractor that preserves a finite countermodel for
  subsequent conjectures.

The strong-coincidence literature also clarifies what the boundary part does
and does not buy.  Akiyama--Lee (2014) show overlap coincidence implies an
appropriate strong-coincidence condition under the height-group hypothesis,
and Akiyama (2016) gives converse statements for sufficiently many
control-point choices under additional topological hypotheses.  These results
explain why endpoint coincidence is a necessary boundary signal but do not
supply Open Problem 5.35 for the single seed-patch graph used here.

References:

- S. Akiyama and J.-Y. Lee, *Algorithm for determining pure pointedness of
  self-affine tilings*, Adv. Math. 226 (2011), 2855--2883,
  DOI 10.1016/j.aim.2010.07.019, arXiv:1003.2898.
- S. Akiyama and J.-Y. Lee, *Overlap coincidence to strong coincidence in
  substitution tiling dynamics*, European J. Combin. 39 (2014), 233--243,
  DOI 10.1016/j.ejc.2014.01.009, arXiv:1403.0377.
- S. Akiyama, *Strong coincidence and overlap coincidence*, DCDS-A 36 (2016),
  5223--5230, DOI 10.3934/dcds.2016027, arXiv:1509.04471.

## 7. Next theorem attack

The immediate next step for #84 should use the extractor only as a normalizer,
not as an end in itself:

1. assume an obstruction `S` from Proposition 2.1;
2. compute/track its exact aligned-pair sets `A_+(S), A_-(S)` and ordered child
   boundary events;
3. prove that full rank plus the child factorization forces a good boundary
   hit, **or** emit the smallest exact interior-only pattern that evades the
   proposed invariant;
4. keep any surviving pattern as a replayable countermodel instead of
   weakening the theorem silently.

That is the smallest next slice that can make mathematical progress on the
one remaining gate without reintroducing G1, finite injectivity, or
unimodularity.
