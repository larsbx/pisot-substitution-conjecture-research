# Exact nine-swap-seed SCC census: one possible extra state beyond the X closure

**Status:** complete **finite-specimen** overlap-graph computation plus an
elementary, parameter-independent **conditional graph reduction**. There is
**no** universal k,t SCC theorem or all-seed BH/PDS/PSC claim here.

## Object and finite reachability predicate

Work with the minus class-A family
k,t>=0; n=k+t+3; d=k+2t+5; A=n+d; and
x->x y^A x, c->c y^n x, y->x y^(n-1) c.
Each overlap is an oriented full five-tuple
(top,bottom,dx,dc,dy), and every real child retains
its **actual top/bottom word occurrence indices**.
The strict intersection guard uses the repository's
unchanged literal-word/Fraction Perron `Geometry`.
No float threshold or quotient-state substitution is used.

Take the **nine** strict swapped-patch tile overlaps from PR #428,
not just the four convenient X/Y0/CY/CC sources in PR #427.
The nine original seed tuples are explicitly listed in the code,
and no unproven equivalence to all realized literature-overlap
classes is assumed. Coincidence is exactly equal tile types
with **all three** Parikh offsets zero, made terminal *only
for existential coincidence reachability and SCC extraction*.

This packet enumerates the **complete strict directed graph**
at each tested k,t, retaining distinct indexed edges, and
**raises inconclusive** if a 6,000-state cap is reached.
The graph is never declared productive when truncated.
It computes the SCCs using main's already existing independent
`reference/psc_research/overlap_obstruction.py`, and
cross-checks nonproductive sink SCCs through that library.
`Reach(X)` is computed **inside the same complete nine-seed graph**,
which is valid because PR #428 proves every seed has a path to X.
This eliminates the need to build two possibly differently
capped graphs and accidentally compare incomplete closures.

## Finite results: 16 fully completed graphs

For exactly 0<=k<=3, 0<=t<=3:

| k,t | Nine-seed graph | Reach(X) | Extra outside Reach(X) | SCC count | X SCC | max reverse-X depth | max coincidence depth |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 0,0 | 784 | 784 | none | 3 | 782 | 9 | 7 |
| 0,1 | 1010 | 1010 | none | 3 | 1008 | 9 | 8 |
| 0,2 | 1220 | 1220 | none | 3 | 1218 | 9 | 8 |
| 0,3 | 1439 | 1438 | S1 | 4 | 1436 | 10 | 8 |
| 1,0 | 436 | 436 | none | 3 | 434 | 6 | 4 |
| 1,1 | 642 | 642 | none | 3 | 640 | 7 | 6 |
| 1,2 | 645 | 644 | S1 | 4 | 642 | 7 | 5 |
| 1,3 | 836 | 836 | none | 3 | 834 | 7 | 5 |
| 2,0 | 378 | 378 | none | 3 | 376 | 6 | 5 |
| 2,1 | 389 | 388 | S1 | 4 | 386 | 6 | 4 |
| 2,2 | 594 | 594 | none | 3 | 592 | 6 | 5 |
| 2,3 | 567 | 566 | S1 | 4 | 564 | 6 | 4 |
| 3,0 | 351 | 350 | S1 | 4 | 348 | 5 | 4 |
| 3,1 | 341 | 340 | S1 | 4 | 338 | 6 | 4 |
| 3,2 | 361 | 360 | S1 | 4 | 358 | 5 | 4 |
| 3,3 | 547 | 546 | S1 | 4 | 544 | 6 | 4 |

Here **S1=(x,x,0,1,0)** is the valid second
literal swapped-patch seed in #428, **not** a nickname
for a different X-family state.

Exactly **one recurrent noncoincident SCC** occurs in each
of these 16 graphs, and it contains X. Every other nonterminal
vertex, including S1 when outside Reach(X), has an actual path
to X. Two typed coincidence terminals are closed.
There are **zero nonproductive sink SCCs** and every tested vertex
is productive. These are finite graph facts only: no claim is
made for any unsampled parameter or non-swap seed.

Three additional separately inspected complete specimens,
(k,t)=(0,4),(0,5),(0,6), had respective
nine-seed counts 1,632/1,807/1,987 and Reach(X)
counts 1,632/1,806/1,986. Their differences were
none/S1/S1 and all their vertices were productive.
They are exploratory checks outside the locked
16-specimen CI matrix, not universal evidence.

## A precise one-state graph-reduction lemma

For any directed graph, fix a set of seeds S, a hub X
and a distinguished possible exception s. Let
R=Reach(X), using **forward** reachability. If

1. Every seed in S belongs to R ∪ {s}; and
2. Every actual child of s belongs to R ∪ {s},

then the entire forward closure of S belongs to
R ∪ {s}, because that union is forward-closed:
R is forward-closed by its definition, and condition
(2) handles the one extra source. This is a graph
fact independent of Perron arithmetic, SCC sizes,
and finiteness. The source file implements the
criterion with negative tests that reject a missing
seed or a single escaping child.

Thus the **specific open universal class-A goal**
suggested by the finite census is:

> For all k,t>=0, all nine swapped-patch overlap
> seeds other than S1 occur in Reach(X), and
> every actual S1 child belongs to Reach(X) ∪ {S1}.

Establishing those two claims by uniform symbolic
occurrence paths (or another valid carrier argument)
would prove that the complete nine-seed closure has
**at most one extra source state** outside Reach(X).
The existing #428 seed->X path ensures S1 itself is
productive regardless of whether X reaches S1.
A separate universal statement that **every member
of Reach(X) has a path back to X** (or at least to
some typed coincidence) is still needed to turn
this closure reduction into global productivity
*for this nine-swap graph*.

Crucially, **seed -> X does not imply X -> seed**.
The finite (k,t)=(3,0) graph exhibits exactly that
directional asymmetry: nine-seed graph 351,
Reach(X) 350, extra S1. A naive attempt to
identify PR #427's four-seed closure with the
nine-seed closure is also unsound because adding
CC as a source can include states that the nine
swaps do not reach at t>0.

## Reproducibility, review and boundaries

`oracles/python/class_a_boundary_nine_seed_scc.py`
and `tests/test_class_a_boundary_nine_seed_scc.py`
completed all five local tests with a faithful
mirror of the repository's exact Fraction Geometry
and SCC implementation. The committed source/test
Git blob SHAs are pinned to the locally executed
bytes. The GitHub workflow must repeat those tests
against **the original repository files** before
fresh exact-head acceptance. No stored evidence
receipts, canonical Mojo kernels or governed
theorem statuses are changed.

The following remain unproved: universal X-SCC
accessibility, universal one-state extension,
all-seed strict-zipper/realized-overlap coverage,
the non-unit representation-space interface,
BH/#139, G1, A1-prime, PDS and PSC.
