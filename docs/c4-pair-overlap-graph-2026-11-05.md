# Complete paired-occurrence graphs give a contractive overlap certificate

**Status:** written sufficiency argument plus executed exact Python replay for
two named non-unit controls; independent human review pending. Native Mojo
tests and driver/oracle packet parity were replayed in a follow-up (see §7);
hosted exact-head execution is a separate CI receipt.
No general C4, G1, BH, A1', pure discreteness or PSC status is promoted.

Baseline: `main@60536272b3d68b4f53ce772e7674efabce840fde`, including merged
#493, #494 and #495. Target: issue #461. The #493 convention corrections are
retained. This experiment uses the compact M-adic prefix sets of
[c4-nonunit-madic-counting-bridge-2026-11-04.md](c4-nonunit-madic-counting-bridge-2026-11-04.md),
not an unproved identification with a different adelic model.

## 1. What changes relative to the finite-cylinder bounds

The two supported sources are exactly `1/021/001` and `1/012/001`, with
M=[[0,1,2],[1,1,1],[0,1,0]], det M=2 and Perron root beta of
x^3-x^2-2x-2. Each has a checked period-two fixed point. Their positive
hull bounds in #495 were all greater than two; those particular enclosures
could not satisfy the strict-density comparison.

Here a COMPLETE finite recursion over paired prefix occurrences supplies
an exact positive subinvariant vector. It proves that all three unshifted
letter-pair overlaps have measure zero for each control, using no
strong-coincidence witness as an input. Their null overlaps were already
known analytically from those witnesses. The new contribution is an
independently replayable finite graph certificate and an explicit decreasing
upper bound, not discovery of an unwitnessed source or a new PDS theorem.

## 2. Prior art and stop/go

Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine
tilings*, arXiv:1003.2898, Section 4, equation (4.2) and Theorem 4.1,
uses potential-overlap multigraphs and compares spectral radii. The arXiv
PDF page 12 (zero-based page 11) was inspected, including the displayed
theorem and its Meyer-set hypothesis. Its full PDS equivalence is NOT
imported here: our objects are compact M-adic prefix sets, and neither a
tiling nor the theorem's full hypothesis package is supplied.

The graph-directed idea and subinvariant-vector argument are standard.
Proceed only with a direct measure-containment proof in the repository's
stated compact model. No strong-coincidence/PDS implication, empirical
spectral radius, or omitted edge may substitute for a finite obligation.
Primary reference: https://arxiv.org/abs/1003.2898 ; published DOI
10.1016/j.aim.2010.07.019. The #495 literature gate supplies the context for
non-unit prefix sets and complete occurrence inventories.

## 3. A smaller certified common box

Use exactly #495's chart:

```
ell=(1,beta,beta^2-beta-1),
W x=(x0-a*x1,x2-b*x1),
a=(3 beta-beta^2)/2, b=(beta^2-beta-2)/2,
B=[[-a,2-a],[-b,-b]], W M=B W.
```

With probability Haar measure on H_M, the internal map A=(B,M) scales
area-times-Haar measure by 1/beta. Consequently A^2 scales by beta^-2,
NOT the Euclidean-only factor 4/beta^2.

The new common Euclidean box is Q=[-16,16] x [-8,8], area 512. Exact
root isolation and block arithmetic certify

```
beta^2 > 103/20,
a in [828911,828912]/10^6,
b in [440619,440620]/10^6,
|B^12| <= [[473,390],[147,344]]/1000.
```

Every one of the 55,583 proper-prefix digits of sigma^12(d), over the
three source letters, has absolute coordinates at most (23/5,14/5).
The independent oracle enumerates every digit; the native code uses the
complete prefix-hull recursion already used in #495. These are complete
bounds, not extrema of a selected sample.

For R=(16,8) and D=(23/5,14/5), the coordinate inequalities are
D+|B^12| R <= R, with strict weighted linear contraction. To see why this
bounds the actual compact sets, let t be the largest weighted norm of a
point in any subtile. The full block set equation gives
`t <= max_i(r_i t+d_i)` with r_i<1 and r_i+d_i<=1. If t>1 then each
right-hand term is less than t, a contradiction. Thus every Euclidean
projection lies in Q. This proof is independent of an initial point plot.

## 4. Every paired occurrence and exact quotient membership

Write K_c for the compact lifted prefix set. For an integer vector z define

```
E(c,c',z) = K_c intersect (K_c' + (Wz, iota(z))).
```

For each actual occurrence sigma^2(d)=P c S and
sigma^2(d')=P' c' S', let p,p' be the proper-prefix Parikh vectors. The two
cylinder terms can intersect only if z+p'-p belongs to M^2 Z^3. If so set

```
z_new = M^-2 (z+p'-p).
```

The paired intersection is an affine A^2-image of E(d,d',z_new). Membership
is checked exactly: native adj(M^2) divisibility by det(M^2)=4; independent
Python rational Gaussian inversion. Coordinatewise modular reduction is
not used.

A child can be discarded geometrically only if its Euclidean translation
W z_new lies strictly outside Q-Q=[-32,32] x [-16,16]. The coarse rational
intervals above are evaluated with INTEGER arithmetic. Touching an endpoint
or uncertain separation is retained. Nonintegral children are discarded
by exact disjointness of compact residue cosets.

Normalize (c,c',z) with its track swap (c',c,-z). This is valid for measure,
since the two intersections are translates of one another. Every paired
occurrence still contributes one edge: repeated targets are NOT collapsed.
The roots are (0,1,0),(0,2,0),(1,2,0). Breadth-first traversal exhausts every
row and stops only at actual finite closure. A retained offset outside the
coordinate budget, or an exhausted state cap, RAISES an inconclusive error;
it is never another geometric pruning rule.

## 5. The exact finite-graph implication

Let T count the retained edges, with rows parent and columns child, and
v_i=mu(E_i). All discarded children have empty intersections, so the full
set equation and subadditivity give

```
0 <= v <= beta^-2 T v,       0 <= v_i <= 512.
```

No disjointness between retained affine pieces is assumed. Let w be a
strictly positive INTEGER vector and suppose the complete graph satisfies

```
T w <= lambda w,             0 < lambda < beta^2.
```

With C=max_i(v_i/w_i), the inequality gives C<=lambda*beta^-2*C. Finite
C and strict contraction force C=0. Therefore every represented overlap
has zero measure. This does not prove it is empty: the root {0,1} contains
the origin for both controls, as #495 already explains.

There is an explicit finite upper bound too. Since w_i>=1 and v_i<=512,
iteration gives

```
v_i <= 512 w_i (lambda/beta^2)^n.
```

The two graphs have lambda=99/20 and 101/20 respectively, while beta^2 is
strictly greater than 103/20. Thus the entirely rational certificates are
`512 w_i (99/103)^n` and `512 w_i (101/103)^n`. These tend to zero with an
explicit rate. At n=1024 two-generation blocks, each of the six root bounds
is strictly less than 1/10, checked by integer cross multiplication through
exact Fractions. This is a compressed recurrence bound for 2048 generations,
not an assertion that words of that length were materialized.

All these implications use the already written compact-set equations and
Haar scaling. A finite replay does not formally verify measure theory.
A supplied strict component would additionally invoke the separate positive
cut-density theorem to obtain a contradiction. No arbitrary positive
number is admitted as a density, and no actual strict PIP component is
exhibited. The two sources are productive controls already treated in #494.

## 6. Exact replay results

| Source | States | Paired-occurrence edges | lambda | Positive weight construction iterations | Minimum integer gap |
|---|---:|---:|---|---:|---:|
| 1/021/001 | 7150 | 34826 | 99/20 | 856 | 99 |
| 1/012/001 | 7083 | 34853 | 101/20 | 1695 | 101 |

The checked integer gap is `numerator*w_i-20*sum_edges(w_child)`.
Root weights, in pair order 01,02,12, are (38500,1,1) and
(82573,12935,44045). The maximum weights are 89510 and 98981.
Neither graph contains a zero-offset diagonal state.

The positive vector is generated without eigensolvers or floating point:
start w=1 and iterate `w_new_i=1+ceil(20*(T w)_i/numerator)` until unchanged.
Every final inequality is checked independently of how w was found. Failure
to converge within the declared budget yields no result. The reference
receipt gives full graph SHA-256 digests; the driver can emit every vertex,
edge target with multiplicity, and weight for inspection.

## 7. Tests, provenance and acceptance debt

Nine Python tests pass locally, with no skipped tests. In addition to the
Gaussian-inverse construction, a separate test reconstructs EVERY candidate
edge with the integer adjugate, independently rescans literal prefixes,
and uses rational interval coordinates. It agrees on both entire graphs
and their rejection totals. The source contains no SC search or stored SC
witness input.

Adversarial controls reject omitted repeated edges, relabelled states,
nonpositive/wrong weights, rates lacking strict separation, missing native
records, duplicate native records, unsupported inputs, and resource-cap
exhaustion. Boundary contact is retained. Python -O cannot bypass the
verifier's explicit acceptance checks. The native-packet calibration test
uses reference-generated text only; it is NOT a native execution receipt.

```
python -m pytest -q tests/test_c4_pair_overlap_graph_oracle.py
python oracles/python/c4_pair_overlap_graph.py
python oracles/python/c4_pair_overlap_graph.py --emit-packet > /tmp/reference-pair-graph.txt
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pair_overlap_graph.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_pair_overlap_graph.mojo) > /tmp/native-pair-graph.txt
PSC_PAIR_GRAPH_NATIVE_OUTPUT=/tmp/native-pair-graph.txt python -m pytest -q tests/test_c4_pair_overlap_graph_oracle.py
python oracles/python/c4_pair_overlap_graph.py --native /tmp/native-pair-graph.txt
python tools/make_proof_bank.py --check
```

Native source reuses the existing chart, exact intervals, matrix arithmetic,
word inflation and radius checks. Mojo/pixi are not installed in this local
runtime, so compilation and native/reference parity remain PENDING, as do
the full-repository Proof Bank, governance and hosted suites. The focused
workflow retains these obligations. No hosted pass or independent human
proof review is claimed. (Historical: superseded by the replay below.)

**Native replay (2026-11-05 follow-up on #496, Mojo 1.1.0.dev2026090805):**
`tests/test_c4_pair_overlap_graph.mojo`, `tests/test_c4_pair_overlap_source_class.mojo`
and `tests/test_c4_pair_overlap_class.mojo` pass, and the three drivers
`c4_pair_overlap_{graph,source_class,class}.mojo` were run and their full
packets accepted by the matching Python oracle `--native` verifier, each
reproducing the committed `receipt.json` exactly. The earlier "not compiled"
statements and the `local-validation.json` records predating this replay are
kept as historical records of what had run at that time.

## 8. Research consequence and remaining target

This removes the numerical upper-enclosure obstruction for the two named
controls by replacing shallow rectangular hull comparisons with a complete
finite recursion and a verified contractive vector. Null overlap was already
known through SC; here the proof procedure does not consume that witness.
It is still not an example of a represented cut pair with no SC witness.

The next real extension is to authenticate this construction for additional
incidence matrices/sources and test whether a complete graph with a strict
subinvariant vector can be obtained on the still-unresolved strict-carrier
route. Finiteness, the chart, compact scaling and complete occurrence edges
must all be supplied anew; a favorable eigenvalue of an arbitrary graph
would prove nothing. General C4 and PSC remain outside this result.
