# Complete overlap contraction for all 18 source orders

**Status:** written finite sufficiency proof plus executed exact arithmetic
replay, independent human review pending. Native tests and driver/oracle
parity were replayed in a follow-up (see the evidence boundary below);
hosted acceptance remains a separate obligation.

**Route status.** This period-aware route (step 2 for prefix periods 1 and 2,
step 3 for the four period-three sources 12, 13, 15, 16) is a recorded
earlier variant. The canonical route for the 18-source-order certificate is
the common-attractor two-step route of
[c4-pair-overlap-class-2026-11-05.md](c4-pair-overlap-class-2026-11-05.md)
(`kernel/psc/c4_pair_overlap_attractor.mojo`). A step-2 request on a
period-three source is refused here because it lies outside THIS route's
premise, not because step 2 is invalid there: the attractor route proves
and accepts it. No general C4, G1, BH,
A1', PDS or PSC claim status is changed.

This extends draft #496 at `d5833e3ad2908cec847002b797d12c73d48045a4`,
on `main@60536272b3d68b4f53ce772e7674efabce840fde`. The original two-control
receipts are retained unchanged. The extension changes the same draft, not
the repository's main branch or an unrelated research stack. Target: #461.

## Exact domain and new conclusion

Freeze M=[[0,1,2],[1,1,1],[0,1,0]], determinant two. Exhaust all substitutions
having that incidence:

```
sigma(0)=1,
sigma(1) in {012,021,102,120,201,210},
sigma(2) in {001,010,100}.
```

These are exactly 18 literal sources. Their common primitive irreducible
Pisot arithmetic is the same as #494/#495: M^4 is positive, the monic cubic
x^3-x^2-2x-2 has no integer root among +/-1,+/-2, discriminant -152, unique
real beta>2, and conjugate squared modulus 2/beta<1. None of these facts
permits substituting one source word order for another in the overlap graph.

For EVERY source, every one of the three unshifted distinct-letter overlaps
of the chosen compact M-adic prefix sets has measure zero. The finite
certificate uses NO strong-coincidence search or witness. It does not claim
that any source is mathematically noncoincident, nor prove a new PDS theorem.

At the scope of the existing written compact bridge (Theorem M1 in
[c4-nonunit-madic-counting-bridge-2026-11-04.md](c4-nonunit-madic-counting-bridge-2026-11-04.md)),
this also excludes every nonempty finite fully strict child-closed system
of irreducible noncoincident balanced pairs for these 18 sources. Such a
system would force a positive-measure union of represented unshifted pair
overlaps; all three are null here. This requires neither a state-count bound
nor an arbitrary density supplied by the caller. It does not prove the
separate general G1 extraction needed outside this finite source class.

## Fixed-point periods are part of admission

A source is not permitted to inherit the old two-generation step blindly.
The first-letter map is followed from letter 0 until its cycle repeats.
Six sources have period one, eight have period two and four have period
three. For periods one/two the graph uses q=2; for period three it uses q=3.
Each chosen cycle letter begins its sigma^period image and has a growing
iterate, giving a one-sided fixed point of that power. The old compact set
equation is therefore applicable to the chosen graph step.

The four q=3 sources are
`1/201/001`, `1/201/010`, `1/210/001`, `1/210/010`.
A request to replay these using q=2 is rejected. All depth-12 enclosure
identities are legitimate because 12 is divisible by each possible period.

## A common enclosure, with all source digits checked

Reuse #495's exact W chart, beta isolation and B stable action. The old
[-16,16] x [-8,8] box is insufficiently justified for the expanded class.
Instead certify Q=[-24,24] x [-12,12], of area 1152. The exact common
bounds are

```
|B^12| <= [[473,390],[147,344]]/1000,
all block prefix digits <= (13/2,4) coordinatewise in absolute value,
beta^2 > 103/20, beta^3 > 292/25.
```

Every one of the 55,583 proper-prefix occurrences per source is included:
1,000,494 depth-12 digits across the class. Integer coarse-chart extrema
are recorded for each source, with denominator 10^6. The largest are
6,440,578/10^6 and 3,989,218/10^6, below the advertised digit bounds.
The full block equation, weighted linear contraction and
D+|B^12|(24,12) <= (24,12) prove compact-set containment. No sampled point
cloud is used. The native implementation independently uses full prefix-hull
recursion rather than the Python literal enumeration.

## Complete graph and certified rates

States are the same translated pair intersections as #496. For every pair
of actual occurrences in sigma^q, compute M^-q(z+p'-p). Exact nonintegrality
means disjoint compact residue cylinders. Otherwise reject only when its
certified W-interval lies strictly outside Q-Q. Boundary contact is retained.
Track swapping is normalized by translation-invariance of measure, and
repeated occurrence targets remain repeated edges.

Python uses Gaussian rational inverses; native and an independent test use
integer adjugates divided by det(M^q). The denominator of a REDUCED rational
inverse need not equal det(M^q); the integrality conditions agree after
scaling, as the independent row replay verifies. No coordinatewise modular
substitute is used.

The graphs exhaust all rows before acceptance. State caps (20,000), offset
coordinate caps (64) and iteration caps yield inconclusive errors, never
additional pruning. In total the 18 graphs contain **288,835 states** and
**1,862,307 occurrence edges**. None contains a zero-offset diagonal state.

| Graph step q | Sources | Certified lambda | Lower bound for beta^q | Rational contraction ratio |
|---|---:|---|---|---|
| 2 | 14 | 102/20 | 103/20 | 102/103 |
| 3 | 4 | 233/20 | 292/25 | 1165/1168 |

Every full graph T has a checked positive integer vector w satisfying
`20 T w <= numerator*w`. Its smallest integer slack is strictly positive;
the maximum weight across all sources is 63,257. The raw source-specific
graphs, root weights, rejection counts and SHA-256 digests are in the receipt.

The existing compact Haar normalization gives
`0 <= v <= beta^-q T v` and `v_i<=1152`. Hence
`max(v_i/w_i) <= (lambda/beta^q) max(v_i/w_i)` forces all v_i=0.
This is a written measure implication supported by the exact finite graph,
not a machine verification of measure theory and not an imported tiling/PDS
equivalence.

There are explicit finite bounds too:
`v_i <= 1152*w_i*(102/103)^n` or `1152*w_i*(1165/1168)^n`.
All 54 root bounds are less than 1/10 at n=8192 blocks, checked by exact
rational arithmetic. This represents 16,384 or 24,576 generations via a
compressed recurrence, not materialization of those substituted words.
Null measure does not assert empty intersections.

## Construction optimization does not change acceptance

Most states lie outside large cyclic components. The Python constructor
uses an iterative SCC decomposition, processing components from sinks to
sources and solving `w_new=1+ceil(20 T w/numerator)` with already fixed
external weights. This gives the same least integer fixed point as global
synchronous iteration; both are independently compared on two full graphs.
The native constructor uses the global iteration. Its emitted full packet
must match the reference, including every weight and repeated target.

No SCC decomposition or eigensolver is trusted by the acceptance test:
regardless of construction, every final inequality is recomputed over the
complete original graph. A synthetic/incomplete graph is not admitted as a
source certificate merely because its weights satisfy an inequality.

## Reproduction and evidence boundary

```
python -m pytest --assert=plain -q tests/test_c4_pair_overlap_source_class_oracle.py
python oracles/python/c4_pair_overlap_source_class.py
python oracles/python/c4_pair_overlap_source_class.py --emit-packet
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pair_overlap_source_class.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_pair_overlap_source_class.mojo) > /tmp/class-native.txt
PSC_PAIR_CLASS_NATIVE_OUTPUT=/tmp/class-native.txt python -m pytest --assert=plain -q tests/test_c4_pair_overlap_source_class_oracle.py
python oracles/python/c4_pair_overlap_source_class.py --native /tmp/class-native.txt
```

The new tests reconstruct every candidate paired edge for all 18 sources
with a separately coded integer cofactor/adjugate route and independently
rescanned literal prefixes. They preserve full multiplicities and rejection
counts; check exact source-domain coverage, outside-premise step refusal, boundary
contact, false weights, omitted repeated edges, caps, optimized-Python
admission, and complete packet reconstruction. A reference-generated packet
is calibration, not a native execution receipt.

The native core in `c4_pair_overlap_graph.mojo` is generalized in place;
the original wrappers, receipts and tests remain separate regressions.
No second canonical graph builder is introduced. A separate independent
Python source-class oracle reuses only exact chart/matrix primitives and
retains its own complete edge construction.

**Executed locally:** all 16 Python tests pass (nine original, seven new),
with no skips, in the completed 78.44-second run. The command used
`PYTEST_DISABLE_PLUGIN_AUTOLOAD=1` and `--assert=plain`; assertions remain
active and the production verifier uses explicit exceptions. The new suite
also passed separately (seven tests in 40.55 seconds). Actual commands,
logs and hashes are recorded in the new evidence folder.
Mojo/pixi are absent locally, so native compilation/execution and parity are
NOT claimed. Full-repository Proof Bank/governance, fresh hosted acceptance
and independent human mathematical review remain pending. No generated
claim status is manually edited. (Historical: superseded by the replay below.)

**Native replay (2026-11-05 follow-up on #496, Mojo 1.1.0.dev2026090805):**
`tests/test_c4_pair_overlap_graph.mojo`, `tests/test_c4_pair_overlap_source_class.mojo`
and `tests/test_c4_pair_overlap_class.mojo` pass, and the three drivers
`c4_pair_overlap_{graph,source_class,class}.mojo` were run and their full
packets accepted by the matching Python oracle `--native` verifier, each
reproducing the committed `receipt.json` exactly. The earlier "not compiled"
statements and the `local-validation.json` records predating this replay are
kept as historical records of what had run at that time.

## Prior art and remaining target

Potential-overlap graph/spectral criteria are established methods; see
Akiyama--Lee, arXiv:1003.2898, and the #496 source discussion. For classical
non-unit Rauzy spaces see Minervino--Thuswaldner, arXiv:1402.2002. The current
continuation checked the abstracts; it does not newly audit or import their
full PDS/tiling theorems. This argument instead uses the repository's scoped
compact-space proof and a complete occurrence graph. The stop/go record for
this route is §2 of
[c4-pair-overlap-graph-2026-11-05.md](c4-pair-overlap-graph-2026-11-05.md).

The additional coverage is sixteen source orders and authenticated period-
three recursions, not a universal result on arbitrary incidence matrices.
The next substantive extension must vary the incidence/representation data
or supply a uniform finiteness/contraction argument. Repeating this now-
complete 18-source class adds no new coverage. General PSC remains outside
this result.
