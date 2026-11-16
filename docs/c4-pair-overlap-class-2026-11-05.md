# Common-attractor refinement: two-step certificates for all 18 source orders

**Status:** written scoped sufficiency proof plus executed exact finite Python
certificates; independent human mathematical review pending. Native Mojo
tests and native/reference packet parity were replayed in a follow-up (§6);
hosted exact-head acceptance is a separate CI receipt. **This common-attractor
two-step route is the canonical route for the 18-source-order certificate;**
the period-aware route is kept as a recorded earlier variant. No general C4/G1/BH/A1'/PDS/PSC
claim status is changed.

Independent continuation begun at #496 head
`d5833e3ad2908cec847002b797d12c73d48045a4`, reconciled without overwriting
the concurrent period-aware extension `cea416ffae3c48875a457e2fed5535f5daa4e126`.
Main remains `60536272b3d68b4f53ce772e7674efabce840fde` at inspection.
The period-aware implementation, original two controls, and their receipts
are preserved. The new native entry point REUSES that current shared graph
engine; no existing source-class admission rule is weakened.

The concurrent extension already certifies all 18 sources using step two
for 14 sources and step three for four. This note does not claim that source
coverage as an additional gain over that commit. Its new ingredient is the
written common-attractor argument below: it authenticates step TWO also
for the period-three sources. The independent finite replay then supplies
one rate, 51/10, for all 18. Compared with the preserved period-aware route,
this uses 285,786 rather than 288,835 states and 1,409,729 rather than
1,862,307 occurrence edges. The new <1/10 bound uses 2,304 two-step blocks
rather than the earlier 8,192 mixed two-/three-step blocks. Both are valid
necessary-upper certificates under their explicitly stated written inputs.

## 1. Complete source domain and conclusion

The incidence is fixed, not estimated:

```text
M = [[0,1,2],[1,1,1],[0,1,0]], det M=2,
chi_M(x)=x^3-x^2-2x-2.
sigma(0)=1,
sigma(1) in {012,021,102,120,201,210},
sigma(2) in {001,010,100}.
```

These are ALL 18 literal substitutions with this incidence. The primitive
irreducible Pisot and compact M-adic normalization inputs are those of the
merged #494/#495 notes; they depend on M, not on source-word order.
The new finite certificates establish zero measure for all three unshifted
distinct-letter intersections for EACH of the 18 sources. The procedure
does not search for or read a strong-coincidence witness.

Combining this conclusion with the repository's lifted strict-cut bound
(Theorem M1 in `c4-nonunit-madic-counting-bridge-2026-11-04.md`) excludes a
nonempty finite fully strict child-closed noncoincident balanced-pair set
for every source in this class. Its size and period are unrestricted; no
particular P,N template is assumed. This does NOT extract a finite strict
component from an arbitrary failure, prove every balanced root productive,
or prove pure discrete spectrum. Those would require additional premises.
It does not assert that any of these sources lacks a coincidence witness.

*Note, 2026-11-09.* "Unrestricted" means: for every finite set, of any size. The bound of Theorem M1 depends on the largest state length and gives nothing for an infinite child-closed set, which is the G1 case. All 18 sources are members of the 4,554-specimen standing corpus (images of length at most three and PIP incidence, §1, so members by the definition of the corpus; also checked with the Python reference `pip_corpus()` for the quantifier audit), where the same exclusion is the governed finite-domain claim `C4StandingCorpus`; for them this note is a second derivation and adds no source to that domain ([quantifier audit](quantifier-transfer-audit-2026-11-09.md), §§12-13).

## 2. A common enclosure, with the six initial refusals retained as refusals

The original two-control certificate uses Q=[-16,16] x [-8,8] and block-digit
bounds (23/5,14/5). Six of the additional source orders fail that digit-bound
test. This is not a counterexample or evidence of positive overlap. The old
box was never silently reused for those sources.

The new independently checked common box is

```text
Q_all=[-24,24] x [-12,12],  area(Q_all)=1152,
D_all=(13/2,4),
|B^12| <= [[473,390],[147,344]]/1000,
beta^2 > 103/20.
```

For each source, ALL 55,583 proper-prefix digits in its three twelfth-level
images are checked against D_all. The class total is 1,000,494 digits.
The root-isolating intervals and polynomial reduction in Q(beta) are exact;
no floating-point comparison is used in acceptance. The native recursion
includes every prefix and the independent Python code materializes all
proper prefixes. The coordinate inequalities are

```text
13/2 + (473*24+390*12)/1000 = 22.532 < 24,
4    + (147*24+344*12)/1000 = 11.656 < 12.
```

The linear weighted max-norm factor is at most 668/1000<1. These rational
inequalities enclose the entire compact attractor, not a sampled plot.
The exact maximum-digit bounds for every source are stored in the receipt.

## 3. Fixed-point periods: why the two-step recursion remains valid

The original controls have period-two fixed points. The enlarged class
also has prefix cycles of length one and three. In particular the sources
`1/201/001`, `1/201/010`, `1/210/001`, `1/210/010` have a three-cycle.
It would be unjustified to assume their prefix sets automatically satisfy
the two-step equation merely because their incidence is unchanged.

Here is the needed compact-attractor argument in the repository's own
space E^s x H_M. Let F send a triple of nonempty compact sets to the unions
of their images under ALL single-step literal prefix maps. Its twelfth
iterate has Euclidean Lipschitz constant at most 668/1000 in the weighted
norm above. Give H_M the usual matrix-adic ultrametric: agreement modulo
M^q has diameter at most 2^-q. Multiplication by M^12 contracts that metric
by 2^-12. Therefore F^12 is a strict contraction on the complete product
Hausdorff space of nonempty compact sets. It has a unique fixed triple.

For any first-letter cycle of length q in this three-letter class, q is
1,2 or 3 and divides 12. Since all letter-image lengths grow under iteration, a letter on that
cycle gives a one-sided sigma^q-fixed word. The literal prefix-set equation
from #494 gives K=F^q(K), and hence K=F^12(K). Thus these actual compact
prefix sets equal the unique F^12 attractor. Also F(K) is fixed by F^12,
because powers of F commute; uniqueness implies F(K)=K. In particular
K=F^2(K), exactly as needed by the two-step overlap graph, even for q=3.
The same argument shows independence of the chosen periodic fixed word.

This is a written compact-space proof, not a conclusion of the graph census.
It assumes the established compactness and literal fixed-word set equation
from #494. It does not identify H_M with an alternative adelic space.

## 4. Complete finite graphs, one common integer rate

All roots are (c,c',z=0), c<c'. Every actual pair of second-image occurrences
with prefixes p,p' contributes the inverse offset

```text
z_new=M^-2(z+p'-p).
```

Reject only exact nonintegrality or strict interval-certified exclusion of
Wz_new from Q_all-Q_all. Preserve boundary contact and every repeated edge.
Track swapping is normalized using translation invariance of measure.
State and coordinate caps are explicit refusal limits, NOT pruning rules.
All 18 traversals finish at genuine graph closure below the 16,000-state
limit; the largest actual offset coordinate is 36, below the checked cap 40.

Every resulting graph T admits a positive integer w satisfying

```text
20 T w <= 102 w,       lambda=102/20=51/10 < beta^2.
```

The minimum integer gap is exactly 102 in every graph. Weights are found
by monotone ordered integer sweeps and checked afterwards, without any
floating-point eigensolver. Nonconvergence is inconclusive, not rejection
of a source. The independent verifier reconstructs the graph before admitting
weights; a small matrix with favorable spectrum is not a certificate.

| Source | States | Occurrence edges | Integer sweeps |
|---|---:|---:|---:|
| 1/012/001 | 15,824 | 78,333 | 334 |
| 1/012/010 | 15,877 | 78,356 | 97 |
| 1/012/100 | 15,850 | 78,359 | 458 |
| 1/021/001 | 15,909 | 78,296 | 148 |
| 1/021/010 | 15,896 | 78,305 | 283 |
| 1/021/100 | 15,897 | 78,246 | 168 |
| 1/102/001 | 15,802 | 78,306 | 129 |
| 1/102/010 | 15,867 | 78,353 | 89 |
| 1/102/100 | 15,847 | 78,359 | 118 |
| 1/120/001 | 15,913 | 78,276 | 161 |
| 1/120/010 | 15,895 | 78,336 | 294 |
| 1/120/100 | 15,876 | 78,348 | 127 |
| 1/201/001 | 15,891 | 78,288 | 152 |
| 1/201/010 | 15,881 | 78,299 | 85 |
| 1/201/100 | 15,890 | 78,278 | 152 |
| 1/210/001 | 15,895 | 78,326 | 471 |
| 1/210/010 | 15,872 | 78,334 | 106 |
| 1/210/100 | 15,904 | 78,331 | 332 |

Totals: **285,786 vertices and 1,409,729 occurrence edges**, across 18
separate graphs. Repeated edges remain repeated occurrences. No graph has
a zero-offset diagonal state. Root weights and complete graph SHA-256
digests are in the receipt; full deterministic packets can be emitted.

## 5. Measure consequence and finite upper bounds

For every state overlap E_i, let v_i=mu(E_i). Compact M-adic Haar scaling
is beta^-2 over two generations (NOT Euclidean-only 4/beta^2). Full
occurrence coverage and subadditivity imply

```text
0 <= v <= beta^-2 T v,    v_i <= 1152.
```

With positive integer w and lambda<beta^2, C=max_i(v_i/w_i) obeys
C<=lambda*beta^-2*C and hence is zero. Thus all 54 source/letter-pair roots
have zero measure. Zero measure does not assert an empty intersection.

The same recurrence provides the entirely rational upper certificate

```text
v_i <= 1152 w_i (102/103)^n.
```

At n=2304 two-generation blocks, all 54 root upper bounds are strictly
less than 1/10, checked using exact Fractions. This is a compressed bound
representing 4608 substitution generations, not materialized words.

If a finite strict child-closed set existed for a covered source, its
represented cut pairs would be a subset of these three null roots. Their
union would be null, contradicting #494's positive lower bound kappa/L_max.
This conditional contradiction uses the written counting bridge, not an
invented density or an SC witness. General strict-component extraction and
PSC are not discharged by a finite incidence class.

## 6. Replays, mutations and acceptance

```sh
python -m pytest -q tests/test_c4_pair_overlap_graph_oracle.py tests/test_c4_pair_overlap_class_oracle.py
python oracles/python/c4_pair_overlap_class.py
python oracles/python/c4_pair_overlap_class.py --source 12
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pair_overlap_graph.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_pair_overlap_class.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_pair_overlap_class.mojo) > /tmp/native-class.txt
python oracles/python/c4_pair_overlap_class.py --native /tmp/native-class.txt
python tools/make_proof_bank.py --check
```

The new 22-test Python suite includes all 18 complete graphs. Each row is
independently reconstructed with the integer adjugate of M^2, direct string
prefix counts and rational interval pruning, against the producer's
Gaussian-inverse/running-counter construction. The row-by-row check covers
all 1,409,729 retained occurrences and every residue/box rejection count.
Additional tests cover the exact source domain, period-three cases,
insufficient old box, omitted repeated edges, wrong weights, non-strict
rates, malformed sources, cap exhaustion, native schema refusal and -O.
The original nine Python tests remain unchanged.

Local tests were executed in bounded shards; the command lines, outputs
and exit statuses are recorded without relabelling them as one unexecuted
monolithic run. The current canonical graph implementation and all its period-aware
wrappers remain unchanged. A small new `c4_pair_overlap_attractor.mojo`
entry point authenticates the common-attractor premises, calls the SAME
complete graph constructor at step two, and uses ordered integer weight
sweeps. The old period-aware constructor still refuses an unqualified
step-two request on a period-three source, now with the message "fixed-point
step outside the period-aware route's premise; see the common-attractor
route": that step lies outside that route's premise, not outside validity.
The new written argument is an additional premise, not a deleted check.
The attractor's `12 % period` test is an invariant assert (every prefix
period on three letters divides 12), not a negative control; the native
`build_source_order_graph(5, state_cap=3)` call is a state-cap refusal
control asserting "state budget exhausted; inconclusive". No second native graph engine
is introduced. Native adapter edits during reconciliation were not executed;
the tested independent Python source and receipt values remain unchanged.

Mojo/pixi are unavailable here, and the network clone attempt failed DNS
resolution. Native compilation/parity, full-repository Proof Bank/governance
and hosted checks remain pending. A Python-generated packet is not native
evidence. The exact-head workflow requires actual native output and both
old and new packet comparisons. No governed status is promoted.
(Historical: superseded by the replay below.)

**Native replay (2026-11-05 follow-up on #496, Mojo 1.1.0.dev2026090805):**
`tests/test_c4_pair_overlap_graph.mojo`, `tests/test_c4_pair_overlap_source_class.mojo`
and `tests/test_c4_pair_overlap_class.mojo` pass, and the three drivers
`c4_pair_overlap_{graph,source_class,class}.mojo` were run and their full
packets accepted by the matching Python oracle `--native` verifier, each
reproducing the committed `receipt.json` exactly. The earlier "not compiled"
statements and the `local-validation.json` records predating this replay are
kept as historical records of what had run at that time.

## 7. Literature and next boundary

Minervino--Thuswaldner, *The geometry of non-unit Pisot substitutions*,
Ann. Inst. Fourier 64 (2014), DOI 10.5802/aif.2884, arXiv:1402.2002,
Section 2.1 and Theorem 8.3, were consulted for periodic-point and
prefix-graph context (arXiv PDF pages 3 and 19 inspected). Their adelic
tiling conclusions are not imported into this compact model. Graph-directed
contraction and spectral/subinvariant-vector criteria are established
methods; the parent #496 note records the Akiyama--Lee comparison
(stop/go record: §2 of `c4-pair-overlap-graph-2026-11-05.md`).

The contribution relative to the concurrent 18-source extension is the
explicit period-three compatibility proof, a separately reconstructed
common two-step certificate, and tighter finite recurrence bounds. Relative
to the original two controls, the shared branch now covers sixteen additional
sources and 48 additional root pairs; that expanded coverage is not counted
twice. No claim is made
that these sources are unwitnessed, nor that this is a universal theorem
for all matrices or non-unit Pisot substitutions. A further substantive
extension must change the incidence matrix or establish a uniform
contraction principle, rather than repeat this completed source class.
