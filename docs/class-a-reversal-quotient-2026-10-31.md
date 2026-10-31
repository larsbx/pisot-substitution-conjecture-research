# Exact reversal-orbit quotient of the class-A X and 18-seed strict overlap graphs

**Status:** a general, exact graph-theoretic quotient/lifting lemma plus
reproducible **finite-parameter** class-A census. Stacked on PR #433's
orientation-complete graph implementation, whose all-parameter closure
reduction itself references unaccepted #428/#430/#431 and #432.
This does **not** prove universally productive X descendants, graph
finiteness, all-seed boundary hitting, realized-overlap coverage, G1 or PSC.
Independent human review and exact-head hosted CI are still outstanding.

## Why a quotient is sound, and when it is not

An actual oriented overlap state is the full five-tuple
(top,bottom,dx,dc,dy). Its reversal is
R(a,b,p,q,r)=(b,a,-p,-q,-r). The child map respects reversal
*with real indexed letters*: for every strict edge

    child(w,i,j)=v

we have

    child(R(w),j,i)=R(v).

The full strict physical overlap guard also respects reversal.
The finite graph builder first terminalizes **only typed full-zero
coincidences** (equal actual tile letters, all Parikh offsets zero).
The terminal set is reversal-invariant, so R is still an automorphism.

For any **complete reversal-closed** occurrence-indexed graph G,
define the orbit vertex [v]={v,R(v)}. The quotient graph Q carries
a directed edge [u]->[v] for every genuine indexed child edge of
one fixed canonical representative u=min(u,R(u)).
Each quotient edge stores (target orbit, actual top index,
actual bottom index), **not** merely its target label.

Crucially, a quotient walk is *effectively liftable* from EITHER
actual orientation of its source: use the stored actual (i,j) when
the current source is the canonical representative; use (j,i) and
reverse the full target when the current source is reversed.
After each step, the actual intermediate state lies in the
selected target orbit. The new oracle performs that transport
against the original literal-word/Fraction Geometry, checking
strict overlap and every full Parikh coordinate.

### Universal quotient hitting and distance lemma

For any reversal-invariant target set T of actual vertices,

    v ->* T    iff    [v] ->* T/R in Q.

More strongly, with ordinary finite integer path length
and shortest distance d,

    d_G(v,T) = d_Q([v],T/R),

allowing both sides to be infinite. Projection proves <= in one
direction; the actual indexed lifting algorithm proves the
reverse inequality. This implication is valid in an infinite
graph as well; computation of any complete instance still
must fail closed on a cap.

**An SCC caveat:** an arbitrary quotient SCC need not lift to
one SCC in the original graph; a pair of reversed SCCs can
collapse together. For the distinguished X component,
the four-edge X<->R(X) bridge constructed in separate PR #432
provides the missing orientation-connection hypothesis.
The quotient is appropriate for coincidence reachability
without any such SCC assumption.

## Exact finite parameter census

The new `oracles/python/class_a_reversal_quotient.py`
reuses the complete, unchanged literal-word/Fraction
strict-closure builder in PR #433 and checks actual reversal
completeness for **every indexed edge**, including transpose
of both child ordinals and the target's complete Parikh tuple.
It explicitly rejects a graph missing a reversed vertex,
a missing reversed edge, duplicated indices, malformed
targets, nonterminal reversal-fixed states and a truncated cap.

For each k,t in {0,1,2,3}, we build the **entire forward
X closure**, and separately the **complete 18-orientation
swapped-patch closure**, then quotient each. All graphs
are finite and complete at these sixteen tested members;
this says nothing about a uniform bound in k,t.

| k,t | X actual | X quotient | S18 actual | S18 quotient |
| --- | ---: | ---: | ---: | ---: |
| 0,0 | 784 | 393 | 784 | 393 |
| 0,1 | 1010 | 506 | 1010 | 506 |
| 0,2 | 1220 | 611 | 1220 | 611 |
| 0,3 | 1438 | 720 | 1440 | 721 |
| 1,0 | 436 | 219 | 436 | 219 |
| 1,1 | 642 | 322 | 642 | 322 |
| 1,2 | 644 | 323 | 646 | 324 |
| 1,3 | 836 | 419 | 836 | 419 |
| 2,0 | 378 | 190 | 378 | 190 |
| 2,1 | 388 | 195 | 390 | 196 |
| 2,2 | 594 | 298 | 594 | 298 |
| 2,3 | 566 | 284 | 568 | 285 |
| 3,0 | 350 | **176** | 352 | **177** |
| 3,1 | 340 | 171 | 342 | 172 |
| 3,2 | 360 | 181 | 362 | 182 |
| 3,3 | 546 | 274 | 548 | 275 |

In every such graph, precisely **two** vertices are fixed by
reversal: the x/x and y/y typed full-zero coincidences.
All nonterminal vertices form two-element reversal orbits.
Consequently, the quotient has exactly (V+2)/2 vertices.
The quotient keeps **one orientation's indexed edges**,
halving the exact multiplicity as well: `E_Q=E_G/2`.
This is audited directly, not deduced from visual symmetry.

For the concrete parameter (k,t)=(3,0):

    Reach(X):        350 states -> 176 quotient vertices,
                     3,222 actual indexed edges -> 1,611 indexed quotient edges.
    Reach(S18):      352 states -> 177 quotient vertices,
                     3,252 actual indexed edges -> 1,626 indexed quotient edges.

The additional orbit in S18 is exactly
`{E6,R(E6)}`, *not* two independent quotient vertices.

All sixteen **X-generated quotients** have exactly
three SCCs: one recurrent nonterminal X-containing SCC
of size `Q-2`, plus two terminal coincidence singletons.
The full 18-seed quotients have three SCCs when the
exception orbit is absent and **four** when it is present
(the extra exceptional orbit is transient).
There is exactly one recurrent nonterminal quotient SCC
in all thirty-two complete finite instances.

In all thirty-two **tested** graphs, every quotient orbit
reaches typed coincidence, and **every original vertex**
has exactly the same shortest coincidence distance as
its quotient orbit. The checker independently reconstructs
all shortest-path witnesses and lifts them through genuine
indexed substitution child transitions, not just graph IDs.
Observed maximum coincidence depth is at most eight on
these specimens, not a universal bound.

## Reproduction and negative controls

The source and tests are pinned as **byte-identical Git
blobs** to files actually exercised locally in the
repository-shaped environment. The exact source SHA is
`8ed3ae599e64f71e6c8df94244b3fe7efb49603a`;
the regression SHA is
`b8d06b898913aaa5945ec3bbd4beecf849d43644`.
The following test groups were run separately and
passed in local runs (the combined invocation hit a
local execution timeout, not a mathematics failure):

    python -m pytest -q tests/test_class_a_reversal_quotient.py -k every_complete_finite_x_graph
    python -m pytest -q tests/test_class_a_reversal_quotient.py -k eighteen_seed_orientation
    python -m pytest -q tests/test_class_a_reversal_quotient.py -k 'actual_lift or nonproductive_cycle or reversal_edge'

The dedicated hosted workflow also runs these test
groups separately and must confirm all of them with
the **actual GitHub source tree and predecessor**.
Negative controls deliberately reject (i) a graph missing
a reversed edge, (ii) an edge with non-transposed indices,
(iii) duplicate indexed occurrences, (iv) capped graphs,
(v) fabricated quotient edge witnesses, and (vi) a
reversal-symmetric **nonproductive directed cycle**.
That last case proves a quotient does not somehow
make an unproductive SCC productive.

## What remains mathematically open

The big gain is an **exact factor-of-two reduction** in
tested state and indexed-edge counts, without losing
coincidence reachability or any shortest-path depth
and with a fully constructive lift back to actual
occurrences. The quotient supplies a smaller and
sound target object for a future parameterized
productivity proof over the entire X closure.

It does **not** prove that every vertex in the
X-generated overlap closure is productive for all
k,t>=0. In particular no uniform symbolic quotient
carrier, exhaustive parameterized boundary-ray
classification, all-seed strict-zipper/literature
realization bridge, non-unit transfer or universal
PSC argument is supplied here.
