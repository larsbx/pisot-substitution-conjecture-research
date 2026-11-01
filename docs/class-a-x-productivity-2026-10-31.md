# X descendants: exact SCC audit and a parameter-indexed productive ladder

**Status:** finite exact observations for 22 completed graphs; a scoped
hand-derived universal local ladder, with polynomial identities checked
over Z[k,t,m]. Native replay acceptance is recorded separately. Universal
X-descendant productivity and coverage of that closure by the ladder remain
open. Independent human review pending (nonblocking validation debt).

## Work shown

### Assumptions and hypotheses

The [stop/go](class-a-x-productivity-stopgo-2026-10-31.md) was recorded before
the diagnostic. Integers k,t>=0, n=k+t+3, d=k+2t+5, A=n+d; actual words are

    x -> x y^A x,   c -> c y^n x,   y -> x y^(n-1) c.

Labels are (top,bottom,p,q,r), with full bottom-minus-top Parikh displacement.
Only strict intersections count. FIRST is ordinal 0, RUN is 1..run length,
LAST is run length+1; LAST in sigma(y) is c, while LAST in sigma(x) is x.
The exact incidence transport is

    M(p,q,r) = (2p+q+r, q+r, (n+d)p+nq+(n-1)r).

Add bottom proper prefix and subtract top proper prefix. Reversal swaps
letters and indices and negates ALL offset coordinates. Typed coincidence
means equal letters and p=q=r=0; equal physical displacement alone is not a
substitute. Coincidences are terminalized for existential reachability only.

For the local uniform argument inherit main's minus-chamber exact root and
length facts from [the W packet](class-a-boundary-w-carrier-2026-10-27.md),
[the P3 packet](class-a-boundary-p3-carrier-2026-10-28.md), and
[the Y0 packet](class-a-boundary-y0-every-child-2026-10-31.md):

    beta > n+2, h=1/beta, alpha=beta-(n+2), rho=alpha-h,
    Ly=1, Lc=1+h, Lx=2+rho,
    0<h<1/5, h<rho, rho+2h<1.

These are algebraic ordered-root predicates implemented with exact rational
root enclosures in the oracle. No decimal roots or analytic approximations
enter the decisions. The local proof below does not use the five open PRs.

### Derivation / reduction

#### Acceptance snapshot and dependency firewall

At this session's initial October 31 inspection main is d4d97dbe63b7.
All five PRs are open and unmerged; no required exact-head workflow had
succeeded. Their dedicated workflows were queued (some unrelated #431
workflows pending).

| PR | Head inspected | Base / dependency | Outstanding acceptance evidence |
| --- | --- | --- | --- |
| #428 | df233242c919 | main | Exact-head CI; unresolved review includes native implementation, stop/go and ledger findings; import-path finding belongs to an earlier head |
| #430 | c36713575759 | #428 | Exact-head CI and native implementation finding |
| #431 | c6a27494124d | #430 | Exact-head CI; native implementation and ledger findings; review also flags an improper human-review prerequisite on an earlier revision |
| #432 | d2b94fe5d682 | main | Exact-head CI; native implementation and ledger findings |
| #433 | 2e9ecf67fe1d | main, mathematical premises #428/#430/#431/#432 | Exact-head CI; native implementation and ledger findings |

An unresolved review thread can describe an older revision; this table does
not assert every finding still reproduces at the current head. It does
establish that universal predecessor acceptance has not been demonstrated.
The identity Reach(S18)=Reach(X) union {E,R(E)} is **conditional on those
source certificates**. Here it is checked independently on finite graphs;
neither those PRs nor their certificate files are integrated by this change.
Pending human review alone is not a progression or integration blocker.

#### Independent complete finite graphs

The new builder derives the nine strict source labels directly from the
twelve two-tile ab/ba candidates, then adds nine genuine reversals. It
independently enumerates every literal indexed strict edge, preserving
multiplicity and refusing a 6,000-vertex cap before any graph verdict.
Its adjacency agrees, as full labelled indexed sets, with #433's pinned
oracle on (0,0), (0,2), (3,0). SCCs are iterative Kosaraju; independently,
the X component equals forward(X) intersect backward(X).

The 16 original members k,t=0..3 plus controls (0,4),(4,0),(4,4),
(0,8),(8,0),(8,8) give **22 complete graphs, 16,132 vertices and
190,966 indexed edges in aggregate**. In each:

* Every vertex admits an actual indexed path to a typed coincidence.
* Every nonterminal vertex returns to X. In Reach(X), all nonterminal
  vertices lie in its single recurrent noncoincident SCC.
* There are exactly two terminal coincidence SCCs, (x,x,0,0,0) and
  (y,y,0,0,0), and no nonproductive sink SCC.
* E=(x,x,0,1,0) and R(E) either belong to X's SCC or are the two extra
  transient vertices, with outgoing paths into X's closure. No other
  extra vertices occur.
* Deleting every RUN/RUN edge preserves productivity on these graphs.
  Requiring BOTH occurrences to be endpoints does not; this stronger
  proposed restriction fails on every tested member.

At (3,0), the X/nine/eighteen sizes are exactly 350/351/352; X's SCC
has 348 vertices. At (0,8), the graph has 2,312 vertices and X's SCC
2,308; a shortest coincidence distance is 12 (14 without RUN/RUN).
Thus an eight-edge global escape bound, which fits the original 16
graphs' unrestricted distances, fails at this parameter control. This
does not prove distances unbounded in parameters.

The committed certificate has states and a strictly decreasing integer-rank
forest giving a genuine selected edge for EVERY non-root vertex, for
coincidence reachability, return to X, and no-RUN/RUN coincidence reachability.
The graph digest additionally pins every enumerated indexed edge. Tests
recompute the graphs and all three forests, not just their counts.

#### A universal two-edge ladder, with precise word-index guards

Define full typed states, for integer m>=1,

    A_m = (x,y,2m,6m+1,1-12m),
    B_m = (y,x,1-2m,2-6m,12m-7).

For the local statement restrict

    k,t>=0, 2k+t>=2, 1<=m, (k+1)m<=k+t+6.                 (D)

For every m>=2 in (D), the actual indexed transfers are

    A_m --(i_m,0)--> B_m --(0,j_m)--> A_(m-1),
    i_m=d+k+8-2(k+1)m,  j_m=d+2k+9-2(k+1)m.

Both moving occurrences are RUN y; the other occurrence is FIRST x.
The formula is a coefficientwise full-Parikh identity, not equality after
physical projection. Before prefixes, the third coordinates are

    (M A_m)_y = (10-2k)m+d+k,
    (M B_m)_y = (2k-10)m-d+5-2k.

Subtract (1,0,i_m-1) in the first edge and add (1,0,j_m-1) in the
second, giving exactly B_m and A_(m-1), in all three coordinates.
The actual ordinal bounds follow from the following slack identities:

    i_m = 2[k+t+6-(k+1)m]+1 >= 1,
    j_m = i_m+k+1 >= 1,
    A-j_m = (2k+t-2)+k+2(k+1)(m-2) >= 0,
    A-i_m = (2k+t-2)+2k+1+2(k+1)(m-2) >= 0.

Thus even i_m=1 and j_m=A are included with their correct RUN type.
The domain is inherited by m-1, so induction on m is legitimate.

For strict geometry, the incidence cubic is

    chi(beta)=beta^3-(n+2)beta^2-(t+3)beta+2=0.

It yields alpha=(t+3)h-2h^2. Consequently

    (alpha+2h)(beta+1)=beta-k,
    v=1-rho-3h=(k+1)/(beta+1)>0.

The EXACT shifts are

    shift(A_m)=2+h-2mv,
    shift(B_m)=-2-h+(2m-1)v.

By (D), 2mv<=2(n+3)/(beta+1)<2. Hence shift(A_m)>h>0,
and its upper strict margin is rho-h+2mv>0. For B_m the lower
margin relative to -Lx is rho-h+(2m-1)v>0; its upper margin
relative to Ly is 3+h-(2m-1)v>1+h>0. Every displayed ladder
vertex is strict, with no floating rounding or missing endpoint case.

The fixed base exit is:

| Parent | Actual indices | Typed target |
| --- | --- | --- |
| A_1 | (d+5-k,0) | D=(y,x,-1,-4,6) |
| D | (0,t+6) | H=(x,y,1,2,-3) |
| H | (A+1,n-1) | J=(x,y,1,-1,1) |
| J | (A+1,0) | X=(x,x,1,0,-1) |
| X | (d+1,0) | Q=(y,x,0,-1,1) |
| Q | (1,2) | C=(y,y,0,0,0) |

Here A-(d+5-k)=2k+t-2>=0 and A-(t+6)=2k+2t+2>=0.
At H the top is LAST x and bottom n-1 is RUN y (not LAST c).
At J the top is LAST x and bottom FIRST x. The final two edges are
main's existing X exit; their indices are valid since n>=3,d>=5.
The shifts of D,H,J,X,Q are respectively

    -rho-4h, 1+rho+2h, 2+rho-h, 1+rho, -h.

D has lower margin 2-4h>0 and negative shift; H is positive with
upper margin 1-2h>0; J has upper margin h>0; X has upper margin 1;
Q has shift -h strictly between -Lx and Ly. These inequalities and
the inherited bounds prove all six target geometries. C is typed full zero.

Combining the two-edge descent with the six-edge base proves the **scoped
universal local statement**: every A_m satisfying (D), and its genuine
reversal, admits a selected coincidence path of length 2m+4. Every B_m
for m>=2 in (D) also has the displayed edge into that path. Reversal
transposes actual indices and negates the full vector; no new geometry
assumption is required. This is an unbounded indexed family, not a finite
list extrapolated to parameters.

The exclusions are real: at (k,t)=(0,1), d+5-k=A+1, so the alleged
base RUN y is actually LAST x and the target is (x,x,-1,-4,6),
not D. At (0,0) that ordinal is beyond the word. No failure of
productivity is claimed at either excluded member; their complete finite
graphs are productive. At m just beyond the transfer bound, the moving
index can be negative; no extrapolation is allowed.

### Evidence and replay

Sources: `kernel/psc/class_a_x_ladder.mojo` is the native member path
implementation; `kernel/psc/class_a_x_productivity.mojo` is the canonical
indexed-graph builder and finite SCC/reachability diagnostic. It preserves
full Parikh lifts and refuses any inconsistent lift at exact-state interning;
strict occurrence enumeration uses a streaming partition sweep. It binds
tables to the actual ordered words and reuses vendored iterative Tarjan SCCs.
The Python module independently uses exhaustive literal occurrence pairs,
Fraction root enclosures and iterative Kosaraju SCCs. The exact polynomial
checker uses SymPy 1.14.0 solely for coefficients/remainders, not root signs.

    python -m pip install pytest==8.4.2 sympy==1.14.0
    python -m pytest -q tests/test_class_a_x_productivity.py
    python oracles/python/class_a_x_ladder_symbolic.py
    python oracles/python/class_a_x_productivity.py --certificates > /tmp/x-certificates.json
    cmp /tmp/x-certificates.json evidence/class-a-x-productivity-2026-10-31/finite-certificates.json
    cd kernel
    pixi run --locked mojo run -I . tests/test_class_a_x_ladder.mojo
    pixi run --locked mojo run -I . tests/test_class_a_x_productivity.mojo --emit-indexed > /tmp/x-native.log
    cd ..
    python oracles/python/class_a_x_productivity.py --native-log /tmp/x-native.log

The polynomial certificate checks eight base/transfer edges plus eight true
reversals, three cubic-root identities, both ladder shift identities and
the index-slack decompositions. The path test covers k=0..12,t=0..8 and
additional (0,20),(0,64),(32,0), every admissible m, both orientations:
**824 oriented paths / 18,456 selected edges over 118 admissible members**
(the other two parameter specimens are explicit excluded-face controls).
Native and hosted acceptance receipts are described separately from Python
results in the evidence README.

The initial toolchain constraint in the stop/go was resolved. The native
finite graph diagnostic has its own regression and contract receipt.
The cross-language replay compares EVERY full typed vertex and indexed edge
for all 22 graphs, plus SCC and distance statistics; agreement of aggregate
counts alone is not its acceptance test. A per-member canonical indexed
digest makes that evidence reproducible. Hosted exact-head CI remains a
separate acceptance obligation.

### Negative controls

Tests refuse capped graphs, negative parameters, wrong child letters,
wrong full offsets, wrong indices, unswapped reversal indices, broken
paths and forest ranks which fail to decrease. An unequal-letter zero
label and E are not coincidences. Synthetic controls distinguish a
nonproductive sink from a cycle with a productive alternative edge.
The sharp base LAST/RUN distinction and both moving-index endpoint
equalities are exercised. A nonzero polynomial m(m-1), invisible to a
two-sample interpolation shortcut, is explicitly rejected coefficientwise.

### Non-claims / remaining gaps

The finite graph result, conditional S18 identity and universal local ladder
are three distinct claims. No parameter-uniform SCC census or universal
X-descendant productivity follows. The ladder does not cover all X
descendants; indeed (3,0) has no A_m in Reach(X) for its proved indices.
At (0,8), A_1..A_5 are actual X descendants, while A_6..A_14 satisfy
the local productive-family domain but are outside that closure.

The next reproducible target is a typed peeling/transfer classification
of the X-SCC vertices outside these ladders, with complete child guards
and a rank decreasing into a registered productive family. The observed
no-RUN/RUN productivity suggests a sparse selected-edge search, but lacks
a universal proof; corners-only selection is already refuted. Neither
increasing isolated packet counts nor forward/reversal closure discharges
that coverage obligation. No realized-literature-overlap coverage,
plus-chamber transfer, BH/#139, G1, PDS or complete PSC proof is claimed.
