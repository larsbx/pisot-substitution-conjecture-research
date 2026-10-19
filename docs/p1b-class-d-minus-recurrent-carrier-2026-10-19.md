# Minus positive-b class D: cycle-sum reduction — 2026-10-19

**Status:** conditional reduction for issue #139. The earlier candidate premise
"every cyclic state lies in the sealed 145-label carrier" is **false** and is
superseded here. No class-D, #139, #84 or PSC theorem is promoted.

## 1. Inputs already on main

For the minus residual

```text
p = 3a+5+b,
q = 3a+6+b,
r = 2a+4+b,
a>=2, b>=1,
```

main contains:

1. **#287 algebraic selected-state descent.** Every non-target sealed label has
   valid occurrence-index formulas whose computed child state is another
   sealed label of strictly lower rank. Maximum rank is four.
2. **#288 conditional target geometry.** Whenever such a sealed source is a
   genuine overlap, its selected lower-rank target is also a genuine overlap;
   both target margins exceed `1/10`.

These facts make every genuine sealed-carrier state productive.

## 2. Why recurrent-carrier inclusion is false

The affine cycle analysis exposes four genuine recurrent candidates outside
the sealed carrier:

```text
U    = (y,c,-2, 4,-3)
Ubar = (c,y, 2,-4, 3)
V    = (y,c, 3,-6, 4)
Vbar = (c,y,-3, 6,-4).
```

The pair `U,Ubar` has an exact two-cycle whenever `b<=a`. The pair
`V,Vbar` has an exact two-cycle whenever `b<=a+1`. Hence unrestricted cyclic-carrier inclusion is false. This alone does not
show seed reachability of these cycles; see the exact grid correction in §9.
The earlier carrier-only diagnostic must not be used as the reduction contract.

This does **not** obstruct BH because all four states have productive exits.

## 3. Productive exceptional exits

### 3.1 The U pair

For

```text
U=(y,c,-2,4,-3)
```

choose top index `0` and bottom run index `b`. Exact affine replay gives

```text
U -> (c,y,2,-3,1),
```

which is sealed row 69, rank two.

The mirror choice gives

```text
Ubar -> (y,c,-2,3,-1),
```

sealed row 97, rank two.

These exits are valid for every `a>=2,b>=1`, whether or not the exceptional
two-cycle itself exists.

### 3.2 The V pair

Put

```text
A    = (y,y,-3, 5,-3),
Abar = (y,y, 3,-5, 3).
```

For every `a>=2,b>=1`:

```text
V -> A
```

by top run index `b` and bottom run index `a+2`; the mirror uses
`a+2` and `b`.

The geometric margins satisfy

```text
A lower = d + 3/beta - 2 > 0,
A upper = V lower.
```

Thus a real `V` produces a real `A`. The mirror statement is identical.

Now split only on `b=1` versus `b>=2`:

```text
b=1:
    A    -> sealed row 44, rank 2, FIRST/FIRST
    Abar -> sealed row 35, rank 2, FIRST/FIRST

b>=2:
    A    -> sealed row 69, rank 2, top FIRST / bottom run index b-1
    Abar -> sealed row 97, rank 2, top run index b-1 / bottom FIRST.
```

The carrier targets are uniformly real on the minus Perron box.

`kernel/psc/class_d_minus_exceptional_cycles.mojo` verifies all eight
occurrence edges and the corresponding geometric implications.

## 4. The remaining scalar premise

Write

```text
s(w) = wx+wc+wy,
m(w) = wx+wc,
tau(w) = wx-wc.
```

For one class-D child edge, the x/c endpoint structure gives

```text
m'   = 2s + eta,       eta in {-1,0,+1},
tau' = 2m - 2s + xi,  xi in {-2,-1,0,+1,+2}.
```

Therefore, on a directed cycle, the premise

```text
|s| <= 1
```

forces

```text
|m| <= 3,
|tau| <= 10.
```

This motivates the final open lemma.

> **CycleSum-.** Every genuine seed-reachable cyclic overlap in the minus
> positive-b residual satisfies `|wx+wc+wy|<=1`.

## 5. Exact guarded cycle superset

Assuming CycleSum-, every genuine cycle lies inside the finite typed box

```text
s in [-1,1],
m in [-3,3],
tau in [-10,10].
```

There are exactly 1,971 integral typed states in this box.

For each state and each of the nine first/run/last segment pairs,
`kernel/psc/class_d_minus_cycle_superset.mojo` computes the required
occurrence-index difference. Its legal interval is affine in `a,b`.
After shifting

```text
u=a-2 >= 0,
v=b-1 >= 0,
```

the two range conditions are affine forms in `u,v`. An edge is deleted only
when the repository's checked exact Farkas kernel proves those forms have no
common point. Failure to refute keeps the edge, so the resulting graph is a
sound overapproximation.

Its recurrent part contains exactly 145 vertices, classified as

```text
131 sealed-carrier states
  2 offset-zero states
  8 boundary-only states
  4 productive exceptional states
---
145 recurrent superset states.
```

The eight boundary-only states have an overlap margin identically zero and
therefore cannot be genuine interior overlap vertices. The four exceptions are
the U/Ubar/V/Vbar states of §3.

Hence:

> **Conditional theorem (CycleSum- => minus BH).** If CycleSum- holds, then
> every genuine cyclic overlap in the minus positive-b residual has an
> offset-zero descendant. Carrier states use #287/#288; offset-zero states are
> already done; boundary-only states are impossible; the four exceptions use
> §3.

The selected-path depth after entering the ranked carrier is at most four.

## 6. Why the sum lemma is genuinely the last gap on this route

For a child chosen at top/bottom word indices `i,j`,

```text
s(w')
 = (3a+7+b) wx
 + (3a+8+b) wc
 + (2a+6+b) wy
 + (j-i).
```

Equivalently,

```text
s(w')
 = b s(w)
 + a(3wx+3wc+2wy)
 + (7wx+8wc+6wy)
 + (j-i).
```

The earlier parameter-free SCC overapproximation that let each edge choose a
different `(a,b)` contains artificial higher-sum cycles. A representative
`|s|=2` cycle requires simultaneously

```text
v = 2u+7
and
v <= u,
```

with `u=a-2,v=b-1`, which is impossible. Thus common-parameter compatibility
around a cycle is essential.

The next proof should exploit this shared-parameter constraint, not enlarge
the overlap carrier.

## 7. Finite calibrations

The independent exact Q(beta) SCC oracle remains useful as a calibration, but
its former RC- interpretation is retired. Finite grids do not prove
CycleSum-.

## 8. Non-claims

- CycleSum- remains open.
- The old RC- premise is false and must not be cited.
- The finite 1,971-state superset is conditional on CycleSum-.
- The plus branch is separate and uses the merged finite chamber decomposition.
- Universal #139, #84 and PSC remain open.


## 9. Diagnostic repair and exact scope correction (2026-10-19)

| Obligation | Governed status |
| --- | --- |
| Minus cycle-sum bound | Open conjectural gate: `MinusClassDPositiveBCycleSum` |
| Minus positive-b boundary hitting | Conditional theorem: `MinusClassDPositiveBBoundaryHitting`, dependent on CycleSum- and seed-graph finiteness |
| Universal boundary hitting, issue #139 | Open; this family implication does not discharge it |
| General PSC / #84 | Open; no implication from this finite grid is asserted |

The old Python carrier-only rejection is retired as the executable contract.
The canonical diagnostic is `kernel/psc/class_d_minus_recurrent_support.mojo`;
`oracles/python/class_d_positive_b_recurrent_support.py` independently computes
Q(beta) signs, offsets and SCCs. Neither constructs its seed graph from the
conditional 1,971-state box. Each closes the actual swap-seed graph (cap
20,000), classifies every recurrent label, replays productive exceptional
exits, and reports any unexplained label or finite CycleSum violation with a
seed path, a closed cycle and top/bottom occurrence indices. Caps refuse.
The canonical driver fixes 2<=a<=8,1<=b<=8; its API additionally refuses
parameters outside 2<=a<=100,1<=b<=100 as an explicit computation budget.

**Correction to the proposed failure diagnosis:** both independently executed
56-specimen grids have no recurrent seed label outside the carrier. They agree
on every recurrent label and count (maximum 129 recurrent vertices). Thus the
old finite carrier test was overstrong as a contract for the formal reduction,
but this grid is not an observed RC- counterexample. The genuine U/Ubar and
V/Vbar cycles are checked directly as formal interior overlaps at a=2,b=1,2,
with their actual occurrence exits; these checks do not assert seed reachability.
Finite absence of these exceptions is not a proof of seed-carrier inclusion.

The two noncarrier offset-zero vertices of the conditional superset are now
identified explicitly:

- `(x,x,0,0,0)` is a genuine tile coincidence;
- `(c,x,0,0,0)` is a distinct-letter boundary-hit target, **not** a coincidence.

The second receives its own named classification in the finite diagnostic.
Other distinct-letter zero offsets must be carrier members or are unexplained;
there is no blanket zero-offset skip. The conditional superset retains terminal
self-loops as an overapproximation; the exact seed graph makes coincidences
terminal. In particular, its recurrent coincidence count is zero.

For completeness, the final finite-graph implication does not need a bound on
transient depth. At fixed (a,b), suppose some reachable vertex has no path to
zero offset. Its forward-reachable subgraph is finite, has no terminal
coincidence, and every genuine overlap has a child. It therefore contains a
directed cycle. CycleSum- puts that cycle in the guarded box; the classification
and verified exits give a zero-offset descendant, a contradiction. This proves
the **conditional** family implication, not its open premise.

## 10. Shared-parameter incompatibility across complete cycles

The new canonical module `kernel/psc/class_d_minus_shared_cycles.mojo` checks
specified closed walks of at most 128 typed states, with each coordinate bounded
by 1,000,000 as an explicit arithmetic budget. For every edge, including the
closing edge, it verifies child types and x/c coordinates against the chosen
FIRST/RUN/LAST segments. It then derives the two occurrence-difference guards.
All guards use the SAME variables u=a-2,v=b-1. There is no fresh parameter pair
at a successive edge. The independent Python oracle derives the guards anew.

Here is a six-edge algebraic negative control, with x=0,c=1,y=2 in the code:

| Edge source `(top,bottom,wx,wc,wy)` | Top / bottom segment | Nonnegative guard forms `[constant,u,v]` |
| --- | --- | --- |
| `(c,c,-4,7,-5)` | FIRST / LAST | `[-7,-2,1]`, `[7,2,-1]` |
| `(c,x,3,-6,4)` | FIRST / FIRST | `[2,1,-1]`, `[-2,-1,1]` |
| `(c,x,-3,5,-4)` | FIRST / RUN | `[11,2,2]`, `[0,1,-1]` |
| `(c,y,3,-6,4)` | FIRST / FIRST | `[2,1,-1]`, `[-2,-1,1]` |
| `(c,c,-3,5,-4)` | RUN / RUN | `[25,5,3]`, `[-1,1,-1]` |
| `(y,y,2,-6,6)` | LAST / FIRST, closes to first row | `[4,2,-1]`, `[-4,-2,1]` |

Each edge separately has an integer (u,v) witness, respectively
`(0,7),(0,2),(0,0),(0,2),(1,0),(0,4)`. Yet guard rows 0 and 5 (zero-based,
flattening the table's pairs) add to `-7-u`. Thus their unit Farkas multipliers
prove incompatibility for every u,v>=0. These are exactly `v>=2u+7` and
`v<=u`; the companion first-edge guard forces equality `v=2u+7`.
This is an algebraic control; no interior geometry or seed realization is
claimed for the impossible walk.

**Generalization.** For any supplied closed walk C, intersect every edge's
legal affine interval in one polyhedron P(C). The exact Farkas kernel checks
nonnegative multipliers with strictly negative combined constant and
nonpositive combined u/v coefficients. Such a certificate excludes C for all
nonnegative rational parameters, hence all integer parameters. A missing
certificate is labelled NOT REFUTED; it does not establish feasibility.
The checker prints the complete typed walk, segment choices, guard rows and
rational multipliers, so no parameter compatibility is lost in an SCC projection.

For integer (u,v), each retained interval condition is sufficient for a legal
integer occurrence-index difference: two contiguous integer index intervals
have every integer difference between their extreme differences. Thus the
conjunction gives exact occurrence compatibility for the specified segment
walk. It still does not supply interior-overlap geometry or seed reachability.
Rational feasibility alone may miss integer infeasibility. A separate geometric
or reachability exclusion can therefore remove survivors, but neither may be
silently assumed.

The genuine U/Ubar cycle is a positive control: LAST/RUN and RUN/LAST give
`11+2u+2v>=0` and `1+u-v>=0`, with u=v=0 a shared witness. The checker retains
it. Mutating the closing edge or exceeding the arithmetic budget refuses.

**Remaining gap:** this supplies a checked refutation mechanism for arbitrary
input cycles within stated budgets, not an exhaustive proof for unbounded sums
or lengths. To prove CycleSum-, one still needs a uniform bound/structural
reduction covering all offending cycles, or a parameter-uniform separating
argument for them. A finite larger box or bounded cycle census alone is
insufficient. No parameter is allowed to change during a cycle or a seed path.

## 11. Replay and validation

Run from `kernel/` with the repository's pixi environment:

```sh
pixi run mojo run -I . tests/test_class_d_minus_cycle_reduction.mojo
pixi run mojo run -I . tests/test_class_d_minus_recurrent_support.mojo
pixi run mojo run -I . class_d_minus_recurrent_support.mojo > ../recurrent-mojo.log
pixi run mojo run -I . tests/test_class_d_minus_shared_cycles.mojo
pixi run mojo run -I . class_d_minus_shared_cycles.mojo
```

Then from the repository root:

```sh
python oracles/python/class_d_positive_b_recurrent_support.py --mojo-log recurrent-mojo.log
python -m pytest -q tests/test_class_d_positive_b_recurrent_support.py tests/test_class_d_minus_shared_cycles.py
python tools/make_ledger.py --check
```

The workflow explicitly installs pytest, runs the canonical driver and compares
all classifications against Python, and uploads logs/JSON with `if: always()`.
The literature decision is in `class-d-minus-cycle-literature-gate-2026-10-19.md`.
Validation receipts and toolchain limitations are recorded in
`../evidence/class-d-minus-reduction-repair-2026-10-19/README.md`.

## 12. An unbounded family excluded with the same two guards

| Obligation | Governed status |
| --- | --- |
| Six-edge unbounded family exclusion | Repository-proved: `MinusSixEdgeFamilyExclusion`; exact symbolic identities; human review pending |

The k=2 control generalizes to **every integer k>=2**, without a search cap
in k. Fix the following ordered itinerary (letters x,c,y; FIRST/RUN/LAST).
The outgoing segment pair is attached to its source, and the last edge
returns to row 0.

| Row | Types | Offset (wx,wc,wy) | Sum | Outgoing segments |
| --- | --- | --- | --- | --- |
| 0 | c,c | (-2k,4k-1,1-3k) | -k | FIRST/LAST |
| 1 | c,x | (2k-1,2-4k,3k-2) | k-1 | FIRST/FIRST |
| 2 | c,x | (1-2k,4k-3,2-3k) | -k | FIRST/RUN |
| 3 | c,y | (2k-1,2-4k,3k-2) | k-1 | FIRST/FIRST |
| 4 | c,c | (1-2k,4k-3,2-3k) | -k | RUN/RUN |
| 5 | y,y | (2k-2,2-4k,3k) | k | LAST/FIRST |

**Lemma (this itinerary only).** No member of this family is an actual
occurrence cycle for any one parameter pair a>=2,b>=1.

**Proof.** The x/c child identities hold identically in k on all six edges,
including closure. Put u=a-2,v=b-1. The lower occurrence-difference guard on
edge 0 and upper guard on edge 2 are respectively

\[
 f_0=2k-11-2u+(k-1)v\ge0,\qquad
 f_5=4-2k+u+(1-k)v\ge0.
\]

Adding them with nonnegative multipliers 1,1 gives

\[
 0\le f_0+f_5=-7-u<0,
\]

a contradiction. Every real occurrence must satisfy these guards, so no
geometric or seed-reachability assumption is needed for the exclusion.
For k=2 these are precisely v=2u+7 (edge 0 also has its opposite guard)
and v<=u. For general k the same cancellation persists.

The unbounded even subfamily k=2t, t>=1, sharpens the negative control: every
edge separately has a nonnegative **integer** parameter witness:

| Edge | Its own (u,v) witness |
| --- | --- |
| 0 | (9(t-1),7) |
| 1 | (8(t-1),2) |
| 2 | (4(t-1),0) |
| 3 | (8(t-1),2) |
| 4 | (4t-3,0) |
| 5 | (6(t-1),4) |

Substitution into each edge's two guards gives nonnegative polynomials for
t>=1. The canonical checker verifies this coefficientwise after shifting
k=2+h, and integrality follows on even k. Thus even arbitrarily large sums
can survive a check that reselects parameters on each edge, while the whole
cycle is impossible. These six different valuations must never be assembled
into a common-parameter witness. For odd k edge 0 already has an integer
parity obstruction; we do not claim individual integer feasibility then.

This is also a reusable **guard-pattern exclusion**: any longer walk with one
shared valuation that includes these two rows with the same k is impossible.
Changing the starting vertex, traversing the itinerary repeatedly, or adding
more constraints cannot make the conjunction feasible. This statement does
not permit k or u,v to change between the two rows.

Canonical implementation: `kernel/psc/class_d_minus_cycle_family.mojo` uses
the existing exact `QX`/vendored rational-polynomial kernels, with k as a
formal indeterminate. It reconstructs all 12 guard rows and verifies the
coefficient identities of their sum, rather than evaluating a finite list of
k values. The test compares k=2 to the separately implemented supplied-cycle
checker and refuses a corrupted closing edge. The independent Python oracle
calibrates k=2,3,7,100,100000, which is additional finite evidence only.

Replay, with the repository environment installed, from `kernel/`:

```sh
MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false pixi run mojo run -I . tests/test_class_d_minus_cycle_family.mojo
MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false pixi run mojo run -I . class_d_minus_cycle_family.mojo
```

**Coverage gap.** This removes an unbounded set of higher-sum candidates, but
no argument shows that all higher-sum cycles contain this guard pattern or
belong to this itinerary family. A proof of CycleSum- still requires such a
uniform structural coverage argument, or a different uniform separating
certificate. The independent sums of an arbitrary cycle have not been reduced
to this one-parameter pattern. Neither universal #139 nor PSC is advanced to
a proved status by this lemma.
