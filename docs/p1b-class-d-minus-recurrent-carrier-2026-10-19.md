# Minus positive-b class D: cycle-sum reduction — 2026-10-19

**Status:** 2026-10-20 UTC. section 14 supplies an exact uniform seed-carrier
certificate for the minus residual a>=2,b>=1. It discharges CycleSum- on that
domain and, with the ranked descent, gives scoped boundary hitting. Available
local Mojo and independent rational replay pass. As of 2026-10-21, pinned CI
and the combined class-D integration gate are accepted at a9457d9, merged
as 4996d21; independent human review remains pending. Complete receipts:
`evidence/class-d-integration-accepted-2026-10-21/`. Universal #139/#84 and PSC remain open.

Sections 1–13 preserve the historical conditional reduction and its negative
controls. Unrestricted cyclic-carrier inclusion remains **false**. The new
positive statement concerns actual swap-seed descendants only; it does not
reclassify the formal exceptional cycles as seed reachable.

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

## 4. The scalar premise of the original reduction

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

This motivated the then-open lemma, discharged at the stated scope in §14.

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

## 6. The original sum-lemma gap

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

Common parameters are necessary, but not sufficient: section 13 constructs
real-interior higher-sum formal cycles at one shared parameter pair. The next
proof must additionally use seed reachability.

## 7. Finite calibrations

The independent exact Q(beta) SCC oracle remains useful as a calibration, but
its former RC- interpretation is retired. Finite grids do not prove
CycleSum-.

## 8. Historical non-claims (before the section 14 certificate)

- CycleSum- was open at this stage; §14 now supplies its seed-qualified proof.
- The old RC- premise is false and must not be cited.
- The finite 1,971-state superset is conditional on CycleSum-.
- The plus branch is separate and uses the merged finite chamber decomposition.
- Universal #139, #84 and PSC remain open.


## 9. Diagnostic repair and exact scope correction (2026-10-19)

| Obligation | Governed status |
| --- | --- |
| Minus cycle-sum bound | Repository-proved: `MinusClassDPositiveBCycleSum`, by the uniform seed carrier in §14; pinned CI accepted at a9457d9; human review pending |
| Minus positive-b boundary hitting | Repository-proved: `MinusClassDPositiveBBoundaryHitting`, only a>=2,b>=1; historical conditional assembly now has CycleSum- discharged; pinned CI accepted at a9457d9; human review pending |
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
the **conditional** family implication; the separate §14 seed certificate now discharges its premise.

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

[PROVED] Exact symbolic identity; independent human review pending.

**Proof.** The x/c child identities hold identically in k on all six edges,
including closure. Put u=a-2,v=b-1. The lower occurrence-difference guard on
edge 0 and upper guard on edge 2 are respectively

$$
 f_0=2k-11-2u+(k-1)v\ge0,\qquad
 f_5=4-2k+u+(1-k)v\ge0.
$$

Adding them with nonnegative multipliers 1,1 gives

$$
 0\le f_0+f_5=-7-u<0,
$$

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

## 13. Scalar reconstruction exposes unbounded real-interior formal cycles

**New route correction:** shared-parameter compatibility and real interior
geometry do not imply CycleSum- without seed reachability. There are formal
occurrence two-cycles with arbitrarily large sums that pass both conditions.
Here “real-interior formal” means integral affine child replay and strictly
positive interval-overlap margins. It does not assert occurrence in a legal
tiling, full non-unit realization, or membership in a swap-seed graph.

### 13.1 Reconstruction for an arbitrary closed itinerary

For the edge from row n to row n+1, write delta_x,n and delta_c,n for the
bottom-minus-top proper-prefix counts of x,c. They depend only on the typed
FIRST/RUN/LAST choices. Put eta_n=delta_x,n+delta_c,n. All subscripts below
are cyclic, including periods one and two. The child update gives

$$
 m_{n+1}=2s_n+\eta_n,\qquad x_{n+1}=m_n+\delta_{x,n}.
$$

Therefore every integral closed itinerary has the uniquely forced coordinates

$$
\begin{aligned}
 m_n&=2s_{n-1}+\eta_{n-1},\\
 x_n&=2s_{n-2}+\eta_{n-2}+\delta_{x,n-1},\\
 c_n&=m_n-x_n,\qquad y_n=s_n-m_n.
\end{aligned}
$$

Conversely these formulas satisfy the x/c child equations for every cyclic
integer word s and every compatible typed segment itinerary. There is no
parity condition or choice of an additional offset coordinate. The remaining
y equation is exactly the occurrence-index-difference equation. For top and
bottom occurrence indices i_n,j_n it becomes

$$
\begin{aligned}
s_{n+1}={}&(2a+b+6)s_n+(2a+4)s_{n-1}-2s_{n-2}\\
 &+(a+2)\eta_{n-1}-\eta_{n-2}-\delta_{x,n-1}+(j_n-i_n).
\end{aligned}
$$

All edges retain ONE a,b. Legal index intervals give the same two guards as
`edge_forms`. These are necessary for any seed-reachable cycle, but geometry
and a seed path remain separate obligations. This exact scalar reduction does
not bound the period or scalar alphabet.

### 13.2 A compatible higher-sum two-cycle

The itinerary LAST/RUN then RUN/LAST on types (y,c),(c,y) has eta=delta_x=0.
Choosing the scalar word (-k,k) reconstructs

$$
 U_k=(y,c,-2k,4k,-3k),\qquad
 \overline U_k=(c,y,2k,-4k,3k).
$$

For the forward edge the required bottom-minus-top index difference is
k(b+1). Its upper legal bound is q-(r+1)=a+1. Thus the two-cycle guards are
compatible whenever k(b+1)<=a+1. In particular, take

$$
 a=2k-1,\quad b=1,\quad k\ge2.
$$

Then p=6k+3, q=6k+4, r=4k+3. The actual forward indices are (r+1,q)=(4k+4,6k+4),
and the reverse indices are exchanged. Both are legal occurrences for the
same substitution. Direct multiplication gives

$$
 M(-2k,4k,-3k)=(2k,-4k,k),
$$

and the prefix difference is (0,0,2k), giving the required mirror. Negating
and reversing proves the closing edge. The sums are -k and k.

### 13.3 Uniform strict interiority on this ray

Normalize ell_y=1, set d=beta-r, and use the already certified minus Perron
bounds 2<d<3 and beta>r+2. Then ell_c=d/2, ell_x=d/2-1/beta. The Perron
identities give beta(d-2)=2a+4-2/beta, so the displacement of U_k on this ray is

$$
 t=k(d-3+2/\beta)=-\frac{k(d-1+2/\beta)}{\beta}.
$$

It is negative. Since beta>4k+5 and d<3,

$$
 2k(d-1+2/\beta)<4k+4k/\beta<4k+1<\beta,
$$

and hence -1/2<t<0. Both margins ell_c+t and ell_y-t are strictly positive;
mirroring exchanges them. Every member is PIP by the existing exact
symbolic PIP certificate, with k>=2 checked without an increased threshold.

| Obligation | Governed status |
| --- | --- |
| Unbounded real-interior formal two-cycle ray | Repository-proved: `MinusHighSumFormalCycleRay`; k>=2, a=2k-1,b=1; this lemma asserts no seed reachability; §14 excludes it uniformly; human review pending |

The canonical module `kernel/psc/class_d_minus_high_sum_cycles.mojo` checks
the incidence/prefix identities as exact polynomials in k, the declared
endpoint types, both strict Perron margins and -1/2<t<0. The executable fails
if any sign proof raises the k threshold above 2. No finite sampling supplies
the unbounded quantifier.

### 13.4 Seed qualification and the then-remaining task

Canonical Mojo and independent Q(beta) Python replay at k=2,3,8 use complete
swap-seed graphs with 139 states each; neither member of these three pairs
is seed reachable. This is a finite nonmembership observation, not a proof
of nonreachability for every k. Graph caps refuse, and any found membership
emits an actual seed path and closed-cycle counterexample. The recurrent
classifier continues to call U_k with k>=2 unexplained; it is not whitelisted.

The simplest negative control is a=3,b=1,k=2:

$$
 (y,c,-4,8,-6)\xrightarrow{(12,16)}(c,y,4,-8,6)
 \xrightarrow{(16,12)}(y,c,-4,8,-6).
$$

**Stop:** do not seek a certificate excluding every higher-sum formal cycle
using only common parameters, occurrence legality and real interiority. Such
a certificate is false already for this two-cycle, and fails at unbounded
sums along the ray.

**Redirect:** prove a seed-preserved constraint (or a predecessor/address
obstruction) that excludes these compatible formal cycles from all actual
swap-seed descendants, and then control the remaining scalar itineraries.
An induction needs complete occurrence-child coverage, not just one selected
productive path. Until such a constraint is established, CycleSum- stays
open. The 1,971-state classification and its four exceptional candidates
remain conditional on |s|<=1; they never claimed to classify the higher-sum
states constructed here. No unconditional minus-BH, universal #139/#84 or
PSC conclusion follows.


## 14. Uniform seed-carrier closure (2026-10-20 UTC)

| Obligation | Governed status |
| --- | --- |
| Uniform minus seed carrier | Repository-proved: `MinusClassDSeedCarrierClosure`; a>=2,b>=1, actual swap seeds and complete occurrence closure; pinned CI accepted at a9457d9; human review pending |

### 14.1 Statement and quantifiers

Fix **one** integer pair a>=2,b>=1 for the entire seed path. Let C be the
sealed 145 typed integral labels in `class_d_minus_spine_data.mojo`. Every
interior swap-seed overlap is in C. Every interior occurrence child of an
interior nonterminal member of C is in C. Hence every vertex of the exact
swap-seed graph is in C, and every such vertex has |wx+wc+wy|<=1.

A terminal state requires **equal letters and zero displacement**. The graph
stops at coincidences. Distinct-letter zero states are expanded normally.
Expanding a genuine coincidence further only produces coincidences, which
also have sum zero. Thus stopping at them does not hide a high-sum cycle.
The upper cover is conditional on source realness: its labels need not all
be real simultaneously. This avoids the failed fixed-real-subcover route.

### 14.2 Exact correlated Perron region

Put d=beta-r, X=d-2 and Y=10/beta. The existing certified root box gives
0<X<1 and 0<Y<1 throughout the declared domain. Normalized tile lengths are

$$
 (\ell_x,\ell_c,\ell_y)=(1+X/2-Y/10,\ 1+X/2,\ 1).
$$

The new certificate checks the positive left eigenvector
(beta*d-2,beta*d,2beta) modulo the exact incidence characteristic polynomial,
so these lengths are bound to the actual substitution, not an auxiliary
geometry. The characteristic identity is

$$
 \beta^3-(r+2)\beta^2-(2a+4)\beta+2=0.
$$

It gives the two checked polynomial identities

$$
 \beta X=2a+4-2/\beta,\qquad
 \beta(1-X)=b+2+X+2/\beta.
$$

Since beta>10 and a>=2, the first right side is greater than 8-1/5>7.
Since b>=1 and X>0, the second is greater than 3. Therefore

$$
 10X>7Y,\qquad 10-10X>3Y.
$$

These correlations are essential. Direct norm-sign search on the new margins
refused on a sign-changing auxiliary polynomial; the preserved refusal is
not a mathematical counterexample. The polynomial identities plus the already
certified root box establish the inequalities without a quadrant cut.

For w=(x,c,y), write s=x+c+y and m=x+c. Its displacement is
s+mX/2-xY/10. Both interior margins, multiplied by 20, are integer-affine
forms in X,Y. The same X,Y is used for source and child. They are **strictly**
positive; boundary contact is not accepted as interior.

### 14.3 All seeds and all children, without assuming CycleSum

The three canonically oriented swap pairs a<b each give four candidate overlaps. Their
types are (a,b), (a,a), (b,b), (b,a), with offsets 0, e_b, -e_a, e_b-e_a.
Nine are in C. The other three are (x,x,e_c), (y,y,-e_x), (y,y,-e_c).
Their interior margins cannot be positive in the correlated region. Thus
all real seeds are included, without assuming any reachability conclusion.
Reversing both rows mirrors every offset and child occurrence. That reverses
the sign of s, so the same absolute-sum conclusion holds for reverse-oriented
swap graphs, even where their mirrored labels differ from C.

For each nonterminal carrier state, partition each image into FIRST, RUN and
LAST. All nine segment pairs are checked. For each pair, its proper-prefix
x/c differences delta_x,delta_c fix

$$
 x'=x+c+\delta_x,\qquad c'=x+c+2y+\delta_c.
$$

Set m'=x'+c'. Because every normalized tile length is less than 3/2, any
interior child, with s'=x'+c'+y', necessarily satisfies

$$
 |s'|<3/2+|m'|/2+|x'|/10.
$$

Consequently enumerating every integer s' from -B through B, where
B=2+|m'|+|x'|, covers **all** possible children. This is a derived geometric
bound, not the desired |s'|<=1 premise. Every candidate has
w'=(x',c',s'-m') and the segment's child types.

A candidate is accepted only if it is already in C. Otherwise the checker
must prove one of two impossibilities:

1. Source and child cannot both be interior in the correlated Perron region.
2. Their required index difference cannot occur for any a>=2,b>=1 in the
   segment intervals. The exact two occurrence guards use u=a-2,v=b-1>=0.

Each exclusion is universal on an outer region. Combining them does not
choose new parameters on successive edges: the conclusion holds for each
fixed original parameter pair, and induction preserves that pair.

For strict geometry f_i(X,Y)>0, choose epsilon>0 below every f_i. The
nonnegative variables (X/epsilon,Y/epsilon,1/epsilon) then satisfy the closed
system -1+a_i*z_1+b_i*z_2+c_i*z_3>=0. A checked exact Farkas certificate
refutes it. This treats zero margins correctly without introducing an
arbitrary positive numerical tolerance. Failure to find a certificate leaves
an unresolved obligation and aborts the positive certificate.

The exhaustive counts agree between canonical Mojo Farkas arithmetic and an
independent Python Fraction vertex method:

| Check | Count |
| --- | ---: |
| Carrier labels | 145 |
| Seed candidates in carrier / excluded as nonreal | 9 / 3 |
| Equal-letter zero terminal labels | 2 |
| Nonterminal source / segment pairs | 1,287 |
| All bounded child candidates | 12,255 |
| Candidates already in carrier | 1,218 |
| Excluded by strict geometry | 9,034 |
| Excluded by occurrence guards | 2,003 |
| Unresolved obligations | 0 |

### 14.4 Consequences and retained negative controls

Induction from the seeds proves carrier inclusion **for seed descendants**.
Every carrier label has |s|<=1, so CycleSum- follows, including all cyclic
vertices. This is stronger than the recurrence-only premise. The selected
ranked exits of #287/#288 give boundary hitting directly; alternatively the
historical conditional 1,971-state reduction now has its premise discharged.
The maximum selected descent depth from these seed labels is four.

U/Ubar/V/Vbar and the unbounded U_k formal cycles remain genuine interior
formal cycles outside C. The seed-closure proof now excludes them uniformly
from these swap-seed graphs. It does not invalidate their occurrence cycles
or exceptional exits, and the diagnostic continues to recognize productive
exceptions rather than reverting to the retired unrestricted RC- assertion.

The independent coarse-box probe leaves 148 child obligations at 19 distinct
outside labels and one seed obligation. These are relaxed-geometry witnesses,
**not** actual counterexamples. The regression preserves a source/child pair
with a strict coarse-box witness and verifies its exclusion after adding the
correlations. Removing the real child target (y,y,0) forces canonical refusal.
The earlier shared-parameter impossible six-edge family and feasible high-sum
formal ray remain unchanged negative controls.

### 14.5 Replay, validation and scope boundary

Canonical implementation: `kernel/psc/class_d_minus_seed_cover.mojo`;
driver and regression have the same basename under `kernel/` and
`kernel/tests/`. Independent calibration:
`oracles/python/class_d_minus_seed_cover.py`. Evidence and commands:
`evidence/class-d-minus-seed-cover-2026-10-20/README.md`.

This is an exact finite certificate for an unbounded parameter domain, with
no sampled-parameter bound in the proof. The five complete graph samples are
retained only as exploratory provenance. Local available Mojo replay and
independent rational calibration establish the recorded certificate; they
are not labelled pinned-nightly CI or independent human review. Those
validation gates remain pending. The updated TLA+ ledger establishes only the
scoped seed-carrier, CycleSum- and minus residual BH nodes; universal aligned
coincidence, universal #139, the two-obstruction completion and PSC remain
unestablished in the open model. No full non-unit tiling realization or
universal spectrum theorem is imported from this seed certificate.

### 14.6 Subsequent full CI acceptance (2026-10-21)

The local-only statements in §14.5 describe the original evidence event.
All 64 checks at a9457d9 have since succeeded; main merge 4996d21 and the
GitHub-tested PR merge have the same accepted source tree. Full locked Pixi,
uniform carrier and strip replays, ranked descent, independent calibration,
complete plus aggregate and scoped assembly now supply integration acceptance.
The ledger establishes scoped determinant-two class D without an assumption,
while every universal firewall in §14.5 remains. Human review is still pending.
See `class-d-assembly-audit-2026-10-21.md` and
`evidence/class-d-integration-accepted-2026-10-21/`.
