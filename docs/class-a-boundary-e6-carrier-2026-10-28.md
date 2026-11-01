# E6: complete stars, uniform image tails and every-first-choice walks

## Conclusion and dependency scope

Throughout the class-A minus boundary, E6=(x,x,0,1,0) and its actual
reversal have **2d-1 indexed children per orientation**. Their outgoing
union consists of the **same 16 labels in every member**. Each image label
has a uniform typed tail of at most eight edges, so every actual first choice
extends to a selected full walk of at most nine. The nine-edge output is
attained at the sole n=3 member and is not claimed shortest. E6's inherited
two-edge source exit is retained.

This increment is based on 8291fc59144c6445013d493de516b8990ffbdeac,
#379's branch after the observed stack merge of #381 at
0dde1a00e182023891bab697e5e8156e6f3577e3. That merge was not into main,
and its fresh hosted workflows were queued/pending at inspection. Do not
infer exact-head acceptance from merge status. The isolated checkout preserves
all concurrent packet work. The [stop/go](class-a-boundary-e6-stopgo-2026-10-28.md)
reuses the three-primary-source actual/every-overlap and non-unit review.
Independent human review remains pending validation debt.

## Hypotheses and full labels

Integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d=2n+t+2, N=n-1.
The exact ordered words are x y^A x, c y^n x, x y^N c. Retain every integer
bottom-minus-top Parikh coordinate and actual zero-based occurrence index.
Only strict physical intersection counts. Reversal swaps types and indices
and negates all coordinates. There is no tile-length independence premise.

Normalize Ly=1 and set h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, w=alpha+2h, a=Lx=2+rho, b=Lc=1+h.
Inherited exact bounds give 0<h<1/5, 0<alpha<1, 0<zeta<rho<1,
and 0<w<1. The cubic and positive-denominator reductions remain exact.

| Name | Full label | Physical shift | Incidence image | Inflated shift G |
| --- | --- | --- | --- | --- |
| E6 | (x,x,0,1,0) | b | (1,1,n) | beta+1=n+3+alpha |
| J6 | (x,y,1,1,-4) | alpha-1 | (-1,-3,3-k) | -k-2-w |
| K6 | (x,y,1,1,-3) | alpha | (0,-2,t+5) | t+3-2h |
| L6 | (x,y,1,1,-2) | 1+alpha | (1,-1,d+2) | d+3+zeta |

Only E6 receives new complete stars. J6/K6/L6 receive uniform selected exits,
not companion star or every-companion-child claims. All displayed sources
are interior: E6 has upper margin a-b=1+zeta; J6 has lower margin alpha>0;
K6 is between 0 and 1; L6 has upper margin 1-h>0.
E6's B5 FIRST/LAST ancestry was established only at n=3. The standalone
E6 statement and its source exit hold on the full cone without extending that
ancestry claim. E7=(x,x,0,1,1) remains governed by its previous n=4-only tails.

## Complete nine-kind star and every excluded kind

For either x parent the FIRST prefix is zero, RUN i is (1,0,i-1), and
LAST A+1 is (1,0,A), with physical prefixes 0, a+i-1, a+A.
Demand -L(bottom child)<G+prefix_bottom-prefix_top<L(top child).
The complete table for base E6 is:

| Kind | All actual accepted pairs |
| --- | --- |
| FIRST/FIRST | none |
| FIRST/RUN | none |
| FIRST/LAST | none |
| RUN/FIRST | i=n+2..n+4, j=0 |
| RUN/RUN | i-j=n+3,n+4; 1<=j<=A-delta |
| RUN/LAST | none |
| LAST/FIRST | none |
| LAST/RUN | i=A+1, j=d-3..d-1 |
| LAST/LAST | none |

Transpose actual indices and reverse every full typed target for R(E6).
All run bounds are true on the cone: d>=5 ensures n+4<=A, d-3>=2,
and both RR strips are nonempty. No clipped phantom or last-as-run index occurs.

* FF exceeds a since G-a=n+1+h>0. FR and FL increase the shift.
* RF shift is n+2+h-i. Its upper bound 1 forces i>=n+2;
  its lower bound -a gives i<n+4+alpha, hence i<=n+4.
* RR shift is n+3+alpha+j-i. Since 0<alpha<1, strict y/y overlap
  leaves exactly delta=n+3,n+4.
* RL is at least G+1>1 and cannot overlap its top y.
* LF shift is b-d. Its lower margin is a+b-d=3+alpha-d<0.
* LR shift is n+2+alpha+j-A. The lower bound -1 gives
  j>A-n-3-alpha, hence j>=d-3. The upper bound a gives
  j<d-h, hence j<=d-1.
* LL has shift G>a and is disjoint.

Counts are 3+(d-3)+(d-4)+3=2d-1. Production synthesis streams these
O(d) true strips/endpoints. The quadratic literal-word rectangle is used only
for independent complete-implementation regression.

## Exact image and constant memberwise attainment

Use M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y), then add actual bottom prefix
minus top prefix. Canonical Q[t,k] coefficient identities check all nine kinds
on affine index bases 1,2 and actual last prefixes. The actual child-type guard
is checked separately from offset equality. Clearing beta>0 gives the exact
identity beta*G=beta^2+beta. Full field transport is reduced modulo the cubic.

| Kind | Complete base typed targets |
| --- | --- |
| RF | (y,x,0,1,r), r=-3,-2,-1, i.e. R(H3), R(H2), R(H1) |
| RR | (y,y,1,1,r), r=-4,-3, i.e. R(P1), R(P0) |
| LR | J6, K6, L6 |

The eight labels and eight disjoint reversals are distinct as full typed
Parikh triples. Each RF/LR label has a true endpoint in every member.
The two RR strip lengths d-3 and d-4 are respectively at least two and one,
so both RR labels also occur in every member. This proves the constant
16-label image uniformly. Archived actual witnesses and both finite replays
independently check this conclusion per member; finite sampling supplies no
universal quantifier.

## Source and companion exits

| Source | Uniform selected actual path | Length |
| --- | --- | --- |
| E6 | inherited (n+2,0)->R(H1), (2,1)->C | 2 |
| J6 | (0,k+1)->D4, then its inherited suffix | 8 at n=3, 4 otherwise |
| K6 | (t+3,0)->B5, then its two-edge suffix | 3 |
| L6 | (d+2,0)->T, (1,2)->C | 2 |

D4=(x,y,0,-3,3), T=(y,x,0,-1,1), C=(y,y,0,0,0).
The symbolic prefix kernel proves k+1<=N, t+3<=A and d+2<=A and binds
all three coordinates and actual child types in every orientation.
The new targets have physical shifts -3h, -1-alpha-h and -h respectively;
the inherited exact bounds make each strict.

D4's seven-edge n=3 suffix is retained exactly, through
(x,y,1,0,-2), (x,x,0,-2,4) and J=(y,x,1,2,-4)'s existing path. Its shorter n>=4
transition at bottom ordinal 3 cannot be substituted at n=3, where ordinal
3 is the actual LAST c. Therefore J6 has a valid uniform bound eight,
with the stated sharper length four on n>=4. No shortest-path claim is made.

All RF labels inherit H1/H2/H3 suffixes of lengths at most 1/2/5;
RR labels inherit the P0/P1 bounds at most five; LR labels have the new
bounds above. Every actual first edge therefore has a typed tail <=8 and
an indexed full walk <=9. Every supplied walk is checked against its entire
intended sequence of types, offsets and indices. The maximum produced length
nine is attained by E6's actual LR(A+1,d-3) first edge at k=t=0.
The theorem selects a suffix after every first choice; it does not assert
that every later continuation terminates.

## Exact cycles, escapes and coverage bookkeeping

At k=t=0 there is the genuine three-cycle
E6(9,3)->K6(3,0)->B5(0,9)->E6, with its full actual reversal.
Every source also has an exit; this is not a closed obstruction. It rules
out a strictly decreasing rank on every edge of a carrier containing it.

Uniformly, E6(A+1,d-2)->K6 escapes the historical S41 candidate, and
K6(t+3,0)->B5 escapes the 16-label image. Their source and target geometry
and full prefix transports are certified, so neither candidate is closed.

Relative specifically to the #381/8291fc59 baseline, S41's complete-star
coverage rises from 29 to 31 including C: 30 nonterminal stars, ten gaps.
Its 33 uniform exits including C are unchanged. The previous B5 image gains
two complete-star registrations, from 18 to 20 among its 24 labels. The new
E6 image has ten registered complete stars and all sixteen registered uniform
exits. New J6/K6/L6 exits do not imply new complete stars. No independent R5
sibling classification is silently counted. All 81 candidate/image/previous-
image rows are compared individually across native and independent interfaces.

## Evidence and deterministic replay

Canonical kernel, driver and test are the matching
`kernel/psc/class_a_boundary_e6_children.mojo`,
`kernel/class_a_boundary_e6_children.mojo` and
`kernel/tests/test_class_a_boundary_e6_children.mojo`.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_e6_children.mojo
pixi run --locked mojo run -I . class_a_boundary_e6_children.mojo
```

Locked Mojo 1.1.0.dev2026090805: 56 members (112 complete-star source cells),
82,096 literal pairs, 3,136 accepted, 1,240 selected source/companion path edges
and 12,664 all-child walk edges. Independent literal-word/integer-polynomial/
Fraction oracle: 117 members (234 source cells, 936 selected-path cells),
297,648 pairs, 8,658 accepted, 2,582 selected path edges and 34,766 all-child
walk edges. Both check all sixteen labels in each member, every actual reversed
edge and attained maximum walk length nine. The independent 512-refinement
sign budget refuses inconclusively on exhaustion.

```sh
python -m pytest -q tests/test_class_a_boundary_e6_children.py
python oracles/python/class_a_boundary_e6_children.py > /tmp/e6.json
cmp /tmp/e6.json evidence/class-a-boundary-e6-2026-10-28/probe.json
```

Negative controls reject the legal same-typed disjoint RF(n+1,0) and LR(A+1,d)
neighbours, wrong interior offsets already in the image, a false short n=3 D4
target, unequal-type zero terminals, invalid IDs/parameters/ordinals, corrupt
symbolic identities, duplicate/incomplete stars, altered/truncated walks and
missing/duplicate/corrupted registry rows. Unsupported companion-star requests
are refused; E7's scoped contract is not promoted.

Receipts, source digests, dependency snapshot and replay instructions are in
`evidence/class-a-boundary-e6-2026-10-28/`; the dedicated hosted replay is
`.github/workflows/class-a-boundary-e6.yml`. Scoped native/Python, integrity,
provenance and all 18 existing TLA expected outcomes are recorded separately.
Local Lean fails before compilation and earns no proof pass. No full-suite or
fresh hosted acceptance is claimed. Predecessor and exact-head gates remain
required before integration; independent human review remains pending debt.

Next full-star gap E7=(x,x,0,1,1) still has only the inherited n=4-scoped
exit contract; its standalone complete star and uniform exit remain open.
No companion all-child result, closed carrier, all-edge descent, all-source
strict-zipper, plus/non-unit realization or universal BH/#139, A1-prime, G1 or
PSC promotion. Preserve 124 governed claims, 34 named Lean proofs and
325 source openings without formal-source changes.
