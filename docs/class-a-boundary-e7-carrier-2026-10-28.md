# E7: complete half-chamber stars and a uniform source exit

## Result and predecessor scope

For every minus class-A boundary member, E7=(x,x,0,1,1) and its actual
reversal have **max(1,2t-1)** strict indexed children each. The outgoing
union over the parameter chamber has **32 labels**, with a genuine exact
alpha=1/2 split in its occurrence tables. E7 has a selected typed exit of
length **three at t=0,1 and five at t>=2**. The n=4-only predecessor tails
are extended without changing their actual occurrence sequences.

Only t<=1 is given an all-direct-child productivity result here: those
stars are singletons. For all t, source productivity does not supply a tail
for every child. Six labels in the new image have registered complete stars;
eight have registered uniform exits. Twenty-four image labels still lack
registered uniform exit interfaces, including labels whose source overlap
is itself conditional on the half-chamber.

Base: #382 at 6bef25b0a24820996989f652d53f1ae5d24039c2, with its fresh
hosted workflows still queued at inspection. Keep predecessor and exact-head
acceptance separate from source proofs and merge status. The isolated checkout
preserves independent packet work. The [stop/go](class-a-boundary-e7-stopgo-2026-10-28.md)
reuses the three-primary-source actual/every-overlap and non-unit boundaries.
Independent human review remains pending validation debt.

## Hypotheses and exact separator

Integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d=2n+t+2, N=n-1.
The exact ordered words are x y^A x, c y^n x, x y^N c. Offsets retain
all bottom-minus-top Parikh coordinates; indices are zero-based actual
occurrences. Reversal swaps types and indices and negates all coordinates.
Use strict -L(bottom child)<shift<L(top child), with actual child lengths.
No tile-length independence premise is used.

Normalize Ly=1, h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, v=alpha+h, a=Lx=2+rho, b=Lc=1+h.
Inherited exact bounds give 0<h<1/5, 0<alpha<1, 0<zeta<rho<1 and 0<v<1.
E7 has physical shift b+1=2+h<a, with upper margin zeta>0.
Its incidence image is (2,2,2n-1), with inflated shift G=2beta+1=2n+5+2alpha.

Reuse the H3 certificate, including the two small diagonal exceptions:

    8 f(n+5/2)=4k^2+20k-4t^2-24t+5.

There is no equality. Put e=1 exactly when alpha>1/2, equivalently
`t>k or (t==k and k>=2)`. Thus e<2alpha<e+1. In particular (0,0)
and (1,1) are low, while all later diagonal members are high.
Neither a finite fit nor an approximate sign decides this branch.

## All nine occurrence kinds

For each x parent, FIRST has prefix 0, RUN i has (1,0,i-1), and LAST A+1
has (1,0,A), with physical prefixes 0, a+i-1, a+A.
The complete base E7 table is:

| Kind | All actual accepted pairs |
| --- | --- |
| FIRST/FIRST | none |
| FIRST/RUN | none |
| FIRST/LAST | none |
| RUN/FIRST | i=2n+4..min(A,2n+6+e), j=0 |
| RUN/RUN | i-j=2n+5+e,2n+6+e; 1<=j<=A-delta |
| RUN/LAST | none |
| LAST/FIRST | (A+1,0) iff t<=3+e |
| LAST/RUN | i=A+1, j=max(1,t-3-e)..t-1 |
| LAST/LAST | none |

Transpose actual indices and reverse full typed targets for R(E7). Every empty
strip contributes no edge; actual last occurrences are never invented runs.

* FF exceeds a, since G-a=2n+3+v>0; FR and FL increase it.
* RF has shift 2n+4+v-i. The upper guard 1 gives i>=2n+4;
  the lower guard -a gives i<2n+6+2alpha, hence i<=2n+6+e.
* RR has shift 2n+5+2alpha+j-i, giving exactly the two displayed diagonals.
* RL is at least G+1>1, exceeding its top y length.
* LF has shift 1-t+v. Its upper guard is automatic because
  a-(1+v)=1-2h>0. The lower margin is 3-t+2alpha, positive exactly
  when t<=3+e.
* LR has shift 2-t+2alpha+j. Its lower bound -1 gives
  j>t-3-2alpha, hence j>=t-3-e; its upper bound a gives
  j<t-v, hence j<=t-1. Clip to genuine runs beginning at 1.
* LL has shift G>a and is disjoint.

For t>=1 put m=t-1, Q=3+e. RF and LR each contribute min(m,Q),
RR contributes max(0,m-Q+1)+max(0,m-Q), and LF contributes one iff m<Q.
Splitting m<Q versus m>=Q gives 2m+1=2t-1. At t=0 the sole LF edge gives
one. This proves max(1,2t-1), independently of e, without discarding the
half-chamber-dependent actual pairs. Production synthesis streams O(t+1)
true strips and endpoints; exhaustive literal rectangles are regression checks.

## Exact transport and chamber-wide image

Use M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y), then add actual bottom prefix minus
top prefix. Canonical coefficientwise identities check all nine kinds on
affine index bases 1,2 and actual last prefixes. The actual child-type check
is independent of offset equality. Positive denominator clearing gives
beta*G=2beta^2+beta; the exact field transport is reduced modulo the cubic.

| Kind | Complete base typed targets |
| --- | --- |
| RF | (y,x,1,2,r), r=-7..-4 |
| RR | (y,y,2,2,r), r=-8..-6 |
| LF | (x,x,1,2,-t-3), t=0..3+e, hence r=-7..-3 |
| LR | (x,y,2,2,r), r=-8..-5 |

Sixteen base labels and sixteen disjoint reversals give 32 labels. Exact
symbolic cancellation and the guards prove containment; archived actual
k,t,i,j witnesses attain every label. This is a chamber-wide union, not a
constant memberwise image or a uniform physical carrier.

For example (y,x,1,2,-7), (y,y,2,2,-8), (x,x,1,2,-7), and
(x,y,2,2,-8) require the high half-chamber, while (y,y,2,2,-6) requires
the low half-chamber. At t=4, high (k,t)=(4,4) has the actual LF target
(x,x,1,2,-7); low (5,4) instead has an RR target (y,y,2,2,-6).
Both stars have seven occurrences, so matching counts cannot identify their
edges. The opposite-chamber versions of those target labels are disjoint.
No uniform source-exit claim is inferred from their union membership.

## Uniform E7 source exit and existing aliases

Use local U7=(x,x,1,2,-3) and V7=(x,x,1,2,-4) for the two low-t targets.
They are already established families: U7 is reversed D0 and V7 is the
existing Dxx family. Their full labels, existing interface IDs and certificates
are retained. U7 has its inherited uniform two-edge exit; V7 has an inherited
uniform four-edge exit. A new two-edge V7 shortcut applies at n>=4.
No new complete star or uniform exit is claimed for an existing alias.

| Source and guard | Actual selected path | Length |
| --- | --- | --- |
| E7, t=0 | (A+1,0)->U7, inherited U7 suffix | 3 |
| E7, t=1 | (A+1,0)->V7, its n>=4 shortcut | 3 |
| E7, t>=2 | (2n+4,0)->J=(y,x,1,2,-4), inherited J suffix | 5 |
| U7, all k,t | inherited (d+3,0)->T, (1,2)->C | 2 |
| V7, n=3 | existing Dxx four-edge path | 4 |
| V7, n>=4 | (t+5,1)->R(B2), (1,3)->C | 2 |

T=(y,x,0,-1,1), B2=(y,y,0,2,-2), C=(y,y,0,0,0).
U7 has image (1,-1,d+3), V7 has image (0,-2,t+6). Their physical source
shifts are 1+v and v, respectively, strict throughout the full parameter cone.
Full-label alias assertions prevent replacing them by merely equal field shifts.

At t=0 the proposed RF ordinal 2n+4 is outside the word. At t=1 it equals
A+1, the actual LAST x, whose target is x/x V7, not y/x J, despite identical
offsets. For t>=2, legality of RF(2n+4,0) is certified on t=t'+2,
n=n'+2, d=d'+4; its target shift v is strictly between zero and one.
The t=0,1 LF identities are certified on their full k cones.

The V7 RR(t+5,1) transition to R(B2) is always real, but R(B2)'s nominal
(1,3) y/y terminal is false at n=3, where bottom ordinal 3 is LAST c.
The implementation reuses the established four-edge Dxx path there. An
initial five-edge B2 construction was unnecessary and is not a new result.
At the two n=4 members, the new E7 paths agree exactly with B5's archived
finite endpoint constructors; the archived n=4-only interface is unchanged.

At t<=1 each complete E7 star is a singleton, and its sole first edge is
the selected LF above. Thus every direct child is productive on that strip.
For t>=2, selected source exits prove only that those selected children are
productive; no all-direct-child statement is supplied for all t.

## Coverage, restored B5 uniformity and escapes

Relative to #382, S41 complete-star coverage rises from 31 to 33 including C:
32 nonterminal stars and eight gaps. Uniform exits rise 33->35 including C,
leaving six gaps. The new E7 image has six registered stars (existing J,
Dxx and H5 orientations) and eight registered uniform exits (J/F4, D0/U7,
Dxx/V7 and H5 orientations). J/F4's different star and exit aliases remain
separate. H5 and J stars are reused certificates, not newly classified families.

The earlier B5 image now has 22 registered stars and **24 uniform exits out
of 24 labels**. A new uniform B5-tail dispatcher intercepts E7 and uses its
full parameter exit, while retaining all other inherited B5 tails. Thus B5's
previous two n=4-only target labels now receive uniform source exits. All 24
image labels have selected tails <=7 over the full cone; B5's existing <=8
actual first-choice bound remains valid. Neither the old finite constructors
nor their historical receipts are rewritten.

All 32 E7 outgoing union labels lie outside S41 by c-coordinate +/-2.
The 32-label image is also not closed: its J source has actual RF(t+2,0)
child K=(y,x,-1,-2,5), outside the image. J has its inherited K suffix to C,
so this escape is not a closed obstruction. All 97 candidate/image/B5-image
rows are compared individually across native and independent interfaces.

## Replay, controls and remaining gap

Canonical kernel, driver and test are the matching
`kernel/psc/class_a_boundary_e7_children.mojo`,
`kernel/class_a_boundary_e7_children.mojo` and
`kernel/tests/test_class_a_boundary_e7_children.mojo`.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_e7_children.mojo
pixi run --locked mojo run -I . class_a_boundary_e7_children.mojo
```

Locked Mojo 1.1.0.dev2026090805 checks 56 members, 112 source cells,
82,096 literal pairs, 592 accepted, 948 source/companion path edges,
1,138 registered E7-image tail edges and 4,704 uniform B5-image tail edges.
Independent literal-word/integer-polynomial/Fraction replay checks 117 members,
234 source cells, 702 selected-path cells, 297,648 pairs, 1,690 accepted,
2,006 source/companion path edges, 2,362 registered E7-image tail edges and
9,880 uniform B5-image tail edges. Both attain all 32 union labels and
verify every actual reversed accepted edge. The independent 512-refinement
sign budget refuses inconclusively on exhaustion.

```sh
python -m pytest -q tests/test_class_a_boundary_e7_children.py
python oracles/python/class_a_boundary_e7_children.py > /tmp/e7.json
cmp /tmp/e7.json evidence/class-a-boundary-e7-2026-10-28/probe.json
```

Controls retain the two small diagonal half-chamber exceptions, equal-count
but different t=4 stars, opposite-chamber disjoint labels, true t=1 LAST x,
false n=3 B2 terminal types, existing D0/Dxx aliases, wrong interior image
targets, corrupt polynomial identities, unknown-tail refusal, malformed stars
and paths, unequal-type zero terminals, bad parameters/ordinals/orientations
and omitted/duplicate/corrupted registry rows.

Receipts, source digests, dependency snapshot and replay instructions are in
`evidence/class-a-boundary-e7-2026-10-28/`; hosted replay is in the dedicated
`.github/workflows/class-a-boundary-e7.yml`. Scoped native/Python, integrity,
provenance and all 18 existing TLA expected outcomes are recorded separately.
Local Lean fails before compilation and earns no pass. No full-suite or fresh
hosted acceptance is claimed. Predecessor and exact-head gates remain required
before integration; independent human review stays pending validation debt.

A concrete next complete-star gap is the existing D0 family, here
U7=(x,x,1,2,-3), with its already certified two-edge exit. Its E7 ancestry is
t=0-only, not uniform ancestry. V7/Dxx and J/H5 stars are already classified.
No all-t all-E7-child result, closed carrier, all-edge rank, all-source
strict-zipper, plus/non-unit realization, universal BH/#139, A1-prime, G1 or
PSC promotion. Preserve 124 governed claims, 34 named Lean proofs and
325 source openings without formal-source changes.
