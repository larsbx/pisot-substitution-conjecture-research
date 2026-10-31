# Class A: bounded negative pumping and four typed exits

This continues #436's local productivity proof. It supplies a selected
coincidence path for the complete signed unit cell

\[
 P_p=(x,y,p,3p+1,-6p),\qquad K|p|\le n-1,
 \quad k,t\ge0,\quad K=k+1,\ n=k+t+3,\ d=k+2t+5.
\]

Write A=n+d and D=floor((n-1)/K). Each such P_p and its genuine reversal
has a path to C=(y,y,0,0,0) of at most **4D+6 edges**. The negative
phase has a bounded pump, rather than a decreasing absolute index.
This is a uniform local result with a parameter-dependent bound. It is
not a proof that all X descendants enter the cell, nor an all-child
invariant. The [stop/go record](class-a-signed-strip-stopgo-2026-10-31.md)
precedes the new diagnostic.

## Exact model and inherited premises

Use the actual ordered minus-class-A substitution

\[
 x\mapsto xy^Ax,\qquad c\mapsto cy^nx,\qquad
 y\mapsto xy^{n-1}c.
\]

Full labels store bottom-minus-top Parikh offsets in the order (x,c,y).
An indexed child is M delta + prefix_bottom(j) - prefix_top(i), with
the two actual child letters. FIRST has ordinal zero; RUN ordinals
are 1..A, 1..n, 1..n-1 respectively; LAST is one beyond the RUN.
In particular, LAST in sigma(x) is x, not y. Reversal swaps types and
ordinals and negates all three offsets.

The inherited exact root premises and positive descent are stated in
[the transfer-plane proof](class-a-x-transfer-plane-2026-10-31.md).
Let beta>n+2, h=1/beta, alpha=beta-(n+2), rho=alpha-h. Normalized
lengths are L_y=1, L_c=1+h, L_x=2+rho, with
0<h<1/5, h<rho and rho+2h<1. The cubic gives

\[
 V=1-\rho-3h=K/(\beta+1)>0,\qquad
 \alpha(\beta+1)=t+3+(\alpha-2h),\quad \alpha-2h=\rho-h>0.
\]

The previous proof gives P_q, q>=0, Kq<=n+3, a typed coincidence
path of exactly 2q+2 edges. Its origin LAST correction is retained.
Also write Q_q=(y,x,-q,1-3q,6q-3); for q>0 this is the first
intermediate state, so its suffix has 2q+1 edges.

## Negative pump and typed exit table

For p=-r, r>=1, put a=Kr. Define

\[
 Z(R,s,u)=(x,y,R,3R+s,u-s-6R),\quad
 H(R,u)=(x,x,-R,1-3R,6R+u-1).
\]

While a<=t-2, use the two actual edges

\[
 P_{-r}\xrightarrow{(n+4+a,0)}Q_{-r}
 \xrightarrow{(0,2n+4+a)}P_{-(r+1)}.
\]

Here K(r+1)<=K+t-2=n-4<n-1. Thus r stays at most D and D-r
decreases by one per pump. It terminates at a>=t-1. With R=r+1,
the four disjoint integer walls have these exits:

| Wall | Indexed path before the known positive suffix | Length including suffix |
| --- | --- | --- |
| a=t-1 | P_-r --(n+4+a,0)--> Q_-r --(0,A+1)--> H(R,1) --(A+1,t+4)--> Z(R+1,-2,2) --(t+8,0)--> reversal(P_R) | 2r+8 |
| a=t | P_-r --(n+4+a,0)--> Q_-r --(0,A+1)--> H(R,0) --(A+1,d+3)--> Z(R,0,1) --(5,0)--> Q_R | 2r+7 |
| a=t+1 | P_-r --(A+1,n-1)--> Z(R,-2,1) --(2,0)--> Q_R | 2r+5 |
| a>=t+2 | P_-r --(A+1,d-a-1)--> Z(R,-2,2) --(2n+3-KR,0)--> reversal(P_r) | 2r+4 |

These are full Parikh identities, not scalar displacement fits. Their
28 directed forms, including genuine reversals, are checked coefficient
by coefficient over Z[k,t,r]. The first two rows replace the tempting
generic second RUN: it would have ordinal A+1 or A+2. In the first
row the actual LAST changes the type; in the second it is a different
selected edge from the nonexistent A+2 occurrence.

## Ordinal guards

The pump RUN upper slacks are d-4-a=K+2t-a and t-2-a; all lower
slacks are positive. Its new radius has the bound above. In the first
two exit rows the initial RUN slack is at least K+t=n-2.

For a=t-1, a>=K implies t>=2. Hence t+4 and t+8 are in 1..A;
the latter upper slack is 2K+2t-2>=0. Here KR=n-3. For a=t,
d+3<=A because A-(d+3)=n-3>=0; 5<=A and KR=n-2. For
a=t+1, n-1 is the final actual y RUN, 2<=A, and KR=n-1.
For a>=t+2 with a<=n-1, d-a-1 lies in [t+2,n-1]. The next
RUN ordinal 2n+3-KR is at least t+6; its upper slack is
t-1+KR>=0. The positive suffix uses index r, not R, in this row.

The symbolic checker covers all five regimes by nonnegative-coefficient
chambers. For pump/cap1/cap0/near take K=u+1, a=K+v and
t=a+2+w/a+1/a/a-1 respectively, u,v,w>=0. For high take
K=u+v+1, a=w+u+2, t=w; u=a-t-2 and v=n-1-a are the two
nonnegative slacks. This covers a superset of the divisible cases a=Kr,
so it loses no integer instance. Thirty-one guard/budget polynomials
have nonnegative coefficients. Equality checks preserve each LAST
ordinal and each child type.

## Strict overlaps and suffix domains

For a label (x,y,b,3b+s,u-s-6b) the normalized shift is
u+sh-bV. The shifts of P_-r, Q_-r and H(R,u) are respectively
1+h+rV, -2+h-rV and u+h+RV. These identities and the root
relation above are checked modulo the exact cubic, not by evaluation.

* Since a<=n-1<beta+1, rV<1. Thus P_-r has upper margin
  1+rho-h-rV>rho-h>0 and positive lower margin.
* Q_-r is used only when a<=t. Its lower margin is
  alpha-rV>0 by alpha(beta+1)>t+3>a; its upper margin is positive.
* In cap1/cap0, KR=n-3/n-2, so 0<RV<1. Thus H(R,1) has
  shift between 1+h and 2+h<2+rho, and H(R,0) between h and
  1+h<2+rho. Both are strict x/x overlaps.
* For cap1's Z(R+1,-2,2), K(R+1)=n+K-3<=2n-5;
  for high's Z(R,-2,2), KR<=n-1+K<=2n-3. Each is less than
  2(beta+1), so the shift 2-2h-bV is greater than -2h>-1
  and less than 2<L_x.
* Near's Z(R,-2,1) has KR=n-1<beta+1, hence shift
  1-2h-RV>-2h>-1 and less than 1. Cap0's Z(R,0,1) has
  KR=n-2 and shift strictly between 0 and 1.

All positive/reversed suffix domains follow from KR=n-3,n-2,n-1
in the first three rows and Kr<=n-1 in the last. All are within
the inherited positive domain Kq<=n+3. Reversal preserves strictness
and indexed edge validity; it is not word reversal of the substitution.

If the initial radius is r0 and there are ell pumps, the terminal radius
r=r0+ell<=D. The longest exit has 2r+8 edges, so total length is
at most 2ell+2r+8<=4D-2r0+8<=4D+6. Positive p uses 2p+2
edges. This proves the stated local result for all parameters in scope.
It does not claim a parameter-independent path bound or shortest paths.

## Executed evidence and rejected variants

Canonical Mojo and the independent literal-word/Fraction oracle replay
all signed indices and both orientations on 120 specimens: k=0..12,
t=0..8 plus (0,20),(0,64),(32,0). Both give **1,464 paths /
46,462 indexed edges**, including **4,412 two-edge pump iterations**.
All four exits occur. The full per-member receipt and symbolic results
are in [the new evidence packet](../evidence/class-a-x-signed-strip-2026-10-31/README.md).
Checked machine overflow and path-cap exhaustion refuse a verdict; the
unbounded mathematical argument is separate from machine-size limits.

The completed 22-graph parent certificates have P_p in Reach(X) exactly
for -D<=p<=D, with both real orientations present. That is a **finite
profile**, not a proved reachable-interval theorem. No additional full
graphs are claimed by the 120 selected-path replays.

A tempting immediate sign fold extrapolates the high-wall first rule
at (k,t,r)=(0,8,1): (i,j)=(33,19), target Z(2,-2,2). Both formal
labels are strict, but sigma(y) has only ordinals 0..11. It is refused;
the valid path pumps six times before cap1. At (0,2,r=1), replacing
the true LAST target H(2,1) by P_-2 is also refused. Wrong reversal
indices, full-offset mutation and out-of-domain radii are rejected.
Neither failure is a nonproductive-state obstruction.

## Dependency and remaining scope

At this extension's inspection #428/#430/#431/#432/#433 remain open
at the heads recorded in dependency-status.json. Their universal
predecessor certificates and conditional S18 identity are neither merged
nor promoted here. The local proof depends on the previous #436 descent,
not on those unaccepted universal identities. #437's separate generic
selected-rank/Lean work is not duplicated. No claim ledger is promoted.

The symbolic certificates check exact algebra, guards and the bound;
the strict-geometry inequalities above are a written proof, not a Lean
formalization. A local Lean version probe failed before compilation
(`failed to locate application`); no Lean receipt is claimed.

The remaining X task includes other s/u strips, the even planes and a
uniform coverage/escape argument for every actual child. The signed cell
is not asserted forward closed. Finite productivity, this local uniform
proof, and the conditional graph reduction remain distinct. Universal
class-A BH and a complete Pisot substitution proof are not established.
