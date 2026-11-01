# Class A: typed RUN shear and productive cross-strip sectors

This extends #436's local productivity results beyond its signed unit cell.
It proves two sectors of parallel strips productive, by changing just the
entrance occurrence and retaining an already proved coincidence suffix.
It does not assert that the sectors contain all X descendants.
The [stop/go record](class-a-cross-strip-stopgo-2026-10-31.md) was written
before the new profile and executable diagnostic.

## Model and statement

Use the minus class-A ordered words, for all integers k,t>=0:

\[
 K=k+1,\ n=k+t+3,\ d=k+2t+5,\ A=n+d,
 \qquad x\mapsto xy^Ax,\ c\mapsto cy^nx,\ y\mapsto xy^{n-1}c.
\]

Offsets are full bottom-minus-top Parikh triples in the order (x,c,y).
Set

\[
 Z(p,s,u)=(x,y,p,3p+s,u-s-6p),\quad P_p=Z(p,1,1),
 \qquad D=\lfloor(n-1)/K\rfloor.
\]

Every state in either following sector, and its genuine reversal, admits
an actual occurrence-indexed path to C=(y,y,0,0,0):

| Sector | Hypotheses | Selected path length |
| --- | --- | --- |
| Nonnegative | p>=0, Kp<=n-1, -3<=s<=3, u=1 | exactly 2p+2 |
| Negative | p<0, K(-p)<=t, -3<=s<=1, u=1 | at most 4D+6 |

These sectors include seven nonnegative-index strips and five guarded
negative-index strips. The earlier signed unit-cell result still applies
separately outside the new negative sector when s=1. The union is not
asserted forward closed. The theorem is local; source reachability from X
is not a premise of its proof and is not inferred from strict geometry.
These rectangular sectors are sufficient domains, not maximal domains of
the guarded covariance lemma.

The previous positive and signed descent arguments are recorded in
[class-a-x-transfer-plane-2026-10-31.md](class-a-x-transfer-plane-2026-10-31.md)
and [class-a-x-signed-strip-2026-10-31.md](class-a-x-signed-strip-2026-10-31.md).
They provide actual typed suffixes, including the origin LAST correction
and all four negative-wall exits. The new proof reuses them at their exact
scope rather than re-proving full graph closure.

## General typed RUN shear

The incidence action on an arbitrary full offset is

\[
 M(x,c,y)=(2x+c+y,\ c+y,\ Ax+nc+(n-1)y),\qquad
 M(0,m,-m)=(0,0,m).
\]

Suppose an actual edge from a strict source w uses a top RUN occurrence i
and a bottom occurrence j. Shear its source offset by (0,m,-m), keep the
source letters, and replace i by i+m. If **both i and i+m lie in the same
actual top RUN**, the child letters are unchanged. The proper-prefix
change is exactly (0,0,m), so the child full offset is unchanged too:

\[
 M(\Delta+(0,m,-m))+P_b(j)-P_a(i+m)
   =M\Delta+P_b(j)-P_a(i).
\]

Thus, provided the sheared source remains strict, this is another actual
edge to precisely the same typed target. The target's strictness and
productive suffix are inherited. This is the usual affine prefix-cocycle
calculation specialized to these ordered words, not a new spectral
criterion. It applies to all nine source-letter pairs and to FIRST, RUN
or LAST bottom occurrences. A symbolic coefficient check verifies all
27 typed cases and their 27 genuine reversals. Reversal swaps the two
indices and negates every offset; it does not reverse the substitution.

The shear preserves p and u=3dx+dc+dy and changes s=dc-3dx. This
identifies a reusable way of reducing several parallel strips to one
known productive successor, conditional on actual RUN and strictness
bounds. It supplies no all-child invariant or global quotient theorem.

## Special entrances and integer guards

For u=1 and m=s-1, apply the shear to the first edge of P_p's path.
For p!=0 that first edge is to
Q_p=(y,x,-p,1-3p,6p-3), and the new entrance is

\[
 Z(p,s,1)\xrightarrow{(n+s+3-Kp,0)} Q_p.
\]

For p=0 the correct common target is instead
B=(y,x,0,1,-1), with entrance (n+s+1,0), followed by (2,1) to C.
Using Q_0 as that two-edge base would be a different unproved suffix.

For p>0 put b=Kp, so K<=b<=n-1. The entrance lower and upper
RUN slacks have exact nonnegative decompositions

\[
 i-1=(n-1-b)+(s+3),\quad
 A-i=2(K-1)+2t+(b-K)+(3-s).
\]

For p=0 the corresponding slacks are

\[
 i-1=(K-1)+t+(s+3),\quad
 A-i=(K-1)+2t+(3-s)+1.
\]

For p<0 put a=K(-p), with K<=a<=t. Then

\[
 i-1=2(K-1)+t+(s+3)+(a-K)+3,\quad
 A-i=(K-1)+t+(t-a)+(1-s)+1.
\]

Also n-1-a=(K-1)+(t-a)+2>=0, placing the negative source within
the signed unit-cell radial domain. Its original path starts with the
RUN/FIRST edge to Q_p: a<=t is exactly within the pump/cap1/cap0
regimes where that first edge is used. The near/high exits are not
substituted without their guards. Seven nonnegative linear implication
certificates check these identities and their nonnegative weights over
unbounded integer parameters; there is no parameter interpolation.

The endpoints are attained. At (k,t,p,s)=(0,0,2,-3) the entrance
ordinal is 1. At (0,0,1,3) it is A=8, the final RUN y, not LAST x.
At (0,0,0,-3) the base entrance also has ordinal 1.

## Strict geometry and lengths

Use the inherited exact root premises beta>n+2, h=1/beta,
rho=beta-(n+2)-h, with 0<h<1/5, h<rho and rho+2h<1.
Normalized lengths are L_y=1, L_c=1+h, L_x=2+rho. The cubic gives
V=1-rho-3h=K/(beta+1)>0. The physical shift of Z(p,s,1) is

\[
 \delta=1+sh-pV.
\]

This identity is checked modulo the exact cubic. No floating geometry is
used. For p>=0, Kp<=n-1<beta+1 implies 0<=pV<1, giving
-3h<delta<=1+3h. Therefore -1<delta<L_x. For p<0, a<=t<n-1
implies 0<(-p)V<1, hence delta>1-3h>0 and
\(\delta<2+sh\le2+h<2+\rho\). Every stated source is strict.
All common targets and suffix states have the inherited strictness proof.

The first target is identical to the previous path's first target; all
remaining edges are unchanged. For p>=0 this retains length 2p+2,
including the p=0 base and the genuine origin LAST correction for p>0.
For p<0 it retains the signed path bound 4D+6. The same proof applies to
real reversals by transposing indices. No shortest-path or parameter-
independent bound is claimed. Checked machine overflow or a fixed path
budget refuses a verdict; the unbounded written proof is separate.

These strips cross the earlier odd-plane slices: on Z(p,s,1),
3dx+3dc+2dy=s+2, so both even and odd planes occur. No uniform range
of these coordinates for all X descendants is asserted.

## Finite coverage and boundary control

The independent literal-word/Fraction oracle replays every edge in
7,574 oriented paths / 243,888 selected-edge instances over the same
120 specimens: k=0..12,t=0..8 plus (0,20),(0,64),(32,0).
The canonical native audit checks all 7,574 distinct entrances and
42,234 shared suffix edges (49,808 actual indexed edge checks), then
compares every reused suffix's indices and full typed targets exactly.
Thus repeated suffix verification is factored without omitting any path.
These are selected-path specimens, not 120 newly completed graphs.

Separately, the immutable 22-graph parent certificate yields these finite
measurements. The comparison carrier includes **all vertices on** the
previous A_m, positive unit, signed unit and E6 paths and their reversals;
it is not a comparison with every result already on main.

| (k,t) | Reached oriented sector sources | Outside the previous local path carrier | All x/y u=1 sources | In new sector |
| --- | ---: | ---: | ---: | ---: |
| (0,0) | 34 | 26 | 32 | 17 |
| (3,0) | 22 | 18 | 20 | 11 |
| (0,8) | 184 | 142 | 129 | 92 |
| (8,8) | 30 | 22 | 28 | 15 |

The remaining u=1 sources are retained in the packet, not dropped from
reporting. These counts are finite coverage observations, not a uniform
reachable-interval theorem, a novelty claim against all main proofs, or
a claim that every X descendant has u=1.

The completed graph at (0,0) contains
W=Z(2,-4,1)=(x,y,2,2,-7), with a five-edge actual indexed X-to-W
witness in the packet. W and formal Q_2 are both strict. However the
proposed entrance ordinal is zero, so its actual FIRST child is
(x,x,-1,-5,8), not Q_2. This refutes extending RUN covariance through
FIRST merely because geometry and X ancestry hold. It is not a
nonproductivity obstruction. Source sector s=-4 is not silently added.

## Dependencies and remaining scope

The [evidence packet](../evidence/class-a-x-cross-strip-2026-10-31/README.md)
contains exact replays, symbolic receipts, negative controls, hashes and
fresh dependency heads. Parent #436 is used at revision 3ee6f9bcbc075822cc1800b4f2ab979dbe2cf2f5.
#428/#430/#431/#432/#433 remain open at inspection; their universal
predecessor identities are not integrated or promoted. Pending human
validation is distinct from missing hosted acceptance receipts. No claim
ledger status changes. The generic selected-rank/Lean work in #437 is
not duplicated; this argument's geometry is written, not Lean formalized.

Other s/u strips, other source types and a uniform argument ensuring that
every X descendant enters a proved productive path remain open. These
local sectors do not establish universal BH, the overlap-realization
bridge or the complete Pisot substitution conjecture.
