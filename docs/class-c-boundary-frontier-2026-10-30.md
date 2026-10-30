# Class-C plus boundary: complete ten-source frontier (2026-10-30)

**Status:** scoped hand proof; independent human review pending. Finite
replays support the argument. No existing ledger claim is promoted.
Depends on the [P/Q interfaces](class-c-boundary-descendants-2026-10-30.md)
and the continuation decision in the
[targeted stop/go](class-c-boundary-descendants-stopgo-2026-10-30.md).

## Work shown

### Assumptions and hypotheses

Integers d>=7, eps=+1, c=0, n=2d-5, p=3d-5, r=d-4, with
sigma(x)=x y^p x, sigma(c)=c y^n x, sigma(y)=c y^r c.
Use Theorems P_C and R_C, ell_y=1, a=ell_x, b=ell_c and displacement
bottom-start minus top-start. The P/Q proof gives

    u=1/beta, rho=1/(beta*(beta+1)), beta=d+2rho,
    0<u<1/7, 0<rho<u/8, a=3+u+2rho, b=2+rho,
    E=-4a+11b, G=-5a+11b.

Q's ten distinct children, all seed-reachable, are
X_t=(x,y,E-t), t=7..10, Y_t=(y,y,G-t), t=6,7,
and Z_t=(y,x,G-t), t=6..9. This note classifies every successor of each.
No new realization or spectral bridge is assumed.

### Derivation / reduction

#### Exact integer endpoint rule

Write [I,U,R] for I+U*u+R*rho. These are integer model coordinates;
field evaluation reuses the existing exact kernel. Since beta*u=1 and
beta*rho=u-rho, inflation acts by

    beta*[I,U,R]=[d*I+U,R,2I-R].

Source triples are [10-t,-4,3] on X_t and [7-t,-5,1] on Y_t,Z_t.
Length triples for x,c,y are [3,1,2], [2,0,1], [1,0,0].

For |U|<=5, |R|<=10 the fractional correction has absolute value
< (5+10/8)/7=25/28<1. Its sign is the sign of the integer
L=U*(d+1)+R unless L=0, in which case it is the sign of U.
Indeed, multiplication by positive beta*(beta+1) reduces its sign to
that of U*(beta+1)+R=L+2U*rho. The last correction has absolute value
<10/56<1, and if L=0 its sign is the sign of U. It vanishes exactly
when U=R=0.

Thus the smallest integer strictly above [I,U,R] is I+1 if its
fractional sign is nonnegative, and I otherwise. The largest integer
strictly below it is I-1 if that sign is nonpositive, and I otherwise.
Integer endpoints are strictly excluded.

#### Complete explicit run windows

In the tables C=[I,U,R]. F/R and L/R produce displacement C+j;
R/F and R/L produce C-i; R/R produces C+ell with ell=j-i.
Ordered letters are the named side's end singleton and y, or y/y for
R/R. F/L mean first/last singleton; i,j are zero-based y-run indices.
All integer endpoints are included after intersection with the stated
actual bounds. An empty intersection contributes no child.

For X_t put k=10-t in {3,2,1,0}. Clip j to [0,d-5], i to [0,3d-6],
ell to [6-3d,d-5]. Singleton types are x on top, c on bottom.

| Kind | C=[I,U,R] | Unclipped integer window |
|---|---|---|
| F/R | [kd-2,3,2k-2] | 1-kd<=j<=4-kd |
| L/R | [(k-3)d,2,2k-4] | (3-k)d-1<=j<=(3-k)d+2 |
| R/F | [kd-7,2,2k-5] | kd-7<=i<=kd-5 |
| R/L | [(k+1)d-9,2,2k-4] | (k+1)d-9<=i<=(k+1)d-7 |
| R/R | [kd-5,2,2k-4] | 4-kd<=ell<=5-kd |

For Y_t put k=7-t in {1,0}. Clip i,j to [0,d-5], ell to [5-d,d-5].
Both singleton types are c.

| Kind | C=[I,U,R] | Unclipped integer window |
|---|---|---|
| F/R | [kd-3,1,2k] | 2-kd<=j<=4-kd |
| L/R | [(k-1)d-1,1,2k-1] | (1-k)d<=j<=(1-k)d+2 |
| R/F | [kd-7,1,2k-2] | kd-7<=i<=kd-5 |
| R/L | [(k+1)d-9,1,2k-1] | (k+1)d-9<=i<=(k+1)d-7 |
| R/R | [kd-5,1,2k-1] | 4-kd<=ell<=5-kd |

For Z_t put k=7-t in {1,0,-1,-2}. Clip j to [0,3d-6], i to [0,d-5],
ell to [5-d,3d-6]. Singleton types are c on top, x on bottom.

| Kind | C=[I,U,R] | Unclipped integer window |
|---|---|---|
| F/R | [kd-2,2,2k+1] | 1-kd<=j<=3-kd |
| L/R | [(k-1)d,2,2k] | (1-k)d-1<=j<=(1-k)d+1 |
| R/F | [kd-7,1,2k-2] | kd-7<=i<=kd-4 |
| R/L | [(k+3)d-9,2,2k] | (k+3)d-9<=i<=(k+3)d-6 |
| R/R | [kd-4,2,2k] | 3-kd<=ell<=4-kd |

The only additional singleton/singleton children are:

| Source | Kind | Child displacement | Guard |
|---|---|---|---|
| X_7 | L/F | [-2,2,1] | every d>=7 |
| X_10 | F/L | [d-6,3,-2] | d=7,8 |
| Y_7 | F/L | [d-7,1,0] | d=7,8 |
| Z_6 | L/F | [-3,1,0] | every d>=7 |
| Z_9 | F/L | [d-7,2,-3] | d=7,8 |

#### Completeness, clipping and duplicates

For each source, take actual run lengths R_A,R_B, first lengths h_A,h_B
and last starts f_A=h_A+R_A, f_B=h_B+R_B. The four singleton/singleton
displacements are S+pos_B-pos_A with pos_A in {0,f_A}, pos_B in
{0,f_B}, and strict margins w+ell_bottom>0, ell_top-w>0.
Substitution of the displayed coordinates leaves exactly the five guarded
singleton rows above. Every other case fails at least one strict margin.

For a top singleton set C=S+h_B-pos_A; the full condition is
-C-1<j<ell_top-C. For a bottom singleton set C=S+pos_B-h_A; its
condition is C-1<i<C+ell_bottom. For R/R set C=S+h_B-h_A; its
condition is -C-1<ell<1-C. Applying the integer endpoint rule gives
exactly the fifteen run rows above. Direct substitution bounds all guard
and endpoint U,R coefficients in absolute value by (3,7) on X, (1,3)
on Y, and (3,7) on Z, inside the proved (5,10) envelope. The canonical
implementation refuses a larger envelope.

These four singleton cases, four singleton/run cases and one R/R case
exhaust all nine segment kinds. Every retained non-R/R integer directly
names an actual run occurrence. For R/R, [1-R_A,R_B-1] is precisely the
attainable difference interval: i=max(0,-ell), j=i+ell is an actual
witness for each retained ell. No infinite-run position is admitted.

Coordinates are injective: if [I,U,R]=0, multiplication by beta*(beta+1)
gives I*beta^2+(I+U)*beta+(U+R)=0. Irreducibility of chi forces I,U,R
to vanish. This derives the needed equality test from P_C; it does not
assume tile-length integer-independence. Distinct integers within one row
give distinct states. R/R pairs of equal difference coincide exactly.
When two run kinds with the same ordered letters survive, their R
coefficients differ by one, so their states do not coincide. Each source
has at most one singleton row, with ordered letters different from those
of its run children. These facts identify all duplicates.

Taking the cardinalities of the clipped windows and retained singleton
gives the following sharp all-parameter counts:

| Source | d=7 | d=8 | d=9 | d>=10 |
|---|---|---|---|---|
| X_7 | 6 | 6 | 6 | 6 |
| X_8 | 8 | 8 | 8 | 8 |
| X_9 | 8 | 8 | 8 | 8 |
| X_10 | 4 | 6 | 8 | 9 |
| Y_6 | 7 | 7 | 7 | 7 |
| Y_7 | 3 | 5 | 7 | 8 |
| Z_6 | 6 | 6 | 6 | 6 |
| Z_7 | 8 | 8 | 8 | 8 |
| Z_8 | 8 | 8 | 8 | 8 |
| Z_9 | 4 | 6 | 8 | 9 |

For X_10 the nonempty run windows are j=1..min(d-5,4),
i=max(0,d-9)..d-7, ell=4..min(d-5,5), plus F/L only at d=7,8.
For Y_7 they are j=2..min(d-5,4), the same i and ell windows, plus
F/L only at d=7,8. For Z_9 they are j=2d+1..min(3d-6,2d+3),
i=max(0,d-9)..d-6, ell=2d+3..min(3d-6,2d+4), plus F/L only at
d=7,8. These prove the three varying rows. Every other surviving window
has constant cardinality for d>=7, as direct substitution of its k shows.

### Evidence and replay

Canonical module/driver: `kernel/psc/class_c_boundary_frontier.mojo` and
`kernel/class_c_boundary_frontier.mojo`. The native regression compares
all 580 interfaces at every d=7..64 against both the general exact segment
transfer and exhaustive actual occurrence enumeration. It also compares
all 231 fractional coefficient choices in the envelope at every d against
the existing exact field, including integer cancellation controls.

The independent integer/Fraction oracle transcribes the fifteen written
windows, enumerates every actual word-occurrence pair, and compares full
sets with both the written tables and canonical export. It records 27,666
accepted pairs, 23,227 duplicates and 4,439 children summed over 580 stars.
This finite replay supports the written all-d proof; it does not replace it.

From kernel/ with the pinned toolchain:

    pixi run --locked mojo run -I . tests/test_class_c_boundary_frontier.mojo
    pixi run --locked mojo run -I . class_c_boundary_frontier.mojo dump > /tmp/class-c-ten-frontier.txt

Then from repository root:

    python3 oracles/python/check_class_c_boundary_frontier.py --mojo-dump /tmp/class-c-ten-frontier.txt --check-receipt evidence/class-c-boundary-descendants-2026-10-30/frontier-receipt.json

The dedicated boundary workflow checks this export and receipt as well as
the unchanged P/Q interfaces. Hosted acceptance is separate from local replay.

### Negative controls

Sign queries outside the proved coefficient/replay envelope refuse. Native
checks guard strict integer endpoints, empty clipped windows and invalid
source indices. Six malformed-export controls reject missing or duplicate
parents/children, corrupted coefficients with unchanged counts, and false
summaries. Actual occurrence multiplicities are kept before deduplication.
The known uniform Q escape is preserved rather than relabelled as closure.

### Non-claims / remaining gaps

Together with P/Q, this gives twelve complete local stars for all d>=7
on plus c=0. These sources are seed-reachable, but their output union has
not been proved forward-closed. Its unclassified successors, other lower
cone chambers, a hitting argument, and the realization/non-unit spectral
bridges remain obligations. No all-depth state bound, BH, PDS or PSC
conclusion follows. Independent human review remains pending validation debt.

A concrete next unclassified source is R=(x,c,2a-3b-2)=[-2,2,1] in
displacement coordinates. It is the X_7 L/F child at actual word indices
(p+1,0), reached uniformly along D_xc -> P -> Q -> X_7 -> R. Its
ordered letters distinguish it from all classified sources except Q, and
R.shift-Q.shift=-1-u+5rho<0 distinguishes those two. Its outgoing star
is not classified here.
