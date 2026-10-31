# Guarded odd-plane transfers and a unit-descent productive family

**Status:** exact polynomial transport identities and a scoped universal
local productivity proof, with native/literal regression evidence. The
reachable-interval profile is finite evidence only. No universal
X-descendant productivity or complete carrier is established. Independent
human review remains nonblocking validation debt.

## Work shown

### Assumptions and hypotheses

The [continuation stop/go](class-a-x-transfer-plane-stopgo-2026-10-31.md)
precedes this extension. Use k,t>=0, n=k+t+3, d=k+2t+5, K=k+1,
A=n+d and the same literal words and bottom-minus-top Parikh convention as
[the X audit](class-a-x-productivity-2026-10-31.md). Reversal transposes
the actual occurrence indices and negates all three coordinates.

Inherit main's exact algebraic root predicates beta>n+2, h=1/beta,
rho=beta-(n+2)-h, 0<h<1/5, h<rho and rho+2h<1, with lengths
Ly=1, Lc=1+h, Lx=2+rho. The cubic identity already derived in #436 gives

    v=1-rho-3h=K/(beta+1)>0.

No analytic approximation or unit-only spectral theorem is imported.
Main's [H5 exit](class-a-boundary-h5-exit-2026-10-27.md) already supplies
the auxiliary (y,x,0,1,-1) --(2,1)--> typed coincidence edge; it is reused
below, not presented as a newly discovered general construction.

### Derivation / reduction

#### A generic odd-plane identity with explicit guards

For arbitrary integers z,s,p, define full typed labels

    S(z,s,p) = (x,y,p,3p+2s+1,z-6p-3s-1),
    T(z,s,p) = (y,x,z-p-s-1,z-3p-s,6p+3s+1-4z).

The two invariants of S are

    3*dx+3*dc+2*dy=2z+1,   dc-3*dx=2s+1.

The incidence map is M(a,b,c)=(2a+b+c,b+c,(n+d)a+nb+(n-1)c).
With the actual x-RUN proper prefix (1,0,i-1), set

    i=(z-s)n-Kp+3z+1,
    j=(K+3)z-Kp+(n-K)s+d+1.

Subtract the top RUN prefix against bottom FIRST to obtain T, then add the
bottom RUN prefix against top FIRST to obtain S(z,s,p-z). Coefficientwise,

    S(z,s,p) --(i,0)--> T(z,s,p) --(0,j)--> S(z,s,p-z).    (G)

**The precise generic claim is conditional:** if 1<=i,j<=A and all three
typed labels are strict overlaps, (G) consists of actual indexed edges.
Both moving ordinals are in sigma(x), whose RUN is 1..A. No generic claim
that these guards hold is made. A positive z would decrease p by z, but
does not by itself supply a valid iteration, base exit or source coverage.

This identity unifies the earlier ladder instead of introducing a
competing path: z=2,s=0,p=2m gives exactly #436's A_m, B_m, and its
two-edge m-to-m-1 transfer. The genuinely reversed identities are checked
by transposing i,j and negating every coordinate.

#### A productive z=1,s=0 slice, including the origin

Write

    P_r=S(1,0,r)=(x,y,r,3r+1,-6r),
    Q_r=T(1,0,r)=(y,x,-r,1-3r,6r-3).

For all integers k,t,r>=0 in the domain

    Kr<=n+3=k+t+6,                                      (U)

P_r is productive. For r>=1 the intended ordinals simplify to

    i_r=n+4-Kr,   j_r=2n+4-Kr.

The exact slacks are

    i_r=(n+3-Kr)+1>=1,
    A-i_r=d-4+Kr>=1,
    j_r=i_r+n>=n+1,
    A-j_r=t-2+Kr.

The last slack is nonnegative except at k=t=0,r=1, where it is -1.
This classification is exhaustive: for t>=2 it is immediate; at t=1 it
is -1+Kr>=0; at t=0,k>=1 it is -2+Kr>=0; at k=t=0,r>=2 it is r-2>=0.
The polynomial certificate independently checks nonnegative coefficients
in each of these four unbounded integer chambers after shifting their
free coordinates to zero. Thus every ordinary transfer uses RUN y.

At the sole exceptional triple k=t=0,r=1, j_r=A+1=9 is **LAST x**.
The full displacement is still (0,1,0), but the actual target is

    E=(x,x,0,1,0),                                      (not P_0).

Hence the complete rule is

    P_r --(i_r,0)--> Q_r --(0,j_r)--> P_(r-1)

except that the last target is E at that one triple. At k=0,t=1,r=1,
j_r=A is still RUN y; it must not be conflated with the exceptional LAST.
At k=t=0,r=6, i_r=1 is included. The next index r=7 violates (U).

For strict geometry, (U) and beta+1>n+3 imply rv<1. The exact shifts are

    shift(P_r)=1+h-rv,   shift(Q_r)=-2+h+rv.

For P_r, shift>h>0 and its upper margin is 1+rho-h+rv>0.
For Q_r (r>=1), the lower margin relative to -Lx is rho+h+rv>0,
and its upper margin relative to Ly is 3-h-rv>2-h>0.
Thus all ordinary intermediate/target overlaps are strict. The domain is
preserved when r decreases. There is no omitted equality case at a strict
geometric boundary.

Both P_0 and E have the following common typed exit, since their bottom
images have FIRST x and zero prefix:

    P_0 or E --(n+2,0)--> D=(y,x,0,1,-1)
             --(2,1)--> C=(y,y,0,0,0).

Indeed M(0,1,0)=(1,1,n); subtracting the top prefix (1,0,n+1)
gives D. Then M(0,1,-1)=(0,0,1), and the prefix difference at (2,1)
is (0,0,-1). The first top ordinal is RUN because A-(n+2)=d-2>=3;
the last top y-RUN ordinal 2 exists because n-1>=2. P_0 and E have
shift 1+h and upper margin 1+rho-h>0; D has shift h in (0,1).
These edges are genuinely strict and C is equal-letter full-zero.

Induction therefore constructs an **exactly 2r+2-edge selected coincidence
path** for every P_r satisfying (U), including all parameter faces.
Every Q_r with r>=1 in that domain has the corresponding 2r+1-edge tail.
Their real reversals inherit these paths. In particular the exceptional
E and R(E) have checked two-edge coincidence exits on the entire minus
chamber, independently of the unaccepted predecessor paths to X.

The symmetry also identifies R(Q_r)=S(1,-1,r); thus the productive sources
include a second parallel strip for r>=1, with the same explicit bound.
This is not a claim about every source on either affine plane.

#### A genuine X-descendant obstruction to guard-free plane transfer

At k=t=0, n=3,d=5,A=8, the actual X descendant

    W=S(1,1,1)=(x,y,1,6,-9)

has a nine-edge indexed X-to-W witness in the committed independent probe.
W, T(1,1,1)=(y,x,-2,-3,6), and S(1,1,0)=(x,y,0,3,-3)
are all strict. W's proposed first edge (3,0) is an actual strict edge.
But (G)'s second ordinal is j=11=A+3, beyond even LAST x at A+1=9.
The generic conditional checker refuses it. This is a counterexample to
waiving occurrence bounds even when the source is an X descendant and all
three formal labels are strict. It is **not** a nonproductive overlap:
the completed finite graph is productive by #436's independent audit.

### Evidence and replay

The canonical native module `kernel/psc/class_a_x_transfer_plane.mojo`
implements generic guarded verification and the productive unit slice.
Every actual edge uses main's typed full-Parikh/Perron-field verifier;
machine-integer arithmetic rejects overflow and path caps refuse a verdict.
The independent oracle uses unchanged literal words and Fraction geometry.

Native and Python both replay **1,090 oriented paths / 17,536 selected
edges**, covering k=0..12,t=0..8 plus (0,20),(0,64),(32,0), every index
in (U) and both orientations. The coefficient checker covers four generic
directed edges, six base directed edges and two exceptional directed edges,
the old-ladder specialization, root/shift identities and all four unbounded
integer guard chambers. It does not infer a guard from a polynomial fit.
An additional **240 oriented E6 base paths / 480 edges** are replayed
independently on those same 120 specimens, including every parameter face.

    python -m pip install pytest==8.4.2 sympy==1.14.0
    python -m pytest -q tests/test_class_a_x_transfer_plane.py
    python oracles/python/class_a_x_transfer_plane.py
    python oracles/python/class_a_x_transfer_plane_symbolic.py
    cd kernel
    pixi run --locked mojo run -I . tests/test_class_a_x_transfer_plane.mojo

The finite coverage profile uses the unchanged 22 complete graph certificates
at parent #436 head 372567d53e62. Their all-edge native/oracle agreement is
a recorded prerequisite; the workflow repeats the native full graph replay
and independent indexed comparison. This profile is not a new assertion of
universal graph completion or accepted predecessor status.

On each of these 22 graphs, the nonnegative P indices actually in Reach(X)
are exactly

    0 <= r <= floor((n-1)/K).                            (finite observation)

This is narrower than the proved productivity domain floor((n+3)/K).
For example, at (0,8), P_0..P_10 are reached, while P_11..P_14 satisfy
the proved local domain but are outside the complete X closure. Both
inclusion and exclusion in a parameter-uniform reachable-interval statement
remain unproved.

At (0,8) the new P/Q source roles and their reversals match 44 oriented
labels in Reach(X); 40 lie outside the earlier A/B ladder's actual path
carrier. Across the 22 graphs there are 284 such source incidences,
204 outside that carrier. These are per-specimen counts, not distinct
new global labels or a claim that no other mainline packet proves them.
The comparison deliberately names that fixed earlier carrier, not the
entire repository's collection of productive sources.

### Negative controls

The origin LAST correction, its adjacent final-RUN control, i=1, the next
out-of-domain index, wrong full offsets, wrong letters, unswapped reversed
indices and path caps are exercised. The generic checker rejects both the
origin's false RUN target and the actual X-descendant beyond-word control.
An exact nonzero p(p-1) polynomial and a negative recession coefficient are
rejected. Native tests also verify that z=2 specializes to the earlier
ladder at genuine word-valid indices, rather than accepting a competing map.

### Non-claims / remaining gaps

The generic map is a **guarded local identity**, (U) is a **universal local
productivity domain**, and the reachable interval/profile is **finite**.
None supplies a closed productive carrier for all X descendants. Negative
indices, other values of the parallel-strip parameter s, and other planes
remain to be classified with their own legal-index and strictness guards.
The W control rules out the most direct guard-free plane generalization.
The next target is a complete typed clipping/peeling rule for the remaining
plane strips, together with proved base exits and a decreasing rank.

No status change for the conditional S18 reduction in #428/#430/#431/#432/
#433, no realized-literature-overlap bridge, plus-chamber transfer, BH/#139,
G1, PDS or complete Pisot substitution proof. #436's earlier evidence packet
and historical failed receipts are preserved unchanged.
