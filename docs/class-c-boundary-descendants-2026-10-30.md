# Class-C plus boundary: two exact descendant interfaces (2026-10-30)

**Status:** scoped hand proof; independent human review pending. Executable
replays check a finite parameter interval. No existing ledger claim is promoted.

Dependencies: Theorems P_C and R_C and the
[nine-seed interfaces](class-c-nine-seed-interfaces-2026-10-30.md), accepted
in PR #405 at 13e5ea48b02ecf9c0bce1e767b5f3b0aec586c88.
The [targeted stop/go](class-c-boundary-descendants-stopgo-2026-10-30.md)
precedes implementation.

## Work shown

### Assumptions and hypotheses

Integers d>=7, eps=+1, c=0, n=2d-5, p=3d-5, r=d-4. The words are

    sigma(x)=x y^p x, sigma(c)=c y^n x, sigma(y)=c y^r c.

Normalize ell_y=1, a=ell_x, b=ell_c, h=2b-a. Displacement is
bottom-start minus top-start; (A,B,w) is a strict overlap iff
-ell_B<w<ell_A. Word indices below start at zero; run indices separately
start at zero after the first singleton. Imported identities are

    beta*a=2a+p, beta*b=a+b+n, beta=r+2b;
    h=1-1/beta; 5<a+b<6; 2<b<5/2; 3<a<4.

No tile-length integer-independence assumption or return-vector realization
bridge is added.

### Derivation / reduction

#### Exact boundary coordinates and three strict chambers

On this boundary the characteristic cubic is

    chi(t)=t(t+1)(t-d)-2.

Consequently beta>d>=7 and beta-d=2/(beta(beta+1)). Put
u=1/beta and rho=1/(beta(beta+1)). Then

    0<u<1/7, 0<rho<u/8,
    b=2+rho, h=1-u, a=3+u+2rho.

These are identities, not fitted asymptotics. They give

    W=3a-10b+10=-1+3u-4rho,        -1<W<0;
    E=-4a+11b=3b+4h=10-4u+3rho,   9<E<10;
    G=-5a+11b=b+5h=7-5u+rho,      6<G<7.

For W, 3u-4rho>0 and 3u-4rho<3/7<1. For E and G, their
deficits from 10 and 7 are positive, and smaller than 4/7 and 5/7.
All three chambers are strict for every integer d>=7.

#### Uniform seed-reachable escape with a singleton outgoing star

Define

    P=(x,y,a+b-6), Q=(x,c,W).

The seed D_xc=(x,x,b) has child P at actual word indices
(p+1,d-5): its top final x and bottom y-run index d-6. These indices
are in range, and the nine-seed theorem lists this child (B=2,M=5).

For P, the inflated displacement is

    S_P=beta(a+b-6)=3a-11b+5d-10-6r.

The bottom final c starts at S_P+b+r=W, since r=d-4. Its preceding
run ends at W<0, so neither that run nor the bottom first singleton
intersects any top tile, whose word starts at zero. The bottom final c
ends at

    W+b=1+3u-3rho,
    0<W+b<10/7<3<a.

It therefore intersects exactly the top first x. All top run and final
tiles start at or beyond a. The complete distinct child set is

    children(P)={Q},

with its unique occurrence pair (0,r+1). This proves completeness by
the positions of all three bottom segments, including strict endpoints.

In the nine seed states and their complete first-child tables, the only
state with ordered letters (x,c) has displacement zero. Since -1<W<0,
Q is outside that candidate for every d>=7 on this boundary. Thus PR #405's
single-member failed-carrier witness extends uniformly to the entire plus
lower boundary. This does not exclude a richer parameter-indexed carrier.

#### Complete ten-child star of Q

Inflating Q gives

    S_Q=beta(3a-10b+10)=-4a+10b-d-5.

Use F/R/L for first singleton, y-run and last singleton. The bottom
first c ends at S_Q+b=E-d-5<5-d<0. The bottom final x starts at
S_Q+b+n=d-10+E>d-1>=6>a and ends before the top final x starts,
since its start minus p is E-2d-5<0. These inequalities exclude
F/F,R/F,L/F,F/L,L/L,L/R. Exactly F/R,R/R,R/L remain.

The complete distinct children are:

| Kind | Child | Integer t | Actual word-index witness (top,bottom) |
|---|---|---|---|
| F/R | (x,y,-4a+11b-t) | 7<=t<=10 | (0,d+6-t) |
| R/R | (y,y,-5a+11b-t) | t=6,7 | (1,d+6-t) |
| R/L | (y,x,-5a+11b-t) | 6<=t<=9 | (d+t-9,n+1) |

Here is the full integer-window derivation, including the actual run bounds.
For F/R the bottom run starts at C=E-d-5, and its run index j obeys

    -C-1<j<a-C, 0<=j<=n-1;
    d+4-E<j<d+5-G.

Since 9<E<10 and 6<G<7, the integers are exactly d-5..d-2.
They are all in 0..n-1 for d>=7. Substituting t=d+5-j gives the first row.

For R/R put k=j-i, with top/bottom run indices i,j. Its displacement is
G-d-5+k. Strict overlap requires

    d+4-G<k<d+6-G,

so k=d-2,d-1. Both are attainable: i=0,j=k lies in the actual runs
0..p-1 and 0..n-1. More precisely, all pairs are i=0..n-1-k,
j=i+k. There are n-k pairs at each difference; no other differences
pass the strict overlap guard. This yields 2d-7 R/R occurrence pairs
and exactly two distinct states.

For R/L, C=S_Q+b+n-a=d-10+G, so the top run index i satisfies

    C-1<i<C+a;
    d-11+G<i<d-10+E.

Its integers are exactly d-4..d-1, all in 0..p-1. Substituting
t=10+i-d gives the third row. No infinite-run positions need clipping
away, and all stated occurrence witnesses are actual word positions.

Different t in a row differ by a nonzero integer multiple of ell_y=1.
Different rows have different ordered letter pairs. R/R pairs at the
same difference give exactly the same displacement. Therefore Q has
exactly ten distinct children and exactly 4+(2d-7)+4=2d+1 accepted
occurrence pairs. Counting occurrence pairs as states is false.

### Evidence and replay

Canonical formulas: `kernel/psc/class_c_boundary_descendants.mojo`;
driver: `kernel/class_c_boundary_descendants.mojo`. The canonical regression
enumerates every actual word-occurrence pair at both parents for every
d=7..64, compares complete sets to both formulas and the existing reusable
segment transfer, and checks the seed path, escape, walls and scope refusals.
The finite executable range is inherited from SeedInterface; the proof above
is quantified over every d>=7.

The independent Python oracle imports only the archived integer/Fraction
literal-word implementation. It independently enumerates all nine seed stars
to check the escape and both new stars to compare full child sets, occurrence
counts and actual witnesses. With a Mojo dump it requires all 116 parent
records and 638 child records with no missing/duplicate keys or states.

From kernel/ (pinned Mojo from pixi.lock):

    pixi run --locked mojo run -I . tests/test_class_c_boundary_descendants.mojo
    pixi run --locked mojo run -I . class_c_boundary_descendants.mojo dump > /tmp/class-c-boundary-descendants.txt

From repository root:

    python3 oracles/python/check_class_c_boundary_descendants.py --mojo-dump /tmp/class-c-boundary-descendants.txt --check-receipt evidence/class-c-boundary-descendants-2026-10-30/receipt.json

The dedicated workflow regenerates the dump, checks the committed receipt
and uploads the full export. Local replay is not hosted acceptance.

### Negative controls

- Wrong sign, c!=0 and invalid stage indices are refused. SeedInterface's
  existing finite-budget and cone guards remain in force.
- Exact sign checks certify all six strict margins for W,E,G at every
  replayed member. The proof gives no equality endpoint to round away.
- The oracle deliberately removes one child from each expected set and
  verifies inequality with the actual set; counts alone are insufficient.
- Six pytest controls reject missing parents, missing children, duplicate
  parents, duplicate children, corrupted child coefficients and a false
  summary, even when the other export rows are present.
- The native and independent checks retain 4,234 accepted occurrence pairs
  and collapse 3,596 duplicates over 116 stars. The R/R multiplicity grows
  with d although its distinct set has size two.
- Q is a strict, seed-reachable state absent from seeds plus the first
  layer, at every replayed d; the all-parameter exclusion is proved above.

### Non-claims / remaining gaps

These are two complete, uniform outgoing stars on plus c=0, not merely
observed edges. The canonical source's numeric range and oracle replays are
finite experiments supporting the written proof. The ten outgoing states
still need their successor classifications. No forward closure, all-depth
state bound, hitting rank or BH certificate follows from these interfaces.
The remaining lower-cone chambers, return-vector realization and non-unit
spectral bridges retain their existing obligations. No PDS or PSC conclusion
or generated completion-ledger promotion is made. Human review is pending.
