# Class-C plus boundary: a parameter-indexed transfer family

**Status:** scoped hand proof; independent human review pending. No ledger
promotion. The [stop/go continuation](class-c-r-transfer-stopgo-2026-10-30.md)
precedes implementation. This family extends the local analysis beyond a
fixed list of sources; it does not supply carrier closure.

## Work shown

### Assumptions and hypotheses

Integers d>=7, plus c=0, n=2d-5, p=3d-5, r=d-4. Use P_C, R_C and
the boundary identities beta=d+2rho, u=1/beta, rho=1/(beta(beta+1)),
0<u<1/7, 0<rho<u/8, a=3+u+2rho, b=2+rho. Coordinates [I,U,R]
mean I+U*u+R*rho, with ell_y=1. Define the formal strict parents

    A_K=(x,c,[-1,3,-K]), 0<=K<=d, K an integer.

Their physical expression is 3a-(K+6)b+2K+2. A_4 is Q; A_0 is the
U last/first child in the [R/T/U proof](class-c-r-transfer-2026-10-30.md).
Those two indices are uniformly seed-reachable. No reachability of the
other indices, return-vector realization or additional independence is assumed.

### Derivation / reduction

#### Two exact mixed corrections and the sharp index wall

Put

    f_K=-K*u+(K-1)rho=-K/(beta+1)-rho,
    g_K=-(K+1)u+(K-3)rho=-(K+1)/(beta+1)-4rho.

For 0<=K<=d, -1<f_K<0. Negativity is immediate. For the lower bound,
K/(beta+1)+rho<=d/(beta+1)+rho<1, since
rho*(beta+1)=u<1+2rho and beta=d+2rho.

For 0<=K<=d-1, -1<g_K<0: the worst lower margin is

    1-d/(beta+1)-4rho=(1+2rho-4u)/(beta+1)>0.

At K=d, however,

    g_d=-1-eta, eta=4rho-2rho/(beta+1), 0<eta<1.

Thus the adjacent integer indices d-1,d lie on opposite strict sides of
g=-1. No equality case is silently rounded. These are rational identities
and inequalities in the exact field, not an asymptotic fit.

Every A_K is a strict overlap. Indeed Krho<=d*rho<u, so
-1<-1+3u-Krho<0, which lies inside (-b,a).

#### Complete child sets for every index

Inflation gives S=[-d+3,-K,K-2]. The bottom first c ends at
S+b=-d+5+f_K<0. The bottom final x starts at d+f_K>d-1>a, and
its end precedes the top final start a+p because d+f_K<p. These
inequalities exclude all singleton/singleton cases, all top-last cases
and the run/first case. Exactly F/R,R/R,R/L remain.

For F/R, C=S+b=-d+5+f_K. Its complete strict run-index condition is

    d-6-f_K<j<d-2-g_K.

For R/R use ell=j-i and C=S+b-a=-d+2+g_K:

    d-3-g_K<ell<d-1-g_K.

For R/L, C=S+b+n-a=d-3+g_K, and

    d-4+g_K<i<d+f_K.

The exact integer windows are:

| Kind | Child displacement | 0<=K<d | K=d |
|---|---|---|---|
| F/R, (x,y) | [-d+5+j,-K,K-1] | d-5<=j<=d-2 | d-5<=j<=d-1 |
| R/R, (y,y) | [-d+2+ell,-K-1,K-3] | ell=d-2,d-1 | ell=d-1,d |
| R/L, (y,x) | [d-3-i,-K-1,K-3] | d-4<=i<=d-1 | d-5<=i<=d-1 |

All listed j are in the actual bottom run 0..n-1, all i are in the
actual top run 0..p-1, and all R/R differences are attainable, witnessed
by i=0,j=ell. The inequalities above exhaust all nine segment kinds,
so the tables are complete, including clipping and strict endpoints.

Different indices within a row differ by a nonzero integer multiple of
ell_y. The rows have different ordered letter pairs. Equal R/R differences
collapse exactly; no further duplicate distinct states occur. Hence

    |children(A_K)|=10 for 0<=K<d; 12 for K=d.

Nevertheless the actual occurrence count is 2d+1 on BOTH sides: the
interior has 4+(2d-7)+4 pairs and the wall has 5+(2d-9)+5 pairs.
Occurrence counts alone cannot detect this child-set transition.

#### A reusable translated block, with its exact scope

For every interior index K<d, the three windows are identical to Q=A_4's
windows, including their actual occurrence witnesses. Their displacements
differ uniformly by

    delta_K=(4-K)*(u-rho)=(4-K)/(beta+1).

Thus children(A_K)=children(Q)+delta_K, with ordered letters preserved.
Equivalently delta_K=beta*(A_K.shift-Q.shift), so the same actual occurrence
pairs survive throughout this index chamber. The formula fails at K=d:
the complete set has twelve states, while a translated Q set has ten.

This is a parameter-indexed local transfer block of d+1 distinct formal
parents, not a frozen graph. Their outgoing types are x/y, y/y, y/x,
so this one block is not itself closed. Reachability/inclusion of any larger
carrier remains a separate obligation.

### Evidence and replay

Canonical module/driver: `kernel/psc/class_c_indexed_transfer.mojo` and
`kernel/class_c_indexed_transfer.mojo`. They directly implement the closed
tables; the fixed (5,10) query envelope is not used to justify large K.
The all-parameter proof above is distinct from the executable budget
d=7..64. The declared finite grid takes every K at d=7,8,9 and
K=0,1,4,d-2,d-1,d at every d=10..64: 357 interfaces over 58 gaps.

Native exact checks compare full sets against every actual occurrence pair
and the general exact segment transfer. Independent Python integer/Fraction
enumeration transcribes the written formulas, checks every full export set,
the interior translation rule and both sides of the sharp wall. The receipt
records 25,213 accepted pairs, 21,527 duplicates and 3,686 child records.

From kernel/:

    pixi run --locked mojo run -I . tests/test_class_c_indexed_transfer.mojo
    pixi run --locked mojo run -I . class_c_indexed_transfer.mojo dump > /tmp/class-c-indexed-transfer.txt

From repository root:

    python3 oracles/python/check_class_c_indexed_transfer.py --mojo-dump /tmp/class-c-indexed-transfer.txt --check-receipt evidence/class-c-r-transfer-2026-10-30/indexed-receipt.json

The dedicated workflow regenerates this export and checks the independent
full sets and receipt, together with the R/T/U and predecessor receipts.
Local finite replay is not hosted acceptance or a replacement for the proof.

### Negative controls

K=-1,d+1 refuse the declared interface; this asserts no non-overlap beyond
the proved range. The strict g+1 signs at K=d-1,d are checked separately.
The incorrect ten-child extension to K=d is rejected despite its unchanged
actual occurrence count. Missing sharp-wall records, missing/duplicate
records, changed coefficients and false summaries fail the independent oracle.

### Non-claims / remaining gaps

These are complete local formulas for formal A_K states; only K=0,4 have
the recorded uniform seed paths. The indexed block is not closed and bounds
neither the remaining descendants nor all possible reachable K-like forms.
No hitting rank, BH, PDS or PSC follows. Other cone chambers, realization
and non-unit spectral obligations remain. Human review is pending.
