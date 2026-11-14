# Class-C plus boundary: selected paths recovered from hand work

**Status: uncompiled hand derivation.** This preserves a side calculation
from the November 14 session, recovered after the executor changed. The
literal prefix arithmetic was rechecked by hand while preparing this note.
No new census, native replay, Lean proof, hosted acceptance, or completion
claim accompanies it.

## Exact hypotheses and conventions

Let `d` be an integer with `d >= 7`, and put `p=3d-5`, `n=2d-5`,
`r=d-4`. The literal substitution is

\[
 \sigma(x)=xy^p x,\qquad \sigma(c)=cy^n x,\qquad
 \sigma(y)=cy^r c.
\]

Use the boundary identities from the
[existing frontier calculation](class-c-boundary-frontier-2026-10-30.md):
`u=1/beta`, `rho=1/(beta*(beta+1))`, `beta=d+2rho`,
`0<u<1/7`, `0<rho<u/8`, and tile lengths
`ell_x=3+u+2rho`, `ell_c=2+rho`, `ell_y=1`.
All displacements are bottom-start minus top-start. A state `(A,B,s)` is
strict when `-ell_B < s < ell_A`.

Write `[I,U,R]=I+U*u+R*rho`. Inflation acts by

\[
 B[I,U,R]=[dI+U,R,2I-R].
\]

These coordinates also record the full integral offset in letter order
`(x,c,y)`:

\[
 T(I,U,R)=(U,R-2U,I+U-2R).
\]

Indeed the literal incidence matrix is
`M=[[2,1,0],[0,1,2],[p,n,r]]`, and `M*T=T*B`. Thus the coefficient
identities below are integral affine identities, not rounded scalar tests.
An edge labelled `(i,j)` uses **zero-based whole-word ordinals**, with
update `s'=beta*s+ell(bottom prefix j)-ell(top prefix i)`.

## A parameter-indexed selected descent

For `0 <= j <= n`, define

\[
 P_j=(c,y,[0,j+1,-j]),\qquad Q_j=(y,c,[0,-j-1,j]).
\]

Here `Q_j` is the genuine reversal of `P_j`. The full offset of `P_j` is
`(j+1,-3j-2,3j+1)`. Its shift is
`(j+1)/(beta+1)+rho`, strictly between `0` and `2+rho`; this follows from
`j+1 <= 2d-4 < 2(beta+1)`. Both orientations are strict.

For `1 <= j <= n`, the actual occurrence pairs give

\[
 P_j\xrightarrow{(j,0)}Q_{j-1},\qquad
 Q_j\xrightarrow{(0,j)}P_{j-1}.
\]

For the first edge the top prefix is `c y^(j-1)` and the bottom prefix
is empty. Its correction is `[-j-1,0,-1]`, so inflation gives
`[j+1,-j,j]+[-j-1,0,-1]=[0,-j,j-1]`. Reversal proves the other edge.
At the base,
`P_0 --(2,1)--> (y,y,0)` and `Q_0 --(1,2)--> (y,y,0)`:
the correction is respectively `-1` and `1`, cancelling the inflated
shift. All indices exist because `n>=9` and `r>=3`.

This gives a selected path of length `j+1`. It is not a shortest-path
claim or a claim that every `P_j` is seed-reachable. The same formula at
`j=n+1` is invalid: that top ordinal is the final `x`, not a run `y`.

## Two previously recorded seed-reachable sources

The [indexed transfer note](class-c-indexed-transfer-2026-10-30.md) records
uniform seed reachability of
`A_0=(x,c,[-1,3,0])` and `A_4=(x,c,[-1,3,-4])=Q`.
The [R/T/U note](class-c-r-transfer-2026-10-30.md) supplies the `A_0`
predecessor. The following selected exits add no reachability premise for
other indexed parents. Their initial shifts lie in `(-1,0)`.

For `A_0`, the three edges are:

| Actual ordinals | Target state | Prefix correction `[I,U,R]` |
|---|---|---|
| `(0,d-4)` | `(x,y,[0,0,-1])` | `[d-3,0,1]` |
| `(1,2)` | `(y,y,[0,-2,0])` | `[0,-1,-1]` |
| `(1,3)` | `(y,y,[0,0,0])` | `[2,0,0]` |

For `A_4`, the eight edges are:

| Actual ordinals | Target state | Prefix correction `[I,U,R]` |
|---|---|---|
| `(0,d-4)` | `(x,y,[0,-4,3])` | `[d-3,0,1]` |
| `(0,3)` | `(x,y,[0,3,-2])` | `[4,0,1]` |
| `(1,0)` | `(y,c,[0,-3,0])` | `[-3,-1,-2]` |
| `(0,2)` | `(c,y,[0,0,1])` | `[3,0,1]` |
| `(1,1)` | `(y,y,[0,1,-1])` | `[0,0,0]` |
| `(0,0)` | `(c,c,[1,-1,1])` | `[0,0,0]` |
| `(d-2,0)` | `(y,c,[0,1,0])` | `[-d+1,0,-1]` |
| `(2,1)` | `(y,y,[0,0,0])` | `[-1,0,0]` |

Applying `B` to each preceding state and adding its displayed correction
gives exactly the target. The first edge in both tables agrees with the
old `A_K` first/run row at run index `d-5`, hence whole-word ordinal `d-4`.
All other ordinals exist for `d>=7`; in particular `3<=r` and `d-2<=n`.
Every intermediate shift in the two tables has absolute value below one:
the largest displayed positive expression is `1-u+rho`, lying in `(0,1)`.
Since every tile length is at least one, all listed child overlaps are
strict. Both final states have the same letter and zero full offset.

## Prior scope and remaining obligation

The earlier notes classify complete outgoing stars and preserve open
closure obligations. A targeted text comparison found no matching `P_j`
descent; this is not an exhaustive novelty claim. The
[completion ledger](completion-ledger-2026-11-02.md) still leaves the lower
Class-C cone open. These selected paths do not give a child-closed carrier,
paths from every seed descendant, or universal boundary hitting. A fresh
primary-source stop/go decision and independent executable/formal replay
are required before theorem-facing implementation or claim promotion.
