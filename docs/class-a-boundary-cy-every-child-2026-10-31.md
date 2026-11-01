# CY every-first-choice productivity, with explicit chamber cases

**Integration candidate (2026-11-01):** canonical native counterparts and
fresh cross-checks are recorded in
[the research integration audit](research-branch-integration-2026-11-01.md).
The original 2026-10-31 scopes and main/research distinctions below are
historical; they do not imply acceptance of this candidate. Exact-head
hosted acceptance remains required. Independent human review is pending.

**Status:** scoped hand symbolic derivation and independent exact-rational
finite replay, stacked on the complete CY star in PR #414. **No general BH,
all-state coverage, forward-closed carrier, all-later-choice termination,
Lean/Mojo formal proof credit or independent human review is claimed.**

## Scoped proposition (hand derivation; independent review pending)

Work on the minus class-A boundary normal form with integer `k,t>=0`,
`n=k+t+3`, `d=2n-1-k`, `A=n+d`, `N=n-1`, actual words
`x->xy^Ax`, `c->cy^nx`, `y->xy^Nc`.
The existing root certificates give `h=1/beta`, `0<h<1/5`,
`rho=alpha-h`, `zeta=rho-h`, and
`0<zeta<rho<1`, `v=rho+2h=alpha+h<1`.
Normalize `Ly=1`, `Lx=2+rho`, `Lc=1+h`.
All offsets are bottom-minus-top full Parikh vectors; all child ordinals
are zero-based *actual occurrences*, not quotient edges.

Let `CY=(c,y,0,-2,2)`. By #414's complete nine-kind source theorem,
**every genuine indexed CY child** has one of six oriented targets
`B0=(c,x,0,0,-2)`, `B1=(c,y,1,0,-2)`,
`B2=(y,y,1,-1,-2)`, `Y0=(y,y,1,-1,-1)`,
`B4=(y,c,1,-1,-1)`, `B5=(y,c,1,-1,-2)`.
Every target has a selected true typed coincidence path within **six
further edges**, and every actual CY first choice reaches `C=(y,y,0,0,0)`
within **seven edges total**. The reversal follows by swapping real
ordered indices and negating all offsets.

## Complete selected paths by exact parameter chamber

Use abbreviations (the **five-tuple is authoritative**):
`J=(y,y,0,2,-2)`, `H=(x,y,0,1,-1)`,
`H1=(x,y,0,-1,1)`, `Q=(y,x,0,-1,1)`,
`V2=(y,x,0,-1,2)`, `W=(c,x,0,1,-1)`,
`U=(x,y,1,2,-3)`. `CY` is not confused with its reversals.
Every arrow lists actual (top,bottom) indices; the source's type
changes at LAST occurrences are explicitly retained.

**B0 (three edges).**
- If `t=0`:
  `B0 -(1,A+1)-> (y,x,-1,-3,4)
       -(0,d+4)-> Z -(2,1)-> C`,
  where `Z=(x,x,0,1,-1)` at `n=3`, and
  `Z=H=(x,y,0,1,-1)` at `n>=4`.
  Here `d+4=A+1` exactly at `n=3`; the LAST x
  cannot be mislabeled RUN y.
- If `t>=1`:
  `B0 -(t,A+1)-> (y,x,-1,-3,5)
       -(1,t+6)-> J -(3,1)-> C`.

**B1 (two edges, all k,t).**
`B1 -(t+2,0)-> (y,x,0,-3,3) -(1,4)-> C`.

**B2 (two or three edges).**
- `t=0`:
  `B2 -(0,n)-> (x,c,0,-3,3)
       -(0,3)-> H -(2,1)-> C`.
- `t=1`:
  `B2 -(0,n)-> (x,c,0,-3,4)
       -(k+3,1)-> J -(3,1)-> C`.
- `t>=2`:
  `B2 -(0,k+3)-> (x,y,0,-3,3) -(1,4)-> C`.
  The latter requires a real RUN ordinal `k+3<=N`,
  and the final y-image RUN index 4 requires `N>=4`;
  both follow for `t>=2`.

**Y0 (three edges).**
Reuse #412's accepted selected path:
`Y0 -(t+1,1)-> (y,y,0,-2,3)
    -(n-1,0)-> (y,x,0,1,-1) -(2,1)-> C`.

**B4 (three edges, except four at k=t=0).**
- `t>=1`:
  `B4 -(t,0)-> (y,c,-1,-2,4)
      -(0,t+4)-> Z -(4,1)-> C`,
  where `Z=(x,x,0,3,-3)` if `k=0` (actual LAST x
  at `t+4=n+1`), otherwise
  `Z=(x,y,0,3,-3)` (actual RUN y).
- `t=0,k>=1`:
  `B4 -(0,0)-> (x,c,0,-2,3)
      -(n,1)-> J -(3,1)-> C`.
- `k=t=0`:
  `B4 -(0,0)-> (x,c,0,-2,3)
      -(n+1,1)-> (y,y,0,2,-3)
      -(0,2)-> H1 -(1,2)-> C`.

**B5 (three to six edges).** First, in every chamber:
`B5 -(0,k+4)-> K`, where
`K=(x,x,-1,-2,4)` at `t=0` (actual LAST x),
and `K=(x,y,-1,-2,4)` for `t>=1` (actual RUN y).
Then:
- `t=0,k>=1`: `K -(1,5)-> J -(3,1)-> C`.
- `k=t=0`: `K -(1,5)-> J
  -(2,0)-> (y,x,-1,0,1)
  -(0,d+1)-> H -(2,1)-> C`.
- `t>=1,k=0`: `K -(0,t+2)-> (x,y,1,2,-5)
  -(0,0)-> (x,x,-1,-3,4)
  -(0,d+4)-> H -(2,1)-> C`.
- `t>=1,k=1`: `K -(0,n)-> (x,c,1,2,-3)
  -(d+4,1)-> C`.
- `t>=1,k=2`: `K -(0,t+4)-> U
  -(d+2,0)-> V2 -(n,0)-> W
  -(1,0)-> Q -(1,2)-> C`.
  This deliberately uses the **already mainline** four-edge
  U suffix, not the shorter #411 recovery awaiting integration.
- `t>=1,k>=3`: `K -(1,t+5)-> J -(3,1)-> C`.

The longest displayed CY-first-choice continuation has seven edges
at `t>=1,k=2`. The paths are bounded above, not claimed shortest.

## Universal correctness and evidence separation

**Literal integer transport:** In each displayed edge use
`w'=Mw+P_bottom(j)-P_top(i)` with
`M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y)`.
FIRST prefix is 0; for RUN i, a parent x/y uses
`(1,0,i-1)`, parent c uses `(0,1,i-1)`.
For LAST use `(1,0,A)` for x, `(1,0,N)` for y,
`(0,1,n)` for c. Substitution gives each of the displayed
**constant** oriented five-tuples, identically over `Z[k,t]`.
No empirical parameter interpolation is used. Every required
RUN/LAST index inequality follows from the designated parameter
chamber, `n>=3`, `d>=5` and `A=n+d`; the two
n=3 and k=0 typed endpoint exceptions are explicit.

**Strict geometry:** Each intermediate label has one of a finite set
of shifts in normalized units:
`0, h, -h, 2h, 3h, 1-h, 1-2h, -3h, 1-3h,
rho, zeta, -1+zeta, -rho-2h, -rho-3h,
-1-rho, -1-rho-3h, -1+2h, -1+v,
1+v, 1-3h, 1-2h`.
Check each against the actual source/target types
`-L(bottom)<s<L(top)`; all are strict using the inherited
`0<h<1/5`, `0<zeta<rho<1`, `0<v<1`,
`Lx=2+rho`, `Lc=1+h`, and `n>=3`.
In particular the potentially delicate `-rho-2h=-v`
is > -1, and `1+v<Lx` because `2h<1`.
Every final edge is an equal-type zero-offset y/y child.
No assertion of internal *newborn* placement beyond strict overlap
is added here.

**Finite independent replay:** The new Python oracle composes the
actual six-label CY star from #414 with **every indexed first choice**
and verifies every intermediate typed child using the existing
literal-word, Parikh and exact Fraction/Perron geometry engine.
Its 117-member grid in both orientations covers **6,318 actual
indexed first choices** and **22,758 replayed composite path edges**.
These counts test implementation; the universal conclusion rests
on the distinct symbolic chamber argument above, and awaits
independent review/formalization.

**Nonclaims:** This does not show that all *later* child choices
of any descendant are productive, that the 12-label CY image is
closed, that every cyclic strict-zipper state is covered, or that
BH/#139, A1-prime, G1, plus/non-unit realization or PSC holds.


## Executable universal affine-transport certificate (added in consolidation)

`oracles/python/class_a_boundary_cy_symbolic_transport.py` now
checks all 60 (six target states × ten disjoint rectangular parameter
chambers) selected paths coefficientwise as **affine integer identities
in k,t**. Unlike the independent 117-member geometry replay, this
certificate evaluates no finite interpolation to infer an all-parameter
identity. For every symbolic edge it classifies the *actual* FIRST/RUN/LAST
letter, verifies the index lies in the correct word for every parameter
in that chamber (including recession-slope guards), recomputes the
proper prefix Parikh vectors, and verifies all three target coordinates
exactly. Negative tests reject a negative unbounded index slope and a
forged typed target.

Strict Perron geometry is still justified by the explicit inequalities
above, with independent exact-Fraction numerical-instance replay; this
affine certificate alone does not prove every inequality and earns no
Lean/native Mojo proof credit. The ten cases are a disjoint cover:
`(0,0)`, `(k>=1,t=0)`, `(k=0,1,2,t=1)`,
`(k>=3,t=1)`, `(k=0,1,2,t>=2)`,
`(k>=3,t>=2)`.


## Executable universal strict-overlap certificate (added)

The exact-affine transport checker is complemented by
`oracles/python/class_a_boundary_cy_symbolic_geometry.py`.
All physical shifts and tile lengths are integer-affine in
`h=1/beta` and `rho=alpha-h`:
`Lx=2+rho`, `Lc=1+h`, `Ly=1`.
The inherited root inequalities imply the *open* rational polygon
`0<h<1/5`, `h<rho`, `rho+2h<1`.
Its closure has the four rational vertices
`(h,rho)=(0,0),(0,1),(1/5,1/5),(1/5,3/5)`.
For every constant typed label on every selected chamber path, both
strict margins `s+Lbottom` and `Ltop-s` are affine.
Checking they are nonnegative on **all four vertices** and
not identically zero proves strict positivity throughout the open
polygon; the checks use exact rational arithmetic.

The path registry has **35** distinct base oriented labels and
**61** after their true reversals. All **122** strict physical
margins pass the universal rational-polytope certificate.
The output is conditional on the established root inequalities;
it does not independently prove that the Perron root lies in the
polygon. The combined two independent algebraic verifiers now
cover actual types/index bounds/full Parikh transports and strict
physical overlap for every chosen universal path. The 117-member
literal-word Fraction replay remains an independent implementation
cross-check, not the source of the quantified proof.
