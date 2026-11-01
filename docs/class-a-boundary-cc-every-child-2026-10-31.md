# CC every-first-choice productivity: bounded selected typed exits

**Integration candidate (2026-11-01):** canonical native counterparts and
fresh cross-checks are recorded in
[the research integration audit](research-branch-integration-2026-11-01.md).
The original 2026-10-31 scopes and main/research distinctions below are
historical; they do not imply acceptance of this candidate. Exact-head
hosted acceptance remains required. Independent human review is pending.
Pending human review is validation debt, not an additional premise for
project acceptance once mathematical, replay, CI and governance checks pass.

**Status:** scoped all-parameter *hand derivation* backed by
independent literal-word/Fraction finite replay and an executable
exact rational-convex strictness check. Stacked on PR #416's
complete four-occurrence CC star. No formal Lean/Mojo proof
credit, independent human review, forward-closed carrier or
universal BH/PSC claim.

## Scope and statement

In the minus class-A boundary chamber `k,t>=0`,
`n=k+t+3`, `d=2n-1-k`, `A=n+d`,
with actual words
`x->x y^A x`, `c->c y^n x`, `y->x y^(n-1) c`,
let `CC=(c,c,0,-2,3)`.
Its complete strict star from #416 consists of exactly
four indexed children (eight across reversals):

| Initial actual address | Typed child |
| --- | --- |
| `(n,0)` | `YC=(y,c,1,0,-2)` |
| `(n+1,0)` | `XC=(x,c,1,0,-3)` |
| `(n+1,1)` | `XY3=(x,y,1,1,-3)` |
| `(n+1,2)` | `XY2=(x,y,1,1,-2)` |

Each has a selected coincidence continuation of **at most four
further edges**, so **every actual CC first choice** has a
typed-coincidence completion within **five edges total**.
This does not say every later edge choice terminates.

## Complete bounded selected paths

Canonical names are oriented five-tuples; all listed addresses
are true zero-based substitution-word occurrences. In the
following, `C=(y,y,0,0,0)`, `Q=(y,x,0,-1,1)`,
`J=(y,y,0,2,-2)`.

**YC: three edges, every k,t.**
`YC -(t+1,0)-> (y,c,-1,-2,4)
   -(0,t+4)-> Z -(4,1)-> C`,
where `Z=(x,x,0,3,-3)` for `k=0` (the
second address t+4=n+1 is ALWAYS the LAST x), and `Z=(x,y,0,3,-3)`
for `k>=1` (true RUN y). Both lead to C.

**XC: three or four edges.**
- `k=0`: `XC -(0,4)-> T
  -(0,0)-> (x,x,1,3,-4)
  -(d+4,0)-> R -(1,2)-> C`, with
  `T=(x,x,-1,-2,5)`, `R=(x,x,0,-1,1)`
  at `t=0`, and `T=(x,y,-1,-2,5)`,
  `R=Q` at `t>=1`. This protects both
  actual LAST/RUN boundaries.
- `k=1`: `XC -(0,4)-> (x,y,-1,-2,4)
  -(0,n)-> (x,c,1,2,-3)
  -(d+4,1)-> C`.
- `k=2`: `XC -(0,6)-> T
  -(2,0)-> (y,x,0,3,-3) -(4,1)-> C`,
  with `T=(x,x,-1,-2,5)` at `t=0`
  and `T=(x,y,-1,-2,5)` at `t>=1`.
- `k>=3`: `XC -(0,k+3)-> (x,y,-1,-2,4)
  -(1,t+5)-> J -(3,1)-> C`.
  Note: `k+3`, **not** constant 6,
  is the actual correct RUN ordinal for all k>=3.

**XY3: two edges except at the sole n=3 member.**
- `n>=4`: `XY3 -(t+4,1)->
  (y,y,0,-2,2) -(1,3)-> C`.
- `n=3` (k=t=0): the second y at index 3
  is actually the LAST c, so use the four-edge
  exit `XY3 -(4,1)-> (y,y,0,-2,2)
    -(0,2)-> (x,y,1,0,-1)
    -(d+1,0)-> Q -(1,2)-> C`.

**XY2: two edges, every k,t.**
`XY2 -(d+2,0)-> Q -(1,2)-> C`.
This is the selected path in #416.

## Universal algebraic basis and strict geometry

For each step, the full bottom-minus-top Parikh update is
`w'=Mw+P_bottom(j)-P_top(i)` in `Z[k,t]`,
using actual FIRST/RUN/LAST prefixes of the three literal
substitution words. The cases above are disjoint and
exhaustive over `k,t>=0`: split `k=0,1,2,>=3`,
`t=0` versus `t>=1`, and isolate `n=3`.
All stated typed five-tuples follow from direct
coefficientwise cancellation. Every RUN and LAST
bound follows from `n=k+t+3`, `d=k+2t+5`,
`A=n+d`; notably `d+4=A+1` only
when n=3, and `t+4=n+1` exactly for k=0.

All selected intermediate physical shifts and
strict margins are *affine* in
`h=1/beta` and `rho=alpha-h` with
`Lx=2+rho`, `Lc=1+h`, `Ly=1`.
The inherited exact bounds imply the open polygon
`0<h<1/5`, `h<rho`, `rho+2h<1`.
Checking the four rational closure vertices
`(0,0),(0,1),(1/5,1/5),(1/5,3/5)`
proves strict overlap for all path states.
The executable checker covers **20** base
oriented states, **37** including true reversals
and **74** exact positive strict margins.
This is conditional on the inherited Perron
bounds, not a new root localization theorem.

## Finite independent replay / status boundaries

`oracles/python/class_a_boundary_cc_every_child.py`
independently replays each complete CC first choice,
every intermediate literal occurrence, every integer
Parikh coordinate, exact rational Perron geometry and
actual reversals across 117 parameter specimens:
234 oriented CC source cells, 57,486 ordered pairs,
936 indexed first choices and **3,298**
composed path edges, maximum length **five**.

This finite grid validates the implementation but
does not establish the unbounded hypotheses; those
are separate symbolic arguments above.
No all-later-choice productivity, full strict-zipper
coverage, forward closure, global BH, A1-prime, G1,
plus/non-unit realization or PSC is inferred.
The Y0->CC parent edge remains strict only
at `t=0`; uniform CC productivity does not
supply Y0 reachability via that edge for t>0.


## Executable coefficientwise universal occurrence checker

`oracles/python/class_a_boundary_cc_symbolic_transport.py`
independently encodes all **eight disjoint integer parameter
chambers** (k=0,1,2,>=3, each with t=0 or t>=1) and all
**four CC first-choice targets**. It checks each of the
**32 full selected paths starting at CC**, not just the
continuation after the first choice.

For each edge it verifies the genuine FIRST/RUN/LAST type
and word index, including nonnegative affine guard coefficients
at infinite chamber recession directions, recomputes the
actual proper prefix Parikh vector and proves the complete
five-coordinate target identity coefficientwise in
`Z[k,t]`. The maximal certified full path is five edges.

The separate exact rational-polytope checker above proves
strict physical intersection under the inherited root
inequalities; the 117-member literal-word/Fraction oracle
is an additional differential regression. These checks
are inspectable arithmetic certificates, **not** a Lean
kernel theorem, a BH argument or a substitute for
independent review.
