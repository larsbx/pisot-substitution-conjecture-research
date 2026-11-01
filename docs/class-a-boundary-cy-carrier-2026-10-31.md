# Complete CY six-label star and four-step selected exit (minus class A)

**Status:** new scoped **hand symbolic derivation**, supported by a separate
independent exact literal-word/Fraction oracle. Independent human
review and any formal/Mojo proof-bank promotion remain pending.
This is not a closed carrier, universal BH or PSC proof.

## Hypotheses and physical normalization

Work for all integers `k,t>=0` in the minus boundary:
`n=k+t+3`, `d=2n-1-k`, `A=n+d`, `N=n-1`,
`x -> x y^A x`, `c -> c y^n x`, `y -> x y^N c`.
All ordered indices start at zero. Parikh coordinates are bottom-minus-top
in the order `(x,c,y)`. Genuine children require **strict** physical
interior overlap and actual typed word occurrence indices.

Let `h=1/beta`, `alpha=beta-(n+2)`,
`rho=alpha-h`, `zeta=alpha-2h=rho-h`.
Reuse the existing exact Perron certificates
`0<h<1/5`, `0<zeta<rho<1`,
`a=Lx/Ly=2+rho`, `b=Lc/Ly=1+h`.
Take `Ly=1`. No independent-length assumption.

The new source is **CY** `(c,y,0,-2,2)`, the true
`Y0=(y,y,1,-1,-1)` LAST/RUN `(n,k+2)` child. It has
physical bottom-minus-top shift `s=-2b+2=-2h`;
because `-1<-2h<b`, CY is a strict c/y overlap.
Its inflated shift is the **exact integer `G=beta*s=-2`**.
Its incidence transport is `M(0,-2,2)=(0,0,-2)`.

## Complete nine FIRST/RUN/LAST physical guards

The top c word has FIRST prefix 0, RUN i prefix start
`b+i-1=h+i` for `1<=i<=n`, LAST x at `b+n`
with ordinal `n+1`. The bottom y word has FIRST x prefix
0, RUN j start `a+j-1` for `1<=j<=N`, LAST c
at `a+N` with ordinal `n`.

For a child at `(i,j)`, use
`D=G + prefix_bottom(j)-prefix_top(i)`
and require `-length(bottom_child)<D<length(top_child)`.

| Actual kind | D in Ly units | Exactly accepted ordered indices |
| --- | --- | --- |
| FIRST/FIRST | `-2` | `(0,0)` (since `a>2`) |
| FIRST/RUN | `rho+j-1` | `(0,1)` only |
| FIRST/LAST | `n-1+rho` | none |
| RUN/FIRST | `-2-h-i` | none |
| RUN/RUN | `-1+zeta+j-i` | `j=i` or `j=i+1`, clipped to `1<=i<=n`, `1<=j<=N` |
| RUN/LAST | `n-i-1+zeta` | `(n-1,n)`, `(n,n)` |
| LAST/FIRST | `-2-b-n` | none |
| LAST/RUN | `-2+zeta+j-n` | none |
| LAST/LAST | `zeta-2` | none |

**Why no hidden endpoints:** At FR `j=2`, the shift is
`1+rho>b` because `rho-h=zeta>0`.
For RR, `0<zeta<1` makes exactly the two integer diagonals
strict. For RL, `0<zeta<1` selects precisely `n-i=0,1`.
At LL, the lower margin would require `zeta+h>1`,
but `zeta+h=rho<1`. Every omitted remaining kind lies
strictly beyond the relevant interval by the displayed inequalities,
using `n>=3`, `2<a<3`, `1<b<6/5`. Thus no boundary
contact is counted as a child.

## Full typed Parikh labels and count

Since `M(CY)=(0,0,-2)`, add the **literal** proper-prefix
difference, not a quotient-state guess.

| Kind | Actual index family | Full typed child |
| --- | --- | --- |
| FF | `(0,0)` | `(c,x,0,0,-2)` |
| FR | `(0,1)` | `(c,y,1,0,-2)` |
| RR | `(i,i)`, `1<=i<=n-1` | `(y,y,1,-1,-2)` |
| RR | `(i,i+1)`, `1<=i<=n-2` | `Y0=(y,y,1,-1,-1)` |
| RL | `(n-1,n)` | `(y,c,1,-1,-1)` |
| RL | `(n,n)` | `(y,c,1,-1,-2)` |

There are `1+1+(n-1)+(n-2)+2=2n+1` **indexed**
children for every `k,t>=0`. Exactly six distinct
typed labels occur at every member; the real reversal supplies
six distinct additional labels, a **12-label** oriented image.
This is an outgoing image, not a forward-closed carrier.

## Selected coincidence path and productive cycle

CY has a genuine uniform first edge
`CY(1,2)->Y0`, because `j-i=1` is one
of the exact RR diagonals for every `n>=3`.
Reuse the #412 accepted selected Y0 path:

`CY --(1,2)--> Y0 --(t+1,1)-->
B=(y,y,0,-2,3) --(n-1,0)-->
RH=(y,x,0,1,-1) --(2,1)--> C=(y,y,0,0,0)`.

All four transitions are actual typed, strictly overlapping
occurrence-indexed children under the inherited exact hypotheses.
The first transition and all CY children are derived above;
the remaining three have their previously recorded symbolic
certificates in `docs/class-a-boundary-tx-carrier-2026-10-28.md`.

Conversely, Y0 has the actual uniform LR child
`Y0(n,k+2)->CY`. Hence **Y0<->CY is a genuine
uniform two-cycle with a productive exit**. It rules out a
strictly decreasing rank on every actual edge but is not a
closed obstruction to existential coincidence.

## Replay / guarded non-claims

New independent oracle
`oracles/python/class_a_boundary_cy_children.py`
compares **every literal ordered pair** against the nine-kind
table and exact Fraction/Perron geometry on 117 members in
both orientations. Expected: 234 oriented source cells,
53,976 literal pairs, 6,318 strict indexed children, 12
distinct labels and 936 selected-path edges. Every selected
path and true reversal is checked. Negative controls reject
a word-legal but disjoint FR(0,2), a false LL occurrence,
nonexistent indices, changed typed targets and damaged
selected packets. This finite replay is independent validation;
the unbounded statement relies on the symbolic guard proof above.

This proves one source's **complete first-choice star**
and a **selected** four-step typed exit. It does **not**
prove every CY child is productive; the c/x, c/y and y/c
descendants need their own known-suffix or complete-star
coverage. It does not prove all-source cyclic strict-zipper
coverage, forward closure, target-aware BPA, BH/#139,
A1-prime, G1, plus chambers, or general PSC.

The open #413 two-image review queue includes both orientations
of CY. Once this new result is accepted, those two can be marked
complete-star certified in the *same scoped registry* (34 -> 32),
but #413's immutable snapshot must not be retrospectively rewritten
and the new 12-label image may open further frontier states.
