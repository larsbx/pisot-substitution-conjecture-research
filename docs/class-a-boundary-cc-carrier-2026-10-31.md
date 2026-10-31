# CC: a four-occurrence star and three-edge typed exit (minus class A)

**Status:** scoped universal *hand symbolic* classification, with an
executable integer-polynomial path-transport check and separate exact
literal-word/Fraction replay. Not a forward-closed carrier, every-child
productivity theorem or general PSC/BH claim. No Lean/Mojo proof credit.
Independent human review pending.

## Exact chamber and source

For `k,t>=0`, put `n=k+t+3`, `d=2n-1-k`, `A=n+d`.
The literal substitutions are
`x->x y^A x`, `c->c y^n x`, `y->x y^(n-1) c`.
A label records (top,bottom, bottom-minus-top Parikh x,c,y).
True reversal swaps top/bottom and negates all three coordinates.

`CC=(c,c,0,-2,3)` is the actual Y0 LAST/LAST child
`Y0(n,n)->CC` **only at t=0**. For other parameters,
this word-occurrence child exists but is not a strict overlap.
The source CC itself is a strict c/c physical overlap for every
`k,t>=0`, even when it is not obtained by this Y0 edge.
Do not promote reachability outside the t=0 endpoint.

Normalize `Ly=1`, `h=1/beta`, `rho=alpha-h`.
Inherited exact root certificates give
`0<h<1/5`, `h<rho`, `rho+2h<1`.
Then `Lx=a=2+rho`, `Lc=b=1+h`,
`alpha=rho+h`, and
`s(CC)=3-2b=1-2h`.
Therefore the inflated shift is the exact affine quantity
`G=beta s=beta-2=n+alpha`.

## Complete nine-kind occurrence table

Each c image has FIRST c at 0, RUN y at ordinals
`1..n` (prefix starts `b+i-1=i+h`), and LAST x at
`n+1` (prefix start `b+n`). For a child (i,j),
`D=G+prefix_bottom(j)-prefix_top(i)` and
`-L(bottom_child)<D<L(top_child)`, strictly.

| Kind | Exact shift D | Surviving indices |
| --- | --- | --- |
| FIRST/FIRST | `n+alpha` | none |
| FIRST/RUN | `n+alpha+j+h` | none |
| FIRST/LAST | `2n+alpha+b` | none |
| RUN/FIRST | `n+rho-i` | `(n,0)` |
| RUN/RUN | `n+alpha+j-i` | none |
| RUN/LAST | `2n+alpha-i+1` | none |
| LAST/FIRST | `rho-1` | `(n+1,0)` |
| LAST/RUN | `alpha+j-1` | `(n+1,1)`, `(n+1,2)` |
| LAST/LAST | `n+alpha` | none |

Every exclusion is strict from `n>=3`, `0<rho<1`,
`0<alpha<1`, `0<h<1/5`; notably LAST/RUN
`j=3` gives shift `2+alpha>a=2+rho`, while
RUN/RUN `i-j<=n-1` gives `D>=1+alpha>1`.
RUN/FIRST `i=n-1` gives `D=1+rho>1`.

## All typed Parikh targets

`M(CC)=M(0,-2,3)=(1,1,n-3)`.
Use each literal proper prefix and the full
`w'=Mw+P_bottom-P_top` integer update:

| Actual address | Child |
| --- | --- |
| `(n,0)` | `(y,c,1,0,-2)` |
| `(n+1,0)` | `(x,c,1,0,-3)` |
| `(n+1,1)` | `(x,y,1,1,-3)` |
| `(n+1,2)` | `(x,y,1,1,-2)` |

Thus there are **exactly four indexed strict children**,
all distinct, for every minus-chamber member, with four
distinct actual reversed child labels: **8 oriented labels**.

## Uniform three-edge coincidence exit

Choose the actual LAST/RUN child `(n+1,2)`:

`CC -(n+1,2)-> (x,y,1,1,-2)
    -(d+2,0)-> Q=(y,x,0,-1,1)
    -(1,2)-> C=(y,y,0,0,0).`

At the first step the relative shift is `1+alpha`,
whose upper margin against `Lx` is
`a-(1+alpha)=1-h>0`.
At Q, the shift is `-h` and the final typed y/y
child has zero displacement. The word ordinals are
valid: `n+1` is genuinely LAST x for c, `2`
is RUN y for c, and `d+2<=A` is RUN y for x,
including the `n=3` endpoint. The independent exact
`Z[k,t]` coefficient checker verifies the three
proper-prefix transport identities. The third
transition reuses the established canonical Q->C certificate.

The existence of this selected three-edge exit is
**not** a claim of productivity of every CC child.

## Independent evidence, controls and nonclaims

`oracles/python/class_a_boundary_cc_children.py` independently
checks every literal ordered pair and exact Perron
strictness for `0<=k<=12`, `0<=t<=8`, in both
actual orientations: 117 members, 234 source cells,
57,486 ordered pairs, 936 strict indexed children,
702 selected-path edges, eight image labels.
Negative controls refuse invalid indices, disjoint
FIRST/FIRST and LAST/LAST, changed intended labels
and the `t>0` noninterior Y0 endpoint.

No unbounded inference is drawn from the 117 finite
members; the unbounded star follows from the explicit
nine-kind inequalities and polynomial transports above.

No closed carrier, all-first-choice productivity of CC,
global seed reachability, every cyclic strict zipper,
target-aware BH, A1-prime, G1, plus/non-unit realization,
or general PSC is asserted. The next obligation is to
reconcile these four child labels with the source
registry and prove their productive continuations
individually rather than guessing a carrier.
