# Recovery of the occurrence-indexed class-A U internal hit

**Status:** scoped constructive selected-path recovery from PR #354; no new
PSC, BH, cyclic-zipper or all-child productivity claim. Independent human
review remains pending. The seven source files in this change are retained
as their exact historical blobs from PR #354 head
`89675acc6a6c89e88f695f1e20072528b9e52a85`, merged only into
`research/class-a-boundary-u-2026-10-26`, not into the current main.
The original exact-head [U-hit hosted run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/40533358980)
completed successfully; that acceptance is historical and does not
replace fresh main-based CI.

## Canonical oriented states and aliases

A state is **identified by** `(top,bottom,dx,dc,dy)`, not its nickname.
Actual reversal is `R(a,b,p,q,r)=(b,a,-p,-q,-r)`.

| Canonical oriented tuple | Historical labels |
| --- | --- |
| `(x,c,0,0,0)` | aligned seed `S` |
| `(y,y,-1,1,1)` | `T_1` on main |
| `(x,y,1,2,-3)` | U in #354 (not P3-family U) |
| `(y,x,0,-1,1)` | `V1` in #354; `Q` on main; `T` in #372 |
| `(y,y,0,0,0)` | typed coincidence `C` |
| `(y,x,0,-1,2)` | distinct state `V` on main; **never** an alias of V1 |

Neither old source names nor archived records are rewritten. The oriented
tuple and actual ordered occurrence indices are authoritative.

## Universal occurrence/transport audit

Assume exactly minus class A, integers `k,t>=0`,
`n=k+t+3`, `d=2*n-1-k=k+2*t+5`, `A=n+d`, and
`x->x y^A x`, `c->c y^n x`, `y->x y^(n-1) c`.
The incidence matrix with columns x,c,y and rows x,c,y is
`M=[[2,1,1],[0,1,1],[A,n,n-1]]`.
The ordered child offset is
`w'=M*w + P_bottom(j)-P_top(i)`, for proper literal prefixes.

| Source | Actual top/bottom ordinals | Prefix difference | Exact target |
| --- | --- | --- | --- |
| `(x,c,0,0,0)` | `(1,2)` | `(-1,1,1)` | `(y,y,-1,1,1)` |
| `(y,y,-1,1,1)` | `(0,t+1)` | `(1,0,t)` | `(x,y,1,2,-3)` |
| `(x,y,1,2,-3)` | `(d+3,0)` | `(-1,0,-d-2)` | `(y,x,0,-1,1)` |
| `(y,x,0,-1,1)` | `(1,2)` | `(0,0,1)` | `(y,y,0,0,0)` |

Each identity simplifies in `Z[k,t]`, not by extrapolating finite
specimens. Word bounds hold for every `k,t>=0`:
`1<=t+1<=n-1`, `1<=d+3<=A`, and each final run
index is a genuine run. There is no substitution of a quotient edge
for an actual letter occurrence.

For physical strictness normalize `L_y=1`, let
`b=L_c=1+1/beta`, `u=d/(beta-1)`, `a=L_x=b+u`.
Use the *inherited* exact Perron constraints
`beta>n+2>=5`, `1<u<2`, `beta=a+n-1+b`.
The successive parent shifts are `0`, `1-u`,
`u+3/beta`, `-1/beta`; these are strictly overlapping.
In particular `a-(u+3/beta)=1-2/beta>0`.
In the final inflated y/x parent, top y-image run #1 and bottom
x-image run #2 both begin at `a`; the common y interval `[a,a+1]`
has strict interior bounds `0<a` and `a+1<beta`.
Thus this is an **internal** equal-type, zero-offset child.

## Replay and proof boundary

The original Mojo symbolic certificate calls `symbolic_child`
coefficientwise over `Q[t,k]`, and the original literal independent
oracle checks exact Parikh, Perron geometry and an incorrect-last-address
negative control. The added 117-member regression independently replays
*all four* actual child addresses and the real reversed edges, using the
shared `Geometry`; it is explicitly a **finite regression**, not the
universal proof. The universal derivation above is separate from its replay.

No old side-notes ledger lines or receipts are overwritten. #354's
source and acceptance provenance remain linked in history. The result
proves only one selected four-step seed lineage and U's two-step hit.
In particular it does not prove forward closure, all-state boundary
hitting, a decreasing rank on every edge, target-aware BPA or PSC.
