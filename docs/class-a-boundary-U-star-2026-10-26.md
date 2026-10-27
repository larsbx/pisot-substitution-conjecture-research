# Class A boundary: complete actual outgoing star of U=(x,y,1,2,-3)

**Status:** scoped symbolic uniform-in-k,t theorem and reproducible real-word/geometry crosscheck, stacked on PR #349's complete 50-label T_m image. No global carrier closure, no rank, no BH, and no claim promotion. Independent human review pending. Reuse the accepted [three-source stop/go](class-a-boundary-child-carrier-2026-10-26.md): balanced-pair algorithms cannot silently assume realization or unimodularity; non-unit internal coordinates are distinct from physical overlap.

## Work shown

### Assumptions and hypotheses
Minus sign class A only: `eps=-1, k,t>=0, n=k+3+t>=3, d=2n-1-k`; images `x->xy^(n+d)x`, `c->cy^nx`, `y->xy^(n-1)c`. Let `beta>n+2` be the certified Perron root, `u=d/(beta-1)`, `b=Lc/Ly=1+1/beta` and `a=Lx/Ly=b+u`. Earlier #347 proves `1<u<2`. Source U has literal tile types (x,y), full bottom-minus-top Parikh vector (1,2,-3), and normalized physical shift `a+2b-3=u+3/beta`.

### Derivation / reduction
**Actual ancestry.** From aligned swap seed `(x,c,0)`, choose run pair `(i,j)=(1,2)`: its actual y/y child is `T1=(y,y,-1,1,1)`. Next choose its top first and bottom y-run `(0,t+1)` to get exactly `U=(x,y,1,2,-3)`. Both parents and children are strict real overlaps in every minus boundary chamber, by the already proved #347 and #349 index/geometry guards. The canonical Mojo kernel also checks all three symbolic Parikh coordinates in `Q[t,k]`, and the native regression replays the literal two-edge ancestry for each test member.

**Physical geometry.** In units of `Ly`, U is genuinely interior: its shifted bottom y starts at `u+3/beta>0`, but `a-(u+3/beta)=1-2/beta>0`. After inflation its offset is
[
B=\beta(u+3/\beta)=d+u+3.
]
The top image has starts `0` (first x), `a+i-1` (run y, 1<=i<=n+d), and `a+n+d` (last x). The bottom y-image has starts `B` (first x), `B+a+j-1` (run y, 1<=j<=n-1), and `B+a+n-1` (last c). Intersect their literal open intervals, retaining the actual ordinal pair:

| Top/bottom kind | Exactly the admitted ordinals | Target letter types, full Parikh offset |
|---|---|---|
| first/anything | none | — |
| run/first | `i=d+2..min(d+5,n+d)`, `j=0` | `(y,x,0,-1,d+4-i)` |
| run/run | `i=j+d+4` for `j=1..n-4`; or `i=j+d+5` for `j=1..n-5` | `(y,y,1,-1,d+3+j-i)` |
| run/last | none | — |
| last/first | `(n+d+1,0)` iff `n<=4` | `(x,x,0,-1,3-n)` |
| last/run | `i=n+d+1`, `j=max(1,n-4)..n-1` | `(x,y,1,-1,j+2-n)` |
| last/last | none | — |

All empty intervals are genuinely empty, and all endpoints are strict. The matrix calculation is
[
M(1,2,-3)^T=(1,-1,d+3)^T.
]

For run/first, the strict guard is `B-a<i<B+1`; because `B-a=d+2-1/beta` and `B+1=d+u+4`, it rounds to `d+2<=i<=d+5`, subject to the *literal* top bound `i<=n+d`. For run/run the relative shift is `B+j-i`; `B in (d+4,d+5)` gives exactly the two index differences `i-j=d+4,d+5`, with the true bottom run bound `j<=n-1` and top bound `i<=n+d`. Run/last is impossible since its bottom start exceeds the top run end by more than 1. For last/first the start difference is `2-n-1/beta`; the lower overlap guard is equivalent to `u>n-3`, which holds exactly for `n=3,4` because `1<u<2`. For last/run the difference is `u+j+2-n`: `-1<...<a` rounds to `n-4<=j<=n-1`, with actual `j>=1`. Last/last is disjoint since its positive offset exceeds the x length by `2-b>0`. The first x ends before the first bottom x begins because `B-a=d+3-b>0`.

**Uniform exact count and image.** The four nonempty kinds have exactly
[
oxed{2n-1}
]
ordered child occurrences for *every* admissible `n>=3`, counting run/run multiplicities. The union of normalized targets over the chamber is exactly **12 typed labels**: (y,x,0,-1,-1..2), (y,y,1,-1,-2..-1), (x,x,0,-1,-1..0), and (x,y,1,-1,-2..1). All 12 are attained at finite valid actual ordinals. The y/y source branch is *not* declared closed, and the c=-1 coordinate is not a descending rank.

### Evidence and replay
`kernel/psc/class_a_boundary_U_star.mojo` constructs the parameter-uniform symbolic ancestry and typed first/run/last exact guard, enumerating only O(n) valid occurrences instead of all Cartesian pairs, and refuses a count or target-envelope mismatch. `kernel/tests/test_class_a_boundary_U_star.mojo` crosschecks **every** Cartesian pair in 24 specimens against exact Perron interior geometry and literal Parikh transport, retaining multiplicities; it also verifies the two-step genuine ancestry and rejects tampered packets. Independent `oracles/python/class_a_boundary_U_star.py` checks all pairs in 72 members with a bounded rational sign-refinement oracle; `tests/test_class_a_boundary_U_star.py` ensures counts and rejects nonexistent ordinals. Dedicated head-specific workflow `.github/workflows/class-a-boundary-U-star.yml`.

Run from root:
```sh
python -m pytest -q tests/test_class_a_boundary_U_star.py
```
From `kernel/`:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_U_star.mojo
pixi run --locked mojo run -I . class_a_boundary_U_star.mojo
```
No hosted run is presumed before its actual result is inspected.

### Negative controls
The first/anything, run/last and last/last pairs are geometrically disjoint despite word-valid ordinals. Run/run is **empty at n<=4**, so it cannot be inferred from the formula absent word bounds. Last/first exists only n=3,4 and must disappear at n=5. An erroneous reduction of the top or bottom ordinal ranges would change the strict `2n-1` count; native full-Cartesian tests detect it. Tampered Parikh coordinates and nonexistent ordinals refuse rather than falling through to a projected adjacency graph.

### Non-claims / remaining gaps
Only the actual outgoing star of the reachable second-generation source U is resolved. The resulting twelve labels are not a proved forward-closed carrier, nor has every seed-reachable cyclic strict zipper been given an offset-zero descendant. The other 49 members of the two-level T_m image are not covered by this theorem. No C4 ordered hub-residual word theorem, universal BH/#139, A1′/#138, G1 or PSC is proved. No independent human review claimed. Next: construct exact children for the other 49 labels, discover common affine envelope/typed descent, and prove productive witnesses; do not mistake the new 2n−1 count for uniform convergence.
