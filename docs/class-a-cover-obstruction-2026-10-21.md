# Class A: a rectangular run-index cover is not child-closed

Status: scoped written argument with exact Mojo identities; independent human
review pending. This is a countermodel to a proposed cover, not to boundary
hitting, and does not close #139 or any remaining class-A/C obligation.

## Target and literature decision

Continue the vertex-family target of
[p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md).
That note's targeted Akiyama–Lee, Minervino–Thuswaldner and Barge review applies:
finite overlap decisions do not supply a uniform family cover, non-unit finite
places cannot be discarded, and the initial-letter hypothesis still fails.
Proceed only with an exact test of a proposed forward cover, preserving the
formal-versus-seed-reachable distinction. The side-notes ledger's class-D
formal-cycle countermodels make that distinction essential here too. This
continuation imports no new literature theorem and makes no novelty claim for
changing eigenvector coordinates.

## Normalized geometry and the proposed cover

Use the same class-A line, letters `(x,c,y)=(0,1,2)`, strict interior geometry,
and bottom-minus-top displacement as the run-index note:

`x -> x y^(n+1) x`, `c -> c y^n x`, `y -> x y^(n+1) c`, `n>=4`.

Its Perron root satisfies `n+2 < beta < n+3`. Put `h=1/(beta-1)`.
Then `0<h<1/(n+1)<=1/5`, and the cubic becomes

\[
P(n,h)=h^3+(n+1)h^2+(n+1)h-1=0.
\]

With the y-length normalized to one, the lengths are
`ell_c=1/(1+h)` and `ell_x=ell_c+h`. Multiplying all lengths by `1+h`
gives `L=(1+h+h^2,1,1+h)`. For each incidence column, the exact residual
`h (M^T L)_j - (1+h)L_j` is `P(n,h)`, binding these lengths to this
substitution, rather than to an approximate root.

Write an integral offset as `w=(k,s-y-k,y)`, where `s=sum(w)`. Its scaled
physical displacement is

\[
T=(1+h)\ell\cdot w=k h(1+h)+s+yh.
\]

The proposed rectangle is the set of all strictly real typed overlaps with
`|k|<=n+1`, `|y|<=2`, and `|s|<=1`. This is a proposed formal superset;
none of its conditions asserts seed reachability. The needed cover property
would include every real ordered occurrence child of every nonterminal
member. Existential productivity inside a pruned graph would not prove that
property.

## Uniform escaping edge

**Proposition (repository-proved, scoped written argument with coefficient-checked
Mojo identities; independent human review pending).** For every integer `n>=4`,
the proposed rectangle is not forward closed.

An explicit witness, with zero-based occurrence indices, is

\[
V_n=(x,c,-n-1,n+4,-2)
\quad\xrightarrow{(0,3)}\quad
W_n=(x,y,-n,n+3,-1).
\]

The source has `s=1`, `k=-n-1`, `y=-2`. The top index zero selects the
first x. The bottom index three selects y in `sigma(c)`, with proper prefix
`c y^2`; it exists for every `n>=4`. Direct multiplication gives
`M(-n-1,n+4,-2)=(-n,n+2,-3)`. Adding the bottom prefix `(0,1,2)` gives the
claimed child, whose sum is **2**. Its other two rectangle bounds still hold.

Both geometries are strictly interior, not boundary contacts. Reducing modulo
`P(n,h)` gives `T_V=h^3-2h` and `T_W=1+h^2+h^3`. The four margins are:

| Margin | Exact expression | Positive because |
| --- | --- | --- |
| Source left, `T_V+L_c` | `1-2h+h^3` | `h<1/5` |
| Source right, `L_x-T_V` | `1+3h+h^2-h^3` | `0<h<1` |
| Child left, `T_W+L_y` | `2+h+h^2+h^3` | `h>0` |
| Child right, `L_x-T_W` | `h-h^3=h(1-h)(1+h)` | `0<h<1` |

The Mojo implementation checks the transformed cubic, all three length
identities, the occurrence identity, both displacement reductions, and the
margin factorization by exact polynomial arithmetic. Those identities and
the displayed rational inequalities prove the statement for arbitrary n;
finite replay is a separate calibration.

## Evidence, controls and remaining work

Canonical implementation: `kernel/psc/class_a_cover_obstruction.mojo`.
The regression replays the real edge at n=4,8,18,64,256 with the existing
Perron-field engine. Wrong occurrence indices, reversed displacement and
changed child type must refuse. A damaged symbolic occurrence identity must refuse.
At n=4 and n=18, separate complete canonical seed graphs omit both witnesses;
that is finite nonmembership only, not a uniform seed-exclusion theorem.

Replay with the repository lock:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_cover_obstruction.mojo
```

The scope is precisely the failed rectangular forward-cover reduction.
It says neither that reachable sums escape nor that either witness fails to
hit. A useful complete cover must retain correlations between tile types,
run index and offset coordinates, or prove a different forward invariant.
The prior explicit reachable family and its parameter-dependent descent remain
valid. Class-D acceptance is unchanged. All-state arbitrary-n class-A hitting,
the remaining A/C domains, and universal #139 remain open.
