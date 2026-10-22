# Class A: exact uniform forward closure of the typed affine carrier (2026-10-22)

**Status:** Repository-proved scoped **all-parameter forward-closure argument**, conditional on exact verification of the canonical Mojo implementation and independent human review (pending). This note asserts no theorem about arbitrary-parameter hitting or general PSC. It builds on the existing accepted uniform strict-geometry and nine-seed result, rather than revisiting class D.

## Scope and precise statement

For each integer `n>=4` consider the determinant-two PIP substitution

```
x -> x y^(n+1) x
c -> c y^n x
y -> x y^(n+1) c.
```

Let `C_n` be the exact **89-row typed candidate** defined by `kernel/psc/class_a_typed_carrier.mojo`; its labels are `(top,bottom,k,c,y)` with integral shift `w=(k,c,y)`, coordinate sum `s=k+c+y`, and affine row bounds `a*n+b<=k<=A*n+B`. The preceding [uniform geometry proof](class-a-uniform-geometry-2026-10-22.md) establishes that `C_n` consists of strict real overlaps, contains all nine canonical swap-patch seeds, and has `40n+115` distinct labels for all `n>=4`.

**Scoped closure result.** For every integer `n>=4` and every **nonterminal** label `u in C_n`, every exact positive-interior ordered child occurrence under the canonical inflation operator lies in `C_n`. This retains both parent letters, occurrence indices, exact integral offsets and strict geometry. In particular, **every canonical swap-seed-reachable nonterminal label lies in `C_n`**. This consequence is a true universal-in-`n` *coverage* result; it is not a proof that all formal labels are reachable or productive.

An equal-letter zero-offset coincidence is a **terminal** state in the repository's overlap automaton, so its children are deliberately excluded from the closure quantifier, as in `build_overlap_graph_from_seeds`. Including its inflation edges would change the accepted graph semantics.

## Reduction to finitely many affine cases

Write `h=1/(beta-1)`, where the PIP cubic gives `0<h<1/(n+1)`, in particular `0<h<1/9` for `n>=8`, and

```
n*h*(1+h) = 1-h-h^2-h^3.
```

In the common scaled metric, `L=(1+h+h^2,1,1+h)`. Every candidate row has `s in {-1,0,1}` and `|k|<=n+1` for all `n>=4`; the source rows are checked to establish these inequalities, not assumed from numerical graphs.

An actual child occurrence chooses zero-based top/bottom indices `i,j`. Partition indices into exactly three types: FIRST (index zero), RUN (the consecutive y-block), and LAST (the final x/c). The index ranges are affine in `n`; each type identifies an actual child letter and whether the proper prefix includes its initial x or c.

Let `q` be the coordinate sum of the child's integral offset. Since the incidence columns have lengths `n+3,n+2,n+3`, the exact affine update implies

```
q=(n+2)*s+k+y+j-i .
```

Write `I_t=1` if `i>0`, else 0, and similarly `I_b`. If `dx` is the difference in x-counts of the two initial proper-prefix letters, then the remaining child coordinates are

```
k_child = k+s+dx,
y_child = q-2*s-I_b+I_t .
```

Thus the *entire child label* is determined by the 89 source rows, the 9 FIRST/RUN/LAST class pairs, `q`, and the affine parameter `k`. Moreover, since `i,j` range over consecutive integer intervals, each possible `j-i` fills exactly a consecutive interval. The occurrence-feasibility constraint gives an **exact** affine interval for `k`, intersected with the parent row interval. Nothing is dropped by this reduction.

### Why only five child-sum values are necessary

The exact scaled child displacement can be rewritten, using the cubic identity, as

```
T_child = (q+k*h)*(1+h) + s*(h^2-h) + delta,
```

where the initial-prefix correction `delta` is a difference of terms from `{0,-h,h^2}` and hence `|delta|<=h+h^2`. Also `|k|*h<1` and `|s|<=1`.

If `q>=3`, then `T_child>2-h^2>L_max=1+h+h^2`; if `q<=-3`, then `T_child<-2+h^2<-L_max`. Both exclude positive interior overlap. Consequently it is **complete** to enumerate exactly `q in {-2,-1,0,1,2}`. No bounded-search assumption is introduced.

## All n>=8: coefficient-certified partition

At `n=8`, every affine line comparison used to select the max/min occurrence bound and subtract destination carrier intervals has an **unchanging order for all n>=8**: comparing `f(n)=an+b` with `g(n)=An+B` succeeds only when the slope and their difference at n=8 give the same order thereafter. The canonical validator fails closed rather than silently choosing a branch when two lines cross.

For the 89 source rows, the 9 occurrence-class pairs and five admissible `q` values, after exact feasibility pruning there are **1,528 nonempty symbolic case cells**. For each cell, subtract the union of *all* matching destination intervals (including proper `k_child` translation). There are **1,006 affine integer gap intervals** not covered by the destination carrier.

Consider one gap `k_lo<=k<=k_hi`. Its child displacement is strictly increasing in `k`. Therefore every such child is non-interior if either

```
L_bottom_child + T_child(k_hi) <= 0    (left separation)
L_top_child    - T_child(k_lo) <= 0    (right separation).
```

At either affine endpoint `k=a*n+b`, the cubic equation eliminates `n` from the child shift. Each sign becomes an integer cubic polynomial `f(h)`. Set `h=t/(9(1+t))`, with `t>0`. If `f(h)=c0+c1*h+c2*h^2+c3*h^3`, then

```
729*(1+t)^3*f(t/(9*(1+t))) =
    (729*c0)
  + (2187*c0 + 81*c1)*t
  + (2187*c0 + 162*c1 + 9*c2)*t^2
  + (729*c0 + 81*c1 + 9*c2 + c3)*t^3 .
```

The validator proves the **negative** of one margin has four nonnegative integer coefficients, including identically zero. This proves the required weak separation at **every h in (0,1/9)** and therefore for **every integer n>=8**, independently of any numerical sample.

The canonical checker verifies **505 left-separation cases and 501 right-separation cases**, all 1,006 gaps, plus the exact 1,528-case partition. A missing gap, changed row, unsound line order, or negative certificate coefficient refuses the proof.

## Exact prefix n=4,5,6,7

The only exceptional parameter values are n=4..7, where some affine interval orderings differ from the stable n>=8 partition. Instead of extrapolating, the canonical checker calls the already existing, strict, cap-refusing `certify_finite(n)` for each of these four values. At each n it constructs the *complete* exact swap-seed graph, compares the candidate and graph as **labelled sets**, and verifies every ordered occurrence child and every seed. The graph cap must not be exhausted.

The independent Python oracle also proves the finite prefix *without* relying on graph enumeration: it repeats the affine gap coverage with exact rational isolation of the unique root of `h^3+(n+1)(h+h^2)-1`; for n=4,5,6,7 it respectively eliminates **958, 988, 1,002, and 1,006 uncovered gaps**, never using floating equality.

The finite prefix and the n>=8 coefficient proof cover **every n>=4**, with no sampling gap.

## Exact replay and nonclaims

Canonical Mojo: `kernel/psc/class_a_uniform_closure.mojo`, with locked driver `kernel/class_a_uniform_closure.mojo` and controls `kernel/tests/test_class_a_uniform_closure.mojo`. Independent Python oracle: `oracles/python/class_a_uniform_closure.py` and tests `tests/test_class_a_uniform_closure.py`. The dedicated locked workflow produces independent fresh receipts.

```sh
python oracles/python/class_a_uniform_closure.py
python -m pytest -q tests/test_class_a_uniform_closure.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_uniform_closure.mojo
```

Mathematical conclusion depends on exact coefficients/finite checks, not on any CI status; however **repository acceptance awaits fresh required CI** for the exact PR head and independent human review remains pending. The previously merged accepted scope of class D is untouched.

**The decisive next mathematical obligation is hitting, not coverage.** Forward closure and seed inclusion show every seed descendant is represented, but a forward-closed finite graph can have a closed nonproductive SCC. Prove a parameter-dependent exit/rank, or eliminate all nonproductive closed SCCs, **for every state of C_n or at least every seed-reachable state**. No global #139/#84/#138/PSC claim is promoted by this closure proof. Remaining class-A parameter regions and residual class C also remain unresolved.
