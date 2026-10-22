# Residual class A: uniform two-sign geometry and a non-transfer theorem (2026-10-22)

**Status:** Repository-proved scoped symbolic/algebraic identities and a written uniform non-transfer argument, with independent human review pending. This note does **not** prove boundary hitting for any previously open family, nor modify #138/#139/#84, G1 or PSC.

## Stop/go and scope

The predecessor [class-A carrier closure and descent](class-a-carrier-closure-2026-10-22.md) (merged PR #310) proves boundary hitting for the **single** plus-sign, gap-one line `(p,q,r)=(n+1,n,n+1)`, all `n>=4`. The September/October literature gate in [the run-index analysis](p1b-class-a-run-index-2026-10-21.md) still applies: Akiyama–Lee's finite algorithm, Minervino–Thuswaldner's non-unit representation, and Barge's initial-letter theorem do not supply a transferable uniform carrier or hitting argument.

Before attempting the next family, identify **exactly what changes** in Perron geometry and offset dynamics when the run gap `d=p-q` or determinant sign changes. Reuse the existing `psc.param_poly` exact arithmetic and `a1_normal_form_census.class_member`, not a new arithmetic package, and subject naive reuse of PR #310's d=1 carrier to an explicit all-parameter falsification attempt. This is the targeted uniform mechanism test—not an unsupported larger finite census.

Use alphabet `(x,c,y)=(0,1,2)` and the class-A normal form:

```
sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,
sigma(y) = x y^(n+eps) c,   eps ∈ {-1,+1}, d>=1.
```

The determinant-two PIP admissible parameter domains established in [p1b-class-a-run-index](p1b-class-a-run-index-2026-10-21.md) are:

| Sign | Parameters |
|---|---|
| `eps=+1` | `n>=0, 1<=d<=2n+11` |
| `eps=-1` | `n>=1, 1<=d<=2n-1` |

These domains (and irreducibility/primitivity) are inherited results, not claims from a numerical screen. They include the residual plus-sign gap-two line `d=2,n>=4` selected below. Do not infer that a formula holding algebraically outside this domain certifies PIP or the spectral conclusion.

## Exact two-variable characteristic and eigenlength identity

The incidence matrix, oriented with columns indexed by parent letters, is

```
              x      c      y
M = x    [    2,     1,     1  ]
    c    [    0,     1,     1  ]
    y    [  n+d,     n,   n+eps].
```

Its characteristic cubic is

```
chi(t) = t^3 - (n+eps+3)t^2 + (n+2+3eps-d)t - 2eps.
```

Let `beta>1` be its Perron root in the stated PIP regime and `h=1/(beta-1)>0`. Then

```
P(n,d,eps,h)
 = h^3 chi(1+1/h)
 = 1 - (n+eps)h - (n+d+1-eps)h^2 - d h^3 = 0.
```

The positivity and uniqueness of the positive root follow from `P(0)=1`, `P(h)->-infinity`, and its strictly negative derivative for `h>0` throughout either admissible parameter domain. **The exact physical tile lengths up to a positive common scale** are

```
L_x = 1 + (d+1-eps)h + d h^2,
L_c = 1 + (1-eps)h,
L_y = 1 + h.
```

A direct coefficient identity in the two independent integer parameters `n,d` and indeterminate `h` is

```
h M^T L - (1+h)L = (-P,-P,-P).
```

Thus at the positive root, `M^T L = beta L`. The order of lengths changes with sign:

```
L_x - L_c = d h(1+h) >0,
L_y - L_c = eps*h.
```

Hence **plus:** `L_x>L_y>L_c`; **minus:** `L_x>L_c>L_y`, uniformly over the admissible domain. In particular, the nine strict swap-patch seed labels and orientation conventions of the gap-one plus family must not silently be assumed to be those of the minus regime.

## Exact child-coordinate update

For any integral offset `w=(k,c,y)`, let `s=k+c+y`. The displacement in the above common length scale becomes

```
T(w) = L . w
     = (1+(1-eps)h)*s + d k h(1+h) + eps*y*h.
```

For a paired actual proper-prefix occurrence, let `delta=(delta_x,delta_c,delta_y)` be **bottom prefix minus top prefix**, retaining both zero-based indices. The child satisfies

```
k' = k+s+delta_x,
c' = s-k+delta_c,
y' = n*s+d*k+eps*y+delta_y,
s' = (n+2)*s+d*k+eps*y+delta_x+delta_c+delta_y.
```

All of these follow coefficient-by-coefficient from `w'=M w+delta`. The canonical Mojo kernel uses the existing exact `Q[n,d][h]` polynomial infrastructure, proves each of the three incidence-column eigenvector identities and each of the three offset-basis update identities for **both signs**, and rejects unsupported determinant signs. Its independent Python oracle uses a separate sparse polynomial ring `Z[n,d,h,k,c,y]`.

This is the algebraic adapter required before attempting a typed carrier on another A region. It is *not* a new hitting theorem.

## A uniform obstruction to transporting the 89-row gap-one carrier

The gap-one table has the explicit row

```
(top,bottom,s,y,a,b,A,B)=(y,y,0,-2,-1,0,0,0).
```

For any integer `n>=4`, this row contains the formal state

```
V_n=(y,y,w),    w=(-n,n+2,-2).
```

This **does not remain a real overlap** on the next residual line, `eps=+1,d=2`. Its root equation is

```
P_2(n,h)=1-(n+1)h-(n+2)h^2-2h^3=0.
```

It has exactly one positive root. As `P_2(n,0)=1`, the derivative is negative for positive `h`, and

```
125 P_2(n,1/5)=88-30n<0   (n>=4),
```

one has `0<h<1/5` uniformly. Both tiles are type `y`, so strict intersection requires `T(V_n)+L_y>0`. But elimination of `n` using the exact root equation gives

```
T(V_n)+L_y
 = 1-h-2n h(1+h)
 = -1+h+4h^2+4h^3
 < -1+1/5+4/25+4/125
 = -76/125 <0.
```

The state is **disjoint**, not even boundary-touching, for every `n>=4`. The canonical coefficient checker verifies the polynomial reduction exactly and that the historical d=1 table includes this row; the native `n=4,d=2` strict-geometry reader independently refuses the state.

This is a uniform countermodel to **reusing the same 89-row table as a strict-overlap carrier for d=2**. It is *not* a counterexample to offset-zero hitting, seed reachability, or PSC. A different typed carrier may exist, and the old d=1 theorem remains valid.

## Replay, negative controls and precise next obligation

Canonical implementation: `kernel/psc/class_a_residual_geometry.mojo`, driver `kernel/class_a_residual_geometry.mojo`, native tests `kernel/tests/test_class_a_residual_geometry.mojo`. Independent symbolic oracle: `oracles/python/class_a_residual_geometry.py`, regressions `tests/test_class_a_residual_geometry.py`. The dedicated locked workflow records fresh receipts.

```sh
python oracles/python/class_a_residual_geometry.py
python -m pytest -q tests/test_class_a_residual_geometry.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_residual_geometry.mojo
```

Negative controls refuse an invalid sign, corrupt a polynomial identity, delete the exact historical witness row, and independently replay the disjoint d=2 state with strict real geometry. Exhausted budgets or finite graph computations are not used to claim the all-n inequality. Fresh CI at the actual PR head remains necessary for repository acceptance.

**Next constructive task:** formulate a d-dependent, sign-aware typed carrier with all nine/all genuinely strict swap seeds computed under the correct tile order. First target `eps=+1,d=2,n>=4`, rather than grafting a d=1 table or pretending its finite graph-size formula transfers. Then prove uniform all-child closure and a parameter-dependent descent, preserving exact ordered occurrences and the distinction between zero offset and equal-letter coincidence. After that extend to the other unbounded A regions and C residual. No status of #139/#84/#138, general G1 or PSC changes.
