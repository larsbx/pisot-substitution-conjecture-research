# Class A: uniform typed geometry and canonical seed inclusion (2026-10-22)

**Status: Repository-proved (scoped all-parameter coefficient certificate), independent human review pending.** This note establishes strict Perron geometry, all-nine-seed inclusion, and the formal cardinality of the 89-row typed carrier for the *selected* determinant-two class-A line. It does **not** establish forward closure, reachability of every row, arbitrary-n offset-zero hitting, or #139.

## Scope and literature reuse

The substitution is
`sigma_n=(x y^(n+1) x, c y^n x, x y^(n+1) c)`, integer `n>=4`. Retain the actual three canonical unordered swap patches `(xc,cx)`, `(xy,yx)`, `(cy,yc)`, both oriented seeds where present, and all positive-interior overlaps. Use bottom-minus-top shifts `w=(k,c,y)` with `s=k+c+y`. The typed carrier is exactly `template_rows()` in `kernel/psc/class_a_typed_carrier.mojo`; do not substitute the failed untyped rectangle.

The literature limits and the non-unimodular hypothesis firewall are inherited from [the October 21 run-index note](p1b-class-a-run-index-2026-10-21.md) and [the rectangular-cover obstruction](class-a-cover-obstruction-2026-10-21.md). No imported tiling, injectivity, or adelic completeness theorem is invoked.

## Mathematical derivation: one global root interval

For the Perron root `beta` put `h=1/(beta-1)`. The characteristic polynomial, already established for this family, transforms into
`P(n,h)=h^3+(n+1)h^2+(n+1)h-1=0`.
The function is strictly increasing for `h>=0`, with `P(n,0)=-1` and
`P(n,1/5)=(30n-94)/125>0` for every `n>=4`. Consequently **`0<h<1/5`**, without numerical root approximation. Rearranging gives

```
 n*h*(1+h) = 1-h-h^2-h^3 .
```

Scale all three tile lengths by `1+h`. The resulting exact left-Perron eigenlengths are
`L_x=1+h+h^2`, `L_c=1`, `L_y=1+h`. The scaled shift associated with integral `w` is

```
 T(k,s,y) = s+h*(k+y)+h^2*k .
```

A row `(top,bottom,s,y,a,b,A,B)` covers all integer `k` between `a*n+b` and `A*n+B`; the middle coordinate is `c=s-k-y`. At an affine endpoint `k=a*n+b`, use the cubic equation to eliminate n:

```
 T(a*n+b,s,y)
   = (s+a)+(-a+b+y)*h+(-a+b)*h^2-a*h^3 .
```

For fixed n and s,y, T is strictly increasing in k because `h(1+h)>0`. Thus **an entire typed interval is a strict real overlap** precisely when both endpoint margins are positive:

```
 lower_margin = L_bottom + T(k_lower,s,y)
 upper_margin = L_top    - T(k_upper,s,y)
```

The two strict inequalities are necessary and sufficient for the intersection of the top interval `[0,L_top]` and shifted bottom interval `[T,T+L_bottom]` to have positive length. This supplies exactly 178 cubic endpoint predicates for the 89 rows.

## Uniform sign certificate; no finite extrapolation

For one margin `f(h)=c0+c1*h+c2*h^2+c3*h^3`, substitute
`h=t/(5(1+t))`. This maps `t>0` bijectively to `0<h<1/5`. Multiply by the strictly positive denominator `125(1+t)^3`. The coefficient list in ascending powers of t is

```
 C0 = 125*c0
 C1 = 375*c0 + 25*c1
 C2 = 375*c0 + 50*c1 + 5*c2
 C3 = 125*c0 + 25*c1 + 5*c2 + c3
```

If all `C_i>=0` and at least one `C_i>0`, then the transformed polynomial is strictly positive for **every** t>0 and hence f(h)>0 throughout the whole root interval. The canonical Mojo code checks this exact integer condition for **all 178 margins**. This is the degree-three Bernstein-coefficient certificate on the same interval, expressed via a positive-power transformation. The separate Python oracle recomputes the transform from typed interval source rows.

Neither test samples n or approximates h. No promise that this sufficient positivity criterion would succeed for an arbitrary proposed carrier is needed: it actually succeeds on every fixed row here. Zero margins and negative coefficients are explicit refusals, not accepted as strictness.

## Uniform formal size and all canonical seeds

Each affine interval has `(A-a)n+(B-b+1)` integer values. Across the 89 rows the exact sums are `40n+115`. Both endpoint difference and width are nonnegative for every n>=4 by checking the affine slope and value at n=4. For each pair of rows in the same `(top,bottom,s,y)` slice, one order has a separation `D(n)=a*n+b-(A'*n+B')>=1`, witnessed by **nonnegative slope and D(4)>=1**. Therefore the intervals are pairwise disjoint for every n>=4 and the cardinality is exactly `40n+115` (not just an upper bound).

The tile ordering is `L_x>L_y>L_c`. The swap patches give exactly nine strict seed labels, written as `(top,bottom,k,c,y)`:

| Swap pair | zero-offset seed | second/second seed | same-type seed |
| --- | --- | --- | --- |
| (x,c) | `(x,c,0,0,0)` | `(c,x,-1,1,0)` | `(x,x,0,1,0)` |
| (x,y) | `(x,y,0,0,0)` | `(y,x,-1,0,1)` | `(x,x,0,0,1)` |
| (c,y) | `(c,y,0,0,0)` | `(y,c,0,-1,1)` | `(y,y,0,-1,0)` |

For each seed, the exact checker locates a typed row matching its letter pair, coordinate sum and y-coordinate. Its interval contains the fixed k at n=4, and its lower endpoint has nonpositive slope while its upper endpoint has nonnegative slope. The same seed therefore remains in that typed interval **for every integer n>=4**. These are the complete swap-patch seeds of `psc.overlap_seed_patch.seed_overlap_states_cached`; no assumption that a swapped word is legal is added.

## Exact replay and negative controls

Canonical Mojo certificate: `kernel/psc/class_a_uniform_geometry.mojo`. Exact test: `kernel/tests/test_class_a_uniform_geometry.mojo`. Independent polynomial oracle: `tests/test_class_a_uniform_geometry.py`. Dedicated workflow: `.github/workflows/class-a-uniform-geometry.yml`.

From the root and then the kernel directory:

```sh
python -m pytest -q tests/test_class_a_uniform_geometry.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_uniform_geometry.mojo
```

The code verifies 89 valid nonempty affine rows, 178 strict margin signs, pairwise all-n disjointness, cardinality `40n+115`, and all nine seeds. Mutants with zero/negative margins, a deleted singleton seed slice, and overlapping or altered interval rows must refuse. The coefficient checks provide **uniform-in-n** mathematical evidence; the new workflow must pass at its actual revision before declaring this integration accepted.

## Explicit residual obligation

This establishes a proper *component* of the desired complete class-A proof rather than another sampled necessary condition. The next obligation is all-child forward closure of the entire typed candidate under every real ordered occurrence and every n>=4. Even once closure is proved, the candidate includes real states not yet proved seed-reachable, and a parameter-dependent exit/ranking theorem is still required to force hits. Treat the 89-row cover as a proposal for those next tasks, not an established all-state hitting theorem. Class D remains accepted at its prior scope; residual A and C families, #139, #138, #84, G1 and PSC are unaffected.
