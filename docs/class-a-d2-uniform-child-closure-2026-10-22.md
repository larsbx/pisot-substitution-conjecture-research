# Class A gap two: exact forward closure on four integer-residue rays (2026-10-22)

**Status:** Conditional theorem — parameter-uniform, exact coefficient proof implemented in canonical Mojo and a separately written integer-polynomial oracle; **new remote locked-toolchain acceptance and independent human review pending**. This result is restricted to the explicitly inferred, parity-indexed d=2 carrier. It proves **forward closure**, not offset-zero hitting.

## Scope and literature stop/go

After merged PR #310 established boundary hitting on the *gap-one plus-sign* line, PR #311 developed both-sign, variable-gap geometry; PR #312 inferred genuinely new even/odd typed carriers for gap two, and PR #313 proposed uniform strict real geometry, disjointness, cardinality and inclusion of all nine seeds in those carriers. The Akiyama–Lee, Minervino–Thuswaldner and Barge literature check, and the non-unit tiling/realization restrictions, remain unchanged. No new imported theorem is silently added.

Here the substitution is fixed:

```
sigma_n(x) = x y^(n+2) x
sigma_n(c) = c y^n x
sigma_n(y) = x y^(n+1) c,   n>=4.
```

The actual seed-patch graph is the existing exact bottom-minus-top strict-overlap graph, including all three swap pairs and all proper-prefix child indices; equal-letter zero-offset coincidences are terminal and **not** inflated. The even carrier consists of 93 typed intervals `(top,bottom,s,y,lower(m),upper(m))` when `n=2m>=8`; the odd carrier consists of 87 such intervals when `n=2m+1>=7`. Their existence and uniform strictness/seed inclusion depend on the exact PR #313 component, which is called as an executable prerequisite. The exceptional finite parameters `n=4,5,6` are separate, complete exact graphs.

## Why parity n alone is insufficient for the transition proof

For a state with integral shift `w=(k,c,y)`, put `s=k+c+y`. The exact d=2 incidence update before prefix corrections is

```
M w = (k+s, s-k, n*s+2*k+y).
```

Every paired proper-prefix occurrence supplies indices `i,j`, and initial prefix-letter contributions `dx,dc` (bottom minus top) and y-prefix counts `z_t,z_b`. Its child has

```
k' = k+s+dx
y' = n*s+2*k+y+z_b-z_t
s' = 2*s+dx+dc+y'.
```

As `k` is the row variable, the exact feasibility inequalities for a fixed child `y'` contain a **division by two**:

```
k >= ceil((y' - n*s - y - z_b^max + z_t^min)/2)
k <= floor((y' - n*s - y - z_b^min + z_t^max)/2).
```

The y-prefix counts vary over consecutive integer intervals in the three FIRST/RUN/LAST segments, so every integer difference in their interval is realizable. This reduction is complete; it retains both child letter types and the zero-based occurrence ranges. A naive affine proof in `m=floor(n/2)` would leave half-integral endpoint ambiguity.

Instead split into **four residue classes**

```
n = 4ℓ+r,     r=0,1,2,3,     ℓ>=3.
```

In each class `m=2ℓ+floor(r/2)`. The two divided affine expressions above have even ℓ slopes, and their ceilings/floors therefore become exact integer-affine functions of ℓ. No rounding operation can change at larger ℓ. All max/min, row ordering and interval containment decisions are proved to retain the same sign on the infinite ray `ℓ>=3`; a crossing causes an explicit refusal rather than an arbitrary branch.

## Uniform child-y window, not a finite alphabet assumption

The d=2 characteristic equation from PR #311 is

```
P_2(n,h) = 1-(n+1)h-(n+2)h²-2h³ = 0,
h=1/(β-1),      0<h<1/(n+1).
```

The scaled tile lengths are `L=(1+2h+2h²,1,1+h)`. A strict state has scaled displacement `-L_bottom<T<L_top`. Child displacement for fixed segment types is

```
T' = (2s+dx+dc+y') + 2(k+s+dx)h(1+h) + y'h.
```

For fixed parent k this is **strictly increasing** in y' with slope `1+h`; it is also strictly increasing in k with slope `2h(1+h)`. On each parent affine row the verifier proves, uniformly, `T'(y'=5,k_min)>=L_topchild` and `T'(y'=-5,k_max)<=-L_bottomchild`. Every y' outside the **exact nine-value range** `-4..4` therefore produces no strict overlap, regardless of occurrence feasibility.

The root sign statements follow by eliminating ℓ in every affine endpoint and requiring the integer polynomial coefficients of

```
q³ (1+t)³ f(t/(q(1+t)))
```

to be nonnegative (zero permitted for non-strict separation), where `q=n_0+1`, `n_0=12+r`. For a cubic `f(h)=a+b h+c h²+d h³`, the four coefficients are

```
[q³a,
 3q³a+q²b,
 3q³a+2q²b+q c,
 q³a+q²b+q c+d].
```

These are **exact integer coefficients**, not numeric signs at a sampled root. The transformation covers all `0<h<1/q` because `h=t/(q(1+t))` maps `t>0` onto that interval.

## Exhaustive affine-gap coverage for every n>=12

For each typed source interval and each of the nine FIRST/RUN/LAST segment pairs, and every possible child y' in -4..4, intersect the source k interval with the exact integer-affine occurrence feasibility interval. Then translate every candidate destination interval by `k'=k+s+dx` and subtract **all** matching destination intervals in the child typed slice `(child_top,child_bottom,s',y')`. No child with a different type, coordinate sum or y-offset is credited as covered.

On any resulting affine gap `[k_lo,k_hi]`, the child shift is increasing in k. Hence every child in that gap is non-interior if either

```
T'(k_hi)+L_bottomchild <= 0,  or
T'(k_lo)-L_topchild >= 0.
```

Each is an exact cubic in h after substituting `k=aℓ+b` and using

```
4ℓ h(1+h)=1-(r+1)h-(r+2)h²-2h³.
```

The canonical checker enforces the root-interval positive-coefficient condition on the *negative of the appropriate overlap margin* for every gap. Thus it does not infer a child omission merely from a finite graph or a numeric inequality.

| n residue r | Nonempty symbolic cells | Gaps proven non-interior | Left separation | Right separation | Window endpoint certificates |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 3,005 | 2,483 | 1,249 | 1,234 | 1,710 |
| 1 | 2,845 | 2,363 | 1,189 | 1,174 | 1,602 |
| 2 | 3,005 | 2,483 | 1,249 | 1,234 | 1,710 |
| 3 | 2,845 | 2,363 | 1,189 | 1,174 | 1,602 |
| **Total** | **11,700** | **9,692** | **4,876** | **4,816** | **6,624** |

The proof uses only finite symbolic case enumeration and exact integer inequalities, with all ℓ comparisons certified for the **infinite** rays ℓ>=3. A finite census is not promoted into a uniform theorem. Two independently written implementations compute the same partition counts.

## Finite exceptional prefix and exact conclusion

The canonical driver handles `n=4,5,6` by the existing complete, cap-refusing seed graph, independently finding all first offset-zero depths finite. For `n=7,8,9,10,11` it additionally verifies complete finite labelled graph equality with the respective parity candidate. These eight exact finite cases and the four infinite rays `n=4ℓ+r`, `ℓ>=3`, exhaust every integer `n>=4`.

**Conditional scoped conclusion.** Assuming successful execution of all exact certificates and the prior PR #313 geometry/seed prerequisites, for every integer n>=4 **every actual seed-reachable ordered child remains within the appropriate typed parity carrier** (or is handled by the exact small-parameter graph). This closes the *coverage* component for the gap-two family. It does **not** prove that every candidate state is reachable, or that every candidate or seed-reachable state has an offset-zero descendant for all n.

## Replay and acceptance

Canonical Mojo: `kernel/psc/class_a_d2_uniform_closure.mojo`, driver `kernel/class_a_d2_uniform_closure.mojo`, native controls `kernel/tests/test_class_a_d2_uniform_closure.mojo`. Independent oracle: `oracles/python/class_a_d2_uniform_closure.py`, `tests/test_class_a_d2_uniform_closure.py`. CI: `.github/workflows/class-a-d2-uniform-closure.yml`.

```sh
python oracles/python/class_a_d2_uniform_closure.py
python -m pytest -q tests/test_class_a_d2_uniform_closure.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_uniform_closure.mojo
```

The verifier refuses: a crossed affine inequality, odd ℓ slope where exact halving requires an even one, unknown residue or shortened parameter ray, a negative coefficient in a gap or window sign, incomplete destination interval sets, wrong source sum, a wrongly inflated terminal coincidence, and a missing or malformed prior geometry/seed prerequisite. A narrowed destination interval is a retained **actual child escape** mutant, not just an artificial row-count failure.

**Next theorem target:** a nonnegative parity-dependent rank or potential and chosen actual ordered child descending from every nonzero-offset seed-reachable state, or a uniform elimination of any closed nonproductive SCC. Closure does not imply hitting. No general #139/#84/#138/G1/PSC promotion, no claim-ledger update, and no reopening of accepted class D or gap-one class-A proofs is justified.
