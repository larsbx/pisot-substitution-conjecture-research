# Class A d=2: uniform geometry of the even/odd typed candidates (2026-10-22)

**Status:** Repository-proved scoped all-parameter polynomial argument with canonical and independent coefficient checkers; **fresh locked CI acceptance and independent human review pending**. This is a strict-overlap, disjointness, cardinality and seed-inclusion component for the inferred parity candidates, **not** the all-child closure or boundary-hitting theorem. It builds on the finite source profiles proposed in [class-a-d2-parity-carrier-2026-10-22.md](class-a-d2-parity-carrier-2026-10-22.md).

## Targeted literature and hypothesis gate

The class-A gap-one closure/descent of merged PR #310 cannot simply be transferred to gap two. PR #311's exact normal-form derivation supplies the correct two-parameter incidence and Perron geometry. Akiyama–Lee's overlap decision is per substitution, Minervino–Thuswaldner's non-unit representation requires its finite places, and Barge's initial-letter hypotheses cannot be silently added. Thus the precise next step is *uniform reality and seed coverage of each new typed candidate* before trying a closure or exit theorem.

Fix the determinant-two PIP plus-sign gap-two line, for every integer `n>=4`:

```
x -> x y^(n+2) x,
c -> c y^n x,
y -> x y^(n+1) c.
```

The potential carrier is the **even/odd row definition** from the exact finite graphs at n=8/12 and n=9/13; every affine endpoint is a function of `m=floor(n/2)`. No step below assumes those rows equal the graph at unseen n. Their entire role is an explicit symbolic *candidate* for one all-n proof.

## Exact positive root and integer coordinates

Let `h=1/(beta-1)>0`, where `beta` is the Perron root. The characteristic identity of PR #311 for d=2, epsilon=+1 is

```
P(n,h) = 1-(n+1)h-(n+2)h^2-2h^3=0.
```

For n>=4, `P(n,0)=1`; its derivative is strictly negative for h>=0 and `P(n,1/(n+1))=-(n+2)/(n+1)^2-2/(n+1)^3<0`. The positive root is therefore unique and satisfies

```
0<h<1/(n+1).
```

The positive common-scaled tile lengths are `(L_x,L_c,L_y)=(1+2h+2h^2,1,1+h)`. Their order is `L_x>L_y>L_c`, unchanged across the full line, giving exactly the nine strict canonical swap seeds from the existing exact seed-patch semantics.

A typed state uses bottom-minus-top `w=(k,c,y)`, `s=k+c+y`, and shift

```
T(w) = s + 2k h(1+h)+y h.
```

The cubic equation eliminates the unbounded parameter:

```
n h(1+h)=1-h-2h^2-2h^3.
```

Write **n=2m+r** for fixed parity `r in {0,1}`; at any affine row endpoint `k=a m+b`,

```
T = (s+a)
  + (-a(1+r)+2b+y) h
  + (-a(2+r)+2b) h^2
  - 2a h^3.
```

Thus every row endpoint strictness obligation reduces to a **single explicit integer cubic** in h, with no remaining m.

## Uniform positivity certificate for every typed row

The top interval is `[0,L_top]`, the shifted bottom interval `[T,T+L_bottom]`. As `T` increases strictly with k, the full row is a strict real overlap exactly when its lower and upper endpoint margins are positive:

```
L_bottom + T(k_min) > 0,
L_top - T(k_max) > 0.
```

For even n>=8, `h<1/9`; for odd n>=7, `h<1/8`. For either case put `q=9` or `q=8`, respectively. If `f(h)=A+B h+C h^2+D h^3`, substitute `h=t/(q(1+t))` for `t>0`. Multiplication by the positive denominator gives

```
q^3 (1+t)^3 f(t/(q(1+t)))
  = q^3 A
  + (3q^3 A+q^2 B)t
  + (3q^3 A+2q^2 B+q C)t^2
  + (q^3 A+q^2 B+q C+D)t^3.
```

All four coefficients nonnegative, at least one strictly positive, prove `f(h)>0` for **every h in (0,1/q)**. The canonical Mojo module checks **all 186** endpoint margins of the **93 even rows** and **all 174** endpoint margins of the **87 odd rows**, using only checked integer coefficients. The independent Python implementation rebuilds the templates from exact `Q(beta)` graphs and verifies the same symbolic implications without floating-point equality.

These 360 uniform strict inequalities are not obtained by checking larger samples of n.

## Uniform disjointness, exact candidate cardinality and seeds

For each parity, every affine candidate interval is `[a m+b,A m+B]`. Its width is affine; `A-a>=0` and its width at the floor `m0` is nonnegative, so every row is nonempty throughout the ray. Every pair of rows in one typed slice is separated in an order that cannot reverse: one endpoint gap has nonnegative slope and value >=1 at `m0`. Thus all intervals are pairwise disjoint for every admissible m.

The exact source rows supply these independent identities:

| Parameter ray | Rows | Typed slices | Strict margins | Formal cardinality |
| --- | ---: | ---: | ---: | --- |
| even n=2m>=8 | 93 | 82 | 186 | `40m+105 = 20n+105` |
| odd n=2m+1>=7 | 87 | 80 | 174 | `40m+111 = 20n+91` |

**These are proven sizes of the explicitly defined formal parity candidates, not proven sizes of the reachable graph for unseen n.**

Every one of the nine strict swap-seed labels has a matching typed row whose affine lower endpoint is nonincreasing and upper endpoint nondecreasing in m, and which contains that fixed seed at the ray floor. The exact checker verifies all nine individual comparisons in both parity classes. Hence the *formal candidates* contain every actual swap seed for all even n>=8 and odd n>=7. Small exceptional n=4,5,6 are already covered as finite exact graphs and are not silently folded into either stable symbolic ray.

## Executable certificates, falsification and remaining proof

Canonical Mojo: `kernel/psc/class_a_d2_uniform_geometry.mojo`; driver: `kernel/class_a_d2_uniform_geometry.mojo`; native controls: `kernel/tests/test_class_a_d2_uniform_geometry.mojo`. Independent integer-polynomial auditor: `oracles/python/class_a_d2_uniform_geometry.py` with `tests/test_class_a_d2_uniform_geometry.py`. Dedicated locked workflow: `.github/workflows/class-a-d2-uniform-geometry.yml`.

```sh
python oracles/python/class_a_d2_uniform_geometry.py
python -m pytest -q tests/test_class_a_d2_uniform_geometry.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_uniform_geometry.mojo
```

Negative controls reject a zero or negative margin, a malformed/missing typed slice containing a seed, changed affine endpoint, wrong parity, nonintegral source fit, overlapping/crossing row bounds, and an unsupported root-bound regime. All-n conditions are checked symbolically; no budget exhaustion returns a mathematical verdict. This is a theorem-facing contribution and fresh CI on the exact PR head is necessary for integration. Existing class-D and gap-one result scopes are unaffected; independent human review remains pending.

**Remaining decisive mathematical step:** for each parity ray, prove **all-child forward closure** of these typed candidates for every actual ordered occurrence, using the d=2 child-offset and prefix formulas. Even strict geometry plus all nine seeds does **not** force boundary hitting. After closure, construct a nonnegative parity-dependent potential with realizable strictly descending children (or an equivalent bad-SCC elimination). Only then may the d=2 line be promoted to uniform boundary hitting. Other class-A/C residual regions and general #139/#84/#138/G1/PSC remain open.
