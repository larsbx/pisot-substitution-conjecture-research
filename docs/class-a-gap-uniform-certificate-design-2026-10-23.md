# Class A, gaps d>=5: design of the d-uniform residue-regime certificate (2026-10-23)

**Status:** design and lemma record for steps (b) and (c) of
[class-a-gap-uniformity-stopgo-2026-10-23.md](class-a-gap-uniformity-stopgo-2026-10-23.md);
no theorem. Everything below is stated for the lines `(n+d, n, n+eps)`,
`sigma(x) = x y^(n+d) x`, `sigma(c) = c y^n x`, `sigma(y) = x y^(n+eps) c`,
with `n = d l + r`, `0 <= r < d`, and the conventions of the residue-ray
certificate ([class-a-residue-rays-2026-10-22.md](class-a-residue-rays-2026-10-22.md)):
`h = 1/(beta-1)`, `P(n,h) = 1-(n+eps)h-(n+d+1-eps)h^2-d h^3 = 0`,
`L = (1+(d+1-eps)h+d h^2, 1+(1-eps)h, 1+h)`, `T(w) = s L_c + k d h(1+h) + eps y h`,
strict overlap iff `-L_bottom < T < L_top`.

## Regimes

Step (a) found that, per sign, the label set of every member is one `l`-affine
table on each of finitely many *regimes* of the residue `r`, independent of `d`:

| kind | residue | parameters |
| --- | --- | --- |
| low `j` | `r = j` | `l >= l0`, `d >= d0` |
| high `j` | `r = d - j` | `l >= l0`, `d >= d0` |
| middle `(j0, j1)` | `j0 <= r <= d - j1` | `l >= l0`, `d >= d0`, `r` free in that range |

A *regime table* is a ray table (rows `[top,bottom,s,y,k_lo_a,k_lo_b,k_hi_a,k_hi_b]`,
pieces, descents, all affine in `l`) asserted for every `(l, d, r)` of the regime.
The certificate below proves closure and descent for the whole regime at once.

## Integer side: forms in Z[l, d, r]

Every integer quantity of the ray certificate (row endpoints, `j_max`, run
lengths `d l + r + {d, 0, eps}`, the child-index base `d(k_lo+s) + r s + eps y`,
prefix-count ranges) is a *gap form*

    F = c1 + cl*l + cd*d + cld*l*d + cr*r        (bilinear in (l,d), linear in r).

**Lemma 1 (quadrant positivity).** For `g(l,d) = c1 + cl l + cd d + cld l d`
and integers `l0, d0`: `g(l,d) >= 0` for all integers `l >= l0`, `d >= d0`
iff `g(l0,d0) >= 0`, `cl + cld d0 >= 0`, `cd + cld l0 >= 0` and `cld >= 0`.
*Proof.* `g(l,d) = g(l0,d0) + (l-l0)(cl + cld d0) + (d-d0)(cd + cld l0) + cld (l-l0)(d-d0)`.
The four conditions make every term non-negative. Conversely `l -> oo` at
`d = d0` forces `cl + cld d0 >= 0`, `d -> oo` at `l = l0` forces
`cd + cld l0 >= 0`, both `-> oo` forces `cld >= 0`, and `(l0,d0)` itself the first.

**Regime reduction for `r`.** `F` is affine in `r` at fixed `(l,d)`, so
`F >= 0` on the regime iff it holds after substituting `r = j` (low),
`r = d - j` (high), or both `r = j0` and `r = d - j1` (middle); each
substitution is again bilinear in `(l,d)`, decided by Lemma 1. The
three-valued comparison `le(u, v)` is `1` if `v - u >= 0` on the regime,
`0` if `u - v - 1 >= 0` on the regime, and `-1` otherwise (undecided; a
consumer either refuses or counts a clip fallback, exactly as today).

**Lemma 2 (uniform division by `d`).** Let `N = c1 + cd d + cld l d + cr r`
(no pure `l` term; a pure `l` term refuses). Then on a regime with `d >= d0`,

    ceil(N/d)  = cld l + cd + K,     floor(N/d) = cld l + cd + K',

with constants `K, K'` given by the value `v(r) = cr r + c1` as follows,
and the division **refuses** in every other case.

- low (`r = j`), or middle with `cr = 0`: put `v0 = cr j + c1` (resp. `c1`).
  `K = 0` if `-d0 < v0 <= 0`; `K = 1` if `0 < v0 <= d0`.
  `K' = 0` if `0 <= v0 < d0`; `K' = -1` if `-d0 <= v0 < 0`.
  (For `d >= d0`, `v0/d` then stays in `(-1, 0]`, `(0, 1]`, `[0, 1)`, `[-1, 0)`.)
- high (`r = d - j`): `v = cr d + (c1 - cr j)`, so `ceil(v/d) = cr + ceil(v0/d)`
  with `v0 = c1 - cr j`, and the low rule applies to `v0` (likewise floor).
- middle, `cr = 1`: `v = r + c1` ranges over `[j0 + c1, d - j1 + c1]`.
  `K = 1` iff `1 - j0 <= c1 <= j1` (then `0 < v <= d`);
  `K' = 0` iff `-j0 <= c1 <= j1 - 1` (then `0 <= v < d`).
- middle, `cr = -1`: `v = c1 - r` ranges over `[c1 - d + j1, c1 - j0]`.
  `K = 0` iff `1 - j1 <= c1 <= j0` (then `-d < v <= 0`);
  `K' = -1` iff `-j1 <= c1 <= j0 - 1` (then `-d <= v < 0`).
- middle, `|cr| >= 2`: refuse (`v` spans more than one multiple of `d` once
  `d > 2(j0 + j1)`).

The middle regime requires `d0 >= j0 + j1`, so that it is non-empty at `d0`.

*Proof.* `N/d = cld l + cd + v(r)/d` exactly. Each listed case pins `v/d` to
one unit interval for every `d >= d0` and every `r` of the regime, so the
rounding is the stated constant; the remaining cases are refused, not decided.
Hence, after division, every realizable child index is `l`-affine and free of
`d` and `r`, which is what step (a) observed for the label sets.

## Perron side: polynomials in (h, u), signs on a box

Put `u = d h`. Then `n h(1+h) = 1 - eps h - (1-eps) h^2 - u h - u h^2` (from
`P = 0`), `L = (1 + (1-eps)h + u + u h, 1 + (1-eps)h, 1 + h)`, and for a
row coordinate `k = a l + b`:

    k d h(1+h) = a n h(1+h) + (d b - a r) h(1+h) = a n h(1+h) + b u (1+h) - a (r h)(1+h).

A displacement or length is therefore `A + n B + (r h) C` with
`A, B, C` in `Z[h,u]`, `C` divisible by `h` whenever it is nonzero. The sign
of `A + nB + (rh)C` is the sign of `A h(1+h) + E B + (rh) C h(1+h)` with
`E = n h(1+h)` as above (multiplying by `h(1+h) > 0`), and `r h` is `j h`
(low), `u - j h` (high), or ranges over `[j0 h, u - j1 h]` (middle; the
margin is affine in `r h`, so both endpoints are checked).

**Lemma 3 (sign on a box).** For every member `(d, n = d l + r)` of a regime
with `l >= l0`, `d >= d0`: `h_n < 1/n` (since `n^3 P(n,1/n) = -(1+eps)n^2 -
(d+1-eps)n - d < 0` and `P(n,.)` decreases on `h > 0` from `P(n,0) = 1`),
hence `u = d h_n < d/n <= 1/l <= 1/l0`, and `t := 1/d` lies in `(0, 1/d0]`.
So `(u, t)` lies in the box `B = (0, 1/l0) x (0, 1/d0]`, where `h = u t`.
Let `G(u,t) = F(u t, u)` for `F` in `Z[h,u]`, with common monomial factors
`u^a t^b` stripped (positive on `B`). `B` is covered by closed cells
`Q = [u0,u1] x [t0,t1]` obtained by bisecting the box alternately in `u` and
`t`. On a cell, let `c_{ij}` be the Bernstein coefficients of `G` (bidegree
`(deg_u G, deg_t G)`, after the affine map of `Q` onto the unit square). The
*sub-faces* of `Q` are its open interior, its four open edges and its four
corners; a sub-face is *inside `B`* unless it lies on `u = 0`, `t = 0` or
`u = 1/l0` (the edge `t = 1/d0` and its corners with `0 < u < 1/l0` are
inside `B`). The coefficients *governing* a sub-face are: all of them for the
interior; the boundary row or column `i = 0`, `i = deg_u`, `j = 0` or
`j = deg_t` for an edge; the single corner coefficient for a corner.

Cell criterion: `G > 0` on `Q ∩ B` if every `c_{ij} >= 0` and every sub-face
of `Q` inside `B` has a positive governing coefficient. (Symmetrically for
`G < 0` with every `c_{ij} <= 0`.) A cell meeting neither criterion is
bisected, to a depth limit; a cell still mixed at the limit, or two cells of
opposite certified sign, is **UNDECIDED** and refuses. If every cell certifies
positive, `G > 0` on `B`.
*Proof.* Bernstein basis polynomials are `>= 0` on the closed square, so
`c_{ij} >= 0` gives `G >= 0` on `Q`; at a point of a sub-face exactly the
governing basis polynomials are nonzero (all of them inside, one row or
column on an open edge, one at a corner), so `G > 0` there iff some
governing coefficient is positive. The sub-faces inside `B` of all cells
cover `B ∩ Q` for every `Q`, hence `B`, which contains the image `(u,t)` of
every member; positivity of `G` at a member is positivity of `F` there.

**Lemma 4 (identities, re-proved by the certificate).** Coefficient-wise in
`(h, u, n)`: `h (M^T L)_j - (1+h) L_j = -P` for each letter, with
`M^T L = (2L_x + n L_y + d L_y, L_x + L_c + n L_y, L_x + L_c + (n+eps) L_y)`
and `d L_y h = u (1+h)`; and `n^3 P(n, 1/n)` has every coefficient `<= 0` as a
polynomial in `(n, d)` and is not zero.

## What the uniform verifier does

It is the ray certificate with these substitutions, otherwise line for line:
`a_*` comparisons become regime comparisons (Lemma 1 + reduction),
`a_div_ceil/floor` become Lemma 2, `AffH.sign` becomes Lemma 3, the Segment
run lengths become gap forms, and the `n0`-based checks become `(l0, d0)`.
Output: `CLASS_A_REGIME_CLOSURE`, `CLASS_A_REGIME_DESCENT` and
`CLASS_A_REGIME_BOUNDARY_HITTING eps=.. regime=.. l>=l0 d>=d0` receipts.

**Theorem shape (target).** For each sign, the fitted regimes cover every
`(d, r)` with `d >= D(eps)` (`D(-1) = 5`, `D(+1) = 11`); together with the
finite exceptional `(d, r)` below `D(eps)` (ray tables, as for `d <= 4`) and
exact complete graphs below the floors, this would give boundary hitting on
every class-A line of gap `d >= 5`, hence on all of determinant-two class A.
Nothing of this is claimed until the verifier accepts the tables.

## Module contract (for the implementation)

`kernel/psc/gap_form.mojo`
- `struct GapForm(ImplicitlyCopyable, Copyable, Movable)`: `c1, cl, cd, cld, cr: Int`;
  `__init__(out self, c1, cl, cd, cld, cr)`; `add`, `sub`, `scale(Int)`; `const(Int)`,
  `lin(a, b)` (= `a l + b`) constructors (module-level `def`s).
- `struct Regime(ImplicitlyCopyable, Copyable, Movable)`: `eps, kind (0 low, 1 high, 2 middle), j, j1, l0, d0: Int`;
  `check()`; `name() -> String`; `r_endpoints() -> List[GapForm]` (one or two forms);
  `nonneg(f: GapForm) -> Bool` (Lemma 1 after the r-reduction);
  `le(u, v: GapForm) -> Int` (1 / 0 / -1 as above);
  `div_ceil(f) raises -> GapForm`, `div_floor(f) raises -> GapForm` (Lemma 2; result has `cd = cld = cr = 0`... i.e. `l`-affine);
  `max(u, v) raises`, `min(u, v) raises` (UNDECIDED raises);
  `run(letter) -> GapForm` (= `d l + r + {d, 0, eps}`).
- Tests `kernel/tests/test_gap_form.mojo`: Lemma 1 on random-free exhaustive small grids (brute force over `l0..l0+6`, `d0..d0+6` agrees with the criterion for a few hundred coefficient tuples), Lemma 2 against brute force over the regime's `(l, d, r)` for `d0..d0+5`, every refusal case, and `require_contract(...)`.

`kernel/psc/poly_hu.mojo`
- `struct PolyHU(Copyable, Movable)`: dense coefficient grid `c[i][j]` of `h^i u^j`, `Int`;
  `zero()`, `const(Int)`, `h()`, `u()`, `add`, `sub`, `scale(Int)`, `mul`, `is_zero()`, `deg_h()`, `deg_u()`.
- `struct AffHU(Copyable, Movable)`: `a, b, c: PolyHU` meaning `a + n b + (r h) c`;
  `add`, `sub`; `numerator(rh: PolyHU, eps: Int) -> PolyHU` = `a h(1+h) + E(eps) b + rh * c * h(1+h)`... (with `c` already the coefficient of `r h`, i.e. `c` need not be divisible by `h`; the caller passes `rh` as the polynomial `j h` or `u - j h`).
- `def sign_on_box(f: PolyHU, l0: Int, d0: Int, max_depth: Int = 12) raises -> Int`: Lemma 3 (substitute `h = u t`, map `(0,1/l0) x (0,1/d0]` to the unit square, Bernstein over `finite_exact.rat_q.Q`, subdivision); returns `0` for the zero polynomial, `+-1` when certified, raises `UNDECIDED sign ...` otherwise. Strip common monomial factors `u^a t^b` first (positive on the box).
- Tests `kernel/tests/test_poly_hu.mojo`: known-sign polynomials (e.g. `1 + u + h` positive; `u - 1` negative on the box for `l0 >= 1`; `u t - 1/2 ...`), a polynomial that changes sign on the box must raise, a polynomial vanishing exactly on the face `t = 1/d0` must raise, agreement of `sign_on_box` with evaluation at a grid of rational points inside the box for a few dozen random-free polynomials, and `require_contract(...)`.

Both modules import only the vendored packages and `psc.exact` helpers, never
the ray certificate; the ray certificate is unchanged.
