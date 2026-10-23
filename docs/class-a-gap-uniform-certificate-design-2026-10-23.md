# Class A, gaps d>=5: design of the d-uniform residue-regime certificate (2026-10-23)

**Status:** design and lemma record for steps (b) and (c) of
[class-a-gap-uniformity-stopgo-2026-10-23.md](class-a-gap-uniformity-stopgo-2026-10-23.md).
The certificate it specifies is implemented and accepted on every fitted
regime; the theorem it yields (every gap `d >= 5`, both signs, every member
`n >= 5d`) and its scope are in
[class-a-gap-theorem-2026-10-23.md](class-a-gap-theorem-2026-10-23.md).
Everything below is stated for the lines `(n+d, n, n+eps)`,
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
lengths `d l + r + {d, 0, eps}`, the child-index base `d k_lo + n s + eps y = (a+s) l d + b d + s r + eps y` (for `k_lo = a l + b`),
prefix-count ranges) is a *gap form*

    F = c1 + cl*l + cd*d + cld*l*d + cr*r        (bilinear in (l,d), linear in r).

**Lemma 1 (quadrant positivity).** For `g(l,d) = c1 + cl l + cd d + cld l d`
and integers `l0, d0`: `g(l,d) >= 0` for all integers `l >= l0`, `d >= d0`
iff `g(l0,d0) >= 0`, `cl + cld d0 >= 0`, `cd + cld l0 >= 0` and `cld >= 0`.
*Proof.* `g(l,d) = g(l0,d0) + (l-l0)(cl + cld d0) + (d-d0)(cd + cld l0) + cld (l-l0)(d-d0)`.
The four conditions make every term non-negative. Conversely `l -> oo` at
`d = d0` forces `cl + cld d0 >= 0`, `d -> oo` at `l = l0` forces
`cd + cld l0 >= 0`, both `-> oo` forces `cld >= 0`, and `(l0,d0)` itself the first.
Only the "if" direction carries soundness (`nonneg`, `le = 1`, `le = 0`); the
converse only keeps `le` from answering `-1` where a uniform order exists. A
finite window cannot test the converse (`g = -7 - l + 4d` is non-negative on
`[5,13] x [5,13]` and first negative at `(14, 5)`), so the test asserts
criterion => window and window failure => criterion failure.

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

*Proof.* `N/d = cld l + cd + v(r)/d` exactly. Each listed case pins `v/d` to
one unit interval for every `d >= d0` and every `r` of the regime, so the
rounding is the stated constant; the remaining cases are refused, not decided.
(Step (a) observed that the *label sets* are `l`-affine; that is a statement
about unions over parents and does not make every per-parent realizable
index range `l`-affine. The refusals are not rare: at every fitted floor
Lemma 2 refuses on row 0, and on the middle regimes `|cr| = 2` occurs for
every row with `s != 0`, so the consumer needs Lemma 2' below.)

The middle regime requires `d0 >= j0 + j1`, so that it is non-empty at `d0`.
Regime hypotheses in general (enforced by `Regime.check`): `l0 >= 1`;
low `0 <= j < d0`; high `1 <= j <= d0`; middle `j0 >= 0`, `j1 >= 1`,
`d0 >= j0 + j1`; so every named member has a residue `0 <= r < d`, and
`l0 >= 1` puts every member in the determinant-two PIP domain
(`n >= d` gives `d <= 2n + 6 eps + 5` for both signs, and `n + eps >= 0`).

**Lemma 2' (one-sided rounding bounds; the consumer's fallback).** Write the
range of `v(r)` over the regime as `[a_min d + b_min, a_max d + b_max]`
(low: both ends `(0, cr j + c1)`; high: both `(cr, c1 - cr j)`; middle: the
ends `r = j0` giving `(0, cr j0 + c1)` and `r = d - j1` giving
`(cr, c1 - cr j1)`, ordered by the sign of `cr`). Then for every `d >= d0`
and `r` of the regime,

    ceil(N/d)  >= cld l + cd + a_min + lb(b_min),   floor(N/d) <= cld l + cd + a_max + ub(b_max),

with `lb(b) = ceil(b/d0)` for `b < 0`, `0` for `b = 0`, `1` for `b > 0`, and
`ub(b) = floor(b/d0)` for `b > 0`, `0` for `b = 0`, `-1` for `b < 0`.
*Proof.* `ceil(v/d) >= ceil(v_min/d) = a_min + ceil(b_min/d)`, and for fixed
`b < 0` the quotient `b/d` increases with `d`, so `ceil(b/d) >= ceil(b/d0)`
for `d >= d0`; for `b > 0`, `ceil(b/d) >= 1`. Symmetrically for the floor.
When Lemma 2 refuses, the closure uses these bounds: the realizable index
range becomes a superset of the true one, counted in `clip_fallbacks`
together with the undecided clips (`a_le == -1`) the ray certificate counts
there; the regime field therefore mixes the two events and is not comparable
to the ray's number at a single gap (the ray closure on the same rows at the
sample gap reports `0`).
Soundness is unchanged, since every realizable child is still examined;
the price is that an unrealizable index in a gap must also be shown
unreal geometrically, or the closure reports an escape it cannot
distinguish from a real one. On the 18 fitted tables every regime closure
certifies with this fallback from its floor (none reports an escape), so
the price was not paid. The geometric test `_unreal_on` is a disjunction of
two one-sided margins; `regime_sign` evaluates one margin at both `r h`
endpoints and refuses unless the signs agree, so each disjunct is "this
margin is `<= 0` at both endpoints", and the disjunction stands outside the
conjunction over endpoints (the other order would be unsound: a child could
sweep through the strict interval at an intermediate residue).


## Perron side: polynomials in (h, u), signs on a box

Put `u = d h`. Then `n h(1+h) = 1 - eps h - (1-eps) h^2 - u h - u h^2` (from
`P = 0`), `L = (1 + (1-eps)h + u + u h, 1 + (1-eps)h, 1 + h)`, and for a
row coordinate `k = a l + b`:

    k d h(1+h) = a n h(1+h) + (d b - a r) h(1+h) = a n h(1+h) + b u (1+h) - a (r h)(1+h).

A displacement or length is therefore `A + n B + (r h) C` with
`A, B, C` in `Z[h,u]`; the coefficient of `r` is `h C`, divisible by `h`,
while `C` itself need not be (for the displacement above `C = -a(1+h)`). The
ray certificate multiplies every length and displacement by `d` to keep its
coefficients integral; the regime certificate compares `T` with `L` unscaled,
since `d` alone is not in `Z[h,u]` (it is `u/h`). The sign
of `A + nB + (rh)C` is the sign of `A h(1+h) + E B + (rh) C h(1+h)` with
`E = n h(1+h)` as above (multiplying by `h(1+h) > 0`), and `r h` is `j h`
(low), `u - j h` (high), or ranges over `[j0 h, u - j1 h]` (middle; the
margin is affine in `r h`, so both endpoints are checked). Precisely: a
margin is `> 0` on the regime iff it is `> 0` at both endpoints, and `<= 0`
iff it is `<= 0` at both; a child is unreal iff for *one* of the two margins
(bottom at `j_hi`, or top at `j_lo`) the sign at both endpoints is `<= 0`,
and a strict overlap needs both margins `> 0` at both endpoints. Mixing a
margin at one endpoint with the other margin at the other endpoint proves
nothing about intermediate residues; `regime_sign` refuses a margin whose
endpoint signs differ, which rules the mixed pattern out by construction.

**Lemma 3 (sign on a box).** For every member `(d, n = d l + r)` of a regime
with `l >= l0`, `d >= d0`: every member has `n >= d0 l0 >= 1`, so `n + eps >= 0`
and `P_h(n,h) = -(n+eps) - 2(n+d+1-eps)h - 3d h^2 < 0` on `h > 0`, i.e.
`P(n,.)` strictly decreases from `P(n,0) = 1` and has one positive root `h_n`;
since `n^3 P(n,1/n) = -(1+eps)n^2 - (d+1-eps)n - d < 0`, `h_n < 1/n`,
hence `u = d h_n < d/n <= 1/l <= 1/l0`, and `t := 1/d` lies in `(0, 1/d0]`.
So `(u, t)` lies in the box `B = (0, 1/l0) x (0, 1/d0]`, where `h = u t`.
`B` is strictly larger than the hull of the member images (the constraint
`n >= d l0`, i.e. `E >= l0 u (1+h)`, is not encoded), so a margin positive at
every member can still be refused as UNDECIDED near the corner
`(u -> 1/l0, t = 1/d0)`; such a refusal is a box artefact, never a
counterexample, and the remedy would be the exact side condition
`E - l0 u(1+h) >= 0`, not a larger `l0`.
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
positive, `G > 0` on `B`. The criterion is sufficient, not necessary: a
polynomial positive on `B` that vanishes on an excluded face (for instance
`(1 - l0 u)^2 + (2 d0 t - 1)^2`) refuses at the depth limit; UNDECIDED is a
refusal, never a disproof.
*Proof.* Bernstein basis polynomials are `>= 0` on the closed square, so
`c_{ij} >= 0` gives `G >= 0` on `Q`; at a point of a sub-face exactly the
governing basis polynomials are nonzero (all of them inside, one row or
column on an open edge, one at a corner), so `G > 0` there iff some
governing coefficient is positive. The sub-faces inside `B` of all cells
cover `B ∩ Q` for every `Q`, hence `B`, which contains the image `(u,t)` of
every member; positivity of `G` at a member is positivity of `F` there.

**Lemma 3' (the member hull).** Let `S(h,u) = E(h,u) - l0 u (1+h)` with
`E = 1 - eps h - (1-eps) h^2 - u h - u h^2` (so `E = n h(1+h)` at a member).
At every member `n >= d l0`, hence `S = (n - d l0) h(1+h) >= 0`. If every
Bernstein coefficient of `S` on a closed cell `Q` is negative, `S < 0` on `Q`,
so no member maps into `Q`; such a cell may be skipped. `sign_within_hull`
runs Lemma 3 with this rule (`sign_on_box` is the case without a side
condition): the certified sign holds at every member, and cells of the box
outside the hull, where a margin positive at every member may vanish or
change sign, no longer force a refusal. The regime certificate uses it for
every Perron sign. It removes box artefacts only; a sign change inside the
hull still refuses.

Cell skipping alone cannot separate a margin from the hull where both vanish
together: at `l0 = 5`, `r = 1` the descent margin `1 - 5u(1+h)` (times
`h(1+h)`) is positive at every member but its margin at `l = 5` is about
`1/(5d)`, so the member images accumulate at the box corner `(u, t) -> (1/5, 0)`
where the margin and `S` vanish together and every cell containing the corner
stays mixed. The second step of Lemma 3' is algebraic: when
`f(0, u) = q S(0, u)` for one rational `q = num/den`, `den > 0`, put
`g = den f - num S`; its `h`-free part vanishes, so `g = h g'`, and `S >= 0` at
members gives `f > 0` wherever `g > 0` (if `q >= 0`) and `f < 0` wherever
`g < 0` (if `q <= 0`). Here `(1 - 5u(1+h)) - S = h(1 + u + u h) > 0`, decided
by Bernstein at depth 0. The two plus regimes refused on the box (low `r = 1`
and `r = 2`) are accepted this way; every other sign is decided directly.

**Lemma 4 (identities, re-proved by the certificate).** Coefficient-wise in
`(h, u, n)`: `h (M^T L)_j - (1+h) L_j = -P` for each letter, with
`M^T L = (2L_x + n L_y + d L_y, L_x + L_c + n L_y, L_x + L_c + (n+eps) L_y)`
and `d L_y h = u (1+h)`; `E(eps) = P.a` and `P.b = -h(1+h)` for the Perron
polynomial `P = E - n h(1+h)` written as `A + n B`; and `n^3 P(n, 1/n) = -(1+eps) n^2 - n d - (1-eps) n - d`
has every coefficient `<= 0` as a polynomial in `(n, d)` and is not zero, so
it is negative at every member, where `n >= 1` and `d >= 1` make each
monomial positive.

## What the uniform verifier does

It is the ray certificate with these substitutions, otherwise line for line:
`a_*` comparisons become regime comparisons (Lemma 1 + reduction),
`a_div_ceil/floor` become Lemma 2, `AffH.sign` becomes Lemma 3, the Segment
run lengths become gap forms, and the `n0`-based checks become `(l0, d0)`.
Output: `CLASS_A_REGIME_CLOSURE`, `CLASS_A_REGIME_DESCENT` and
`CLASS_A_REGIME_BOUNDARY_HITTING eps=.. regime=.. l>=l0 d>=d0` receipts.

**Theorem shape.** For each sign, the fitted regimes cover every residue of
every gap `d >= D(eps)` (`D(-1) = 7`, `D(+1) = 11`, the largest fitted floor;
`psc.class_a_gap_theorem.eventual_cover` proves the covering pattern once for
all larger gaps). A regime certifies from its *uniform* floor `d0`, which may
exceed its fitted floor; the gaps in between are finite rays certified on the
same tables by the ray certificate, with exact complete graphs below the ray
floor. The residues of `5 <= d < D(eps)` that no fitted regime reaches (seven
rays of the plus sign: `(d, r) = (5,1), (5,2), (6,1), (6,2), (7,2), (7,3),
(8,3)`) carry their own ray tables, as for `d <= 4`. All of this is quantified
over `l >= l0` (`l0 = 5`, where the regime rows were fitted): the theorem is
boundary hitting on every class-A line of gap `d >= 5` for every member
`n = d l + r >= 5 d`. The strip `n < 5 d` (every gap `d > n/5` up to the PIP
bound `d <= 2n + 6 eps + 5`) is **not** covered: for each fixed `l < 5` it is
again a two-parameter family in `(d, r)`, and its label sets have not been
fitted. It is the recorded remaining gap of class A, not a finite list of
exceptions. Nothing is claimed beyond what `kernel/class_a_gap_theorem.mojo
certify-all 5` accepts.

## Module contract (for the implementation)

`kernel/psc/gap_form.mojo`
- `struct GapForm(ImplicitlyCopyable, Copyable, Movable)`: `c1, cl, cd, cld, cr: Int`;
  `__init__(out self, c1, cl, cd, cld, cr)`; `add`, `sub`, `scale(Int)`; `const(Int)`,
  `lin(a, b)` (= `a l + b`) constructors (module-level `def`s).
- `struct Regime(ImplicitlyCopyable, Copyable, Movable)`: `eps, kind (0 low, 1 high, 2 middle), j, j1, l0, d0: Int`;
  of its comparisons the certificate uses only `nonneg` (descent realizability)
  and the divisions; after division every comparison is on `l`-affine forms
  through the ray `a_le` at `n0 = l0`, so `le`, `max`, `min` are tested but unused;
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
- `def sign_within_hull(f: PolyHU, side: PolyHU, l0: Int, d0: Int, max_depth: Int = 12) raises -> Int`: Lemma 3 with Lemma 3' (cells on which every Bernstein coefficient of `side` is negative are skipped; the zero `side` is no restriction); `regime_sign` calls it with `side = E - l0 u(1+h)`.
- `def sign_on_box(f: PolyHU, l0: Int, d0: Int, max_depth: Int = 12) raises -> Int`: Lemma 3 (substitute `h = u t`, map `(0,1/l0) x (0,1/d0]` to the unit square, Bernstein over `finite_exact.rat_q.Q`, subdivision); returns `0` for the zero polynomial, `+-1` when certified, raises `UNDECIDED sign ...` otherwise. Strip common monomial factors `u^a t^b` first (positive on the box).
- Tests `kernel/tests/test_poly_hu.mojo`: known-sign polynomials (e.g. `1 + u + h` positive; `u - 1` negative on the box for `l0 >= 1`; `u t - 1/2 ...`), a polynomial that changes sign on the box must raise, a polynomial vanishing exactly on the face `t = 1/d0` must raise, agreement of `sign_on_box` with evaluation at a grid of rational points inside the box for a few dozen random-free polynomials, and `require_contract(...)`.

Both modules import only the vendored packages and `psc.exact` helpers, never
the ray certificate; the ray certificate is unchanged.
