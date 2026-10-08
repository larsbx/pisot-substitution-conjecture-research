# P1c: boundary hitting on the wedge q < p < 2q of class B — 2026-10-08

**Status:** one theorem (Theorem W, §4), computer-assisted, repository-proved
and unreviewed, and the two-parameter method behind it (§§2–3). It is step 1
of §7 of [`p1-seed-strength-2026-10-08.md`](p1-seed-strength-2026-10-08.md)
("`k` symbolic"). It extends Theorem L′ from finitely many lines of Theorem E's
class B to a two-dimensional region, on both branches. No ledger node or
manuscript statement changes.

Canonical implementation:

- `kernel/psc/param_poly.mojo`: polynomials in two parameters, and the quadrant
  sign certificate;
- `kernel/psc/symbolic_line.mojo`, generalised: its coefficient ring is now
  `Q[s, d]`, and a line is the `d`-free case;
- driver `kernel/symbolic_wedge_certificate.mojo`, which reuses
  `certify_family_line` of `kernel/symbolic_line_certificate.mojo`;
- regression `kernel/tests/test_symbolic_wedge.mojo`;
- evidence workflow `.github/workflows/class-b-wedge-evidence.yml`.

## 1. What the data said

Class B is `sigma(x) = x y^p x`, `sigma(c) = c y^q x`, `sigma(y) = c y^r x`
with `r = q ± 1` and `p > q`. Write `p = q + s`. For fixed `q`, the size of the
exact swap-seed graph as `s` runs from 1 to `q + 5` is:

| branch | `q` | `p = q+1, q+2, q+3` | `q + 4 <= p <= 2q − 1` | `p = 2q, …, 2q+4` |
| --- | --- | --- | --- | --- |
| `+1` | 12, 20, 30 | 121, 77, 79 | **74 throughout** (`p = q+4`: 76) | 76, 84, 119, 123, 123 |
| `−1` | 20, 30 | 166, 144, 131 | 125, then a **123** plateau (`s` up to about `q/2`), then 125, 164, then a **171** plateau, then 173, 175, 186, 195, 112 | 124, 274, 255, 248, 233 |

On branch `+1` the graph is the same size across the whole interior of the
wedge. On branch `−1` there are two plateaus, split near `s = d`, where
`d = 2q − p`. Both suggest a two-parameter symbolic graph.

## 2. Why the one-parameter method does not extend verbatim

Take `(s, d)` as parameters (`q = s + d`, `p = q + s`). Running
`psc.symbolic_line` with coefficients in `Q[s, d]` hit three obstructions. Each
is a genuine two-parameter effect.

1. **Sturm chains change sign inside the wedge.** The Sturm count of the
   roots of `chi` in `(−1, 1)` reads an entry that is about
   `9 d^2 (s + d)^2 − 72 s^3`, which changes sign along `d^2 ≈ 8s`. The two
   non-Perron conjugates are a real pair on one side and a complex pair on the
   other. In a Tarski query `sign g(beta)`, an intermediate leading
   coefficient had top form `−d (d+s) (2d+s)^2 (d^2 − ds − s^2)`, which changes
   sign along the irrational ray `d / s = (1 + sqrt 5)/2`. The answer does not
   change there, but the chain is not valid where that coefficient vanishes.
2. **Run-position bounds are not affine on the whole quadrant.** One bound is
   `2s + d + 3` for `s > d` and `2s + d + 2` for `s <= d`. It is a floor of a
   function whose bounded part depends on `s / d`.
3. Signs of polynomials in two parameters have no "largest real root".

## 3. The method on a quadrant

A **cone** is an affine image of a quadrant: its parameters `(t, d)` range
over `{t > S, d > D}`, and the runs are affine in `(t, d)`. Every decision is
made on the quadrant, which only shrinks.

- **Signs of polynomials** (`param_poly.quadrant_sign`). `P > 0` on
  `{t > S, d > D}` if every coefficient of
  `(1 + u + v)^N P(S + u, D + v)` is `>= 0` and some is nonzero, for some
  `N <= 4` (Pólya). Every monomial and the multiplier are positive where
  `u, v > 0`. The reader tries `(S, D)` and then geometric enlargements, and
  keeps the first that certifies. A polynomial in `t` alone is still read by
  its largest real root, as on a line. A sign with no certificate raises.
- **PIP by Rouché.** For `chi = t^3 + c2 t^2 + c1 t + c0`, if
  `|c2| > 1 + |c1| + |c0|`, then on `|t| = 1` the term `c2 t^2` strictly
  dominates the rest. So `chi` has exactly two roots in the open unit disc and
  none on the circle. The third root is real, and it is the Perron root, so it
  lies in `(1, ∞)`. These are three sign reads, and none of them tells a real
  pair from a complex pair. (This is the classical dominant-coefficient
  sufficient condition for a Pisot polynomial; the argument here is
  self-contained.) The support, primitivity and rational-root screens are as
  on a line.
- **Signs at `beta` without a chain.** `beta` is enclosed in a bracket
  `lo < beta < hi` whose ends are rational functions of the parameters with
  certified positive denominators.
  - The seed bracket is `trace − k < beta < trace + j`, certified by the signs
    of `chi` at both ends, with the lower end `> 1`.
  - Level `k + 1` takes a Newton step from `hi` and a chord step from `lo`.
    Each new end is certified directly: `chi(lo') < 0`, and `chi(hi') > 0`
    with `hi' > 1`. Below `beta`, `chi < 0` exactly on `(1, beta)` and on
    intervals below 1.
  - For `r = g mod chi` (`deg r <= 2`, exact because `chi` is monic),
    `sign r(beta) = s` if `r` has the certified sign `s` at both ends and
    either `r'` has one certified sign at both ends (`r` is monotone), or `r`
    curves against `s`, or its vertex value `(4AC − B^2)/(4A)` has sign `s`.
  - Otherwise the reader refines, up to four levels, and then raises.
- **Run positions.** On a cone, a run end that is itself real binds, and it
  is tested first with one sign read. Only when it does not bind is the
  integer bound fitted, at three sample points (affine in both parameters),
  and certified by two sign reads as before. This removes obstruction 2
  wherever the run ends bind. Lines keep their old query order, so every
  pinned line verdict of Theorems L and L′ is reproduced unchanged.

*Lemma S₂ (soundness).* If the closure of a cone finishes on the quadrant
`{t > S, d > D}`, then for every integer point of that quadrant the exact
swap-seed overlap graph is the symbolic graph with the point substituted.

*Proof.* As Lemma S of
[`p1b-symbolic-line-2026-10-07.md`](p1b-symbolic-line-2026-10-07.md) §2, with
the threshold replaced by the quadrant. Every sign read is valid on the final
quadrant, because the quadrant only shrinks and each certificate holds on
every sub-quadrant. A bracketed sign at `beta` rests only on certified signs of
`chi` and `r` at the bracket ends and on the Rouché PIP step. `square`

## 4. Theorem W

Cut the wedge `q < p < 2q`, that is `s = p − q >= 1` and `d = 2q − p >= 1`,
into:

- **cone A**, `s >= d`: parameters `(e, d)` with `s = d + e`, so `q = e + 2d`
  and `p = 2e + 3d`;
- **cone B**, `s < d`: parameters `(s, e)` with `d = s + e`, so `q = 2s + e`
  and `p = 3s + e`.

| branch | cone | quadrant | symbolic vertices, all hitting | sign reads |
| --- | --- | --- | --- | --- |
| `+1` | A | `e >= 9, d >= 9` | 74 | 1,687 |
| `+1` | B | `s >= 9, e >= 1` | 74 | 1,687 |
| `−1` | A | `e >= 9, d >= 9` | 171 | 4,087 |
| `−1` | B | `s >= 9, e >= 5` | 123 | 2,751 |

Each cone is cross-checked, vertex for vertex, against the exact kernel at
`(t0, d0)`, `(t0 + 5, d0)`, `(t0, d0 + 5)` and `(t0 + 5, d0 + 5)`. The cross-checks
are not part of the proof. The vertex counts are the plateaus of §1.

The rest of the wedge lies on lines (`wedge_boundary`):

- cone A with `e <= 8`: the lines `s = d + e`, so `p = 3d + 2e`, `q = 2d + e`;
- cone A with `1 <= d <= 8`: the lines `p = 2q − d`;
- cone B with `1 <= s <= 8`: the lines `p = q + s`;
- on branch `−1`, cone B with `1 <= e <= 4`: the lines `d = s + e`, so
  `p = 3s + e`, `q = 2s + e`.

That is 25 lines on branch `+1` and 29 on branch `−1`. Each is certified by
`certify_family_line`: a symbolic graph from its threshold on, every PIP
member below it decided by the exact kernel, and a cross-check. §5 lists their
verdicts.

**Theorem W.** Let `sigma` be in class B, with `q < p < 2q` and `r = q ± 1`.
If `sigma` is PIP, then `|det M| = 2`, and every overlap reachable from any of
its swap seeds has an offset-zero descendant. Consequently, as in Theorem L′,
`sigma` has:

- strong coincidence for every pair (Corollary E2);
- productivity of every seed-reachable overlap (Corollary
  `cor:scc-reduction`(ii));
- **pure discrete spectrum** (Theorem `thm:main-density`);
- a **finite balanced-pair automaton** (Proposition
  `prop:G1-from-half-coincidences`).

Every member in the two cone quadrants is PIP (Rouché). Status:
computer-assisted, unreviewed, resting on Theorem E (unreviewed) and the
imported Barge–Štimac–Williams theorem, as Theorems L and L′ do.

Together with the lines `p = 2q + k`, `0 <= k <= 4` (branch `+1`) and
`0 <= k <= 3` (branch `−1`) of Theorem L′, this covers every PIP member of
class B with:

- `q < p <= 2q + 4` on branch `+1`;
- `q < p <= 2q + 3` on branch `−1`.

## 5. Boundary-line verdicts

BOUNDARY_TABLE

## 6. Literature gate (stop/go)

The family-level gate of
[`p1b-catch-up-free-ppvc-2026-10-07.md`](p1b-catch-up-free-ppvc-2026-10-07.md)
governs. A search on 2026-10-08 for pure discrete spectrum of non-unimodular
three-letter Pisot families found infinite-family results only for unimodular
families:

- Chevallier, *Yet another characterization of the Pisot substitution
  conjecture*, arXiv:1810.03500, which includes an automata-based proof for
  infinite families;
- Berthé–Bourdon–Jolivet–Siegel, a generic algorithm for families from
  continued-fraction algorithms.

It found nothing on class B. **GO**, with the same narrow novelty claim as
Theorem L.

The method is standard in its parts: Pólya's positivity certificate,
Rouché's theorem, and bracketed Newton and chord steps. Its combination with
the symbolic overlap closure is what is new here.

## 7. What this does not establish, and next

- **Branch `+1` above `p = 2q + 4`, branch `−1` above `p = 2q + 3`.** At
  `q = 12` the exact graph grows with `k = p − 2q` (149, 287, 297, …,
  3101 vertices for `k = 5, …, 23`). The next cone, `2q < p < 3q`, is untested.
  The `p ≫ q` corner still needs expansions in `sqrt(p)`.
- The full quadrant `(s, d)` does not close. A bound splits along `s = d`, so
  the cone cut is needed. Whether other families need finer fans is open.
- `quadrant_sign` is sound, not complete. Thresholds come from a geometric
  search and are not optimal. Lower thresholds would only shorten the boundary
  list.
- No review beyond its author.
