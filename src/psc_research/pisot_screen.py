"""Oracle for the degree-`n` Pisot screen, exact and fail-closed.

The canonical implementation is `mojo/psc/pisot_screen.mojo`. This module is
the Python oracle it was differentially tested against, kept in step with it
function for function; `mojo/tests/test_pisot_screen.mojo` and
`tests/test_pisot_screen.py` pin the same classifications. The literature gate
for the diagnostic is `docs/pisot-screen-literature-gate-2026-09-16.md`.

`mojo/psc/pisot.mojo` decides the Pisot condition for degree three only, and it
does so with a cubic-specific trick: for one real root and one conjugate pair,
`beta * |beta_2|^2 = det`, so the conjugate pair sits inside the unit disc
exactly when `chi(det) < 0`. That identity does not generalise, so degree four
and above needs a different method.

The method here is exact and works at any degree. Send the unit circle to the
imaginary axis by the Moebius substitution

    z = (1 + w) / (1 - w),      q(w) = (1 - w)^n p((1 + w) / (1 - w)),

under which `|z| < 1` becomes `Re(w) < 0` and `|z| > 1` becomes `Re(w) > 0`.
Then count right-half-plane roots of `q` with a Routh array over exact
rationals. `z = -1` maps to `w = infinity`, which shows up as a degree drop in
`q`, and `z = 1` maps to `w = 0`; both are handled before the array is built.

Nothing here is floating point. Coefficients are `Fraction`, so no rounding and
no coefficient growth can change an answer.

**A refusal is not a negative result, and it is not a positive one either.**
The array is undecided when a first-column entry vanishes or a row terminates
early. Those are the two classical Routh singularities and they do not mean the
same thing. A *vanishing row* is handled here by the auxiliary-derivative rule.
A *first-column zero in a row that is not itself zero* is a different
singularity, with its own classical remedies, and this module implements none
of them: it refuses. Such a refusal says only that this array did not resolve.

So `REFUSED` must not be read either way. `x**3 - 3*x**2 - 3*x - 3` is refused
here and is nevertheless a genuine Pisot polynomial: its image is
`4w^3 + 12w - 8`, whose second Routh row is `[0, -8]`, while its roots are
3.951... and a conjugate pair of modulus 0.871... . Its real part on the
imaginary axis is the constant `-8`, so it has no axis root at all. That bound
is recorded in the literature gate; see `known_first_column_refusal`.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

PISOT = "pisot"
NOT_PISOT = "not-pisot"
REFUSED = "refused"

# Rational-root testing rules out linear factors only, so irreducibility is
# decided here only up to degree three, where no factor can escape it.
MAX_DECIDABLE_IRREDUCIBLE_DEGREE = 3


def degree(coeffs: Sequence[int]) -> int:
    """Index of the highest non-zero coefficient; `-1` for the zero polynomial.
    Coefficients are low-degree-first throughout this module."""
    for i in range(len(coeffs) - 1, -1, -1):
        if coeffs[i] != 0:
            return i
    return -1


def evaluate(coeffs: Sequence[Fraction | int], x: Fraction) -> Fraction:
    """Horner evaluation."""
    acc = Fraction(0)
    for c in reversed(coeffs):
        acc = acc * x + Fraction(c)
    return acc


def is_monic_integer(coeffs: Sequence[int]) -> bool:
    n = degree(coeffs)
    return n >= 1 and coeffs[n] == 1 and all(isinstance(c, int) for c in coeffs)


def cauchy_bound(coeffs: Sequence[int]) -> Fraction:
    """A rational `B` with every root of monic `p` strictly inside `|z| < B`."""
    n = degree(coeffs)
    return Fraction(1 + max((abs(coeffs[i]) for i in range(n)), default=0))


def halfplane_transform(coeffs: Sequence[int]) -> list[Fraction]:
    """`q(w) = (1 - w)^n p((1 + w) / (1 - w))`, low-degree-first.

    `q` has degree `n` unless `z = -1` is a root of `p`, in which case the
    leading coefficient vanishes and the degree drops."""
    n = degree(coeffs)
    out = [Fraction(0)] * (n + 1)
    for k in range(n + 1):
        if coeffs[k] == 0:
            continue
        left = _binomial_power(k, +1)        # (1 + w)^k
        right = _binomial_power(n - k, -1)   # (1 - w)^(n - k)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                out[i + j] += Fraction(coeffs[k]) * a * b
    return out


def _binomial_power(k: int, sign: int) -> list[Fraction]:
    """Coefficients of `(1 + sign * w)^k`."""
    row = [Fraction(1)]
    for _ in range(k):
        row = [
            (row[i] if i < len(row) else Fraction(0))
            + sign * (row[i - 1] if i >= 1 else Fraction(0))
            for i in range(len(row) + 1)
        ]
    return row


def routh_right_half_plane_count(q: Sequence[Fraction]) -> int | None:
    """Roots of `q` with `Re(w) > 0`, or None when the array is undecided.

    None means this array did not resolve, and nothing more. It never means
    zero, and it is not evidence of a root on the imaginary axis: a
    first-column zero in a non-zero row refuses here whether or not `q` has an
    axis root. Use `has_root_on_unit_circle` to decide that question."""
    n = degree(q)
    if n < 1:
        return None
    q = list(q[: n + 1])
    rows = [
        [q[n - 2 * i] for i in range(n // 2 + 1)],
        [q[n - 1 - 2 * i] for i in range((n - 1) // 2 + 1)],
    ]
    while rows[-1] and len(rows) <= n:
        above, current = rows[-2], rows[-1]
        if all(x == 0 for x in current):
            # A vanishing row means `q` has roots placed symmetrically about the
            # origin, which in `z` is a reciprocal pair. The classical remedy is
            # to continue from the derivative of the auxiliary polynomial the row
            # above represents. Without it the array stops and every reciprocal
            # Pisot polynomial, `x^2 - 3x + 1` among them, is refused.
            rows[-1] = current = _auxiliary_derivative(above, n - (len(rows) - 2))
            if not current or all(x == 0 for x in current):
                return None
        if current[0] == 0:
            return None                      # first-column zero, not a whole row
        nxt = []
        for i in range(1, max(len(above), len(current))):
            a = above[i] if i < len(above) else Fraction(0)
            b = current[i] if i < len(current) else Fraction(0)
            nxt.append((current[0] * a - above[0] * b) / current[0])
        while nxt and nxt[-1] == 0:
            nxt.pop()
        if not nxt:
            break
        rows.append(nxt)
    column = [row[0] for row in rows if row]
    if len(column) < n + 1 or any(x == 0 for x in column):
        return None                          # early termination or a zero
    return sum(1 for i in range(n) if (column[i] > 0) != (column[i + 1] > 0))


def _auxiliary_derivative(row: Sequence[Fraction], top_degree: int) -> list[Fraction]:
    """Derivative of the auxiliary polynomial a Routh row stands for.

    A row holds the coefficients of `w^d, w^(d-2), w^(d-4), ...`, so the
    derivative's coefficients in the same stepped layout are those scaled by the
    exponent they carried."""
    out = []
    for i, value in enumerate(row):
        power = top_degree - 2 * i
        if power <= 0:
            break
        out.append(value * power)
    return out


def _poly_gcd(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Monic greatest common divisor over the rationals."""
    a, b = [Fraction(x) for x in a], [Fraction(x) for x in b]
    while degree(b) >= 0:
        a, b = b, _poly_rem(a, b)
    d = degree(a)
    if d < 0:
        return []
    return [x / a[d] for x in a[: d + 1]]


def _poly_rem(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    a, db = list(a), degree(b)
    while degree(a) >= db >= 0:
        d = degree(a)
        factor = a[d] / b[db]
        for i in range(db + 1):
            a[d - db + i] -= factor * b[i]
        a[d] = Fraction(0)
    return a[:db] if db > 0 else []


def _real_root_count(p: Sequence[Fraction]) -> int:
    """Distinct real roots, by Sturm's theorem on a Cauchy bound."""
    n = degree(p)
    if n < 1:
        return 0
    chain = [list(p[: n + 1]), [Fraction(i) * p[i] for i in range(1, n + 1)]]
    while degree(chain[-1]) > 0:
        rest = _poly_rem(chain[-2], chain[-1])
        if degree(rest) < 0:
            break
        chain.append([-x for x in rest])
    bound = Fraction(1) + max((abs(p[i] / p[n]) for i in range(n)), default=Fraction(0))

    def changes(x: Fraction) -> int:
        signs = [evaluate(c, x) for c in chain]
        signs = [s for s in signs if s != 0]
        return sum(1 for i in range(len(signs) - 1) if (signs[i] > 0) != (signs[i + 1] > 0))

    return changes(-bound) - changes(bound)


def has_root_on_unit_circle(coeffs: Sequence[int]) -> bool:
    """Whether `p` has a root of absolute value exactly one.

    Such a root disqualifies a Pisot polynomial outright, and the Routh count
    alone cannot see it: once the auxiliary-row rule completes an array, a Salem
    polynomial, whose conjugates lie *on* the circle, counts one root outside
    and reads as Pisot. This is the check that stops that.

    On the imaginary axis `w = iy` the transform splits into real and imaginary
    parts, so a purely imaginary root of `q` is a common real root of the two."""
    if evaluate(coeffs, Fraction(1)) == 0 or evaluate(coeffs, Fraction(-1)) == 0:
        return True
    q = halfplane_transform(coeffs)
    real_part, imag_part = [], []
    for k, c in enumerate(q):
        sign = (-1) ** (k // 2)
        if k % 2 == 0:
            while len(real_part) <= k:
                real_part.append(Fraction(0))
            real_part[k] = sign * c
        else:
            while len(imag_part) <= k:
                imag_part.append(Fraction(0))
            imag_part[k] = sign * c
    shared = _poly_gcd(real_part, imag_part)
    return degree(shared) >= 1 and _real_root_count(shared) > 0


def roots_outside_unit_circle(coeffs: Sequence[int]) -> int | None:
    """How many roots of `p` satisfy `|z| > 1`, or None when undecided.

    Undecided means the count was not established. A root at `z = 1` or
    `z = -1` is one reason; an unresolved Routh singularity is another, and it
    carries no implication about the unit circle."""
    n = degree(coeffs)
    if n < 1:
        return None
    if evaluate(coeffs, Fraction(1)) == 0 or evaluate(coeffs, Fraction(-1)) == 0:
        return None                          # a root at z = 1 or z = -1
    return routh_right_half_plane_count(halfplane_transform(coeffs))


def screen(coeffs: Sequence[int]) -> str:
    """`PISOT`, `NOT_PISOT`, or `REFUSED` for a monic integer polynomial.

    `PISOT` means exactly one root lies outside the closed unit disc, that root
    is real and greater than one, and every other root lies *strictly* inside
    the disc. The last clause is not redundant: a Salem polynomial meets the
    first two and is refused by `has_root_on_unit_circle` precisely because its
    remaining conjugates sit on the boundary.

    It is a statement about root location, not about irreducibility: use
    `irreducibility` for that, and note that a Pisot *number* is defined by its
    minimal polynomial."""
    if not is_monic_integer(coeffs):
        return REFUSED
    if has_root_on_unit_circle(coeffs):
        return NOT_PISOT                     # a conjugate on the circle disqualifies
    outside = roots_outside_unit_circle(coeffs)
    if outside is None:
        return REFUSED
    if outside != 1:
        return NOT_PISOT
    # The lone root outside is real, since non-real roots come in conjugate
    # pairs of equal absolute value. Every other root satisfies |z| < 1, so the
    # only root in [1, B) is that one, and a sign change across it says it is
    # positive. p(1) is non-zero, or `outside` would have been None.
    bound = cauchy_bound(coeffs)
    low = evaluate(coeffs, Fraction(1))
    high = evaluate(coeffs, bound)
    if (low > 0) == (high > 0):
        return NOT_PISOT                     # the outside root is below -1
    return PISOT


def irreducibility(coeffs: Sequence[int]) -> str:
    """`"irreducible"`, `"reducible"`, or `"refused"` over the rationals.

    Degree one is irreducible outright. Above that, a rational root of a monic
    integer polynomial is an integer dividing the constant term, which settles
    degrees two and three because a factorisation there must include a linear
    factor. At degree four and above a product of
    two irreducible quadratics has no rational root, so the same test proves
    nothing and this refuses rather than guessing."""
    n = degree(coeffs)
    if not is_monic_integer(coeffs):
        return "refused"
    if n == 1:
        # A non-constant linear polynomial is irreducible, and it always has a
        # rational root, so the test below would call every one of them
        # reducible. Degree one has to be settled before asking.
        return "irreducible"
    if _has_rational_root(coeffs):
        return "reducible"
    if n > MAX_DECIDABLE_IRREDUCIBLE_DEGREE:
        return "refused"
    return "irreducible"


def _has_rational_root(coeffs: Sequence[int]) -> bool:
    constant = coeffs[0]
    if constant == 0:
        return True                          # zero is a root
    for divisor in _divisors(abs(constant)):
        for candidate in (divisor, -divisor):
            if evaluate(coeffs, Fraction(candidate)) == 0:
                return True
    return False


def _divisors(value: int) -> list[int]:
    out, d = [], 1
    while d * d <= value:
        if value % d == 0:
            out.append(d)
            if d != value // d:
                out.append(value // d)
        d += 1
    return sorted(out)


# --- non-claims -----------------------------------------------------------------


def known_first_column_refusal() -> list[int]:
    """`x**3 - 3*x**2 - 3*x - 3`: Pisot, refused, and with no root on the circle.

    Kept as a named witness so the bound is visible from the module rather than
    only from the tests. Its image `4w^3 + 12w - 8` has second Routh row
    `[0, -8]`, a first-column zero this module does not resolve."""
    return [-3, -3, -3, 1]


def refusal_means_not_pisot() -> bool:
    """A refusal says the method could not decide, which is a different fact
    from the polynomial not being Pisot."""
    return False


def screen_decides_irreducibility() -> bool:
    """Root location and irreducibility are independent questions here."""
    return False


def refusal_means_root_on_unit_circle() -> bool:
    """The converse mistake: a refusal is not evidence of a circle root, so a
    refused specimen must never be recorded as one."""
    return False
