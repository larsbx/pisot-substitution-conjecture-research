"""Rational-interval enclosure layer for the cubic Perron embedding.

This module is intentionally separate from the Sturm--Tarski oracle.  It first
isolates the distinguished Perron root inside a checked rational interval, then
uses the natural interval extension of ``a0 + a1 X + a2 X^2``.  A strict sign
is returned only when the enclosure excludes zero.  Ambiguous or unsafe
interval work falls back to ``sign_at_perron``; it is never interpreted as a
zero or a negative mathematical result.
"""

from psc.perron_field3 import CubicElt, PerronField3, sign_at_perron
from psc.rational_interval import (
    CheckedRat,
    RatInterval,
    eval_int_poly_at_rat,
    interval_horner_int,
)


struct PerronIntervalDecision(ImplicitlyCopyable, Copyable, Movable):
    var sign: Int
    var interval_certified: Bool

    def __init__(out self, sign: Int, interval_certified: Bool):
        self.sign = sign
        self.interval_certified = interval_certified


def _safe_abs(x: Int) raises -> Int:
    if x == Int.MIN:
        raise Error("Perron interval cannot take abs(Int.MIN)")
    return -x if x < 0 else x


def _safe_add_one(x: Int) raises -> Int:
    if x == Int.MAX:
        raise Error("Perron interval integer bound overflow")
    return x + 1


def _integer_bound(field: PerronField3) raises -> Int:
    var m = _safe_abs(field.chi0)
    var t = _safe_abs(field.chi1)
    if t > m:
        m = t
    t = _safe_abs(field.chi2)
    if t > m:
        m = t
    return _safe_add_one(m)


def _charpoly(field: PerronField3) -> List[Int]:
    return [field.chi0, field.chi1, field.chi2, 1]


def _sign_at_rational(coeffs: List[Int], x: CheckedRat) raises -> Int:
    return eval_int_poly_at_rat(coeffs, x).sign()


def perron_root_interval(
    field: PerronField3, refinements: Int = 10
) raises -> RatInterval:
    """Return a checked rational enclosure containing the unique Perron root.

    The initial bracket is located between consecutive integers in ``(1,B]``.
    It is then bisected a bounded number of times with checked rational
    arithmetic.  Overflow raises and therefore cannot silently corrupt the box.
    """
    if refinements < 0:
        raise Error("Perron interval refinement count must be nonnegative")
    var coeffs = _charpoly(field)
    var bound = _integer_bound(field)
    if bound <= 1:
        raise Error("invalid Perron interval bound")

    var lo = CheckedRat(1, 1)
    var flo = _sign_at_rational(coeffs, lo)
    if flo == 0:
        raise Error("irreducible Perron cubic unexpectedly vanishes at 1")
    var hi = CheckedRat(bound, 1)
    var found = False

    for k in range(2, bound + 1):
        var right = CheckedRat(k, 1)
        var fright = _sign_at_rational(coeffs, right)
        if fright == 0:
            raise Error("irreducible Perron cubic unexpectedly has an integer root")
        if fright != flo:
            hi = right
            found = True
            break
        lo = right
        flo = fright
    if not found:
        raise Error("failed to bracket the Perron root between consecutive integers")

    for _ in range(refinements):
        var mid = lo.midpoint(hi)
        var fm = _sign_at_rational(coeffs, mid)
        if fm == 0:
            raise Error("irreducible Perron cubic unexpectedly has a rational root")
        if fm == flo:
            lo = mid
            flo = fm
        else:
            hi = mid
    return RatInterval(lo, hi)


def cubic_perron_interval(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> RatInterval:
    """Natural rational interval extension of ``x(beta)``."""
    var beta_box = perron_root_interval(field, refinements)
    var coeffs: List[Int] = [x.a0, x.a1, x.a2]
    return interval_horner_int(coeffs, beta_box)


def interval_sign_at_perron(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> Int:
    """Return +/-1 when the rational enclosure proves the sign, else 0."""
    if x.is_zero():
        return 0
    return cubic_perron_interval(field, x, refinements).strict_sign()


def perron_sign_decision(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> PerronIntervalDecision:
    """Interval-first sign decision with exact Sturm--Tarski fallback.

    Interval arithmetic is an accelerator/certificate layer.  If it is
    ambiguous or cannot be represented safely, the independent algebraic oracle
    decides the sign.  Therefore interval failure is never mathematical
    evidence.
    """
    if x.is_zero():
        # Exact coefficient equality proves zero; no strict interval excludes it.
        return PerronIntervalDecision(0, False)
    var boxed_sign = 0
    try:
        boxed_sign = interval_sign_at_perron(field, x, refinements)
    except:
        boxed_sign = 0
    if boxed_sign != 0:
        return PerronIntervalDecision(boxed_sign, True)
    return PerronIntervalDecision(sign_at_perron(field, x), False)


def sign_at_perron_interval_first(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> Int:
    return perron_sign_decision(field, x, refinements).sign
