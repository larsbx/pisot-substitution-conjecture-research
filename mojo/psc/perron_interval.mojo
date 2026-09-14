"""Rational-interval enclosure layer for the cubic Perron embedding.

This module is intentionally separate from the Sturm--Tarski oracle. It first
isolates the distinguished Perron root inside an exact rational interval, then
uses the natural interval extension of ``a0 + a1 X + a2 X^2``. A strict sign
is returned only when the enclosure excludes zero. Ambiguous or invalid interval
work falls back to ``sign_at_perron``; it is never interpreted as a zero or a
negative mathematical result. Endpoints are unbounded ``finite_exact``
rationals, so refinement depth is limited by cost only, never by overflow.
"""

from finite_exact.interval_q import IQ
from finite_exact.rat_q import Q
from psc.exact import eval_int_poly_at_q, interval_horner_int, midpoint, q_int, q_sign, require_iq, strict_sign
from psc.perron_field3 import CubicElt, PerronField3, sign_at_perron


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


def _sign_at_rational(coeffs: List[Int], x: Q) raises -> Int:
    return q_sign(eval_int_poly_at_q(coeffs, x))


def perron_root_interval(
    field: PerronField3, refinements: Int = 10
) raises -> IQ:
    """Return an exact rational enclosure containing the unique Perron root.

    The initial bracket is located between consecutive integers in ``(1,B]``.
    It is then bisected a bounded number of times with exact rational
    arithmetic.
    """
    if refinements < 0:
        raise Error("Perron interval refinement count must be nonnegative")
    var coeffs = _charpoly(field)
    var bound = _integer_bound(field)
    if bound <= 1:
        raise Error("invalid Perron interval bound")

    var lo = Q.one()
    var flo = _sign_at_rational(coeffs, lo)
    if flo == 0:
        raise Error("irreducible Perron cubic unexpectedly vanishes at 1")
    var hi = q_int(bound)
    var found = False

    for k in range(2, bound + 1):
        var right = q_int(k)
        var fright = _sign_at_rational(coeffs, right)
        if fright == 0:
            raise Error("irreducible Perron cubic unexpectedly has an integer root")
        if fright != flo:
            hi = right.copy()
            found = True
            break
        lo = right.copy()
        flo = fright
    if not found:
        raise Error("failed to bracket the Perron root between consecutive integers")

    for _ in range(refinements):
        var mid = midpoint(lo, hi)
        var fm = _sign_at_rational(coeffs, mid)
        if fm == 0:
            raise Error("irreducible Perron cubic unexpectedly has a rational root")
        if fm == flo:
            lo = mid.copy()
            flo = fm
        else:
            hi = mid.copy()
    return require_iq(IQ(lo, hi), "Perron root enclosure")


struct PerronEnclosure(Copyable, Movable):
    """One field's Perron root enclosure, computed once and reused.

    Bracketing and bisection depend only on the field, so a census computes
    this once per substitution (AGENTS.md rule 3) and evaluates the natural
    interval extension of each ``x(beta)`` against the stored box.
    """

    var field: PerronField3
    var beta_box: IQ

    def __init__(out self, field: PerronField3, refinements: Int = 10) raises:
        self.field = field
        self.beta_box = perron_root_interval(field, refinements)

    def interval(self, x: CubicElt) raises -> IQ:
        """Natural rational interval extension of ``x(beta)``."""
        var coeffs: List[Int] = [x.a0, x.a1, x.a2]
        return interval_horner_int(coeffs, self.beta_box)

    def interval_sign(self, x: CubicElt) raises -> Int:
        """Return +/-1 when the rational enclosure proves the sign, else 0."""
        if x.is_zero():
            return 0
        return strict_sign(self.interval(x))

    def sign_decision(self, x: CubicElt) raises -> PerronIntervalDecision:
        """Interval-first sign decision with exact Sturm--Tarski fallback.

        ``interval_certified`` means specifically that a strict nonzero sign
        was proved because the entire rational enclosure excluded zero.
        Symbolic zero is exact but is not a strict interval sign certificate.
        """
        if x.is_zero():
            return PerronIntervalDecision(0, False)
        var boxed_sign = 0
        try:
            boxed_sign = self.interval_sign(x)
        except:
            boxed_sign = 0
        if boxed_sign != 0:
            return PerronIntervalDecision(boxed_sign, True)
        return PerronIntervalDecision(sign_at_perron(self.field, x), False)

    def sign_interval_first(self, x: CubicElt) raises -> Int:
        return self.sign_decision(x).sign


def cubic_perron_interval(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> IQ:
    """Natural rational interval extension of ``x(beta)``."""
    return PerronEnclosure(field, refinements).interval(x)


def interval_sign_at_perron(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> Int:
    """Return +/-1 when the rational enclosure proves the sign, else 0."""
    if x.is_zero():
        return 0
    return PerronEnclosure(field, refinements).interval_sign(x)


def perron_sign_decision(
    field: PerronField3,
    x: CubicElt,
    refinements: Int = 10,
) raises -> PerronIntervalDecision:
    """One-shot form of ``PerronEnclosure.sign_decision``; a failed bracket
    counts as an unresolved interval and falls back to the exact oracle."""
    if x.is_zero():
        return PerronIntervalDecision(0, False)
    var boxed_sign = 0
    try:
        boxed_sign = PerronEnclosure(field, refinements).interval_sign(x)
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
