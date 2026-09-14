"""Secondary Python oracle for the rational-interval layer.

Specification: docs/rational-interval-arithmetic-spec.md (sections 1 to 3).
Canonical implementation: ``mojo/psc/rational_interval.mojo``.

This oracle exists only to cross-check the spec's laws with an independently
written implementation over :class:`fractions.Fraction`. It is not a research
kernel and must not become the executable source of truth.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence


@dataclass(frozen=True)
class Interval:
    """Closed interval ``[lo, hi]`` with exact rational endpoints (spec 2.1)."""

    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval endpoints (J1)")

    @classmethod
    def point(cls, x: Fraction | int) -> "Interval":
        return cls(Fraction(x), Fraction(x))

    def __contains__(self, x: Fraction | int) -> bool:
        return self.lo <= x <= self.hi

    def __add__(self, o: "Interval") -> "Interval":
        return Interval(self.lo + o.lo, self.hi + o.hi)

    def __sub__(self, o: "Interval") -> "Interval":
        return Interval(self.lo - o.hi, self.hi - o.lo)

    def __mul__(self, o: "Interval") -> "Interval":
        products = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Interval(min(products), max(products))

    def reciprocal(self) -> "Interval":
        if self.contains_zero():
            raise ZeroDivisionError("reciprocal of an interval containing zero")
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, o: "Interval") -> "Interval":
        return self * o.reciprocal()

    def square(self) -> "Interval":
        if self.contains_zero():
            return Interval(Fraction(0), max(self.lo * self.lo, self.hi * self.hi))
        return self * self

    def contains_zero(self) -> bool:
        return 0 in self

    def strict_sign(self) -> int:
        """Three-valued sign (spec 2.4): ``0`` means unknown, never zero."""
        return 1 if self.lo > 0 else -1 if self.hi < 0 else 0

    def subset_of(self, o: "Interval") -> bool:
        return o.lo <= self.lo and self.hi <= o.hi


def horner(coeffs: Sequence[int], x: Interval) -> Interval:
    """Natural interval extension of an integer polynomial, low degree first."""
    acc = Interval.point(0)
    for c in reversed(coeffs):
        acc = acc * x + Interval.point(c)
    return acc


def filter_then_exact(enclosure: Interval, exact_sign: Callable[[], int]) -> tuple[int, bool]:
    """Spec 3.2: ``(sign, interval_certified)``; the oracle runs only on ``0``."""
    s = enclosure.strict_sign()
    return (s, True) if s != 0 else (exact_sign(), False)
