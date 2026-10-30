#!/usr/bin/env python3
"""Independent exact-rational controls for the Class-C tile-ratio chamber proof.

No symbolic cone code, numerical root approximations or third-party packages.
The finite grid tests the *hand-proved* identities rather than replacing proof.
"""
from fractions import Fraction


def chi(n: int, d: int, eps: int, t: Fraction) -> Fraction:
    # Independent expanded cubic, not Mojo's factored characteristic form.
    A = n - d + eps + 3
    B = n - 3 * d + 3 * eps + 2
    return t * t * t - A * t * t + B * t - 2 * eps


def checked() -> None:
    cases = 0
    for eps in (1, -1):
        for d in range(7, 97):
            for c in range(d + 7):
                n = (2 * d - 5 if eps == 1 else 2 * d + 1) + c
                p = n + d
                assert p > 0
                expressions = (
                    (
                        (2*d-1)*c + 6*d*d - 9*d + 4,
                        c*c + 2*c*d - 2*c - 3*d*d - 2*d - 3,
                        2*c*c + 6*c*d + c - 3*d - 10,
                        3*c*c + 10*c*d + 10*c + 3*d*d + 6*d - 13,
                    )
                    if eps == 1 else (
                        (2*d+1)*c + 6*d*d + 9*d + 2,
                        c*c + 2*c*d + 6*c - 3*d*d - 2*d + 9,
                        2*c*c + 6*c*d + 19*c + 15*d + 44,
                    )
                )
                for m, expected in enumerate(expressions, start=1):
                    # Exact rational evaluation, then exact cross multiplication.
                    t = Fraction(2*m + p, m)
                    actual = (m**3) * chi(n, d, eps, t)
                    claimed = p * expected * (1 if m == 1 else -1)
                    assert actual == claimed, (d, eps, c, m, actual, claimed)
                g1, f2, f3 = expressions[:3]
                assert g1 > 0
                if eps == 1:
                    f4 = expressions[3]
                    assert f4 > 0
                    if c == 0:
                        assert f3 < 0
                    elif c <= d+1:
                        assert f3 > 0 and f2 < 0
                    elif c <= d+4:
                        assert f2 > 0
                    if c == 0:
                        assert f3 == -3*d-10
                    if c == 1:
                        assert f3 == 3*d-7
                    if c == d+1:
                        assert f2 == -4
                    if c == d+2:
                        assert f2 == 4*d-3
                elif c <= d-2:
                    assert f2 < 0 and f3 > 0
                    if c == d-2:
                        assert f2 == 1-4*d
                cases += 1
    print("TILE_RATIO_EXACT_RATIONAL_ORACLE_PASS", cases)


if __name__ == "__main__":
    checked()
