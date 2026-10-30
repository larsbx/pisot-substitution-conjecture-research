"""Class-C exact PIP-boundary integer identity regression.

The quantified argument is proved by hand in
docs/class-c-residual-domain-2026-10-29.md. This bounded executable
checks only the displayed polynomial identities and their sharp signs.
It does not replace the proof and does not claim BH.
"""
from std.testing import assert_true, assert_equal


def pip_floor(d: Int, eps: Int) -> Int:
    return 2 * d - 3 * eps - 2


def chi(d: Int, eps: Int, n: Int, t: Int) -> Int:
    var a = n - d + eps + 3
    var b = n - 3 * d + 3 * eps + 2
    return t * t * t - a * t * t + b * t - 2 * eps


def main() raises:
    var checked = 0
    for eps in [1, -1]:
        for d in range(6, 65):
            var lo = pip_floor(d, eps)
            assert_equal(lo, 2 * d - 5 if eps == 1 else 2 * d + 1)
            for offset in range(-2, 9):
                var n = lo + offset
                if n - d + eps < 1:
                    continue
                assert_equal(chi(d, eps, n, -1), 2 * (2 * d - 3 * eps - n - 3))
                assert_equal(chi(d, eps, n, 1), -2 * d)
                assert_equal(chi(d, eps, n, 2), -2 * (d + n))
                assert_equal(chi(d, eps, n, -2), 2 * (5 * d - 6 * eps - 3 * n - 12))
                assert_equal(chi(d, eps, n, -1) < 0, n >= lo)
                if n >= lo:
                    assert_true(chi(d, eps, n, -2) < 0)
                    assert_true(chi(d, eps, n, 1) < 0)
                    assert_true(chi(d, eps, n, 2) < 0)
                if n == lo - 1:
                    assert_equal(chi(d, eps, n, -1), 0)
                checked += 1
    print("P_C integer identities PASS", checked, "normal-form members")
