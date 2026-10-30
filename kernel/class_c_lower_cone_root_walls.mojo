"""Finite exact-integer regression for proven Class-C Perron-root wall identities.

The quantified algebraic proof and scope are in
docs/class-c-lower-cone-root-walls-2026-10-30.md.
No numerical root approximation and no overlap-graph assumption.
The finite loops are regression controls, not themselves a uniform theorem.
"""
from std.testing import assert_equal, assert_true


def chi(d: Int, n: Int, eps: Int, t: Int) -> Int:
    var r = n - d + eps
    return (t - r) * (t - 1) * (t - 2) - 2 * n * (t - 2) - 2 * (n + d)


def main() raises:
    var tested = 0
    for d in range(7, 81):
        for eps in [1, -1]:
            # Test crossing points on both sides of the lower-cone boundary.
            for c in range(0, d + 7):
                var n = 2 * d + (-5 if eps == 1 else 1) + c
                var r = n - d + eps
                var at2 = chi(d, n, eps, r + 2)
                var at3 = chi(d, n, eps, r + 3)
                var at4 = chi(d, n, eps, r + 4)
                var at5 = chi(d, n, eps, r + 5)
                assert_true(at2 < 0)
                assert_true(at5 > 0)
                if eps == 1:
                    assert_equal(at2, -2 * ((d - 1) * c + d * d - 3 * d + 3))
                    assert_equal(at3, c * (c - 1) - d * (d - 1) - 2)
                    assert_equal(at4, 2 * (c * c + c * d - 1))
                    assert_equal(at5, 3 * c * c + 4 * c * d + 5 * c + d * d + 3 * d)
                    if c == 0:
                        assert_equal(at4, -2)
                    if c == 1:
                        assert_equal(at4, 2 * d)
                    if c <= d:
                        assert_true(at3 < 0)
                    else:
                        assert_true(at3 > 0)
                    if c >= 1:
                        assert_true(at4 > 0)
                    if c == d:
                        assert_equal(at3, -2)
                    if c == d + 1:
                        assert_equal(at3, 2 * d - 2)
                else:
                    assert_equal(at2, -2 * ((d + 1) * c + d * d + 3 * d + 1))
                    assert_equal(at3, c * (c + 3) - d * (d + 3) + 2)
                    assert_equal(at4, 2 * (c * c + c * d + 6 * c + 2 * d + 9))
                    assert_equal(at5, 3 * c * c + 4 * c * d + 25 * c + d * d + 15 * d + 52)
                    assert_true(at4 > 0)
                    if c <= d - 1:
                        assert_true(at3 < 0)
                    else:
                        assert_true(at3 > 0)
                    if c == d - 1:
                        assert_equal(at3, -2 * d)
                    if c == d:
                        assert_equal(at3, 2)
                tested += 1
    print("ROOT_WALL_INTEGER_IDENTITIES_PASS", tested)
