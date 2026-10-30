"""Integer-only regression for the exact Class-C normalized Perron tile-ratio chambers.

Docs: docs/class-c-lower-cone-tile-ratio-walls-2026-10-30.md
Polynomial identities are proved in the note. These bounded tests validate
the arithmetic independently from psc.symbolic_cone and perron_field3.
No floating-point roots, rounding, or inferred BH conclusions.
"""
from std.testing import assert_equal, assert_true


def cube_test(n: Int, d: Int, eps: Int, m: Int) -> Int:
    """m^3 chi(2+(n+d)/m), evaluated using integers only."""
    var p = n + d
    var t = 2 * m + p
    var a = n - d + eps + 3
    var b = n - 3 * d + 3 * eps + 2
    return t * t * t - a * t * t * m + b * t * m * m - 2 * eps * m * m * m


def main() raises:
    var checked = 0
    for eps in [1, -1]:
        for d in range(7, 97):
            for c in range(d + 7):
                var n = 2 * d + (-5 if eps == 1 else 1) + c
                var p = n + d
                var g1: Int
                var f2: Int
                var f3: Int
                var f4: Int = 0
                if eps == 1:
                    g1 = (2 * d - 1) * c + 6 * d * d - 9 * d + 4
                    f2 = c * c + 2 * c * d - 2 * c - 3 * d * d - 2 * d - 3
                    f3 = 2 * c * c + 6 * c * d + c - 3 * d - 10
                    f4 = 3 * c * c + 10 * c * d + 10 * c + 3 * d * d + 6 * d - 13
                else:
                    g1 = (2 * d + 1) * c + 6 * d * d + 9 * d + 2
                    f2 = c * c + 2 * c * d + 6 * c - 3 * d * d - 2 * d + 9
                    f3 = 2 * c * c + 6 * c * d + 19 * c + 15 * d + 44
                var at_d_plus_1 = (d + 1) * (d + 1) * (d + 1) - (n - d + eps + 3) * (d + 1) * (d + 1) + (n - 3 * d + 3 * eps + 2) * (d + 1) - 2 * eps
                if eps == 1:
                    assert_equal(at_d_plus_1, -d * ((d + 1) * c - d - 3))
                    assert_equal(at_d_plus_1 > 0, c <= 1)
                else:
                    assert_equal(at_d_plus_1, -d * ((d + 1) * c + 3 * d + 5))
                    assert_true(at_d_plus_1 < 0)
                assert_equal(cube_test(n, d, eps, 1), p * g1)
                assert_equal(cube_test(n, d, eps, 2), -p * f2)
                assert_equal(cube_test(n, d, eps, 3), -p * f3)
                assert_true(g1 > 0)
                if eps == 1:
                    assert_equal(cube_test(n, d, eps, 4), -p * f4)
                    assert_true(f4 > 0)
                    if c == 0:
                        assert_equal(f3, -3 * d - 10)
                    if c == 1:
                        assert_equal(f3, 3 * d - 7)
                    if c == d + 1:
                        assert_equal(f2, -4)
                    if c == d + 2:
                        assert_equal(f2, 4 * d - 3)
                    if c == 0:
                        assert_true(f3 < 0)
                    elif c <= d + 1:
                        assert_true(f2 < 0 and f3 > 0)
                    elif c <= d + 4:
                        assert_true(f2 > 0)
                elif c <= d - 2:
                    assert_true(f2 < 0 and f3 > 0)
                    if c == d - 2:
                        assert_equal(f2, 1 - 4 * d)
                checked += 1
    print("TILE_RATIO_INTEGER_IDENTITIES_PASS", checked)
