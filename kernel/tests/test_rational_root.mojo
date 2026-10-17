"""Exact root shortcut equivalence, integer growth, and refusal boundaries."""
from std.testing import assert_equal, assert_true
from finite_exact.bigint_z import bigz_from_i64
from psc.exact import q_poly, q_int, q_is_zero
from psc.pisot import poly_eval
from psc.pisot_screen import has_rational_root, irreducibility, screen, known_first_column_refusal, IRREDUCIBLE, REDUCIBLE, IRREDUCIBILITY_REFUSED, SCREEN_REFUSED, SCREEN_NOT_PISOT
from rational_root_reference import has_rational_root as reference_root
from mojo_smoke.claims import require_contract


def check(p: List[Int], expected: Bool) raises:
    assert_equal(has_rational_root(p), expected)
    assert_equal(has_rational_root(p), reference_root(p))
    var padded = p.copy()
    padded.append(0)
    padded.append(0)
    assert_equal(has_rational_root(padded), expected)


def main() raises:
    for a in range(-4, 5):
        for b in range(-4, 5):
            for c in range(-4, 5):
                var p: List[Int] = [a, b, c, 1]
                var root = reference_root(p)
                check(p, root)
                assert_equal(irreducibility(p), REDUCIBLE if root else IRREDUCIBLE)
    var positive: List[Int] = [-6, -1, 1]
    var negative: List[Int] = [6, 5, 1]
    var zero: List[Int] = [0, -7, 0, 1]
    var square: List[Int] = [49, -14, 1]
    var large: List[Int] = [-1000003, 1, -1000003, 1]
    var large_negative: List[Int] = [1000003, 1, 1000003, 1]
    var many: List[Int] = [5040, -100, 20, -5, 1]
    var irreducible: List[Int] = [-1, 0, 0, -1, 1]
    var reducible_no_root: List[Int] = [1, 0, 2, 0, 1]
    # Horner at +/-36 exceeds Int64; a native Int accumulator would be unsound.
    var growth: List[Int] = [36, 9223372036854775807, 0, 1]
    check(positive, True)
    check(negative, True)
    check(zero, True)
    check(square, True)
    check(large, True)
    check(large_negative, True)
    check(many, False)
    check(irreducible, False)
    check(reducible_no_root, False)
    check(growth, False)
    assert_equal(irreducibility(irreducible), IRREDUCIBILITY_REFUSED)
    assert_equal(irreducibility(reducible_no_root), IRREDUCIBILITY_REFUSED)
    var linear: List[Int] = [-2, 1]
    assert_equal(irreducibility(linear), IRREDUCIBLE)
    var nonmonic: List[Int] = [1, 2]
    assert_equal(irreducibility(nonmonic), IRREDUCIBILITY_REFUSED)
    assert_equal(screen(nonmonic), SCREEN_REFUSED)
    assert_equal(screen(known_first_column_refusal()), SCREEN_REFUSED)
    var salem: List[Int] = [1, -1, -1, -1, 1]
    assert_equal(screen(salem), SCREEN_NOT_PISOT)
    # The old machine abs(Int.MIN) silently skipped enumeration. Test the exact
    # witness directly, not that unsafe baseline's incorrect negative answer.
    var minimum: List[Int] = [-9223372036854775807 - 1, 9223372036854775807, 1]
    assert_true(has_rational_root(minimum))
    # (x-2)(x^127-2520): small root before costly large candidates.
    var high = List[Int](length=129, fill=0)
    high[0] = 5040
    high[1] = -2520
    high[127] = -2
    high[128] = 1
    check(high, True)
    require_contract("Integer rational-root equivalence and fail-closed irreducibility")
