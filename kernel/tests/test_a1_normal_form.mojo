"""Exact regressions for the A1' normal-form census (a1_normal_form_census).

docs/p1a-a1-prime-2026-10-05.md §3a. The census decides A1' for each member of
the Proposition D normal form with the canonical exact procedure
`psc.coincidence_formula.coincidence_level`, so a negative would be a verdict
rather than an exhausted budget and the driver raises on one. These pins fix
the two things the sweep is for: that A1' holds on every member of two
parameter bounds, and that the hard tail does **not** move between them.
"""

from std.testing import assert_equal, assert_false, assert_true
from a1_normal_form_census import DEEP_LEVEL, census, normal_form
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.claim_tests import require_contract
from psc.coincidence_formula import coincidence_level, first_letter_merge_level
from psc.pisot import is_pip


def test_the_normal_form_is_built_as_proposition_d_states_it() raises:
    """`sigma(x) = x y^p s_x`, `sigma(c) = c y^q s_c`, `sigma(y) = t y^r s_y`."""
    var sigma = normal_form(2, 1, 0, 1, 0, 1, 1)
    assert_equal(sigma[0], List[Int]([0, 2, 2, 1]))  # x y y c
    assert_equal(sigma[1], List[Int]([1, 2, 0]))     # c y x
    assert_equal(sigma[2], List[Int]([1, 1]))        # c c
    # and it is a genuine member: PIP with |det M| = 2
    assert_true(is_pip(Mat3(substitution_incidence(sigma))))
    assert_equal(abs(Mat3(substitution_incidence(sigma)).det()), 2)
    # Every image begins with its own letter for x and c, which is the template's
    # hypothesis: the first-letter map fixes both letters of the bad edge.
    assert_equal(sigma[0][0], 0)
    assert_equal(sigma[1][0], 1)


def test_a_normal_form_member_is_never_merged_at_the_endpoint() raises:
    """Proposition A: `h` fixes both `x` and `c`, so `h^n(x) != h^n(c)` always
    and the pair is residual. The merge level must be absent."""
    var sigma = normal_form(2, 1, 0, 1, 0, 1, 1)
    assert_true(first_letter_merge_level(sigma, 0, 1) < 0)
    # and the witness exists, strictly interior
    assert_equal(coincidence_level(sigma, 0, 1), 4)


def test_the_all_odd_case_is_excluded_by_lemma_d0() raises:
    """Lemma D0's mechanism: if every image had length two, every column of `M`
    would sum to two, so the Perron root would be the rational number 2 and the
    characteristic cubic could not be irreducible. The length-two members of the
    normal form are exactly those with `p = q = r = 0`, and none is PIP."""
    for sx in range(2):
        for sc in range(2):
            for t in range(2):
                for sy in range(2):
                    var sigma = normal_form(0, 0, 0, sx, sc, t, sy)
                    var m = Mat3(substitution_incidence(sigma))
                    for j in range(3):
                        var col = 0
                        for i in range(3):
                            col += m.e[3 * i + j]
                        assert_equal(col, 2)
                    assert_false(is_pip(m))


def test_a1_prime_holds_on_the_normal_form_and_the_tail_does_not_move() raises:
    """The census at two bounds. A1' holds on every member of both -- the driver
    raises otherwise -- and the level-4-and-up rows are identical, so the hard
    cases do not scale with the parameters."""
    var small = census(5)
    assert_equal(small.members, 174)
    assert_equal(small.levels.count(2), 96)
    assert_equal(small.levels.count(3), 64)
    assert_equal(small.max_level, 7)
    assert_equal(len(small.deep), 14)

    var large = census(8)
    assert_equal(large.members, 420)
    assert_equal(large.levels.count(2), 268)
    assert_equal(large.levels.count(3), 138)
    assert_equal(large.max_level, 7)
    assert_equal(len(large.deep), 14)

    # The tail: identical counts at every level at or above DEEP_LEVEL, while
    # the shallow counts grew. That is the whole point of the sweep.
    assert_true(large.levels.count(2) > small.levels.count(2))
    assert_true(large.levels.count(3) > small.levels.count(3))
    for k in range(DEEP_LEVEL, small.max_level + 1):
        assert_equal(small.levels.count(k), large.levels.count(k))
    assert_equal(small.levels.count(4), 8)
    assert_equal(small.levels.count(5), 2)
    assert_equal(small.levels.count(6), 2)
    assert_equal(small.levels.count(7), 2)

    # Every deep member has small parameters, and they pair off under x <-> c.
    for i in range(len(small.deep)):
        assert_true(small.deep[i].p <= 3)
        assert_true(small.deep[i].q <= 3)
        assert_true(small.deep[i].r <= 3)


def test_the_deepest_member_is_the_one_the_note_names() raises:
    """`sigma(x) = x y c`, `sigma(c) = c x`, `sigma(y) = c y c` at level 7, and
    its mirror under `x <-> c`."""
    var deepest = normal_form(1, 0, 1, 1, 0, 1, 1)
    assert_equal(deepest[0], List[Int]([0, 2, 1]))  # x y c
    assert_equal(deepest[1], List[Int]([1, 0]))     # c x
    assert_equal(deepest[2], List[Int]([1, 2, 1]))  # c y c
    assert_true(is_pip(Mat3(substitution_incidence(deepest))))
    assert_equal(abs(Mat3(substitution_incidence(deepest)).det()), 2)
    assert_equal(coincidence_level(deepest, 0, 1), 7)

    var mirror = normal_form(0, 1, 1, 1, 0, 0, 0)
    assert_equal(mirror[0], List[Int]([0, 1]))      # x c
    assert_equal(mirror[1], List[Int]([1, 2, 0]))   # c y x
    assert_equal(mirror[2], List[Int]([0, 2, 0]))   # x y x
    assert_equal(coincidence_level(mirror, 0, 1), 7)


def test_the_bound_is_refused_rather_than_truncated() raises:
    var raised = False
    try:
        _ = census(99)
    except:
        raised = True
    assert_true(raised)


def main() raises:
    test_the_normal_form_is_built_as_proposition_d_states_it()
    print("[PASS] test_the_normal_form_is_built_as_proposition_d_states_it")
    test_a_normal_form_member_is_never_merged_at_the_endpoint()
    print("[PASS] test_a_normal_form_member_is_never_merged_at_the_endpoint")
    test_the_all_odd_case_is_excluded_by_lemma_d0()
    print("[PASS] test_the_all_odd_case_is_excluded_by_lemma_d0")
    test_a1_prime_holds_on_the_normal_form_and_the_tail_does_not_move()
    print("[PASS] test_a1_prime_holds_on_the_normal_form_and_the_tail_does_not_move")
    test_the_deepest_member_is_the_one_the_note_names()
    print("[PASS] test_the_deepest_member_is_the_one_the_note_names")
    test_the_bound_is_refused_rather_than_truncated()
    print("[PASS] test_the_bound_is_refused_rather_than_truncated")
    require_contract("A1' on the Proposition D normal form (sigma(x) = x y^p s_x, sigma(c) = c y^q s_c, sigma(y) = t y^r s_y), decided by the canonical exact psc.coincidence_formula.coincidence_level so a negative is a verdict: A1' holds on every PIP member with |det M| = 2 at parameter bounds 5 and 8 (174 and 420 members), the deepest level is 7 at both, and the level-4-and-up rows are identical (8/2/2/2) while levels 2 and 3 grow (96/64 to 268/138) -- the hard tail does not scale with the parameters, and all 14 deep members have p, q, r <= 3; no member is merged at the endpoint, as Proposition A requires; the p = q = r = 0 members all have every column of M summing to 2 and none is PIP, which is Lemma D0's mechanism; the deepest member is sigma(x) = xyc, sigma(c) = cx, sigma(y) = cyc with its mirror under x <-> c; a parameter bound past MAX_BOUND is refused rather than truncated")
