"""Exact regressions for the catch-up (one-tile) analysis (psc.one_tile)."""

from std.testing import assert_equal, assert_true
from psc.claim_tests import require_contract
from psc.one_tile import catch_up_free, mirror, one_tile, two_sided
from psc.vertex_coincidence import decide_vertex_coincidence


def sigma_of(a: List[Int], b: List[Int], c: List[Int]) -> List[List[Int]]:
    var sigma = List[List[Int]]()
    sigma.append(a.copy())
    sigma.append(b.copy())
    sigma.append(c.copy())
    return sigma^


def assert_counts(sigma: List[List[Int]], recurrent: Int, in_cu: Int, reach_cu: Int) raises:
    var v = one_tile(sigma)
    assert_equal(v.recurrent, recurrent)
    assert_equal(v.in_cu, in_cu)
    assert_equal(v.reach_cu, reach_cu)


def test_every_recurrent_vertex_reaches_a_catch_up() raises:
    """Q1 holds: cube 1160/1160/1160, golden pump 714/2/714 (only 2 recurrent
    vertices are themselves in CU, but all reach it), 0 -> 210, 1 -> 0,
    2 -> 110 704/4/704, plastic 68/12/68, Tribonacci 14/14/14."""
    assert_counts(sigma_of([1], [2, 2, 2], [0, 2, 2, 2]), 1160, 1160, 1160)
    assert_counts(sigma_of([1], [0, 2, 1], [0, 0, 1]), 714, 2, 714)
    assert_counts(sigma_of([2, 1, 0], [0], [1, 1, 0]), 704, 4, 704)
    assert_counts(sigma_of([1], [2], [0, 1]), 68, 12, 68)
    assert_counts(sigma_of([0, 1], [0, 2], [0]), 14, 14, 14)


def test_q1_fails_where_no_catch_up_is_reachable() raises:
    """0 -> 1, 1 -> 012, 2 -> 010: none of 694 recurrent vertices reaches a
    catch-up hit, so every new common vertex is a simultaneous birth;
    0 -> 1, 1 -> 12, 2 -> 022: 2 of 14 cannot reach one."""
    assert_counts(sigma_of([1], [0, 1, 2], [0, 1, 0]), 694, 0, 0)
    assert_counts(sigma_of([1], [1, 2], [0, 2, 2]), 14, 4, 12)
    # the 2 that cannot are fixed points of the inflation: nonzero closure is
    # the vertex itself; the 694 of the catch-up-free specimen are not short
    assert_equal(one_tile(sigma_of([1], [1, 2], [0, 2, 2])).short, 2)
    assert_equal(one_tile(sigma_of([1], [0, 1, 2], [0, 1, 0])).short, 0)


def assert_two_sided(sigma: List[List[Int]], recurrent: Int, left: Int, right: Int, either: Int) raises:
    var v = two_sided(sigma)
    assert_equal(v.recurrent, recurrent)
    assert_equal(v.reach_left, left)
    assert_equal(v.reach_right, right)
    assert_equal(v.reach_either, either)


def test_right_endpoints_do_not_rescue_q1() raises:
    """Right-endpoint catch-ups, read off the mirror substitution through the
    vertex map (a, b, t) -> (a, b, l_a - l_b - t). Both Tribonacci and its
    mirror have 14 recurrent vertices, but 6 of Tribonacci's are
    right-aligned, hence offset zero in the mirror, so the nonzero counts are
    14 and 8 and the check is per vertex. 1 -> 12, 2 -> 022: the same 2 of 14 reach neither; 1 -> 012,
    2 -> 010: none of 694 reaches a catch-up at either endpoint."""
    assert_two_sided(sigma_of([0, 1], [0, 2], [0]), 14, 14, 14, 14)
    assert_equal(one_tile(mirror(sigma_of([0, 1], [0, 2], [0]))).recurrent, 8)
    assert_equal(decide_vertex_coincidence(mirror(sigma_of([0, 1], [0, 2], [0]))).recurrent, 14)
    assert_two_sided(sigma_of([1], [1, 2], [0, 2, 2]), 14, 12, 12, 12)
    assert_two_sided(sigma_of([1], [0, 1, 2], [0, 1, 0]), 694, 0, 0, 0)
    var v = decide_vertex_coincidence(sigma_of([1], [0, 1, 2], [0, 1, 0]))
    assert_equal(v.holds, True)  # PPVC still holds: every hit is a simultaneous birth
    assert_equal(v.deepest, 14)


def test_lemma_p_explains_the_total_failures() raises:
    """Lemma P: with no proper prefix in M Z^3, no hit is a catch-up. Both
    total failures are |det M| = 2 and catch-up-free: for 1 -> 012, 2 -> 010,
    M Z^3 = {x + z even} and the proper prefixes 0, 01 have abelianisations
    (1,0,0), (1,1,0). So is the mirror. The partial failure 1 -> 12,
    2 -> 022 and the unimodular Tribonacci and plastic specimens are not."""
    assert_true(catch_up_free(sigma_of([1], [0, 1, 2], [0, 1, 0])))
    assert_true(catch_up_free(mirror(sigma_of([1], [0, 1, 2], [0, 1, 0]))))
    assert_true(catch_up_free(sigma_of([1], [2, 2], [0, 1, 2])))
    assert_true(not catch_up_free(sigma_of([1], [1, 2], [0, 2, 2])))
    assert_true(not catch_up_free(sigma_of([0, 1], [0, 2], [0])))
    assert_true(not catch_up_free(sigma_of([1], [2], [0, 1])))
    assert_equal(one_tile(sigma_of([1], [2, 2], [0, 1, 2])).in_cu, 0)


def main() raises:
    test_every_recurrent_vertex_reaches_a_catch_up()
    print("[PASS] test_every_recurrent_vertex_reaches_a_catch_up")
    test_q1_fails_where_no_catch_up_is_reachable()
    print("[PASS] test_q1_fails_where_no_catch_up_is_reachable")
    test_right_endpoints_do_not_rescue_q1()
    print("[PASS] test_right_endpoints_do_not_rescue_q1")
    test_lemma_p_explains_the_total_failures()
    print("[PASS] test_lemma_p_explains_the_total_failures")
    require_contract("one-tile catch-up analysis: recurrent/in-CU/reach-CU pinned on seven specimens; Q1 holds on cube, golden pump, 210/0/110, plastic, Tribonacci; fails totally on 1/012/010 (694/0/0) and partly on 1/12/022 (14/4/12, both failures short); two-sided (left/right/either), Tribonacci 14/14/14 of 14 (mirror recurrent 14, of which 8 nonzero), 1/12/022 12/12/12 of 14, 1/012/010 0/0/0 of 694 while PPVC holds with K_V 14; Lemma P catch-up-free on 1/012/010, its mirror and 1/22/012 (in_cu 0), not on 1/12/022, Tribonacci, plastic")
