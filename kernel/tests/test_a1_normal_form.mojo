"""Exact regressions for the A1' normal-form census (a1_normal_form_census).

docs/p1a-a1-prime-2026-10-05.md §3a. The census decides A1' for each member of
the Proposition D normal form with the canonical exact procedure
`psc.coincidence_formula.coincidence_level`, so a negative would be a verdict
rather than an exhausted budget and the driver raises on one. These pins fix
the two things the sweep is for: that A1' holds on every member of two
parameter bounds, and that the hard tail does **not** move between them.
"""

from std.testing import assert_equal, assert_false, assert_true
from a1_normal_form_census import (
    C,
    CLASS_A,
    CLASS_B,
    CLASS_C,
    CLASS_D,
    DEEP_LEVEL,
    X,
    census,
    class_member,
    f_at,
    lemma_witness,
    normal_form,
    residual_points,
    shared_tile_at,
    theorem_e_check,
)
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


def test_theorem_e_lemmas_cover_everything_but_the_listed_residue() raises:
    """Theorem E's certificate at parameter bound 11: every named lemma witness
    is a shared tile, every PIP point satisfies the Pisot necessary conditions
    f(1) < 0 and f(-1) < 0, and the PIP points no lemma covers are exactly the
    27 listed. Bound 11 is the smallest that reaches the whole residue, whose
    largest member is (11, 0, 1) in class B."""
    var t = theorem_e_check(11)
    assert_equal(t.lemma_failed, 0)
    assert_equal(t.lemma_verified, 453)
    assert_equal(t.pip_points, 383)
    assert_equal(t.pisot_conditions_held, 383)
    assert_equal(t.residual_found, 27)
    assert_equal(t.residual_unexpected, 0)


def test_every_residual_point_is_eventually_coincident() raises:
    """The finite part of Theorem E: each of the 27 residual points is decided
    by the exact procedure, and every one is eventually coincident."""
    var expected = List[List[Int]]()
    expected.append(List[Int]([4, 3, 3]))                                   # A
    expected.append(List[Int]([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]))        # B
    expected.append(List[Int]([4, 3, 3, 3]))                                # C
    expected.append(List[Int]([6, 7, 5, 4, 3, 4, 3, 3]))                    # D
    var total = 0
    for cls in range(4):
        var pts = residual_points(cls)
        assert_equal(len(pts), len(expected[cls]))
        for k in range(len(pts)):
            var sigma = class_member(cls, pts[k][0], pts[k][1], pts[k][2])
            var m = Mat3(substitution_incidence(sigma))
            assert_true(is_pip(m))
            assert_equal(abs(m.det()), 2)
            assert_equal(coincidence_level(sigma, X, C), expected[cls][k])
            total += 1
    assert_equal(total, 27)


def test_the_three_lemmas_name_real_shared_tiles() raises:
    """Spot checks of each lemma's closed-form position, one per sub-case."""
    # L_BC, class B: p > q, r >= 1, q >= 1.
    var w = lemma_witness(CLASS_B, 3, 1, 2)
    assert_equal(w.level, 2)
    assert_true(shared_tile_at(class_member(CLASS_B, 3, 1, 2), w.level, w.position))
    # L_BC, class C.
    w = lemma_witness(CLASS_C, 4, 2, 1)
    assert_equal(w.level, 2)
    assert_true(shared_tile_at(class_member(CLASS_C, 4, 2, 1), w.level, w.position))
    # L_D, both orders.
    w = lemma_witness(CLASS_D, 3, 2, 2)
    assert_equal(w.level, 2)
    assert_true(shared_tile_at(class_member(CLASS_D, 3, 2, 2), w.level, w.position))
    w = lemma_witness(CLASS_D, 2, 3, 3)
    assert_equal(w.level, 2)
    assert_true(shared_tile_at(class_member(CLASS_D, 2, 3, 3), w.level, w.position))
    # L_A, the four sub-cases: r = q +- 1, p = q + 1 or p > q + 1.
    for pqr in [(5, 2, 3), (3, 2, 3), (6, 3, 2), (5, 4, 3)]:
        var p = pqr[0]
        var q = pqr[1]
        var r = pqr[2]
        w = lemma_witness(CLASS_A, p, q, r)
        assert_equal(w.level, 3)
        assert_true(shared_tile_at(class_member(CLASS_A, p, q, r), w.level, w.position))
    # The lemma regions exclude exactly what the proof says they exclude.
    assert_equal(lemma_witness(CLASS_A, 1, 0, 1).level, 0)
    assert_equal(lemma_witness(CLASS_A, 5, 1, 0).level, 0)
    assert_equal(lemma_witness(CLASS_A, 6, 2, 1).level, 0)
    assert_equal(lemma_witness(CLASS_B, 4, 0, 1).level, 0)
    assert_equal(lemma_witness(CLASS_D, 4, 3, 1).level, 0)


def test_the_pisot_conditions_are_affine_and_bound_every_line() raises:
    """The Pisot conditions f(1) and f(-1) are affine in (p, q, r), since the parameters sit only in
    the bottom row of M. Pinned per class, and the line bounds they give."""
    # Classes A and B: f(1) = q - p, f(-1) = p + 3q - 6r - 6.
    for cls in [CLASS_A, CLASS_B]:
        var m = Mat3(substitution_incidence(class_member(cls, 7, 2, 3)))
        assert_equal(f_at(m, 1), 2 - 7)
        assert_equal(f_at(m, -1), 7 + 6 - 18 - 6)
    # Class C: f(1) = 2(q - p), f(-1) = -2p + 6q - 6r - 6.
    var mc = Mat3(substitution_incidence(class_member(CLASS_C, 7, 2, 3)))
    assert_equal(f_at(mc, 1), 2 * (2 - 7))
    assert_equal(f_at(mc, -1), -14 + 12 - 18 - 6)
    # Class D: f(1) = -2p + r - 1, f(-1) = -2p + 4q - 3r - 3.
    var md = Mat3(substitution_incidence(class_member(CLASS_D, 7, 2, 3)))
    assert_equal(f_at(md, 1), -14 + 3 - 1)
    assert_equal(f_at(md, -1), -14 + 8 - 9 - 3)
    # Line bounds: B (n, 0, 1) has f(-1) = n - 12, so PIP only for n <= 11.
    for n in range(1, 30):
        var m = Mat3(substitution_incidence(class_member(CLASS_B, n, 0, 1)))
        assert_equal(f_at(m, -1), n - 12)
        if n >= 12:
            assert_false(is_pip(m))
    # D (1, 0, n) has f(1) = n - 3, so PIP only for n <= 2.
    for n in range(0, 30):
        var m = Mat3(substitution_incidence(class_member(CLASS_D, 1, 0, n)))
        assert_equal(f_at(m, 1), n - 3)
        if n >= 3:
            assert_false(is_pip(m))


def test_the_eight_excluded_endings_have_no_pip_member() raises:
    """Four are not primitive (a letter produced only by itself), two have
    det M = 0, and two have the left eigenvector (1, -1, 0) for eigenvalue 2,
    a rational root. None has a PIP member at any parameter value."""
    var excluded = List[List[Int]]()
    excluded.append(List[Int]([X, X, X, X]))
    excluded.append(List[Int]([X, C, X, X]))
    excluded.append(List[Int]([X, C, C, C]))
    excluded.append(List[Int]([C, C, C, C]))
    excluded.append(List[Int]([C, X, X, C]))
    excluded.append(List[Int]([C, X, C, X]))
    excluded.append(List[Int]([X, C, X, C]))
    excluded.append(List[Int]([X, C, C, X]))
    for k in range(len(excluded)):
        var e = excluded[k].copy()
        for p in range(8):
            for q in range(8):
                for r in range(8):
                    var m = Mat3(substitution_incidence(normal_form(p, q, r, e[0], e[1], e[2], e[3])))
                    assert_false(is_pip(m))
    # the eigenvalue-2 mechanism, directly: (1, -1, 0) M = 2 (1, -1, 0)
    var m = Mat3(substitution_incidence(normal_form(3, 5, 2, X, C, X, C)))
    for j in range(3):
        assert_equal(m.e[0 * 3 + j] - m.e[1 * 3 + j], 2 * (1 if j == 0 else (-1 if j == 1 else 0)))


def test_the_mirror_relabelling_preserves_the_verdict() raises:
    """The relabelling x <-> c maps an ending to its mirror and (p, q, r) to (q, p, r), with
    the same PIP status, |det M| and coincidence level. Class D's mirror is the
    ending (c, x, x, x)."""
    var sigma = class_member(CLASS_D, 2, 1, 1)
    var mirror = normal_form(1, 2, 1, C, X, X, X)
    var m1 = Mat3(substitution_incidence(sigma))
    var m2 = Mat3(substitution_incidence(mirror))
    assert_equal(is_pip(m1), is_pip(m2))
    assert_equal(abs(m1.det()), abs(m2.det()))
    assert_equal(coincidence_level(sigma, X, C), coincidence_level(mirror, X, C))


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
    test_theorem_e_lemmas_cover_everything_but_the_listed_residue()
    print("[PASS] test_theorem_e_lemmas_cover_everything_but_the_listed_residue")
    test_every_residual_point_is_eventually_coincident()
    print("[PASS] test_every_residual_point_is_eventually_coincident")
    test_the_three_lemmas_name_real_shared_tiles()
    print("[PASS] test_the_three_lemmas_name_real_shared_tiles")
    test_the_pisot_conditions_are_affine_and_bound_every_line()
    print("[PASS] test_the_pisot_conditions_are_affine_and_bound_every_line")
    test_the_eight_excluded_endings_have_no_pip_member()
    print("[PASS] test_the_eight_excluded_endings_have_no_pip_member")
    test_the_mirror_relabelling_preserves_the_verdict()
    print("[PASS] test_the_mirror_relabelling_preserves_the_verdict")
    require_contract("Theorem E certificate (A1' on the catch-up-free |det M| = 2 class): the eight surviving endings are four mirror classes A-D and the other eight have no PIP member (four non-primitive, two det 0, two with left eigenvector (1,-1,0) for eigenvalue 2); f(1) and f(-1) are affine in (p,q,r) and every PIP point has both negative; lemmas L_BC and L_D (level 2) and L_A (level 3) name explicit positions, and at bound 11 all 453 named witnesses are shared tiles with none failing, over 383 PIP points; the PIP points no lemma covers are exactly the 27 listed (A 3, B 12, C 4, D 8), and the exact coincidence_level decides every one coincident at levels 3 to 7; the B line (n,0,1) has f(-1) = n - 12 and the D line (1,0,n) has f(1) = n - 3, so neither is PIP past its bound; the x <-> c mirror preserves PIP, |det M| and the level. Also the earlier sweep pins: A' holds at bounds 5 and 8 (174 and 420 members), deepest level 7, level-4-and-up rows identical (8/2/2/2) while levels 2 and 3 grow; no member merged at the endpoint; p = q = r = 0 members have all column sums 2 and none is PIP; deepest member sigma(x) = xyc, sigma(c) = cx, sigma(y) = cyc; a bound past MAX_BOUND is refused")
