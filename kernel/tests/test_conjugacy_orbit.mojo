"""Conjugacy classes by letter rotations, and their shape on Theorem E's classes."""
from std.testing import assert_true, assert_false, assert_equal
from mojo_smoke.claims import require_contract
from a1_normal_form_census import CLASS_A, CLASS_B, CLASS_C, CLASS_D, class_member
from lateral_conjugacy_census import census, check_b_chain, theorem_c_region
from psc.conjugacy_orbit import conjugacy_class, is_left_conjugate_by, same_incidence, step_left, step_right
from psc.one_tile import catch_up_free


def _refuses_left(sigma: List[List[Int]]) -> Bool:
    try:
        _ = step_left(sigma)
    except:
        return True
    return False


def _refuses_right(sigma: List[List[Int]]) -> Bool:
    try:
        _ = step_right(sigma)
    except:
        return True
    return False


def main() raises:
    # Tribonacci 0->01, 1->02, 2->0: one left step, to 10, 20, 0.
    var trib = List[List[Int]]([List[Int]([0, 1]), List[Int]([0, 2]), List[Int]([0])])
    var cls = conjugacy_class(trib, 16)
    assert_equal(len(cls), 2)
    assert_true(is_left_conjugate_by(trib, cls[1], List[Int]([0])))
    assert_true(same_incidence(trib, cls[1]))
    # Negative controls: no shared letter refuses; a wrong conjugate is rejected.
    assert_true(_refuses_left(cls[1]))
    assert_true(_refuses_right(trib))
    assert_false(is_left_conjugate_by(trib, trib, List[Int]([0])))

    # Classes A, C, D: isolated (x and c head their own images; last letters differ).
    for c in [CLASS_A, CLASS_C, CLASS_D]:
        assert_equal(len(conjugacy_class(class_member(c, 5, 4, 3), 16)), 1)

    # Class B (5, 2, 3): the right-step chain of min(p, q, r) + 2 = 4 members.
    var b = class_member(CLASS_B, 5, 2, 3)
    assert_true(theorem_c_region(5, 2, 3))
    assert_true(catch_up_free(b))
    var chain = conjugacy_class(b, 16)
    assert_equal(len(chain), 4)
    check_b_chain(b, chain, 5, 2, 3)
    for k in range(1, len(chain)):
        assert_false(catch_up_free(chain[k]))

    # A cap below the class size refuses rather than truncating.
    var refused = False
    try:
        _ = conjugacy_class(b, 3)
    except:
        refused = True
    assert_true(refused)

    # The bounded census runs to completion; every internal check raises on failure.
    var result = census(8)
    var tallies = result[0].copy()
    var transfer = result[1].copy()
    assert_equal(tallies[CLASS_A].nontrivial, 0)
    assert_equal(tallies[CLASS_C].nontrivial, 0)
    assert_equal(tallies[CLASS_D].nontrivial, 0)
    assert_equal(tallies[CLASS_B].nontrivial, tallies[CLASS_B].members)
    assert_equal(transfer.catch_up_free_conjugates, 0)
    require_contract("letter-rotation conjugacy classes are closed exactly and refuse past a cap; Theorem E classes A, C, D are conjugacy-isolated and every class-B member has the right-step chain of min(p,q,r)+2 conjugates, same incidence, none but sigma catch-up-free; bounded census p,q,r<=8; spectral transfer is the imported invariance, not tested here")
