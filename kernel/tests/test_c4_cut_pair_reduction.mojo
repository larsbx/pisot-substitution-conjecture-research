"""Cut-pair reduction controls: strict non-PIP systems and a PIP refusal."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_cut_pair_reduction import audit_cut_pairs, inflated_cut_pair_mask, strong_coincidence_level
from psc.words import Pair


def test_uniform_three_pair_control() raises:
    # Constant-length, all-ones incidence (not Pisot): A(C) is all three pairs.
    var sigma: List[List[Int]] = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    var states: List[Pair] = [
        Pair(sigma[0], sigma[1]), Pair(sigma[0], sigma[2]), Pair(sigma[1], sigma[2]),
    ]
    var audit = audit_cut_pairs(sigma, states, 3, 6)
    assert_equal(audit.first_mask, 0b111)
    assert_equal(audit.cut_mask, 0b111)
    assert_equal(audit.initial_image, 0b111)
    assert_equal(audit.witnessed_mask, 0)


def test_single_pair_reducible_control() raises:
    # Primitive nonsingular reducible strict system (PR #459): A(C) = {{1,2}}.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var states: List[Pair] = [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    var audit = audit_cut_pairs(sigma, states, 3, 8)
    assert_equal(audit.first_mask, 0b100)
    assert_equal(audit.cut_mask, 0b100)
    assert_equal(audit.initial_image, 0b100)
    assert_equal(audit.witnessed_mask, 0)
    # {0,1} is the witnessed good edge (level 1). {0,2} has no witness within
    # this budget either; that is an exhausted budget, not a verdict, and the
    # pair is not a cut pair of this component.
    assert_equal(strong_coincidence_level(sigma, 0, 1, 8), 1)
    assert_equal(strong_coincidence_level(sigma, 0, 2, 8), -1)
    # The audit checks necessary conditions only; full closure is certified by
    # the strict birth atlas. A state cut on the good edge is refused: g
    # collapses {0,1}, so its first child is coincident.
    var good_edge: List[Pair] = [Pair([0, 1], [1, 0])]
    var refused = False
    try:
        _ = audit_cut_pairs(sigma, good_edge, 1, 8)
    except:
        refused = True
    assert_true(refused)


def test_pip_family_member_refuses_every_candidate() raises:
    # PIP 01/121/012: every letter pair strongly coincides by level 2, so
    # A(C) would be empty; a supplied candidate meets a coincident factor.
    var sigma: List[List[Int]] = [[0, 1], [1, 2, 1], [0, 1, 2]]
    for a in range(3):
        for b in range(a + 1, 3):
            var level = strong_coincidence_level(sigma, a, b, 4)
            assert_true(level >= 1 and level <= 2)
    var candidates: List[Pair] = [Pair([0, 1], [1, 0]), Pair([1, 2], [2, 1]), Pair([0, 2], [2, 0])]
    for c in candidates:
        var single: List[Pair] = [c.copy()]
        var refused = False
        try:
            _ = inflated_cut_pair_mask(sigma, single, 3)
        except:
            refused = True
        assert_true(refused)



def test_bounded_refusal_is_not_a_mathematical_noncoincidence_verdict() raises:
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var input: List[Pair] = [Pair([1, 0, 2], [2, 1, 0])]
    # Zero or negative witness budget does NOT mean that no witness
    # exists. A positive finite -1 means the *search* exhausted.
    for budget in [-1, 0, 13]:
        var refused = False
        try:
            _ = strong_coincidence_level(sigma, 1, 2, budget)
        except:
            refused = True
        assert_true(refused)
    for depth in [-1, 11]:
        var refused = False
        try:
            _ = inflated_cut_pair_mask(sigma, input, depth)
        except:
            refused = True
        assert_true(refused)
    var malformed: List[Pair] = [Pair([1, 3, 2], [2, 3, 1])]
    var refused = False
    try:
        _ = inflated_cut_pair_mask(sigma, malformed, 1)
    except:
        refused = True
    assert_true(refused)


def test_positive_letter_witness_refuses_even_at_depth_zero() raises:
    # The depth-zero literal factorization is not yet productive, but the
    # supplied first pair {0,1} is genuinely strongly coincident at level 2.
    # An audit MUST refuse it rather than returning a seemingly valid
    # strict-system receipt with a nonzero witnessed_mask.
    var pip: List[List[Int]] = [[0, 1], [1, 2, 1], [0, 1, 2]]
    var singleton: List[Pair] = [Pair([0, 1], [1, 0])]
    assert_equal(strong_coincidence_level(pip, 0, 1, 2), 2)
    var refused = False
    try:
        _ = audit_cut_pairs(pip, singleton, 0, 2)
    except:
        refused = True
    assert_true(refused)

def main() raises:
    test_uniform_three_pair_control()
    test_single_pair_reducible_control()
    test_pip_family_member_refuses_every_candidate()
    test_bounded_refusal_is_not_a_mathematical_noncoincidence_verdict()
    test_positive_letter_witness_refuses_even_at_depth_zero()
    print("C4 cut-pair reduction: strict controls keep A(C) g-closed and witness-free; PIP candidates refused.")
    require_contract("every balanced cut of every inflation of a supplied strict system carries a first-letter pair of the system, the initial-letter map preserves and never collapses that pair set, and no such pair carries a bounded strong-coincidence witness; PIP candidates and malformed/capped inputs are refused")
