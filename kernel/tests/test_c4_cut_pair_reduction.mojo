"""Cut-pair reduction controls: strict non-PIP systems and a PIP refusal."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_cut_pair_reduction import audit_cut_pairs, first_pair_mask, inflated_cut_pair_mask, strong_coincidence_level
from psc.words import Pair


def test_uniform_three_pair_control() raises:
    # Constant-length, all-ones incidence (not Pisot): A(C) is all three pairs.
    # The ordered 3-cycle is genuinely closed; the earlier listing
    # (012,120),(012,201),(120,201) was closed only up to track swap.
    var sigma: List[List[Int]] = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    var states: List[Pair] = [
        Pair(sigma[0], sigma[1]), Pair(sigma[1], sigma[2]), Pair(sigma[2], sigma[0]),
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


def assert_word_letter_refused(states: List[Pair], expected: String) raises:
    var sigma: List[List[Int]] = [[0], [1], [2]]
    var first_error = String("")
    try:
        _ = first_pair_mask(states)
    except e:
        first_error = String(e)
    assert_equal(first_error, expected)
    for depth in [0, 1]:
        var inflation_error = String("")
        try:
            _ = inflated_cut_pair_mask(sigma, states, depth)
        except e:
            inflation_error = String(e)
        assert_equal(inflation_error, expected)
    var audit_error = String("")
    try:
        _ = audit_cut_pairs(sigma, states, 1, 2)
    except e:
        audit_error = String(e)
    assert_equal(audit_error, expected)


def test_word_letters_are_checked_before_parikh_indexing() raises:
    var valid = Pair([0, 2], [2, 0])
    assert_word_letter_refused([Pair([1, 3, 2], [2, 3, 1])], "invalid top word letter")
    for invalid in [-1, 3]:
        assert_word_letter_refused(
            [valid.copy(), Pair([0, invalid], [2, 0])], "invalid top word letter"
        )
        assert_word_letter_refused(
            [valid.copy(), Pair([0, 2], [2, invalid])], "invalid bottom word letter"
        )

    # Both alphabet endpoints are legal. Reversing the tracks preserves the mask.
    var sigma: List[List[Int]] = [[0], [1], [2]]
    for state in [valid.copy(), Pair([2, 0], [0, 2])]:
        var states: List[Pair] = [state.copy()]
        assert_equal(first_pair_mask(states), 0b010)
        assert_equal(inflated_cut_pair_mask(sigma, states, 0), 0b010)
        assert_equal(inflated_cut_pair_mask(sigma, states, 1), 0b010)
        var audit = audit_cut_pairs(sigma, states, 1, 2)
        assert_equal(audit.first_mask, 0b010)
        assert_equal(audit.cut_mask, 0b010)
        assert_equal(audit.initial_image, 0b010)
        assert_equal(audit.witnessed_mask, 0)


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

def test_transient_cut_pair_in_non_strongly_connected_strict_system() raises:
    # Closure of (02,20) under 10/102/211: six states, strictly closed but not
    # strongly connected. A(C) = {{0,2},{1,2}}; the transient pair {0,2} never
    # labels a cut of an inflation, and g maps it into {1,2}.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var states: List[Pair] = [
        Pair([0, 2], [2, 0]),
        Pair([1, 0, 2, 1, 1], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    var audit = audit_cut_pairs(sigma, states, 3, 8)
    assert_equal(audit.first_mask, 0b110)
    assert_equal(audit.cut_mask, 0b100)
    assert_equal(audit.initial_image, 0b100)
    assert_equal(audit.witnessed_mask, 0)


def test_unit_pip_left_witness_levels() raises:
    # Unit PIP 01/12/021 (det 1): left strong-coincidence witnesses on all
    # three pairs, the semantics used by Theorem A(4) and Lemma P (#480 §4).
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    assert_equal(strong_coincidence_level(sigma, 0, 2, 8), 1)
    assert_equal(strong_coincidence_level(sigma, 0, 1, 8), 4)
    assert_equal(strong_coincidence_level(sigma, 1, 2, 8), 4)
    assert_equal(strong_coincidence_level(sigma, 0, 1, 3), -1)


def main() raises:
    test_uniform_three_pair_control()
    test_single_pair_reducible_control()
    test_transient_cut_pair_in_non_strongly_connected_strict_system()
    test_unit_pip_left_witness_levels()
    test_pip_family_member_refuses_every_candidate()
    test_bounded_refusal_is_not_a_mathematical_noncoincidence_verdict()
    test_word_letters_are_checked_before_parikh_indexing()
    test_positive_letter_witness_refuses_even_at_depth_zero()
    print("C4 cut-pair reduction: strict controls keep A(C) g-closed and witness-free; PIP candidates refused.")
    require_contract("every balanced cut of every inflation of a supplied strict system carries a first-letter pair of the system, the initial-letter map preserves and never collapses that pair set, and no such pair carries a bounded strong-coincidence witness; transient pairs of non-strongly-connected strict systems are admitted; unit-PIP left witness levels are pinned; PIP candidates and malformed/capped inputs are refused")
