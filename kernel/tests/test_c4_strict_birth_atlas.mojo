"""C4 all-child literal boundary atlas; strong controls, no C4 promotion."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_strict_birth_atlas import strict_birth_atlas
from psc.words import Pair


def test_fullrank_primitive_nonpip_strict_twelve_actual_births() raises:
    # This is a strict, closed four-state non-PIP component; chi has
    # an eigenvalue one. It must NOT be mislabelled a PIP counterexample.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var states: List[Pair] = [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    var atlas = strict_birth_atlas(sigma, states)
    assert_equal(len(atlas), 12)
    var counts: List[Int] = [0, 0, 0, 0]
    for j in range(len(atlas)):
        ref event = atlas[j]
        counts[event.parent_id] += 1
        assert_true(event.top_digit != 0 or event.bottom_digit != 0)
        assert_true(event.left_top_letter != event.left_bottom_letter)
        assert_equal(event.right_top_letter, 1)
        assert_equal(event.right_bottom_letter, 2)
        assert_true(event.left_sign == 1 or event.left_sign == -1)
        assert_true(event.right_sign == 1 or event.right_sign == -1)
    assert_equal(counts, [0, 0, 4, 8])
    # Full occurrence index and child ordinals, not an SCC quotient mask.
    ref e = atlas[0]
    assert_equal(e.parent_id, 2)
    assert_equal(e.right_ordinal, 1)
    assert_equal(e.physical_cut, 8)
    assert_equal(e.left_child_id, 2)
    assert_equal(e.right_child_id, 0)
    assert_equal(e.top_source, 3)
    assert_equal(e.bottom_source, 2)
    assert_equal(e.top_digit, 0)
    assert_equal(e.bottom_digit, 2)
    assert_equal(e.source_defect, [1, 0, 0])
    assert_equal(e.local_correction, [-1, -1, 0])
    ref f = atlas[2]
    assert_equal(f.right_ordinal, 3)
    assert_equal(f.physical_cut, 14)
    assert_equal(f.top_source, 5)
    assert_equal(f.bottom_source, 5)
    assert_equal(f.top_digit, 1)
    assert_equal(f.bottom_digit, 0)
    assert_equal(f.source_defect, [1, -1, 0])
    assert_equal(f.local_correction, [0, 0, 1])
    ref last = atlas[11]
    assert_equal(last.parent_id, 3)
    assert_equal(last.right_ordinal, 8)
    assert_equal(last.physical_cut, 35)
    assert_equal(last.top_source, 13)
    assert_equal(last.bottom_source, 12)


def test_productive_pip_and_singular_strict_are_refused() raises:
    # The actual recurrent Tribonacci source SCC is productive: cannot
    # be passed as a strict derived system by truncating its diagonal child.
    var pip: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var bad: List[Pair] = [
        Pair([0, 1], [1, 0]),
        Pair([1, 0, 2], [2, 0, 1]),
        Pair([0, 1, 0, 2], [2, 0, 1, 0]),
    ]
    var refused = False
    try:
        _ = strict_birth_atlas(pip, bad)
    except:
        refused = True
    assert_true(refused)
    # The old non-Pisot strict component has singular incidence:
    # it is not in the domain of the new full-rank newborn theorem.
    var singular: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var strict: List[Pair] = [
        Pair([0, 1], [1, 0]),
        Pair([1, 2], [2, 1]),
    ]
    refused = False
    try:
        _ = strict_birth_atlas(singular, strict)
    except:
        refused = True
    assert_true(refused)


def test_resource_budget_and_partial_component_refusal() raises:
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var strict: List[Pair] = [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    var refused = False
    try:
        _ = strict_birth_atlas(sigma, strict, birth_cap=11)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = strict_birth_atlas(sigma, strict, birth_cap=0)
    except:
        refused = True
    assert_true(refused)
    # Omitting even one actual state breaks all-child closure.
    var incomplete: List[Pair] = [strict[0].copy(), strict[1].copy(), strict[2].copy()]
    refused = False
    try:
        _ = strict_birth_atlas(sigma, incomplete)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_fullrank_primitive_nonpip_strict_twelve_actual_births()
    test_productive_pip_and_singular_strict_are_refused()
    test_resource_budget_and_partial_component_refusal()
    print("C4 strict literal birth atlas: 12 complete births and refusal controls.")
    require_contract("literal strict C4 atlas validates all ordered child boundaries, source/digit addresses, Parikh corrections and endpoint non-sync, refuses partial/productive/singular/capped systems; non-PIP control only")
