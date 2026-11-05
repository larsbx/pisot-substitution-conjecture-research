"""Cut-attractor bookkeeping on the strict controls, the configuration census,
the endpoint-collapse survey and the deep strong-coincidence class."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_cut_attractor import (
    child_matrix,
    configuration_census,
    cut_edges,
    cut_lattice_recursion_holds,
    endpoint_collapse_survey,
    hub_on_one_track,
    inflated_first_pair_mask,
    intertwines,
    left_witness,
    reversed_substitution,
    shifted_source_count,
    strict_closure,
)
from psc.corpus import pip_corpus
from psc.words import Pair


def test_reducible_strict_control() raises:
    # Primitive, nonsingular, reducible 10/102/211 (PR #459); good edge {0,1}, hub 2.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var c = strict_closure(sigma, Pair([1, 0, 2], [2, 1, 0]))
    assert_equal(c.size(), 4)
    var expected: List[Pair] = [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    for i in range(4):
        assert_equal(c.states[i], expected[i])
    var N = child_matrix(c)
    var expected_N: List[List[Int]] = [[0, 3, 0, 5], [1, 1, 0, 1], [0, 1, 0, 3], [0, 0, 1, 0]]
    for t in range(4):
        assert_equal(N[t], expected_N[t])
    assert_true(intertwines(sigma, c))
    var edges = cut_edges(sigma, c)
    assert_equal(len(edges), 12)
    assert_equal(shifted_source_count(c, edges), 8)
    assert_true(cut_lattice_recursion_holds(sigma, c, 3))
    assert_equal(inflated_first_pair_mask(sigma, c, 4), 0b100)
    assert_true(hub_on_one_track(sigma, c, 2, 4))
    assert_false(hub_on_one_track(sigma, c, 0, 1))  # 0 never heads a cut
    # The good edge has a level-one left witness; the cut pair has none within budget.
    assert_equal(left_witness(sigma, 0, 1, 8), [1, 0, 1])
    assert_equal(left_witness(sigma, 1, 2, 8), [-1, -1, -1])


def test_uniform_strict_control() raises:
    var sigma: List[List[Int]] = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    var c = strict_closure(sigma, Pair([0, 1, 2], [1, 2, 0]))
    assert_equal(c.size(), 3)
    var N = child_matrix(c)
    for t in range(3):
        assert_equal(N[t], [1, 1, 1])
    assert_true(intertwines(sigma, c))
    var edges = cut_edges(sigma, c)
    assert_equal(len(edges), 6)
    assert_equal(shifted_source_count(c, edges), 6)
    assert_true(cut_lattice_recursion_holds(sigma, c, 3))
    assert_equal(inflated_first_pair_mask(sigma, c, 3), 0b111)


def test_pip_seed_and_malformed_inputs_are_refused() raises:
    var pip: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var refused = False
    try:
        _ = strict_closure(pip, Pair([1, 0], [0, 1]))
    except:
        refused = True
    assert_true(refused)
    # Unit PIP 01/12/021: left witnesses on all three pairs (Theorem A(4) excludes it).
    assert_equal(left_witness(pip, 0, 2, 8), [1, 0, 0])
    assert_equal(left_witness(pip, 0, 1, 8)[0], 4)
    assert_equal(left_witness(pip, 1, 2, 8)[0], 4)
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    for bad in [Pair([1, 0], [0, 1, 1]), Pair([1, 3], [3, 1]), Pair([1, 2], [1, 2]), Pair([1, 0, 1, 0], [0, 1, 0, 1])]:
        refused = False
        try:
            _ = strict_closure(sigma, bad)
        except:
            refused = True
        assert_true(refused)
    refused = False
    try:
        _ = strict_closure(sigma, Pair([1, 0, 2], [2, 1, 0]), cap=3)
    except:
        refused = True
    assert_true(refused)
    for budget in [0, 33]:
        refused = False
        try:
            _ = left_witness(sigma, 0, 1, budget)
        except:
            refused = True
        assert_true(refused)


def test_configuration_census() raises:
    var census = configuration_census()
    assert_equal(census.triples, 54)
    assert_equal(census.single_cycle_one, 36)
    assert_equal(census.double_cycle_one, 15)
    assert_equal(census.double_cycle_two, 3)
    assert_equal(census.single_fixed, 18)
    assert_equal(census.single_swap, 18)
    assert_true(census.square_fixes_a_pair_everywhere)
    assert_equal(census.nonmerged_instances, 42)
    # key 8 t + m: (0,1):9 (1,1):6 (0,2):15 (1,2):6 (0,3):6
    assert_equal(census.transient_period.count(1), 9)
    assert_equal(census.transient_period.count(9), 6)
    assert_equal(census.transient_period.count(2), 15)
    assert_equal(census.transient_period.count(10), 6)
    assert_equal(census.transient_period.count(3), 6)
    assert_equal(census.transient_period.total(), 42)


def test_endpoint_collapse_survey() raises:
    var survey = endpoint_collapse_survey(pip_corpus())
    assert_equal(survey.first, 1896)
    assert_equal(survey.last, 1896)
    assert_equal(survey.either, 3012)
    assert_equal(survey.remainder, 1542)
    # key 4 n_+ + n_-: (2,2):534 (2,3):408 (3,2):408 (3,3):192
    assert_equal(survey.joint.count(10), 534)
    assert_equal(survey.joint.count(11), 408)
    assert_equal(survey.joint.count(14), 408)
    assert_equal(survey.joint.count(15), 192)
    assert_equal(survey.joint.total(), 1542)


def test_deep_strong_coincidence_class() raises:
    # 1/2/01 (Perron root the plastic number): the corpus class whose left
    # witnesses need levels 13 and 14, beyond the 12-level budget of the
    # cut-pair audit; its reversal 1/2/10 needs level 15.
    var sigma: List[List[Int]] = [[1], [2], [0, 1]]
    assert_equal(left_witness(sigma, 0, 1, 16), [13, 17, 1])
    assert_equal(left_witness(sigma, 0, 2, 16), [14, 17, 1])
    assert_equal(left_witness(sigma, 1, 2, 16), [12, 17, 1])
    assert_equal(left_witness(sigma, 0, 1, 12), [-1, -1, -1])
    var reversed = reversed_substitution(sigma)
    assert_equal(reversed[2], [1, 0])
    assert_equal(left_witness(reversed, 0, 1, 16), [15, 47, 1])
    assert_equal(left_witness(reversed, 0, 2, 16), [1, 0, 1])
    assert_equal(left_witness(reversed, 1, 2, 16), [14, 47, 1])


def main() raises:
    test_reducible_strict_control()
    test_uniform_strict_control()
    test_pip_seed_and_malformed_inputs_are_refused()
    test_configuration_census()
    test_endpoint_collapse_survey()
    test_deep_strong_coincidence_class()
    print("C4 cut attractor: strict-control bookkeeping, 54 configurations, endpoint collapse 1896/1896/3012, deep class 1/2/01.")
    require_contract("cut-attractor bookkeeping of a supplied strict system: ordered closure, P N = M P, two-track nesting at every interior cut, multiplicity-one cut-lattice recursion, cut pairs inside A(C), hub on one track; the 54 first-letter configurations of Theorem A(3); endpoint-collapse census 1896/1896/3012/1542; bounded left witnesses with exhausted budgets reported as -1")
