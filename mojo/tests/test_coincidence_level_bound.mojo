"""Regression for the fixed-substitution coincidence-depth bound.

The first test pins the graph-theoretic inequality on substitutions with least
strong-coincidence levels 1, 3, 14 and 15.  The second is a negative control for
a uniform proof: the unimodular cubic PIP family

    0 -> 1,  1 -> 2,  2 -> 0 2^n,  n >= 3

has unbounded image length and incidence height.  The accompanying note proves
the family statement algebraically.  The finite samples here only guard the
encoding and must not be cited as that proof.
"""

from std.testing import assert_equal, assert_true

from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.claim_tests import require_contract
from psc.coincidence_level_bound import pair_depth_bound, substitution_depth_bound
from psc.dumont_thomas import max_image_length
from psc.numeration_addition import powered_field
from psc.words import ALPHABET


def deep_specimens() -> List[List[List[Int]]]:
    var out = List[List[List[Int]]]()
    out.append([[0, 1], [0, 2], [0]])
    out.append([[1], [0, 1, 2], [0, 1, 0]])
    out.append([[1], [2], [0, 1]])
    out.append([[2], [0], [0, 1]])
    return out^


def height_family(n: Int) raises -> List[List[Int]]:
    if n < 3:
        raise Error("the documented irreducible family starts at n = 3")
    var zero: List[Int] = [1]
    var one: List[Int] = [2]
    var two: List[Int] = [0]
    for _ in range(n):
        two.append(2)
    var sigma = List[List[Int]]()
    sigma.append(zero^)
    sigma.append(one^)
    sigma.append(two^)
    return sigma^


def test_shortest_level_is_bounded_by_reachable_states() raises:
    var expected: List[Int] = [1, 3, 14, 15]
    var corpus = deep_specimens()
    for s in range(len(corpus)):
        var whole = substitution_depth_bound(corpus[s])
        assert_true(not whole.empty)
        assert_equal(whole.level, expected[s])
        assert_true(whole.level <= whole.upper)
        for top in range(ALPHABET):
            for bottom in range(top + 1, ALPHABET):
                var pair = pair_depth_bound(corpus[s], top, bottom)
                assert_true(pair.certifies_level())


def test_unimodular_pip_inputs_have_unbounded_syntactic_parameters() raises:
    var ns: List[Int] = [3, 7, 31]
    for i in range(len(ns)):
        var n = ns[i]
        var sigma = height_family(n)
        _ = powered_field(sigma)
        var incidence = Mat3(substitution_incidence(sigma))
        assert_equal(incidence.det(), 1)
        assert_equal(max_image_length(sigma), n + 1)
        assert_equal(incidence.at(2, 2), n)


def main() raises:
    test_shortest_level_is_bounded_by_reachable_states()
    print("[PASS] test_shortest_level_is_bounded_by_reachable_states")
    test_unimodular_pip_inputs_have_unbounded_syntactic_parameters()
    print("[PASS] test_unimodular_pip_inputs_have_unbounded_syntactic_parameters")
    print("2 coincidence-level-bound tests passed.")
    require_contract("a nonempty pair coincidence language has least level at most the number of reachable affine-automaton states minus one; this is substitution-local, does not prove nonemptiness, and supplies no uniform alphabet-three PIP bound")
