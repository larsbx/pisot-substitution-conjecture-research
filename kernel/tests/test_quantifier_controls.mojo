"""Literal controls for the three quantifier readings of productivity.

`proof/PscVerif/PscVerif/QuantifierBinding.lean` proves, on the Lean
definitions of the balanced-pair automaton, that

* Fibonacci `0 -> 01, 1 -> 0` terminates with coincidence from `(01, 10)`,
  so every reachable state is productive, **and** has a cycle of
  noncoincident states through the seed, so some admissible path never
  meets a coincidence (`fib_lasso`);
* under Thue-Morse `0 -> 01, 1 -> 10` the irreducible balanced pair
  `(001, 100)` has a coincidence child **and** the child `(01, 10)`, which
  lies in a closed coincidence-free class (`tm_fork`); the incidence
  matrix of Thue-Morse is singular (`tm_incidence_singular`).

This file replays the same literal rows through the vendored
`substitution_dynamics` kernel, written independently of the Lean
development. States of the Mojo automaton are pairs up to side swap, so
the two Lean states `(01, 10)` and `(10, 01)` are one state here and the
Lean two-cycle is a self-loop.

The contract is the finite rows below, for these two substitutions. It
says nothing about any other substitution, and Thue-Morse is outside the
standing primitive irreducible Pisot class.
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from substitution_dynamics.automaton import (
    build,
    nonproductive_states,
    recurrent_noncoincident_sccs,
)
from substitution_dynamics.balanced_pairs import children
from substitution_dynamics.substitution import Substitution
from substitution_dynamics.words import Pair


def binary(a: List[Int], b: List[Int]) raises -> Substitution:
    var images = List[List[Int]]()
    images.append(a.copy())
    images.append(b.copy())
    return Substitution.checked(images)


def keys(ps: List[Pair]) -> List[String]:
    var out = List[String]()
    for i in range(len(ps)):
        out.append(ps[i].key())
    return out^


def test_fibonacci_every_state_productive_and_a_strict_cycle() raises:
    """(AE) holds and (A) fails on a primitive irreducible Pisot substitution."""
    var sigma = binary([0, 1], [0])
    var a = build(sigma)
    assert_false(a.capped)
    assert_equal(keys(a.states), ["01|10", "0|0"])

    # (AE): the reachable set is finite and no reachable state is nonproductive.
    assert_equal(len(nonproductive_states(a)), 0)

    # Not (A): the seed is a noncoincident state on a cycle, so the path that
    # stays on it never meets a coincidence. The cycle is not child-closed:
    # the same state has the coincidence child `0|0`.
    var seed = Pair([0, 1], [1, 0])
    assert_equal(keys(children(sigma, seed)), ["0|0", "01|10"])
    var strict = recurrent_noncoincident_sccs(a)
    assert_equal(len(strict), 1)
    assert_equal(len(strict[0]), 1)
    assert_equal(a.states[strict[0][0]].key(), "01|10")
    assert_true(0 in a.adj[0])
    assert_true(1 in a.adj[0])


def test_thue_morse_productive_root_with_a_closed_strict_child() raises:
    """(E) holds at the root and (AE) fails, outside the standing class."""
    var sigma = binary([0, 1], [1, 0])

    # The seed class is closed and coincidence-free: one state, one self-loop,
    # nonproductive.
    var a = build(sigma)
    assert_false(a.capped)
    assert_equal(keys(a.states), ["01|10"])
    assert_equal(a.adj[0], [0, 0])
    assert_equal(nonproductive_states(a), [0])

    # The irreducible balanced pair (001, 100) has a coincidence child, so it
    # is productive, and it has the child 01|10 of the closed strict class.
    var root = Pair([0, 0, 1], [1, 0, 0])
    assert_equal(keys(children(sigma, root)), ["01|10", "0|0", "1|1", "01|10"])

    # First violated standing premise: the incidence matrix kills (1, -1).
    for letter in range(2):
        var in_zero = 0
        var in_one = 0
        for j in range(len(sigma.images[0])):
            if sigma.images[0][j] == letter:
                in_zero += 1
        for j in range(len(sigma.images[1])):
            if sigma.images[1][j] == letter:
                in_one += 1
        assert_equal(in_zero - in_one, 0)


def main() raises:
    test_fibonacci_every_state_productive_and_a_strict_cycle()
    test_thue_morse_productive_root_with_a_closed_strict_child()
    require_contract("literal controls for the exists-path, every-descendant and every-path readings of productivity")
