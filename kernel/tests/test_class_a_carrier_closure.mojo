"""Uniform closure and descent of the typed class-A carrier: certificate and refusals."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_typed_carrier import template_rows, certify_finite
from psc.class_a_carrier_closure import certify_closure, certify_closure_rows, sign_on_interval, a_le
from psc.class_a_carrier_descent import certify_descent, certify_descent_rows, replay_descent_finite
from psc.class_a_descent_data import piece_rows, descent_rows
from finite_exact.rat_q import Q


def refuses_closure(n0: Int, rows: List[List[Int]]) -> Bool:
    try:
        _ = certify_closure_rows(n0, rows)
        return False
    except:
        return True


def refuses_descent(n0: Int, pieces: List[List[Int]], descents: List[List[Int]]) -> Bool:
    try:
        _ = certify_descent_rows(n0, template_rows(), pieces, descents)
        return False
    except:
        return True


def main() raises:
    # Exact sign decisions on (0, q]: a root inside refuses, a vanishing bound refuses.
    assert_equal(sign_on_interval([1, -3], Q(1, 5)), 1)
    assert_equal(sign_on_interval([0, 0, -2, 1], Q(1, 5)), -1)
    var refused = False
    try:
        _ = sign_on_interval([-1, 10], Q(1, 5))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = sign_on_interval([-1, 5], Q(1, 5))
    except:
        refused = True
    assert_true(refused)
    assert_equal(a_le([1, -4], [0, 1], 8), 0)
    assert_equal(a_le([1, -4], [0, 1], 5), -1)
    # The uniform certificates: no fallback at n>=8, conservative clips at n>=5.
    var closure8 = certify_closure(8)
    assert_equal(closure8[0], 89)
    assert_equal(closure8[7], 9)
    assert_equal(closure8[9], 0)
    var closure5 = certify_closure(5)
    assert_equal(closure5[7], 9)
    var descent8 = certify_descent(8)
    assert_equal(descent8, List[Int]([155, 8, 221, 2, 9]))
    # Below the floor the closure must refuse rather than extrapolate.
    assert_true(refuses_closure(4, template_rows()))
    # A removed carrier row is an escape, not a smaller theorem.
    var original = template_rows()
    var damaged = List[List[Int]]()
    for i in range(len(original) - 1):
        damaged.append(original[i].copy())
    assert_true(refuses_closure(8, damaged))
    # A raised child potential (no drop), a negative potential, a removed
    # descent row and a mislabelled child all refuse.
    var pieces = piece_rows()
    var all_descents = descent_rows()
    var raised = pieces.copy()
    raised[all_descents[0][8]][7] += 50
    assert_true(refuses_descent(8, raised, all_descents))
    var negative = pieces.copy()
    negative[0][7] -= 100
    assert_true(refuses_descent(8, negative, all_descents))
    var fewer = List[List[Int]]()
    for i in range(len(all_descents) - 1):
        fewer.append(all_descents[i].copy())
    assert_true(refuses_descent(8, pieces, fewer))
    var mislabelled = all_descents.copy()
    mislabelled[0][7] += 1
    assert_true(refuses_descent(8, pieces, mislabelled))
    var wrong_child = all_descents.copy()
    wrong_child[0][8] = (wrong_child[0][8] + 1) % len(pieces)
    assert_true(refuses_descent(8, pieces, wrong_child))
    # Finite differential controls against the exact Perron-field engine, and
    # the exact finite certificates for the members below the uniform floor.
    for n in [4, 5, 6, 7]:
        _ = certify_finite(n)
    for n in [8, 11]:
        _ = replay_descent_finite(n, template_rows(), pieces, all_descents)
    require_contract("class-A line (n+1,n,n+1) boundary hitting for every n>=4: uniform forward closure of the 89-row typed carrier and a 155-piece affine potential with 221 descent occurrences for n>=8 by exact Sturm signs on (0,1/9], exact finite certificates at n=4..7, differential replay at n=8,11; undecided sign, removed row, damaged potential and mislabelled child refuse; other A/C regions and universal #139 open")
