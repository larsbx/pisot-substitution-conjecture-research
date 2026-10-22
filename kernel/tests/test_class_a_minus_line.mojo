"""Boundary hitting on the class-A minus line (n+1,n,n-1): certificate and refusals."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_line import ALine, plus_line, minus_line
from psc.class_a_line_graph import survey
from psc.class_a_minus_carrier import minus_rows
from psc.class_a_minus_descent_data import minus_piece_rows, minus_descent_rows
from psc.class_a_typed_carrier import template_rows, certify_finite_line
from psc.class_a_carrier_closure import certify_closure_line, check_line_identity
from psc.class_a_carrier_descent import certify_descent_line, replay_descent_finite_line


def refuses_closure(line: ALine, n0: Int, rows: List[List[Int]]) -> Bool:
    try:
        _ = certify_closure_line(line, n0, rows)
        return False
    except:
        return True


def refuses_descent(n0: Int, pieces: List[List[Int]], descents: List[List[Int]]) -> Bool:
    try:
        _ = certify_descent_line(minus_line(), n0, minus_rows(), pieces, descents)
        return False
    except:
        return True


def incidence_matches(line: ALine, n: Int) raises -> Bool:
    """Letter counts of the actual images are (2,0,n+1), (1,1,n), (1,1,n+eps)."""
    var images = line.member(n)
    var expected = List[List[Int]]()
    expected.append(List[Int]([2, 0, n + 1]))
    expected.append(List[Int]([1, 1, n]))
    expected.append(List[Int]([1, 1, n + line.eps]))
    for j in range(3):
        var counts = List[Int]([0, 0, 0])
        for letter in images[j]:
            counts[letter] += 1
        if counts != expected[j]:
            return False
    return True


def main() raises:
    # Line data: the eigenvector/elimination identity and the actual images.
    check_line_identity(plus_line())
    check_line_identity(minus_line())
    var refused = False
    try:
        check_line_identity(ALine(1, 0, 0))
    except:
        refused = True
    assert_true(refused)
    for n in [5, 9, 24]:
        assert_true(incidence_matches(minus_line(), n))
        assert_true(incidence_matches(plus_line(), n))
    # Uniform closure of the 104-row carrier: conservative clips at n>=8, none at n>=10.
    var closure8 = certify_closure_line(minus_line(), 8, minus_rows())
    assert_equal(closure8, List[Int]([104, 208, 936, 10296, 4508, 3842, 1872, 9, 3, 56, 65]))
    var closure10 = certify_closure_line(minus_line(), 10, minus_rows())
    assert_equal(closure10[9], 0)
    # Uniform descent: 176 pieces, 8 targets, 265 occurrences, depth <= 2n+11.
    var descent8 = certify_descent_line(minus_line(), 8, minus_rows(), minus_piece_rows(), minus_descent_rows())
    assert_equal(descent8, List[Int]([176, 8, 265, 2, 11]))
    # Below the floor the certificates refuse rather than extrapolate.
    assert_true(refuses_closure(minus_line(), 6, minus_rows()))
    assert_true(refuses_descent(7, minus_piece_rows(), minus_descent_rows()))
    # A carrier is bound to its line: swapping lines refuses in both directions.
    assert_true(refuses_closure(plus_line(), 8, minus_rows()))
    assert_true(refuses_closure(minus_line(), 8, template_rows()))
    # A removed carrier row is an escape, not a smaller theorem.
    var original = minus_rows()
    for drop in [0, 50, len(original) - 1]:
        var damaged = List[List[Int]]()
        for i in range(len(original)):
            if i != drop:
                damaged.append(original[i].copy())
        assert_true(refuses_closure(minus_line(), 8, damaged))
    # A raised child potential, a removed descent row and a mislabelled child refuse.
    var pieces = minus_piece_rows()
    var descents = minus_descent_rows()
    var raised = pieces.copy()
    raised[descents[0][8]][7] += 50
    assert_true(refuses_descent(8, raised, descents))
    var fewer = List[List[Int]]()
    for i in range(1, len(descents)):
        fewer.append(descents[i].copy())
    assert_true(refuses_descent(8, pieces, fewer))
    var mislabelled = descents.copy()
    mislabelled[0][7] += 1
    assert_true(refuses_descent(8, pieces, mislabelled))
    # Exact finite certificates below the uniform floor: complete graphs n=1..7
    # all hit; from n=5 the carrier equals the graph label set (40n+138).
    for n in range(1, 8):
        var s = survey(minus_line(), n)
        assert_true(s[0] > 0)
    for n in [5, 6, 7, 8, 18]:
        var f = certify_finite_line(minus_line(), n, minus_rows(), 40, 138)
        assert_equal(f[0], 40 * n + 138)
    # Differential replay of every chosen occurrence against the exact engine.
    for n in [8, 11]:
        _ = replay_descent_finite_line(minus_line(), n, minus_rows(), pieces, descents, 40, 138)
    require_contract("class-A minus line (n+1,n,n-1) boundary hitting for every n>=1: uniform forward closure of the 104-row typed carrier and a 176-piece affine potential with 265 descent occurrences for n>=8 by exact Sturm signs on (0,1/8], exact complete-graph certificates at n=1..7, differential replay at n=8,11; undecided sign, swapped line, removed row, damaged potential and mislabelled child refuse; other A/C regions and universal #139 open")
