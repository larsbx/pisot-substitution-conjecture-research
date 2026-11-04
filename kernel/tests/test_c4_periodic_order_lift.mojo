"""Complete 46,656-case exclusion for one P,N and all 36 source word orders.

Includes the original sigma=(01,121,012) 1,296-order regression.
P=[M^2,M^2], N=[[0,M],[M,0]] are fixed. Not general C4 or PSC.
"""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, decompose
from psc.c4_ordered_lift_certificate import validate_lift_inverse, lift_numerators
from c4_periodic_lift_fixture import inverse_numerator


def _area(word: List[Int]) raises -> List[Int]:
    if len(word) > 128:
        raise Error("area word budget")
    for z in word:
        if z < 0 or z >= 3:
            raise Error("invalid letter before area indexing")
    var seen: List[Int] = [0, 0, 0]
    var out: List[Int] = [0, 0, 0]
    var lo: List[Int] = [0, 0, 1]
    var hi: List[Int] = [1, 2, 2]
    for z in word:
        for k in range(3):
            if z == hi[k]:
                out[k] += seen[lo[k]]
            if z == lo[k]:
                out[k] -= seen[hi[k]]
        seen[z] += 1
    return out^


def _row(parent: Int, choice: Int) -> List[Int]:
    var local = List[Int]()
    if parent % 3 == 0:
        if choice == 0:
            local = [0, 1]
        else:
            local = [1, 0]
    elif parent % 3 == 1:
        if choice == 0:
            local = [1, 1, 2]
        elif choice == 1:
            local = [1, 2, 1]
        else:
            local = [2, 1, 1]
    else:
        var options: List[List[Int]] = [
            [0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0],
        ]
        local = options[choice].copy()
    var offset = 0
    if parent < 3:
        offset = 3
    var out = List[Int]()
    for x in local:
        out.append(x + offset)
    return out^


def _first_state_outcome(
    sigma: List[List[Int]], mean: List[Int], expected_ids: List[Int],
    P: List[List[Int]],
) raises -> Int:
    # 0=no possible irreducible word pair; 1=every pair makes a diagonal;
    # 2=some pair avoids diagonals, but all literal rows have wrong masses;
    # 3=necessary-condition survivor (NOT a certified realization).
    var words = List[List[Int]]()
    for zero in range(5):
        for two in range(5):
            if zero == two:
                continue
            var word = List[Int]()
            for pos in range(5):
                var z = 1
                if pos == zero:
                    z = 0
                elif pos == two:
                    z = 2
                word.append(z)
            words.append(word^)
    assert_equal(len(words), 20)
    var found_pair = False
    var saw_nondiagonal = False
    for i in range(20):
        for j in range(i + 1, 20):
            var a = _area(words[i])
            var b = _area(words[j])
            var match = True
            for k in range(3):
                if a[k] + b[k] != 2 * mean[k]:
                    match = False
            if not match:
                continue
            var source_factors = decompose(words[i], words[j])
            if len(source_factors) != 1:
                continue
            found_pair = True
            var top = apply_substitution(sigma, words[i])
            var bottom = apply_substitution(sigma, words[j])
            var children = decompose(top, bottom)
            var diagonal = False
            var masses_agree = len(children) == len(expected_ids)
            for c in range(len(children)):
                if children[c].u == children[c].v:
                    diagonal = True
                var mass: List[Int] = [0,0,0]
                for z in children[c].u:
                    mass[z] += 1
                if c < len(expected_ids):
                    for k in range(3):
                        if mass[k] != P[k][expected_ids[c]]:
                            masses_agree = False
            if not diagonal:
                saw_nondiagonal = True
                if masses_agree:
                    return 3
    if not found_pair:
        return 0
    if saw_nondiagonal:
        return 2
    return 1


def replay_source_orders(sigma: List[List[Int]]) raises -> List[Int]:
    # A necessary-condition replay restricted to this EXACT incidence class.
    if len(sigma) != 3:
        raise Error("source must have three images")
    var expected: List[List[Int]] = [[1,1,0],[0,2,1],[1,1,1]]
    for j in range(3):
        _ = _area(sigma[j])  # range check before mass indexing
        var mass: List[Int] = [0,0,0]
        for z in sigma[j]:
            mass[z] += 1
        if mass != expected[j]:
            raise Error("source outside fixed incidence class")
    var M: List[List[Int]] = [[1,0,1], [1,2,1], [0,1,1]]
    var P: List[List[Int]] = [
        [1,1,2,1,1,2], [3,5,4,3,5,4], [1,3,2,1,3,2],
    ]
    var lo: List[Int] = [0,0,1]
    var hi: List[Int] = [1,2,2]
    var N = List[List[Int]]()
    for i in range(6):
        var row = List[Int]()
        for j in range(6):
            var v = 0
            if i // 3 != j // 3:
                v = M[i % 3][j % 3]
            row.append(v)
        N.append(row^)
    for a in range(3):
        for j in range(6):
            var pn = 0
            var mp = 0
            for i in range(6):
                pn += P[a][i] * N[i][j]
            for i in range(3):
                mp += M[a][i] * P[i][j]
            assert_equal(pn, mp)
    var S = List[List[Int]]()
    for i in range(6):
        for a in range(3):
            var row = List[Int]()
            for j in range(6):
                for b in range(3):
                    var v = 0
                    if i == j:
                        v = M[lo[a]][lo[b]] * M[hi[a]][hi[b]] - M[lo[a]][hi[b]] * M[hi[a]][lo[b]]
                    if a == b:
                        v -= N[j][i]
                    row.append(v)
            S.append(row^)
    var Q = inverse_numerator()
    validate_lift_inverse(S, Q, 1694)
    var areas = List[List[Int]]()
    for letter in range(3):
        areas.append(_area(sigma[letter]))
    var radices: List[Int] = [2,3,6,2,3,6]
    var report: List[Int] = [0,0,0,0,0,0]
    for code in range(1296):
        var q = code
        var choices = List[Int]()
        for j in range(6):
            choices.append(q % radices[j])
            q //= radices[j]
        assert_equal(q, 0)
        var rhs = List[Int]()
        for parent in range(6):
            var children = _row(parent, choices[parent])
            var observed: List[Int] = [0,0,0,0,0,0]
            for child in children:
                observed[child] += 1
            for child in range(6):
                assert_equal(observed[child], N[child][parent])
            for a in range(3):
                var value = 0
                for r in range(len(children)):
                    for t in range(r + 1, len(children)):
                        value += P[lo[a]][children[r]] * P[hi[a]][children[t]] - P[hi[a]][children[r]] * P[lo[a]][children[t]]
                for letter in range(3):
                    value -= areas[letter][a] * P[letter][parent]
                rhs.append(value)
        var values = lift_numerators(Q, rhs)
        var is_integer = True
        for value in values:
            if value % 1694 != 0:
                is_integer = False
        if is_integer:
            report[1] += 1
            var mean: List[Int] = [values[0] // 1694, values[1] // 1694, values[2] // 1694]
            var first_row = _row(0, choices[0])
            var outcome = _first_state_outcome(sigma, mean, first_row, P)
            report[2 + outcome] += 1
        else:
            report[0] += 1
    assert_equal(report[0] + report[1], 1296)
    assert_equal(report[1], report[2] + report[3] + report[4] + report[5])
    return report^


def test_all_orderings_and_exact_inverse() raises:
    # The original #490 result remains a separate regression.
    var sigma: List[List[Int]] = [[0,1], [1,2,1], [0,1,2]]
    assert_equal(replay_source_orders(sigma), [1291,5,5,0,0,0])


def test_complete_incidence_order_class() raises:
    var first: List[List[Int]] = [[0,1], [1,0]]
    var middle: List[List[Int]] = [[1,1,2], [1,2,1], [2,1,1]]
    var last: List[List[Int]] = [
        [0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0],
    ]
    var total: List[Int] = [0,0,0,0,0,0]
    var sources = 0
    for i in range(2):
        for j in range(3):
            for k in range(6):
                var sigma = List[List[Int]]()
                sigma.append(first[i].copy())
                sigma.append(middle[j].copy())
                sigma.append(last[k].copy())
                var receipt = replay_source_orders(sigma)
                for t in range(6):
                    total[t] += receipt[t]
                sources += 1
    assert_equal(sources, 36)
    assert_equal(total, [46466,190,176,8,6,0])


def test_false_certificate_and_invalid_letter_refuse() raises:
    var refused = False
    try:
        validate_lift_inverse([[1,0],[0,1]], [[2,0],[0,3]], 2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = _area([0,3])
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_all_orderings_and_exact_inverse()
    test_complete_incidence_order_class()
    test_false_certificate_and_invalid_letter_refuse()
    print("fixed six-state packet: all 36 sources and 46656 ordered lifts excluded")
    require_contract("fixed six-state periodic packet for all 36 source word orders: 46656 complete child orders, 46466 nonintegral, 176 impossible first-state words, 8 diagonal and 6 wrong literal child rows; preserve 1296-order original, no general C4/PSC")
