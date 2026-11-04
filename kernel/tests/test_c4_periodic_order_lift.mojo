"""Complete 1,296-order exclusion of ONE six-state, period-two matrix packet.

P=[M^2,M^2] is all-positive; PN=MP and each phase index is 4.
Sigma=(01,121,012). No general C4 or PSC claim follows.
"""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import decompose
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


def _no_first_state_pair(mean: List[Int]) raises:
    # Every word with mass (1,3,1), not a sample of possible realizations.
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
            words.append(word)
    assert_equal(len(words), 20)
    var hits = 0
    for i in range(20):
        for j in range(20):
            if i == j:
                continue
            var a = _area(words[i])
            var b = _area(words[j])
            var match = True
            for k in range(3):
                if a[k] + b[k] != 2 * mean[k]:
                    match = False
            if match:
                var factors = decompose(words[i], words[j])
                if len(factors) == 1:
                    hits += 1
    assert_equal(hits, 0)


def test_all_orderings_and_exact_inverse() raises:
    var sigma: List[List[Int]] = [[0,1], [1,2,1], [0,1,2]]
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
        N.append(row)
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
            S.append(row)
    var Q = inverse_numerator()
    validate_lift_inverse(S, Q, 1694)
    var areas = List[List[Int]]()
    for letter in range(3):
        areas.append(_area(sigma[letter]))
    var radices: List[Int] = [2,3,6,2,3,6]
    var nonintegral = 0
    var integral = 0
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
            integral += 1
            var mean: List[Int] = [values[0] // 1694, values[1] // 1694, values[2] // 1694]
            _no_first_state_pair(mean)
        else:
            nonintegral += 1
    assert_equal(integral, 5)
    assert_equal(nonintegral, 1291)


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
    test_false_certificate_and_invalid_letter_refuse()
    print("one six-state periodic template: all 1296 ordered lifts excluded")
    require_contract("complete 1296-order six-state periodic mean-area replay: 1291 nonintegral, five fail actual irreducible first-state words; exact two-sided inverse and malformed-input refusal; one synthetic template only, no general C4/PSC")
