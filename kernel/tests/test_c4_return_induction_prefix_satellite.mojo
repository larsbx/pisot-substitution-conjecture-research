"""Native exact controls: genuine Pisot return induction, word vs code prefixes."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution
from psc.c4_return_induction_prefix_satellite import (
    source_sigma, source_return_words, expected_return_substitution,
    induce_marker_zero_return, images_are_prefix_incomparable,
    verify_exact_return_induction,
)


def _matmul(a: List[List[Int]], b: List[List[Int]]) -> List[List[Int]]:
    var out = List[List[Int]]()
    for i in range(len(a)):
        var row = List[Int]()
        for j in range(len(b[0])):
            var acc = 0
            for k in range(len(b)):
                acc += a[i][k] * b[k][j]
            row.append(acc)
        out.append(row)
    return out^


def test_exact_return_images_from_actual_three_letter_substitution() raises:
    var sigma = source_sigma()
    var words = source_return_words()
    assert_equal(sigma, [[0, 1], [1, 2, 1], [0, 1, 2]])
    assert_equal(words, [
        [0, 1, 1, 2, 1, 1, 2, 1],
        [0, 1, 2, 1, 2, 1, 1, 2, 1],
        [0, 1, 2, 1, 2, 1],
        [0, 1, 1, 2, 1],
    ])
    var tau = induce_marker_zero_return(sigma, words)
    assert_equal(tau, [[0, 1, 2], [3, 2, 1, 2], [3, 2, 2], [0, 2]])
    assert_equal(tau, expected_return_substitution())
    assert_true(images_are_prefix_incomparable(tau))


def test_primitivity_of_induced_substitution() raises:
    # All matrix arithmetic is exact integer: positive N^3 is a complete
    # finite certificate of primitivity for this four-letter substitution.
    var tau = verify_exact_return_induction(1)
    var n: List[List[Int]] = [
        [1, 0, 0, 1],
        [1, 1, 0, 0],
        [1, 2, 2, 1],
        [0, 1, 1, 0],
    ]
    for i in range(4):
        for j in range(4):
            var count = 0
            for c in tau[j]:
                if c == i:
                    count += 1
            assert_equal(count, n[i][j])
    var square = _matmul(n, n)
    var cube = _matmul(square, n)
    assert_equal(cube, [
        [3, 4, 3, 2],
        [3, 2, 1, 2],
        [17, 20, 13, 10],
        [7, 8, 5, 4],
    ])
    for row in cube:
        for entry in row:
            assert_true(entry > 0)


def test_all_actual_return_image_factorisations_and_bounded_powers() raises:
    var tau = verify_exact_return_induction(6)
    assert_true(images_are_prefix_incomparable(tau))
    # The first source return itself really occurs as an initial complete
    # return word, not as a fabricated codeword.
    var sigma = source_sigma()
    var third: List[Int] = [0]
    for _ in range(3):
        third = apply_substitution(sigma, third)
    assert_equal(third, [
        0,1,1,2,1,1,2,1,0,1,2,1,2,1,
    ])


def test_malformed_or_incomplete_return_set_refuses() raises:
    var sig = source_sigma()
    var r = source_return_words()
    # A non-closed return inventory must never yield a made-up induced edge.
    var missing: List[List[Int]] = [r[0].copy(), r[1].copy(), r[2].copy()]
    var malformed: List[List[Int]] = [
        [0,1,0,2], r[1].copy(), r[2].copy(), r[3].copy(),
    ]
    var repeated: List[List[Int]] = [
        r[0].copy(), r[0].copy(), r[2].copy(), r[3].copy(),
    ]
    for specimen in [missing, malformed, repeated]:
        var refused = False
        try:
            _ = induce_marker_zero_return(sig, specimen)
        except:
            refused = True
        assert_true(refused)
    var wrong_sig: List[List[Int]] = [[0, 2], [1, 2, 1], [0, 1, 2]]
    var refused_wrong = False
    try:
        _ = induce_marker_zero_return(wrong_sig, r)
    except:
        refused_wrong = True
    assert_true(refused_wrong)
    for cap in [-1, 0, 7]:
        var refused_cap = False
        try:
            _ = verify_exact_return_induction(cap)
        except:
            refused_cap = True
        assert_true(refused_cap)


def test_prefix_code_refuses_literal_satellite_but_not_strong_coincidence() raises:
    var prefix_code: List[List[Int]] = [
        [0, 1, 2], [3, 2, 1, 2], [3, 2, 2], [0, 2]
    ]
    var proper_prefix: List[List[Int]] = [
        [0, 1], [0, 1, 2], [2], [3],
    ]
    var duplicate: List[List[Int]] = [
        [0, 1], [0, 1], [2], [3],
    ]
    assert_true(images_are_prefix_incomparable(prefix_code))
    assert_true(not images_are_prefix_incomparable(proper_prefix))
    assert_true(not images_are_prefix_incomparable(duplicate))
    # The source is positively strong coincident, tested by the oracle
    # and directly in the canonical module; loss is only a LITERAL
    # prefix-satellite word relation in the return alphabet.



def _inflate_physical(
    sigma: List[List[Int]], input: List[Int], level: Int,
) -> List[Int]:
    var word = input.copy()
    for _ in range(level):
        word = apply_substitution(sigma, word)
    return word^


def test_shared_expanding_residual_is_literal_at_all_bounded_depths() raises:
    var sigma = source_sigma()
    var returns = source_return_words()
    var B = sigma[1].copy()
    var r3B = returns[3].copy()
    var r2B = returns[2].copy()
    for c in B:
        r3B.append(c)
        r2B.append(c)
    assert_equal(returns[0], r3B)
    assert_equal(returns[1], r2B)
    var earlier_tail_length = 0
    for n in range(5):
        var tail = _inflate_physical(sigma, [1], n+1)
        assert_true(len(tail) > earlier_tail_length)
        earlier_tail_length = len(tail)
        var u0 = _inflate_physical(sigma, returns[0], n)
        var u1 = _inflate_physical(sigma, returns[1], n)
        var u2 = _inflate_physical(sigma, returns[2], n)
        var u3 = _inflate_physical(sigma, returns[3], n)
        var expected0 = u3.copy()
        var expected1 = u2.copy()
        for c in tail:
            expected0.append(c)
            expected1.append(c)
        assert_equal(u0, expected0)
        assert_equal(u1, expected1)



def test_exact_return_parikh_intertwiner_and_killed_kernel() raises:
    var sigma = source_sigma()
    var returns = source_return_words()
    var tau = induce_marker_zero_return(sigma, returns)
    var M: List[List[Int]] = [
        [1, 0, 1],
        [1, 2, 1],
        [0, 1, 1],
    ]
    var P: List[List[Int]] = [
        [1, 1, 1, 1],
        [5, 5, 3, 3],
        [2, 3, 2, 1],
    ]
    var N: List[List[Int]] = [
        [1, 0, 0, 1],
        [1, 1, 0, 0],
        [1, 2, 2, 1],
        [0, 1, 1, 0],
    ]
    # Independent reconstruction of both incidence matrices and Parikh map.
    for col in range(3):
        for row in range(3):
            var actual = 0
            for c in sigma[col]:
                if c == row:
                    actual += 1
            assert_equal(actual, M[row][col])
    for col in range(4):
        for row in range(3):
            var actual = 0
            for c in returns[col]:
                if c == row:
                    actual += 1
            assert_equal(actual, P[row][col])
        for row in range(4):
            var actual_n = 0
            for c in tau[col]:
                if c == row:
                    actual_n += 1
            assert_equal(actual_n, N[row][col])
    assert_equal(_matmul(M, P), _matmul(P, N))
    assert_equal(_matmul(M, P), [
        [3, 4, 3, 2],
        [13, 14, 9, 8],
        [7, 8, 5, 4],
    ])
    # Integer witness: determinant of first three columns of P is 2.
    var minor = (
        P[0][0] * (P[1][1] * P[2][2] - P[1][2] * P[2][1])
        - P[0][1] * (P[1][0] * P[2][2] - P[1][2] * P[2][0])
        + P[0][2] * (P[1][0] * P[2][1] - P[1][1] * P[2][0])
    )
    assert_equal(minor, 2)
    var v: List[Int] = [-1, 1, -1, 1]
    for i in range(3):
        var pv = 0
        for j in range(4):
            pv += P[i][j] * v[j]
        assert_equal(pv, 0)
    for i in range(4):
        var nv = 0
        for j in range(4):
            nv += N[i][j] * v[j]
        assert_equal(nv, 0)


def main() raises:
    test_exact_return_images_from_actual_three_letter_substitution()
    test_primitivity_of_induced_substitution()
    test_all_actual_return_image_factorisations_and_bounded_powers()
    test_malformed_or_incomplete_return_set_refuses()
    test_prefix_code_refuses_literal_satellite_but_not_strong_coincidence()
    test_shared_expanding_residual_is_literal_at_all_bounded_depths()
    test_exact_return_parikh_intertwiner_and_killed_kernel()
    print("C4 return induction: exact four-return code, all-power prefix-code obstruction and negative controls passed.")
    require_contract("the PIP substitution 01/121/012 has a literal prefix satellite and level-two simultaneous coincidence, but its exact four-letter return substitution on zero is primitive with pairwise prefix-incomparable images; the all-power absence is proved by prefix-code argument, not cap exhaustion")
