"""Exact regression for Theorem FP (psc.fixed_point_count): the number of
tilings fixed by the n-th power of the inflation, by the trace formula and by
a literal count of reproduced pointed windows.

docs/c4-rank-two-wall-2026-11-16.md, Theorem FP (the Anderson--Putnam zeta
count, restated). Two computations that share only the validation gate are
compared for `1 <= n <= 6` on every fixture:

- the formula `tr(M^n) - #Fix(g^n) - #Fix(g_R^n) + #{fixed legal seams}`,
  from checked powers of the incidence matrix, the endpoint maps and
  `psc.h1_census.legal_two_words`;
- the literal count: the legal three-letter windows `b.j.c` that
  `sigma^n(b) sigma^n(j) sigma^n(c)` reproduces around the `k`-th letter of
  `sigma^n(j)`, read off the words themselves, the windows taken from
  `substitution_dynamics.return_lattice.factor_set`.

They are compared as totals, part by part (interior fixed points letter by
letter, the seams as lists), and the literal count is repeated at radius 2.
The totals below were first produced by a scratch Python oracle of this
landing and by the scratch scripts of the prover and the verifiers
(`011/120/2012`: 11 at `n = 2`; `10/102/211`: 7 and 19 at `n = 2, 3`;
`1/012/101`: 5, 33, 197 at `n = 2, 4, 6`); those are not evidence, the two
Mojo computations are. Three rows are closed forms that neither computation
uses: `2^n - 1` on the periodic control (from the circle map, independently
of Theorem FP), and `L_n - 1` on Fibonacci and `2^n - 1 + (-1)^n` on
Thue--Morse (the formula evaluated by hand).

Fixtures: Tribonacci and four more members of the standing corpus with
different endpoint classes (asserted PIP, images of length at most 3); the
reducible strict controls `011/120/2012`, `1/012/101`, `10/102/211`; the
periodic control `1/012/1`; Fibonacci and Thue--Morse on two letters.

Nothing here certifies a coincidence rank, strong coincidence or pure
discrete spectrum, and no claim status changes: these are counts of periodic
points of the inflation.

Replay:
`cd kernel && pixi run --locked mojo run -I . -I tests tests/test_fixed_point_count.mojo`
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import apply_substitution, substitution_incidence
from psc.endpoint_core import endpoint_type, prefix_endpoint_map, suffix_endpoint_map
from psc.fixed_point_count import (
    LITERAL_WORD_CAP,
    fixed_point_formula,
    literal_fixed_tilings,
    matrix_power,
    primitive_incidence,
)
from psc.h1_census import legal_two_words
from psc.periodic_pair import incidence_power
from psc.pisot import is_irreducible_cubic, is_pip, is_primitive
from substitution_dynamics.return_lattice import factor_set
from substitution_dynamics.substitution import Substitution

comptime MAX_N = 6


def tribonacci() -> List[List[Int]]:
    return [[0, 1], [0, 2], [0]]


def check(
    sigma: List[List[Int]],
    totals: List[Int],
    traces: List[Int],
    firsts: List[Int],
    lasts: List[Int],
    seams: List[Int],
) raises -> Int:
    """Both counts at `n = 1..MAX_N` against the pinned rows, and against each
    other part by part. Returns the sum of the totals."""
    var size = len(sigma)
    var running = 0
    for n in range(1, MAX_N + 1):
        var f = fixed_point_formula(sigma, n)
        assert_equal(f.power, n)
        assert_equal(f.trace, traces[n - 1])
        assert_equal(f.first_fixed, firsts[n - 1])
        assert_equal(f.last_fixed, lasts[n - 1])
        assert_equal(f.seams, seams[n - 1])
        assert_equal(len(f.seam_keys), f.seams)
        assert_equal(f.total(), totals[n - 1])
        assert_equal(f.trace - f.first_fixed - f.last_fixed + f.seams, totals[n - 1])
        # The two checked matrix powers agree, and the trace is theirs.
        var power = matrix_power(primitive_incidence(sigma), size, n)
        if size == 3:
            assert_equal(power, incidence_power(sigma, n).e)
        var diagonal = 0
        for j in range(size):
            diagonal += power[size * j + j]
        assert_equal(diagonal, traces[n - 1])

        var l = literal_fixed_tilings(sigma, n)
        assert_equal(l.power, n)
        assert_equal(l.radius, 1)
        assert_equal(l.total(), totals[n - 1])
        # Part by part. Interior fixed points, letter by letter: the diagonal
        # of M^n less the first and the last occurrence.
        assert_equal(len(l.interior), size)
        assert_equal(len(f.interior), size)
        var interior = 0
        for j in range(size):
            assert_equal(l.interior[j], f.interior[j])
            interior += l.interior[j]
        assert_equal(interior, f.trace - f.first_fixed - f.last_fixed)
        assert_equal(l.interior_total(), interior)
        # Vertex type: the same seams, as lists; each is seen once from the
        # tile on its right and once from the tile on its left.
        assert_equal(l.left_vertex, f.seams)
        assert_equal(l.right_vertex, f.seams)
        assert_equal(l.left_seams, f.seam_keys)
        assert_equal(l.right_seams, f.seam_keys)
        for i in range(1, len(f.seam_keys)):
            assert_true(f.seam_keys[i - 1] < f.seam_keys[i])
        # The count does not depend on the radius of the window.
        var wide = literal_fixed_tilings(sigma, n, 2)
        assert_equal(wide.radius, 2)
        assert_equal(wide.total(), totals[n - 1])
        assert_equal(wide.left_seams, f.seam_keys)
        assert_equal(wide.right_seams, f.seam_keys)
        for j in range(size):
            assert_equal(wide.interior[j], f.interior[j])
        running += totals[n - 1]
    return running


def window_key(w: List[Int], start: Int, length: Int, size: Int) -> Int:
    var key = 0
    for i in range(length):
        key = key * size + w[start + i]
    return key


def scanned_windows(sigma: List[List[Int]], length: Int, min_length: Int) raises -> Dict[Int, Bool]:
    """The `length`-letter factors read off `sigma^K(0)`, `K` least with at
    least `min_length` letters: a literal sample of the language."""
    var s = Substitution.checked(sigma)
    var w: List[Int] = [0]
    for _ in range(64):
        if len(w) >= min_length:
            break
        w = s.apply(w)
    if len(w) < min_length:
        raise Error("scanned windows: the seed word does not grow")
    var out = Dict[Int, Bool]()
    for i in range(len(w) - length + 1):
        out[window_key(w, i, length, len(sigma))] = True
    return out^


def check_language(sigma: List[List[Int]], two: Int, three: Int, five: Int) raises:
    """The three language computations agree: the closure of
    `legal_two_words` (formula side), the window closure of `factor_set`
    (literal side) and a scan of a 20,000-letter word."""
    var size = len(sigma)
    var s = Substitution.checked(sigma)
    var mask = legal_two_words(sigma)
    var pairs = factor_set(s, 2)
    assert_equal(len(pairs), two)
    var masked = 0
    for k in range(len(mask)):
        if mask[k]:
            masked += 1
    assert_equal(masked, two)
    for i in range(len(pairs)):
        assert_true(mask[size * pairs[i][0] + pairs[i][1]])
    var lengths: List[Int] = [2, 3, 5]
    var expected: List[Int] = [two, three, five]
    for t in range(3):
        var closure = factor_set(s, lengths[t])
        assert_equal(len(closure), expected[t])
        var scan = scanned_windows(sigma, lengths[t], 20000)
        assert_equal(len(scan), expected[t])
        for i in range(len(closure)):
            assert_true(window_key(closure[i], 0, lengths[t], size) in scan)
    var l = literal_fixed_tilings(sigma, 1)
    assert_equal(l.windows, three)
    assert_equal(literal_fixed_tilings(sigma, 1, 2).windows, five)


def test_tribonacci_by_hand() raises:
    """`0 -> 01, 1 -> 02, 2 -> 0`, by hand; `g` is constant `0`, `g_R` the
    3-cycle `0 -> 1 -> 2 -> 0`.

    `n = 1`: no letter occurs strictly inside its own image and `g_R` has no
    fixed letter: 0.
    `n = 2`: `sigma^2 = 0102 / 010 / 01`; `0` at index 2 of `0102` and `1` at
    index 1 of `010` are interior; `g_R^2` has no fixed letter: 2.
    `n = 3`: `sigma^3 = 0102010 / 010201 / 0102`; `0` at indices 2 and 4, `1`
    at index 1 (index 5 is last), `2` only last: 3 interior. `g_R^3` is the
    identity and `g^3(a) = a` only for `a = 0`, so the fixed seams are the
    legal words `b0`: `00`, `10`, `20` (the legal two-letter words are
    `00, 01, 02, 10, 20`). 3 + 3 = 6 = 7 - 1 - 3 + 3."""
    var sigma = tribonacci()
    assert_equal(apply_substitution(sigma, apply_substitution(sigma, [0])), List[Int]([0, 1, 0, 2]))
    assert_equal(
        apply_substitution(sigma, apply_substitution(sigma, apply_substitution(sigma, [0]))),
        List[Int]([0, 1, 0, 2, 0, 1, 0]),
    )
    var one = literal_fixed_tilings(sigma, 1)
    assert_equal(one.total(), 0)
    var two = literal_fixed_tilings(sigma, 2)
    assert_equal(two.interior, List[Int]([1, 1, 0]))
    assert_equal(two.left_vertex, 0)
    assert_equal(two.total(), 2)
    var three = literal_fixed_tilings(sigma, 3)
    assert_equal(three.interior, List[Int]([2, 1, 0]))
    assert_equal(three.left_seams, List[Int]([0, 3, 6]))
    assert_equal(three.right_seams, List[Int]([0, 3, 6]))
    assert_equal(three.total(), 6)
    var f = fixed_point_formula(sigma, 3)
    assert_equal(f.trace, 7)
    assert_equal(f.first_fixed, 1)
    assert_equal(f.last_fixed, 3)
    assert_equal(f.seam_keys, List[Int]([0, 3, 6]))
    assert_equal(f.interior, List[Int]([2, 1, 0]))
    assert_equal(f.total(), 6)
    check_language(sigma, 5, 7, 11)


def assert_corpus_member(sigma: List[List[Int]], plus: Int, minus: Int) raises:
    """A member of the standing corpus (PIP, images of length at most 3) with
    the stated endpoint types `A..G = 0..6` of `g` and `g_R`."""
    assert_equal(len(sigma), 3)
    for a in range(3):
        assert_true(len(sigma[a]) >= 1 and len(sigma[a]) <= 3)
    assert_true(is_pip(Mat3(substitution_incidence(sigma))))
    assert_equal(endpoint_type(prefix_endpoint_map(sigma)), plus)
    assert_equal(endpoint_type(suffix_endpoint_map(sigma)), minus)


def test_corpus_specimens() raises -> Int:
    """Five members of the standing corpus, pairwise different in the
    endpoint types of `(g, g_R)`: (A, G), (C, F), (G, B), (E, G), (D, G)."""
    var sum = 0
    # Tribonacci 01/02/0: g constant, g_R a 3-cycle.
    assert_corpus_member(tribonacci(), 0, 6)
    sum += check(
        tribonacci(),
        [0, 2, 6, 10, 20, 38], [1, 3, 7, 11, 21, 39], [1, 1, 1, 1, 1, 1], [0, 0, 3, 0, 0, 3], [0, 0, 3, 0, 0, 3],
    )
    # 01/12/021: g has two fixed letters, g_R a 2-cycle with a leaf.
    var interior_control: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    assert_corpus_member(interior_control, 2, 5)
    sum += check(
        interior_control,
        [1, 5, 10, 29, 66, 158], [3, 5, 12, 29, 68, 158], [2, 2, 2, 2, 2, 2], [0, 2, 0, 2, 0, 2], [0, 4, 0, 4, 0, 4],
    )
    check_language(interior_control, 7, 13, 24)
    # 1/2/02: g a 3-cycle, g_R with one fixed letter and a tail of length two.
    var cyclic: List[List[Int]] = [[1], [2], [0, 2]]
    assert_corpus_member(cyclic, 6, 1)
    sum += check(
        cyclic,
        [0, 0, 3, 4, 5, 9], [1, 1, 4, 5, 6, 10], [0, 0, 3, 0, 0, 3], [1, 1, 1, 1, 1, 1], [0, 0, 3, 0, 0, 3],
    )
    check_language(cyclic, 5, 7, 11)
    # 1/02/200: g a transposition with a fixed letter, g_R a 3-cycle; every
    # two-letter word is legal, and at n = 6 all nine seams are fixed.
    var permutations: List[List[Int]] = [[1], [0, 2], [2, 0, 0]]
    assert_corpus_member(permutations, 4, 6)
    sum += check(
        permutations,
        [0, 0, 6, 8, 20, 42], [1, 3, 7, 11, 21, 39], [1, 3, 1, 3, 1, 3], [0, 0, 3, 0, 0, 3], [0, 0, 3, 0, 0, 9],
    )
    check_language(permutations, 9, 17, 35)
    assert_equal(fixed_point_formula(permutations, 6).seam_keys, List[Int]([0, 1, 2, 3, 4, 5, 6, 7, 8]))
    # 01/12/210: g the identity, g_R a 3-cycle.
    var identity: List[List[Int]] = [[0, 1], [1, 2], [2, 1, 0]]
    assert_corpus_member(identity, 3, 6)
    sum += check(
        identity,
        [0, 2, 15, 26, 65, 161], [3, 5, 12, 29, 68, 158], [3, 3, 3, 3, 3, 3], [0, 0, 3, 0, 0, 3], [0, 0, 9, 0, 0, 9],
    )
    check_language(identity, 9, 16, 33)
    return sum


def test_reducible_controls() raises -> Int:
    """The three reducible strict controls. Theorem FP needs primitivity
    only, so it applies to them; none is in PIP3."""
    var sum = 0
    # C-D1 = 011/120/2012, chi = (x - 1)(x^2 - 3x - 1); an image of length 4.
    var cd1: List[List[Int]] = [[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]]
    var m1 = Mat3(substitution_incidence(cd1))
    assert_true(is_primitive(m1))
    assert_false(is_irreducible_cubic(m1.charpoly()))
    sum += check(
        cd1,
        [1, 11, 34, 119, 391, 1298], [4, 12, 37, 120, 394, 1299], [3, 3, 3, 3, 3, 3], [1, 3, 1, 3, 1, 3],
        [1, 5, 1, 5, 1, 5],
    )
    check_language(cd1, 5, 8, 15)
    # 1/012/101, chi = (x + 1)(x^2 - 2x - 1).
    var flat: List[List[Int]] = [[1], [0, 1, 2], [1, 0, 1]]
    var m2 = Mat3(substitution_incidence(flat))
    assert_true(is_primitive(m2))
    assert_false(is_irreducible_cubic(m2.charpoly()))
    sum += check(
        flat,
        [1, 5, 13, 33, 81, 197], [1, 7, 13, 35, 81, 199], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 0, 2],
    )
    check_language(flat, 4, 5, 7)
    # 10/102/211, chi = (x - 1)(x^2 - 2x - 2). By hand at n = 1: no letter
    # is strictly inside its own image (0 is last in 10, 1 first in 102, 2
    # first in 211); g = (1, 1, 2), g_R = (0, 2, 1); the legal two-letter
    # words are 02, 10, 11, 21, and the only one `ba` with g_R(b) = b and
    # g(a) = a is 02: one fixed tiling, with the seam 0.2 at the origin.
    var seam: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var m3 = Mat3(substitution_incidence(seam))
    assert_true(is_primitive(m3))
    assert_false(is_irreducible_cubic(m3.charpoly()))
    sum += check(
        seam,
        [1, 7, 19, 55, 151, 415], [3, 9, 21, 57, 153, 417], [2, 2, 2, 2, 2, 2], [1, 3, 1, 3, 1, 3], [1, 3, 1, 3, 1, 3],
    )
    check_language(seam, 4, 6, 8)
    var first = literal_fixed_tilings(seam, 1)
    assert_equal(first.interior, List[Int]([0, 0, 0]))
    assert_equal(first.left_seams, List[Int]([2]))
    assert_equal(fixed_point_formula(seam, 1).seam_keys, List[Int]([2]))
    return sum


def test_periodic_control() raises -> Int:
    """`0 -> 1, 1 -> 012, 2 -> 1` is primitive with eigenvalues `2, -1, 0`
    and its fixed bi-infinite words are periodic: `sigma(1012) = 012 1 012 1`
    is `(1012)^2` rotated, so the hull is one circle, on which the inflation
    is `t -> 2t + const`. A map `t -> 2^n t + const` of a circle has
    `2^n - 1` fixed points. Neither computation knows that; Theorem FP holds
    for periodic primitive substitutions too."""
    var periodic: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var m = Mat3(substitution_incidence(periodic))
    assert_true(is_primitive(m))
    assert_equal(m.det(), 0)
    var block: List[Int] = [1, 0, 1, 2]
    assert_equal(apply_substitution(periodic, block), List[Int]([0, 1, 2, 1, 0, 1, 2, 1]))
    var totals = List[Int]()
    var power = 1
    for _ in range(MAX_N):
        power *= 2
        totals.append(power - 1)
    assert_equal(totals, List[Int]([1, 3, 7, 15, 31, 63]))
    var sum = check(
        periodic, totals, [1, 5, 7, 17, 31, 65], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 0, 2],
    )
    # The language of a periodic word of period 4 has four factors of every
    # length from 2 on.
    check_language(periodic, 4, 4, 4)
    return sum


def test_two_letter_calibrations() raises -> Int:
    """Fibonacci `0 -> 01, 1 -> 0`: `tr(M^n) = L_n` (Lucas), `#Fix(g^n) = 1`,
    and the last-letter and seam terms cancel (0 and 0 for odd `n`; 2 and the
    two legal words `00`, `10` for even `n`), so the count is `L_n - 1`:
    0, 2, 3, 6, 10, 17. Thue--Morse `0 -> 01, 1 -> 10`: `tr(M^n) = 2^n`,
    `#Fix(g^n) = 2`, and `g_R^n` is the exchange for odd `n` (no fixed letter,
    no seam) and the identity for even `n` (2 fixed letters, all 4 words
    legal): `2^n - 2` for odd `n`, `2^n` for even `n`, i.e. `2^n - 1 + (-1)^n`."""
    var fibonacci: List[List[Int]] = [[0, 1], [0]]
    var lucas: List[Int] = [1, 3]
    while len(lucas) < MAX_N:
        lucas.append(lucas[len(lucas) - 1] + lucas[len(lucas) - 2])
    var fib_totals = List[Int]()
    for n in range(MAX_N):
        fib_totals.append(lucas[n] - 1)
    assert_equal(fib_totals, List[Int]([0, 2, 3, 6, 10, 17]))
    var sum = check(fibonacci, fib_totals, lucas, [1, 1, 1, 1, 1, 1], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 0, 2])
    check_language(fibonacci, 3, 4, 6)

    var thue_morse: List[List[Int]] = [[0, 1], [1, 0]]
    var tm_totals = List[Int]()
    var tm_traces = List[Int]()
    var power = 1
    for n in range(1, MAX_N + 1):
        power *= 2
        tm_traces.append(power)
        tm_totals.append(power - 2 if n % 2 == 1 else power)
    assert_equal(tm_totals, List[Int]([0, 4, 6, 16, 30, 64]))
    sum += check(thue_morse, tm_totals, tm_traces, [2, 2, 2, 2, 2, 2], [0, 2, 0, 2, 0, 2], [0, 4, 0, 4, 0, 4])
    check_language(thue_morse, 4, 6, 12)
    return sum


def formula_refuses(sigma: List[List[Int]], n: Int, expected: String) -> Bool:
    try:
        _ = fixed_point_formula(sigma, n)
        return False
    except e:
        return expected in String(e)


def literal_refuses(sigma: List[List[Int]], n: Int, radius: Int, cap: Int, expected: String) -> Bool:
    try:
        _ = literal_fixed_tilings(sigma, n, radius, cap)
        return False
    except e:
        return expected in String(e)


def both_refuse(sigma: List[List[Int]], expected: String) -> Bool:
    return formula_refuses(sigma, 1, expected) and literal_refuses(sigma, 1, 1, LITERAL_WORD_CAP, expected)


def test_refusals() raises:
    # Not primitive: the diagonal 00/11/22, and 1/0/22, whose strict system
    # {(01,10), (10,01)} is pinned in test_c4_reducible_pisot_controls.
    assert_true(both_refuse([[0, 0], [1, 1], [2, 2]], "not primitive"))
    assert_true(both_refuse([[1], [0], [2, 2]], "not primitive"))
    # A permutation of the letters is not primitive either.
    assert_true(both_refuse([[1], [2], [0]], "not primitive"))
    # Malformed: an empty image, a letter outside the alphabet, one letter,
    # nine letters.
    assert_true(both_refuse([[0, 1], List[Int](), [0]], "erasing"))
    assert_true(both_refuse([[0, 3], [0, 2], [0]], "outside the alphabet"))
    assert_true(both_refuse([[0, 0]], "at least two letters"))
    var nine = List[List[Int]]()
    for a in range(9):
        nine.append([(a + 1) % 9, a])
    assert_true(both_refuse(nine, "alphabet size must lie in 2..8"))
    # The power is at least one.
    assert_true(formula_refuses(tribonacci(), 0, "at least one"))
    assert_true(formula_refuses(tribonacci(), -1, "at least one"))
    assert_true(literal_refuses(tribonacci(), 0, 1, LITERAL_WORD_CAP, "at least one"))
    # The window radius is 1 or 2.
    assert_true(literal_refuses(tribonacci(), 1, 0, LITERAL_WORD_CAP, "radius"))
    assert_true(literal_refuses(tribonacci(), 1, 3, LITERAL_WORD_CAP, "radius"))
    # A word cap is an exhausted budget, never a count: sigma^6(0) of
    # Tribonacci has 44 letters.
    assert_true(literal_refuses(tribonacci(), 6, 1, 43, "inconclusive"))
    assert_equal(literal_fixed_tilings(tribonacci(), 6, 1, 44).total(), 38)
    assert_true(literal_refuses(tribonacci(), 1, 1, 0, "cap must be positive"))
    # Checked arithmetic: tr(M^70) = 2^70 for Thue--Morse does not fit, and
    # the formula raises instead of wrapping.
    assert_true(formula_refuses([[0, 1], [1, 0]], 70, "overflow"))
    assert_equal(fixed_point_formula([[0, 1], [1, 0]], 62).total(), 4611686018427387904)
    # The gate itself.
    assert_equal(primitive_incidence(tribonacci()), List[Int]([1, 1, 1, 1, 0, 0, 0, 1, 0]))


def main() raises:
    test_tribonacci_by_hand()
    var corpus_sum = test_corpus_specimens()
    var control_sum = test_reducible_controls()
    var periodic_sum = test_periodic_control()
    var two_letter_sum = test_two_letter_calibrations()
    test_refusals()
    assert_equal(corpus_sum, 76 + 269 + 21 + 76 + 269)
    assert_equal(control_sum, 1854 + 330 + 648)
    assert_equal(periodic_sum, 120)
    assert_equal(two_letter_sum, 38 + 120)
    print(
        "fixed points of the inflation (Theorem FP): formula and literal window count agree for n = 1 ..", MAX_N,
        "on 11 substitutions; sums of |Fix(Phi^n)| over n: five corpus specimens", corpus_sum,
        ", reducible controls", control_sum, ", periodic control", periodic_sum, ", Fibonacci and Thue-Morse",
        two_letter_sum,
    )
    require_contract("Fixed points of the inflation on a one-dimensional substitution tiling space (psc.fixed_point_count, Theorem FP: the Anderson-Putnam zeta count, restated), exact checked integer arithmetic, for a primitive substitution on 2..8 letters: |Fix(Phi^n)| = tr(M^n) - #Fix(g^n) - #Fix(g_R^n) + #{legal two-letter words ba with g_R^n(b) = b, g^n(a) = a}, computed from checked powers of the incidence matrix (psc.periodic_pair.incidence_power on three letters, compared with the alphabet-generic matrix_power), the endpoint maps and psc.h1_census.legal_two_words, equals for 1 <= n <= 6 the literal count of pointed legal windows b.j.c that sigma^n(b) sigma^n(j) sigma^n(c) reproduces around the k-th letter of sigma^n(j), 0 <= k <= |sigma^n(j)| - 2 (the tile is half-open; the windows come from substitution_dynamics.return_lattice.factor_set and the words from literal substitution), part by part: interior fixed points letter by letter, the fixed seams as lists, each vertex-type tiling seen once from the tile on its right and once from the tile on its left, and the same count at window radius 2. Pinned |Fix(Phi^n)|, n = 1..6: Tribonacci 01/02/0: 0, 2, 6, 10, 20, 38 (n = 1, 2, 3 by hand); corpus specimens 01/12/021: 1, 5, 10, 29, 66, 158; 1/2/02: 0, 0, 3, 4, 5, 9; 1/02/200: 0, 0, 6, 8, 20, 42; 01/12/210: 0, 2, 15, 26, 65, 161 (endpoint types (A,G), (C,F), (G,B), (E,G), (D,G), each asserted PIP with images of length at most 3); reducible controls 011/120/2012: 1, 11, 34, 119, 391, 1298; 1/012/101: 1, 5, 13, 33, 81, 197; 10/102/211: 1, 7, 19, 55, 151, 415 (n = 1 by hand: the seam 0.2); periodic control 1/012/1: 2^n - 1 = 1, 3, 7, 15, 31, 63; Fibonacci 01/0: L_n - 1 = 0, 2, 3, 6, 10, 17; Thue-Morse 01/10: 0, 4, 6, 16, 30, 64. The legal words of length 2 (psc.h1_census.legal_two_words and factor_set) and of length 3 and 5 (factor_set) agree with a scan of a 20,000-letter word on every fixture. Refusals: non-primitive 00/11/22, 1/0/22 and the cyclic permutation, an erasing image, a letter outside the alphabet, one letter, nine letters, a power below one, a window radius other than 1 or 2, a word cap (inconclusive, not a count) and an overflowing trace (Thue-Morse at n = 70) raise, each matched on its message. Counts of periodic points only: no coincidence rank, strong coincidence or pure discrete spectrum is certified, and no claim status changes")
