"""Exact regression for the divisor condition of Theorem P+
(psc.rank_two_parity).

docs/c4-rank-two-wall-2026-11-16.md, Lemma S+ and Theorem P+;
docs/c4-geometric-f-class-2026-11-16.md, Lemma 7. What is pinned:

- the substitution action `f` on the eventual range `ER` as a graph map, on
  hand-checked fixtures (edges, vertices, images, cycle types, order);
- `c_n`, the characteristic polynomial of `(f^n)*` on `H^1(ER; Q)`, by hand
  on the fixtures and, on every corpus specimen and every control the graph
  level accepts, against an independent computation in this test: Newton's
  identities applied to the Lefschetz traces
  `tr((f^m)* | H^1) = 1 - #Fix_V(f^m) + #Fix_E(f^m)`, with the fixed
  points counted by iterating the permutation lists, no cycle type and no
  polynomial division;
- the cyclotomic factorisation of `c_n` (from the cycle type, and by trial
  division in the module, which must agree), and the cyclotomic
  polynomials `Phi_1 .. Phi_12` by hand;
- `chi_{M^n} mod 2` and `h_n`, by hand on the fixtures (the Frobenius
  argument) and, on every corpus specimen for `n = 1..8`, against the
  vendored `Mat3.charpoly` of the checked integer power `M^n` reduced mod 2;
- the admissible `n` of the note, by hand, and against the seams of Theorem
  FP (`psc.fixed_point_count`, the legal words `ba` with `g_R^n(b) = b`,
  `g^n(a) = a`) on every corpus specimen for `n = 1..6`;
- that all data at `n` and `n + 42` agree on every corpus specimen for
  `n = 1..42` (the periodicity the module's docstring proves, on which the
  finite set `n = 1..42` rests);
- the exhaustive sub-multiset search on hand-made instances;
- three consequences of Theorem P+ that are elementary given the definitions,
  on every corpus specimen: the dimension bound fails only if every
  admissible `n` fails; `d_2 = 1` never fails; for odd determinant the
  condition at `n = 6` fails exactly on the class of Theorem P
  (`dim H^1 <= 4` or `tr M != e_2(M) mod 2`);
- the census over `pip_corpus()`, split by determinant parity and by (F) with
  two periodic letters on both sides, and its effect on the open classes of
  §15.3 item 1 of the closure-attempt note (132 even, 180 odd).

Results pinned below: the divisor condition fails on 2,364 odd and 930 even
specimens; beyond the hypotheses of the recorded theorems without it (odd:
`dim H^1 <= 4` or `tr M != e_2(M) mod 2`; even: `dim H^1 = 3`) on 12 odd and
24 even specimens, all first failing at `n = 2`, none with (F), all with two
periodic letters on both sides; the open classes of §15.3 item 1 (132 even,
180 odd, all with (F)) are unchanged. The scratch figures "24 even and 12
odd specimens beyond the dimension bound" of the round-2 route, and the same
36 specimens, were also produced by a scratch Python prototype of this
landing (literal legal words, `c_n` from the cycle space, integer
`chi_{M^n}`, sympy factorisation); they are not evidence, the Mojo census
is. Refusals: every control of the round-3 brief that is not PIP3 is
refused by `divisor_profile`, each matched on its message; at the graph
level the reducible controls and `1/012/1` are refused because their
eventual range is disconnected, and `1/0/22` because it is not primitive.

These are class counts under a recorded conditional theorem: Theorem P+ is a
written proof conditional on its imports (Barge 2015, Barge--Diamond 2008, the
identification of the two coincidence ranks), not machine-checked. A
specimen on which the divisor condition fails is one on which the recorded
theorem, if its imports hold, excludes coincidence rank 2; nothing here
certifies a coincidence rank, strong coincidence or pure discrete spectrum,
and no claim status changes.

Replay:
`cd kernel && pixi run --locked mojo run -I . -I tests tests/test_rank_two_parity.mojo`
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.integer_matrix import matmul
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.c4_geometric_f import fc3_profile
from psc.corpus import pip_corpus
from psc.fixed_point_count import fixed_point_formula
from psc.h1_census import h1_profile, legal_two_words
from psc.rank_two_parity import (
    ADMISSIBLE_PERIOD,
    CELL_DET_ODD,
    CELL_DIMENSION_BOUND,
    CELL_F,
    CELL_FAILS,
    CELL_PARITY,
    CELL_PRIOR,
    CELL_TWO_PERIODIC,
    CyclotomicTable,
    DivisorProfile,
    ERGraphMap,
    chi_power_mod2,
    cyclotomic,
    cyclotomic_exponents,
    cyclotomic_factorisation,
    cyclotomic_product,
    divisor_profile,
    divisor_search,
    er_charpoly,
    er_graph_map,
    f2_mul,
    f2_reduce,
    f2_strip_t,
    graph_map_on,
    h_polynomial,
    incidence_mod2,
    is_admissible,
    rank_two_parity_census,
)


def tribonacci() -> List[List[Int]]:
    return [[0, 1], [0, 2], [0]]


def ints(*values: Int) -> List[Int]:
    var out = List[Int]()
    for v in values:
        out.append(v)
    return out^


def exps(size: Int, *pairs: Int) raises -> List[Int]:
    """An exponent list of length `size + 1` (index `d` is the exponent of
    `Phi_d`) from pairs `d, e`."""
    if len(pairs) % 2 != 0:
        raise Error("exps: pairs")
    var out = List[Int](length=size + 1, fill=0)
    var k = 0
    while k < len(pairs):
        out[pairs[k]] = pairs[k + 1]
        k += 2
    return out^


def trimmed(e: List[Int]) -> List[Int]:
    """Exponent list without trailing zeros (index 0 is always 0)."""
    var out = e.copy()
    while len(out) > 1 and out[len(out) - 1] == 0:
        _ = out.pop()
    return out^


def raises_on_profile(sigma: List[List[Int]], expected: String) -> Bool:
    try:
        _ = divisor_profile(sigma)
        return False
    except e:
        return expected in String(e)


def raises_on_graph(sigma: List[List[Int]], expected: String) -> Bool:
    try:
        _ = er_graph_map(sigma)
        return False
    except e:
        return expected in String(e)


# ----------------------------------------------------------------------------
# Independent recomputations (this test only).


def iterate_perm(p: List[Int], m: Int) -> List[Int]:
    var out = List[Int]()
    for i in range(len(p)):
        var x = i
        for _ in range(m):
            x = p[x]
        out.append(x)
    return out^


def fixed_count(p: List[Int], m: Int) -> Int:
    var q = iterate_perm(p, m)
    var c = 0
    for i in range(len(q)):
        if q[i] == i:
            c += 1
    return c


def charpoly_from_traces(map: ERGraphMap, n: Int) raises -> List[Int]:
    """Characteristic polynomial of `(f^n)*` on `H^1(ER)` from the Lefschetz
    traces `p_k = 1 - #Fix_V(f^{nk}) + #Fix_E(f^{nk})`, `k = 1..l`, by
    Newton's identities `k e_k = sum_{i=1..k} (-1)^{i-1} e_{k-i} p_i`, with
    exact integer division. Low-to-high coefficients, monic."""
    var l = map.edge_count() - map.vertex_count() + 1
    var p = List[Int](length=l + 1, fill=0)
    for k in range(1, l + 1):
        p[k] = 1 - fixed_count(map.vertex_image, n * k) + fixed_count(map.edge_image, n * k)
    var e = List[Int](length=l + 1, fill=0)
    e[0] = 1
    for k in range(1, l + 1):
        var s = 0
        for i in range(1, k + 1):
            var term = e[k - i] * p[i]
            if (i - 1) % 2 == 0:
                s += term
            else:
                s -= term
        if s % k != 0:
            raise Error("Newton's identities: inexact division")
        e[k] = s // k
    # chi(t) = sum_k (-1)^k e_k t^{l-k}
    var out = List[Int](length=l + 1, fill=0)
    for k in range(l + 1):
        out[l - k] = e[k] if k % 2 == 0 else -e[k]
    return out^


def h_from_integer_power(sigma: List[List[Int]], n: Int) raises -> Int:
    """`chi_{M^n} mod 2` with its factors `t` removed, from the checked
    integer power `M^n` and the vendored `Mat3.charpoly`, as a bit mask."""
    var m = substitution_incidence(sigma)
    var p = m.copy()
    for _ in range(n - 1):
        p = matmul(p, m, 3)
    var chi = Mat3(p).charpoly()
    var bits = 0
    for i in range(4):
        if chi[i] % 2 != 0:
            bits |= 1 << i
    while bits != 0 and bits & 1 == 0:
        bits >>= 1
    return bits


# ----------------------------------------------------------------------------
# Hand-checked fixtures.


def test_polynomial_helpers() raises:
    # Phi_d by hand, low-to-high coefficients.
    assert_equal(cyclotomic(1), ints(-1, 1))
    assert_equal(cyclotomic(2), ints(1, 1))
    assert_equal(cyclotomic(3), ints(1, 1, 1))
    assert_equal(cyclotomic(4), ints(1, 0, 1))
    assert_equal(cyclotomic(5), ints(1, 1, 1, 1, 1))
    assert_equal(cyclotomic(6), ints(1, -1, 1))
    assert_equal(cyclotomic(7), ints(1, 1, 1, 1, 1, 1, 1))
    assert_equal(cyclotomic(8), ints(1, 0, 0, 0, 1))
    assert_equal(cyclotomic(9), ints(1, 0, 0, 1, 0, 0, 1))
    assert_equal(cyclotomic(10), ints(1, -1, 1, -1, 1))
    assert_equal(cyclotomic(12), ints(1, 0, -1, 0, 1))
    var table = CyclotomicTable(12)
    # t^6 - 1 = Phi_1 Phi_2 Phi_3 Phi_6.
    assert_equal(trimmed(cyclotomic_factorisation(ints(-1, 0, 0, 0, 0, 0, 1), table)), exps(6, 1, 1, 2, 1, 3, 1, 6, 1))
    assert_equal(cyclotomic_product(exps(6, 1, 1, 2, 1, 3, 1, 6, 1), table), ints(-1, 0, 0, 0, 0, 0, 1))
    # (t^2 - 1)^2 = Phi_1^2 Phi_2^2; 1 is the empty product.
    assert_equal(trimmed(cyclotomic_factorisation(ints(1, 0, -2, 0, 1), table)), exps(2, 1, 2, 2, 2))
    assert_equal(trimmed(cyclotomic_factorisation(ints(1), table)), ints(0))
    # A Pisot quadratic, a product with a non-cyclotomic factor, a non-monic
    # polynomial and the zero polynomial are refused.
    var refused = 0
    var bad: List[List[Int]] = [ints(1, -3, 1), ints(2, -3, 1), ints(-1, 2), List[Int]()]
    for k in range(len(bad)):
        try:
            _ = cyclotomic_factorisation(bad[k], table)
        except e:
            if "cyclotomic" in String(e):
                refused += 1
    assert_equal(refused, 4)
    # F_2 helpers: bit i is the coefficient of t^i.
    assert_equal(f2_mul(3, 3), 5)  # (t + 1)^2 = t^2 + 1
    assert_equal(f2_mul(7, 3), 9)  # (t^2 + t + 1)(t + 1) = t^3 + 1
    assert_equal(f2_reduce(ints(1, -1, 1)), 7)  # Phi_6 = Phi_3 mod 2
    assert_equal(f2_reduce(ints(-1, 1)), 3)  # Phi_1 = Phi_2 mod 2
    assert_equal(f2_reduce(ints(1, 0, -2, 0, 1)), 17)
    assert_equal(f2_strip_t(14), 7)
    assert_equal(f2_strip_t(8), 1)
    assert_equal(f2_strip_t(9), 9)


def test_divisor_search_by_hand() raises:
    var table = CyclotomicTable(12)
    # c = 1, h = t + 1: r = q_1 = 1 is a witness (the d_2 = 1 case).
    var w = divisor_search(exps(1), 3, table)
    assert_true(w.found)
    assert_equal(w.examined, 1)
    # c = 1, h = 1 (d_2 = 0): 1 != t + 1.
    w = divisor_search(exps(1), 1, table)
    assert_false(w.found)
    assert_equal(w.examined, 1)
    # c = Phi_1^2, h = (t + 1)^3: r = 1, q_1 = Phi_1^2 (Theorem P at n = 6,
    # l = 2, tr = e_2). Options of Phi_1 in order (0,0), (0,1), (0,2): third.
    w = divisor_search(exps(1, 1, 2), 15, table)
    assert_true(w.found)
    assert_equal(w.examined, 3)
    assert_equal(trimmed(w.r), ints(0))
    assert_equal(trimmed(w.q1), exps(1, 1, 2))
    # c = Phi_1, h = (t + 1)^3: 3 + a = 1 + b with a + b <= 1 is impossible.
    w = divisor_search(exps(1, 1, 1), 15, table)
    assert_false(w.found)
    assert_equal(w.examined, 3)
    # c = Phi_3, h = t^2 + t + 1: (0,0): 7 != 3; (0,1): 7 != 9; (1,0): 21 != 3.
    w = divisor_search(exps(3, 3, 1), 7, table)
    assert_false(w.found)
    assert_equal(w.examined, 3)
    # c = Phi_1 Phi_3, h = t^2 + t + 1: r = Phi_1, q_1 = Phi_3, the eighth
    # candidate (the last support index varies fastest).
    w = divisor_search(exps(3, 1, 1, 3, 1), 7, table)
    assert_true(w.found)
    assert_equal(w.examined, 8)
    assert_equal(trimmed(w.r), exps(1, 1, 1))
    assert_equal(trimmed(w.q1), exps(3, 3, 1))
    # c = Phi_1^2 Phi_2, h = (t + 1)(t^2 + t + 1): no product of Phi_1, Phi_2
    # carries t^2 + t + 1, so 6 * 3 = 18 candidates and no witness.
    w = divisor_search(exps(2, 1, 2, 2, 1), 9, table)
    assert_false(w.found)
    assert_equal(w.examined, 18)


def test_tribonacci_by_hand() raises:
    # 0 -> 01, 1 -> 02, 2 -> 0. g = (0, 0, 0), g_R = (1, 2, 0) a 3-cycle.
    # Legal words 00, 01, 02, 10, 20; ER = {e_00, e_10, e_20}, a star at 0^-.
    var sigma = tribonacci()
    var map = er_graph_map(sigma)
    assert_equal(map.edges, ints(0, 3, 6))
    assert_equal(map.vertices, ints(0, 1, 2, 3))
    assert_equal(map.edge_image, ints(1, 2, 0))  # e_00 -> e_10 -> e_20 -> e_00
    assert_equal(map.vertex_image, ints(1, 2, 0, 3))
    assert_equal(map.betti(), 0)
    assert_equal(map.order(), 3)
    assert_equal(map.edge_cycle_type(1), ints(3))
    assert_equal(map.vertex_cycle_type(1), ints(1, 3))
    assert_equal(map.edge_cycle_type(3), ints(1, 1, 1))
    for n in range(1, 7):
        assert_equal(er_charpoly(map, n), ints(1))
    var m2 = incidence_mod2(sigma)
    var legal = legal_two_words(sigma)
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        # chi_M = t^3 - t^2 - t - 1 = (t + 1)^3 mod 2: every root is 1.
        assert_equal(h_polynomial(m2, n), 15)
        assert_equal(is_admissible(sigma, legal, n), n % 3 == 0)
    var p = divisor_profile(sigma)
    assert_equal(p.d2, 3)
    assert_equal(p.h1_dimension, 3)
    assert_false(p.dimension_bound_holds())
    assert_true(p.fails())
    assert_equal(p.first_failure, 3)
    assert_equal(p.admissible_count(), 14)
    assert_equal(p.failure_count(), 14)


def test_productive_control_01_12_021() raises:
    # 0 -> 01, 1 -> 12, 2 -> 021: g = (0, 1, 0), g_R = (1, 2, 1).
    # ER = K_{2,2} on 1^+, 2^+ | 0^-, 1^-: e_10, e_11, e_20, e_21; f swaps
    # 1^+ and 2^+ and fixes 0^-, 1^-, so it reverses the one cycle.
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var map = er_graph_map(sigma)
    assert_equal(map.edges, ints(3, 4, 6, 7))
    assert_equal(map.vertices, ints(1, 2, 3, 4))
    assert_equal(map.edge_image, ints(2, 3, 0, 1))
    assert_equal(map.vertex_image, ints(1, 0, 2, 3))
    assert_equal(map.betti(), 1)
    assert_equal(map.order(), 2)
    assert_equal(er_charpoly(map, 1), ints(1, 1))  # t + 1
    assert_equal(er_charpoly(map, 2), ints(-1, 1))  # t - 1
    assert_equal(trimmed(cyclotomic_exponents(map, 1)), exps(2, 2, 1))
    assert_equal(trimmed(cyclotomic_exponents(map, 2)), exps(1, 1, 1))
    # chi_M = t^3 - 3t^2 + 2t - 1 = t^3 + t^2 + 1 mod 2, irreducible, roots
    # of order 7 in F_8. Squaring permutes them (Frobenius): h_n = 13 for
    # n = 1, 2, 4 mod 7; their inverses are the roots of t^3 + t + 1: h_n = 11
    # for n = 3, 5, 6 mod 7; h_n = (t + 1)^3 = 15 for 7 | n.
    var m2 = incidence_mod2(sigma)
    var legal = legal_two_words(sigma)
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        var r = n % 7
        var expected = 15 if r == 0 else (13 if r == 1 or r == 2 or r == 4 else 11)
        assert_equal(h_polynomial(m2, n), expected)
        assert_equal(is_admissible(sigma, legal, n), n % 2 == 0)
    var p = divisor_profile(sigma)
    assert_equal(p.d2, 3)
    assert_equal(p.h1_dimension, 4)
    assert_true(p.parity_clause())
    assert_false(p.dimension_bound_holds())
    assert_equal(p.first_failure, 2)
    assert_equal(p.admissible_count(), 21)
    assert_equal(p.failure_count(), 21)


def test_even_beyond_the_bound_11_012_01() raises:
    # Corpus label 7 17 4: 0 -> 11, 1 -> 012, 2 -> 01; det 2, tr 1, e_2 -3,
    # chi_M = t (t^2 + t + 1) mod 2, d_2 = 2. g = (1, 0, 0), g_R = (1, 2, 1).
    # ER = K_{2,2} on 1^+, 2^+ | 0^-, 1^-; f swaps both sides, so it keeps
    # the orientation of the cycle: c_n = t - 1 for every n.
    var sigma: List[List[Int]] = [[1, 1], [0, 1, 2], [0, 1]]
    var map = er_graph_map(sigma)
    assert_equal(map.edges, ints(3, 4, 6, 7))
    assert_equal(map.edge_image, ints(3, 2, 1, 0))  # e_10 <-> e_21, e_11 <-> e_20
    assert_equal(map.vertex_image, ints(1, 0, 3, 2))
    for n in range(1, 7):
        assert_equal(er_charpoly(map, n), ints(-1, 1))
    var m2 = incidence_mod2(sigma)
    var legal = legal_two_words(sigma)
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        # roots of t^2 + t + 1 have order 3: h_n = 7 for 3 !| n, (t + 1)^2 = 5 else.
        assert_equal(h_polynomial(m2, n), 5 if n % 3 == 0 else 7)
        assert_equal(is_admissible(sigma, legal, n), n % 2 == 0)
    var p = divisor_profile(sigma)
    assert_equal(p.d2, 2)
    assert_equal(p.h1_dimension, 4)
    assert_true(p.dimension_bound_holds())
    # n = 2: (t^2 + t + 1) r = (t + 1) q_1 with deg r + deg q_1 <= 1 is
    # impossible; n = 6: r = 1, q_1 = Phi_1.
    assert_equal(p.first_failure, 2)
    assert_false(p.satisfied[2])
    assert_false(p.satisfied[4])
    assert_true(p.satisfied[6])
    assert_equal(p.admissible_count(), 21)
    assert_equal(p.failure_count(), 14)
    assert_false(fc3_profile(sigma).rank_two_hypotheses_hold())


def test_odd_beyond_theorem_p_12_012_211() raises:
    # Corpus label 8 17 34: 0 -> 12, 1 -> 012, 2 -> 211; det 1, tr 2, e_2 -2,
    # chi_M = t^3 + 1 = (t + 1)(t^2 + t + 1) mod 2: tr = e_2 mod 2, so
    # Theorem P is silent; dim H^1 = 5. g = (1, 0, 2), g_R = (2, 2, 1).
    # ER = K_{2,3} on 1^+, 2^+ | 0^-, 1^-, 2^-: three 2-cycles of edges, vertex
    # cycles 2, 2, 1: c_1 = (t - 1)(t^2 - 1)^3 / ((t^2 - 1)^2 (t - 1)) = t^2 - 1.
    var sigma: List[List[Int]] = [[1, 2], [0, 1, 2], [2, 1, 1]]
    var map = er_graph_map(sigma)
    assert_equal(map.edges, ints(3, 4, 5, 6, 7, 8))
    assert_equal(map.betti(), 2)
    assert_equal(map.edge_cycle_type(1), ints(2, 2, 2))
    assert_equal(map.vertex_cycle_type(1), ints(1, 2, 2))
    assert_equal(er_charpoly(map, 1), ints(-1, 0, 1))
    assert_equal(er_charpoly(map, 2), ints(1, -2, 1))
    assert_equal(trimmed(cyclotomic_exponents(map, 1)), exps(2, 1, 1, 2, 1))
    var m2 = incidence_mod2(sigma)
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        assert_equal(h_polynomial(m2, n), 15 if n % 3 == 0 else 9)
    var p = divisor_profile(sigma)
    assert_equal(p.d2, 3)
    assert_equal(p.h1_dimension, 5)
    assert_false(p.parity_clause())
    assert_true(p.dimension_bound_holds())
    # n = 2: h = (t + 1)(t^2 + t + 1), c_2 = Phi_1^2: no witness. n = 6:
    # h = (t + 1)^3, r = 1, q_1 = Phi_1^2 (Theorem P passes).
    assert_equal(p.first_failure, 2)
    assert_true(p.satisfied[6])
    assert_equal(p.failure_count(), 14)
    assert_false(fc3_profile(sigma).rank_two_hypotheses_hold())


def test_satisfied_1_212_021() raises:
    # The fixture of the rank-two note (d_2 = 2, dim H^1 = 5, (F), meets no
    # hypothesis). g = (1, 2, 0) a 3-cycle, g_R = (1, 2, 1). ER = K_{2,3},
    # f = (2-cycle) x (3-cycle): one 6-cycle of edges, vertex cycles 2, 3.
    # c_1 = (t - 1)(t^6 - 1) / ((t^2 - 1)(t^3 - 1)) = Phi_6.
    var sigma: List[List[Int]] = [[1], [2, 1, 2], [0, 2, 1]]
    var map = er_graph_map(sigma)
    assert_equal(map.order(), 6)
    assert_equal(map.edge_cycle_type(1), ints(6))
    assert_equal(map.vertex_cycle_type(1), ints(2, 3))
    assert_equal(er_charpoly(map, 1), ints(1, -1, 1))  # Phi_6
    assert_equal(er_charpoly(map, 2), ints(1, 1, 1))  # Phi_3
    assert_equal(er_charpoly(map, 3), ints(1, 2, 1))  # Phi_2^2
    assert_equal(er_charpoly(map, 6), ints(1, -2, 1))  # Phi_1^2
    var legal = legal_two_words(sigma)
    var m2 = incidence_mod2(sigma)
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        assert_equal(is_admissible(sigma, legal, n), n % 6 == 0)
        assert_equal(h_polynomial(m2, n), 5)  # chi_M = t (t + 1)^2 mod 2
    var p = divisor_profile(sigma)
    assert_equal(p.d2, 2)
    assert_equal(p.h1_dimension, 5)
    assert_false(p.fails())
    assert_equal(p.admissible_count(), 7)


def test_other_productive_controls() raises:
    # 1/02/002: g = (1, 0, 0), g_R = (1, 2, 2); ER = {e_20, e_21}, a tree;
    # chi_M = t^3 - t^2 - t - 1 (Tribonacci's), (t + 1)^3 mod 2.
    var a: List[List[Int]] = [[1], [0, 2], [0, 0, 2]]
    var ma = er_graph_map(a)
    assert_equal(ma.edges, ints(6, 7))
    assert_equal(ma.betti(), 0)
    var pa = divisor_profile(a)
    assert_equal(pa.h1_dimension, 3)
    assert_equal(pa.first_failure, 2)
    assert_equal(pa.failure_count(), pa.admissible_count())
    assert_equal(pa.admissible_count(), 21)
    # 01/20/200: g = (0, 2, 2), g_R = (1, 0, 0); ER = K_{2,2} on 0^+, 1^+ |
    # 0^-, 2^-; f swaps 0^+, 1^+: c_1 = t + 1. chi_M = t^3 - 2t^2 - 1,
    # (t + 1)(t^2 + t + 1) mod 2.
    var b: List[List[Int]] = [[0, 1], [2, 0], [2, 0, 0]]
    var mb = er_graph_map(b)
    assert_equal(mb.edges, ints(0, 2, 3, 5))
    assert_equal(er_charpoly(mb, 1), ints(1, 1))
    var pb = divisor_profile(b)
    assert_equal(pb.d2, 3)
    assert_equal(pb.h1_dimension, 4)
    assert_false(pb.parity_clause())
    assert_equal(pb.first_failure, 2)
    assert_equal(pb.failure_count(), 21)


def test_graph_level_controls() raises:
    # Thue-Morse 01/10: ER = K_{2,2}, f swaps 0^+ and 1^+ and fixes 0^-, 1^-,
    # so it reverses the one cycle: c_1 = t + 1, c_2 = t - 1. Graph level
    # only: Thue-Morse is outside PIP3 and outside Lemma 7.
    var tm: List[List[Int]] = [[0, 1], [1, 0]]
    var t = er_graph_map(tm)
    assert_equal(t.edges, ints(0, 1, 2, 3))
    assert_equal(er_charpoly(t, 1), ints(1, 1))
    assert_equal(er_charpoly(t, 2), ints(-1, 1))
    # 012/120/201 (singular): all nine words legal, g = id, g_R = (2, 0, 1):
    # three 3-cycles of edges, vertex cycles 3, 1, 1, 1: c_1 = Phi_3^2.
    var c3: List[List[Int]] = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    var m3 = er_graph_map(c3)
    assert_equal(m3.betti(), 4)
    assert_equal(er_charpoly(m3, 1), ints(1, 2, 3, 2, 1))
    assert_equal(er_charpoly(m3, 3), ints(1, -4, 6, -4, 1))
    # 01/2/120 (singular): g = (0, 2, 1), g_R = (1, 2, 0): edges one 3-cycle
    # and one 6-cycle, vertex cycles 3 | 1, 2: c_1 = (t^6 - 1)/(t^2 - 1).
    var s3: List[List[Int]] = [[0, 1], [2], [1, 2, 0]]
    var n3 = er_graph_map(s3)
    assert_equal(er_charpoly(n3, 1), ints(1, 0, 1, 0, 1))
    assert_equal(er_charpoly(n3, 2), ints(1, 2, 3, 2, 1))
    assert_equal(er_charpoly(n3, 3), ints(1, 0, -2, 0, 1))
    assert_equal(er_charpoly(n3, 6), ints(1, -4, 6, -4, 1))
    # Disconnected eventual ranges (G_0 != 0, Lemma 7(2) fails): refused.
    var disconnected = "eventual range is disconnected"
    assert_true(raises_on_graph([[1], [0, 1, 2], [1]], disconnected))  # 1/012/1: e_10, e_21
    assert_true(raises_on_graph([[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]], disconnected))  # C-D1
    assert_true(raises_on_graph([[0, 1, 0], [1, 2, 2, 2], [2, 0, 1, 2]], disconnected))  # C-D2
    assert_true(raises_on_graph([[1], [0, 1, 2], [1, 0, 1]], disconnected))  # 1/012/101
    assert_true(raises_on_graph([[1, 0], [1, 0, 2], [2, 1, 1]], disconnected))  # 10/102/211
    assert_true(raises_on_graph([[0, 1], [2, 0, 1], [1, 1, 2]], disconnected))  # 01/201/112
    assert_true(raises_on_graph([[1], [0, 1, 0]], disconnected))  # two letters
    # Not primitive.
    assert_true(raises_on_graph([[1], [0], [2, 2]], "not primitive"))
    # Malformed input.
    assert_true(raises_on_graph([[0, 3], [0, 2], [0]], "outside the alphabet"))
    assert_true(raises_on_graph([[0, 1], List[Int](), [0]], "empty"))
    # A mask that f does not permute: the legal words of Tribonacci
    # (f(e_01) = f(e_02) = e_10), and a mask that f leaves (f(e_01) = e_10).
    var trib = tribonacci()
    var refused_injective = False
    try:
        _ = graph_map_on(trib, legal_two_words(trib))
    except e:
        refused_injective = "not injective" in String(e)
    assert_true(refused_injective)
    var single = List[Bool](length=9, fill=False)
    single[1] = True
    var refused_outside = False
    try:
        _ = graph_map_on(trib, single)
    except e:
        refused_outside = "outside the edge set" in String(e)
    assert_true(refused_outside)
    # A power below one.
    var refused_power = False
    try:
        _ = er_charpoly(er_graph_map(trib), 0)
    except e:
        refused_power = "power" in String(e)
    assert_true(refused_power)


def test_profile_refusals() raises:
    # Every control of the round-3 brief that is not PIP3 is refused.
    var reducible = "reducible"
    assert_true(raises_on_profile([[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]], reducible))  # C-D1
    assert_true(raises_on_profile([[0, 1, 0], [1, 2, 2, 2], [2, 0, 1, 2]], reducible))  # C-D2
    assert_true(raises_on_profile([[1], [0, 1, 2], [1, 0, 1]], reducible))  # 1/012/101
    assert_true(raises_on_profile([[1, 0], [1, 0, 2], [2, 1, 1]], reducible))  # 10/102/211
    assert_true(raises_on_profile([[0, 1], [2, 0, 1], [1, 1, 2]], reducible))  # 01/201/112
    assert_true(raises_on_profile([[0, 1, 2], [1, 2, 0], [2, 0, 1]], reducible))  # singular
    assert_true(raises_on_profile([[0, 1], [2], [1, 2, 0]], reducible))  # singular
    assert_true(raises_on_profile([[1], [0, 1, 2], [1]], reducible))  # singular
    assert_true(raises_on_profile([[0, 1], [1, 0]], "three letters"))  # Thue-Morse
    assert_true(raises_on_profile([[1], [0], [2, 2]], "not primitive"))  # 1/0/22
    assert_true(raises_on_profile([[1], [2], [0, 0, 1]], "not a Pisot"))  # chi = t^3 - t - 2
    assert_true(raises_on_profile([[0, 3], [0, 2], [0]], "outside the alphabet"))
    assert_true(raises_on_profile([[0, 1], List[Int](), [0]], "empty"))


# ----------------------------------------------------------------------------
# The corpus.


def test_corpus_cross_checks() raises -> Int:
    """Per specimen, independently of the census: c_n against Newton's
    identities on the Lefschetz traces (n = 1..6), against the cyclotomic
    factorisation, and of degree dim H^1 - 3; h_n against the integer power
    (n = 1..8); admissibility against the seams of Theorem FP (n = 1..6); the
    data at n and n + 42 (n = 1..42); and the consequences of Theorem P+
    named in the module docstring. Returns the number of specimens checked."""
    var corpus = pip_corpus()
    var table = CyclotomicTable(32)
    var checked = 0
    var odd_n6 = 0
    for s in range(len(corpus)):
        var sigma = corpus[s].sigma.copy()
        var map = er_graph_map(sigma)
        assert_equal(map.betti(), h1_profile(sigma).dimension - 3)
        assert_equal(6 % map.order(), 0)
        var legal = legal_two_words(sigma)
        var m2 = incidence_mod2(sigma)
        for n in range(1, 7):
            var c = er_charpoly(map, n)
            assert_equal(c, charpoly_from_traces(map, n))
            assert_equal(trimmed(cyclotomic_factorisation(c, table)), trimmed(cyclotomic_exponents(map, n)))
            assert_equal(len(c) - 1, map.betti())
            var seams = fixed_point_formula(sigma, n).seams
            assert_equal(is_admissible(sigma, legal, n), seams > 0)
            assert_equal(map.fixed_edges(n), seams)
        for n in range(1, 9):
            assert_equal(h_polynomial(m2, n), h_from_integer_power(sigma, n))
        for n in range(1, ADMISSIBLE_PERIOD + 1):
            var later = n + ADMISSIBLE_PERIOD
            assert_equal(is_admissible(sigma, legal, n), is_admissible(sigma, legal, later))
            assert_equal(er_charpoly(map, n), er_charpoly(map, later))
            assert_equal(h_polynomial(m2, n), h_polynomial(m2, later))
            assert_equal(chi_power_mod2(m2, n), chi_power_mod2(m2, later))
        var p = divisor_profile(sigma)
        var f = fc3_profile(sigma)
        assert_equal(p.d2, f.d2())
        assert_equal(p.h1_dimension, f.h1_dimension)
        assert_equal(p.parity_clause(), f.parity_clause())
        assert_equal(p.dimension_bound_holds(), not f.dimension_clause())
        # n = 6 is admissible (Lemma 7(1)).
        assert_true(p.admissible[6])
        # Degree count: the dimension bound fails only if every admissible n fails.
        if not p.dimension_bound_holds():
            assert_equal(p.failure_count(), p.admissible_count())
        # d_2 = 1: h_n = t + 1, and r = q_1 = 1 is a witness at every n.
        if p.d2 == 1:
            assert_false(p.fails())
        # Odd determinant, n = 6: c_6 = (t - 1)^l, and the condition fails
        # exactly when dim H^1 <= 4 or tr M != e_2(M) mod 2 (Theorem P).
        if p.d2 == 3:
            assert_equal(not p.satisfied[6], f.arithmetic_clause())
            odd_n6 += 1
        checked += 1
    assert_equal(odd_n6, 2628)
    return checked


def test_census() raises:
    var census = rank_two_parity_census(pip_corpus())
    assert_equal(census.total, 4554)
    var fails = CELL_FAILS
    var odd = CELL_DET_ODD
    var bound = CELL_DIMENSION_BOUND
    var prior = CELL_PRIOR
    var parity = CELL_PARITY
    var open_mask = CELL_F | CELL_TWO_PERIODIC
    # The divisor condition fails (Theorem P+ excludes coincidence rank 2,
    # conditionally): by determinant parity.
    assert_equal(census.count_where(fails | odd, fails | odd), 2364)
    assert_equal(census.count_where(fails | odd, fails), 930)
    # The dimension bound fails on 3,042 = 2,136 odd + 906 even (pinned in
    # test_c4_geometric_f); the divisor condition fails on all of them.
    assert_equal(census.count_where(bound | odd, odd), 2136)
    assert_equal(census.count_where(bound | odd, 0), 906)
    assert_equal(census.count_where(fails | bound, bound), 1260)
    # Beyond the dimension bound: 228 odd (216 in the parity class of
    # Theorem P, 12 beyond it) and 24 even.
    assert_equal(census.count_where(fails | bound | odd, fails | bound | odd), 228)
    assert_equal(census.count_where(fails | bound | odd | parity, fails | bound | odd | parity), 216)
    assert_equal(census.count_where(fails | bound | odd, fails | bound), 24)
    # Beyond the prior hypotheses (FC3Profile.rank_two_hypotheses_hold: odd
    # and (dim H^1 <= 4 or tr != e_2); even and dim H^1 = 3): 24 even + 12 odd.
    assert_equal(census.count_where(fails | prior | odd, fails | odd), 12)
    assert_equal(census.count_where(fails | prior | odd, fails), 24)
    assert_equal(census.count_where(prior, prior), 3714)
    assert_equal(len(census.beyond), 36)
    # Every one of them first fails at n = 2, with d_2 = 2, dim H^1 = 4
    # (even) or d_2 = 3, dim H^1 = 5 (odd).
    assert_equal(census.beyond_classes.count(10 * 2 + 4), 24)
    assert_equal(census.beyond_classes.count(10 * 3 + 5), 12)
    assert_equal(census.beyond_classes.total(), 36)
    assert_equal(census.beyond_first_failure.count(2), 36)
    assert_equal(census.beyond_first_failure.total(), 36)
    # (F) with two periodic letters on both sides: the open classes of
    # §15.3 item 1 (132 even, 180 odd) and what the divisor condition removes.
    assert_equal(census.count_where(open_mask | prior | odd, open_mask), 132)
    assert_equal(census.count_where(open_mask | prior | odd, open_mask | odd), 180)
    assert_equal(census.count_where(open_mask | prior | odd | fails, open_mask | fails), 0)
    assert_equal(census.count_where(open_mask | prior | odd | fails, open_mask | odd | fails), 0)
    # The beyond-prior failures by (F) and periodic letters: none has (F),
    # all have two periodic letters on both sides.
    assert_equal(census.count_where(fails | prior | CELL_F, fails | CELL_F), 0)
    assert_equal(census.count_where(fails | prior | CELL_TWO_PERIODIC, fails | CELL_TWO_PERIODIC), 36)
    # On the whole (F) class the divisor condition fails only where the prior
    # hypotheses already hold.
    assert_equal(census.count_where(fails | CELL_F, fails | CELL_F), 144 + 684 + 42 + 36 + 36 + 408 + 48 + 72)
    assert_equal(census.count_where(fails | prior | CELL_F, fails | prior | CELL_F), 1470)
    # The 36 specimens, by corpus label (image indices into image_words).
    var labels = String("")
    for k in range(len(census.beyond_labels)):
        labels += census.beyond_labels[k] + "|"
    assert_equal(
        labels,
        "7 17 4|7 26 31|7 33 6|7 34 23|8 11 27|8 17 7|8 17 34|8 37 27|10 11 19|10 29 19|10 33 7|"
        + "10 33 26|11 5 19|11 9 27|11 23 37|11 31 29|13 27 3|14 3 33|16 33 6|17 11 36|19 24 7|"
        + "20 9 27|21 19 3|23 3 6|23 5 3|23 5 30|23 13 6|24 17 4|27 16 7|30 3 17|31 3 4|31 9 3|"
        + "31 9 14|31 21 4|33 11 20|36 5 19|",
    )
    # The whole census table, keyed by the CELL_* bits (1 fails, 2 det odd,
    # 4 (F), 8 two periodic letters on both sides, 16 dimension bound holds,
    # 32 prior hypotheses hold, 64 tr != e_2 mod 2).
    assert_equal(
        census.cells.line("cells"),
        "cells 24:120 25:24 26:84 27:12 28:12 30:180 33:378 35:156 37:144 39:684 43:132 45:42 47:36"
        + " 88:288 92:120 97:306 99:444 101:36 103:408 107:228 111:48 112:444 116:12 123:144 127:72",
    )
    # Least failing admissible n, keyed 64 * (det odd) + n.
    assert_equal(census.first_failure.line("first"), "first 1:450 2:276 3:204 65:1044 66:888 67:408 70:24")
    # Specimens on which n is admissible (n = 6, 12, ... on all: Lemma 7(1)).
    var admissible_line = String("admissible")
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        var expected = 4554 if n % 6 == 0 else (2934 if n % 3 == 0 else (3174 if n % 2 == 0 else 1734))
        assert_equal(census.admissible_at.count(n), expected)
        admissible_line += " " + String(n) + ":" + String(expected)
    assert_equal(census.admissible_at.line("admissible"), admissible_line)
    # Failures at each n for even determinant depend on n mod 6 only.
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        var r = n % 6
        var expected = 906 if r == 0 else (654 if r == 3 else (726 if r % 2 == 0 else 450))
        assert_equal(census.failures_at.count(n), expected)
    assert_equal(census.failures_at.count(64 + 6), 2352)  # odd, n = 6: Theorem P's class
    assert_equal(census.failures_at.count(64 + 42), 2136)  # odd, n = 42: dim H^1 <= 4
    assert_equal(census.examined, 176220)
    print(census.summary())


def main() raises:
    test_polynomial_helpers()
    test_divisor_search_by_hand()
    test_tribonacci_by_hand()
    test_productive_control_01_12_021()
    test_even_beyond_the_bound_11_012_01()
    test_odd_beyond_theorem_p_12_012_211()
    test_satisfied_1_212_021()
    test_other_productive_controls()
    test_graph_level_controls()
    test_profile_refusals()
    var checked = test_corpus_cross_checks()
    assert_equal(checked, 4554)
    test_census()
    require_contract("Divisor condition of Theorem P+ (psc.rank_two_parity; docs/c4-rank-two-wall-2026-11-16.md, Lemma S+ and Theorem P+), exact checked integer and F_2[t] arithmetic: f = g_K restricted to the eventual range ER of psc.h1_census as a graph map (edges e_ab -> e_{g_R(a) g(b)}, vertices a^+ -> g_R(a)^+, b^- -> g(b)^-), refused when ER is disconnected or f is not a permutation; c_n = charpoly((f^n)* | H^1(ER; Q)) = (t - 1) prod_{edge cycles of f^n} (t^L - 1) / prod_{vertex cycles} (t^L - 1) (Proposition C, proved in the module docstring), equal on every corpus specimen for n = 1..6 to Newton's identities on the Lefschetz traces 1 - #Fix_V(f^m) + #Fix_E(f^m), of degree dim H^1 - 3, and factored into cyclotomic polynomials both from the cycle type and by trial division, which agree; h_n = chi_{M^n} mod 2 without its factors t, equal for n = 1..8 to Mat3.charpoly of the checked integer power M^n reduced mod 2; n admissible iff a legal word ba has g_R^n(b) = b and g^n(a) = a, equal to 'the Theorem FP seam count is positive' for n = 1..6; admissibility, c_n and h_n equal at n and n + 42 for n = 1..42 on every specimen (Lemma N: they depend on n mod 42, so n = 1..42 decides 'for every admissible n'); the search over every pair of sub-multisets (a_d), (b_d) with a_d + b_d <= e_d of c_n = prod Phi_d^{e_d} for h_n rbar = (t + 1) q_1bar. Hand-checked: Phi_1..Phi_12; the search on seven instances; Tribonacci 01/02/0 (ER a star, c_n = 1, admissible n = 3k, h_n = (t + 1)^3, fails first at n = 3), 01/12/021 (c_1 = t + 1, c_2 = t - 1, h_n by the Frobenius argument, fails at every even n), 11/012/01 (c_n = t - 1, h_n = t^2 + t + 1 for 3 !| n, fails at n = 2, 4 mod 6, holds at 6 | n), 12/012/211 (c_1 = t^2 - 1, h_n = t^3 + 1 for 3 !| n, fails at n = 2), 1/212/021 (c_1 = Phi_6, c_2 = Phi_3, c_3 = Phi_2^2, c_6 = Phi_1^2, admissible n = 6k, holds), 1/02/002 and 01/20/200 (fail at n = 2); graph level: Thue-Morse c_1 = t + 1, 012/120/201 c_1 = Phi_3^2, 01/2/120 c_1 = t^4 + t^2 + 1. Refusals: C-D1, C-D2, 1/012/101, 10/102/211, 01/201/112 and 1/012/1 have a disconnected ER; 1/0/22 is not primitive; divisor_profile refuses every non-PIP3 control of the round-3 brief (reducible or singular: reducible; Thue-Morse: three letters; 1/0/22: not primitive; 1/2/001: not Pisot) and malformed input, each matched on its message. On every corpus specimen: the dimension bound fails only where every admissible n fails, d_2 = 1 never fails, and for odd determinant the condition fails at n = 6 exactly on the class of Theorem P (dim H^1 <= 4 or tr != e_2 mod 2). Census over the 4,554 specimens of pip_corpus(): the condition fails on 2,364 odd and 930 even specimens; beyond the dimension bound on 228 odd (216 with tr != e_2, 12 beyond Theorem P) and 24 even; beyond the hypotheses of the recorded theorems without the divisor condition (odd: dim H^1 <= 4 or tr != e_2; even: dim H^1 = 3) on 12 odd (d_2 = 3, dim H^1 = 5) and 24 even (d_2 = 2, dim H^1 = 4) specimens, all first failing at n = 2, none with (F), all with two periodic letters on both sides (labels pinned); on the (F) class it fails on 1,470 specimens, all already in those hypotheses; the open classes of section 15.3 item 1 of the closure-attempt note (132 even, 180 odd) are unchanged: the condition fails on none of them; the full cell table, the least failing n and the admissible n are pinned. These are class counts under a recorded conditional theorem: Theorem P+ is a written proof conditional on its imports (Barge 2015, Barge-Diamond 2008, the identification of the two coincidence ranks), not machine-checked; a failure is not a certificate of a coincidence rank, and no coincidence rank, strong coincidence or spectrum is certified, and no claim status changes")
