"""Proposition Q on every strict-carrier class with images of length at most
three: the Parikh span is invariant and its quotient spectrum is neutral; the
rank-three strict system of 01/2/120 (lattice index 1, every first-letter
pair); refusals, including every reachable non-invariance branch."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_cut_attractor import StrictClosure, intertwines, parikh_matrix, strict_closure
from psc.c4_quotient_spectrum import is_neutral, parikh_span_basis, quotient_charpoly
from psc.words import Pair


struct Carrier(Copyable, Movable):
    var sigma: List[List[Int]]
    var u: List[Int]
    var v: List[Int]
    var size: Int
    var rank: Int
    var poly: List[Int]

    def __init__(out self, sigma: List[List[Int]], u: List[Int], v: List[Int], size: Int, rank: Int, poly: List[Int]):
        self.sigma = sigma.copy()
        self.u = u.copy()
        self.v = v.copy()
        self.size = size
        self.rank = rank
        self.poly = poly.copy()


def carriers() -> List[Carrier]:
    # one strict system per relabelling x reversal class of strict carriers with
    # images of length <= 3 (28 classes): images, a state, ordered size, rank P,
    # quotient polynomial (leading first)
    var out = List[Carrier]()
    out.append(Carrier([[0, 1], [1, 2], [0, 1]], [0, 1, 1, 2], [1, 2, 0, 1], 2, 1, [1, 0, 0]))  # 01/12/01
    out.append(Carrier([[0, 1], [1, 2, 0], [1, 1, 2]], [0, 1, 1, 2], [1, 1, 2, 0], 4, 2, [1, -1]))  # 01/120/112
    out.append(Carrier([[0, 1], [1, 2, 0], [1, 2]], [0, 1, 1, 2], [1, 2, 0, 1], 3, 2, [1, -1]))  # 01/120/12
    out.append(Carrier([[0, 1], [2], [1, 2, 0]], [0, 0, 1, 2], [2, 0, 0, 1], 20, 3, [1]))  # 01/2/120
    out.append(Carrier([[0, 1], [2], [2, 0, 1]], [0, 1, 2], [2, 0, 1], 2, 1, [1, 0, 0]))  # 01/2/201
    out.append(Carrier([[0, 1], [2, 0], [1, 0]], [0, 1], [1, 0], 6, 2, [1, 0]))  # 01/20/10
    out.append(Carrier([[0, 1], [2, 0], [1, 2]], [0, 1, 2], [1, 2, 0], 2, 1, [1, 0, -1]))  # 01/20/12
    out.append(Carrier([[0, 1], [2, 0], [2, 0, 2]], [0, 1, 2], [2, 0, 1], 3, 2, [1, -1]))  # 01/20/202
    out.append(Carrier([[0, 1], [2, 0, 1], [1, 1, 2]], [0, 1, 1, 1, 2], [2, 0, 1, 1, 1], 4, 2, [1, -1]))  # 01/201/112
    out.append(Carrier([[0, 1, 0], [1, 0, 2], [1]], [0, 1], [1, 0], 4, 2, [1, -1]))  # 010/102/1
    out.append(Carrier([[0, 1, 0], [1, 0, 2], [1, 0, 2]], [0, 1], [1, 0], 2, 2, [1, -1]))  # 010/102/102
    out.append(Carrier([[0, 1, 0], [1, 0, 2], [2, 0, 1]], [0, 1], [1, 0], 4, 2, [1, -1]))  # 010/102/201
    out.append(Carrier([[0, 1, 0], [1, 2, 1], [0, 1, 0]], [0, 1, 0, 1, 2, 1], [1, 2, 1, 0, 1, 0], 1, 1, [1, -1, 0]))  # 010/121/010
    out.append(Carrier([[0, 1, 0], [1, 2, 2], [0, 1]], [0, 1], [1, 0], 4, 2, [1, -1]))  # 010/122/01
    out.append(Carrier([[0, 1, 0], [1, 2, 2], [2, 0, 1]], [0, 1], [1, 0], 9, 2, [1, -1]))  # 010/122/201
    out.append(Carrier([[0, 1, 0], [2], [1, 0, 2]], [0, 1], [1, 0], 3, 2, [1, -1]))  # 010/2/102
    out.append(Carrier([[0, 1, 2], [1, 2, 0], [2, 0, 1]], [0, 1, 2], [1, 2, 0], 3, 1, [1, 0, 0]))  # 012/120/201
    out.append(Carrier([[0, 1, 2], [2, 0, 1], [1, 2, 0]], [0, 1, 2], [1, 2, 0], 6, 1, [1, 0, 0]))  # 012/201/120
    out.append(Carrier([[1], [0, 1, 2], [1]], [0, 1], [1, 0], 4, 2, [1, 1]))  # 1/012/1
    out.append(Carrier([[1], [0, 1, 2], [1, 0, 1]], [0, 1], [1, 0], 6, 2, [1, 1]))  # 1/012/101
    out.append(Carrier([[1], [0, 1, 2], [1, 2, 1]], [0, 1], [1, 0], 6, 2, [1, 1]))  # 1/012/121
    out.append(Carrier([[1], [0, 2], [0, 2, 1]], [0, 2, 1], [1, 0, 2], 2, 1, [1, 1, 0]))  # 1/02/021
    out.append(Carrier([[1], [0, 2, 0], [0, 2, 0]], [0, 2, 0, 1], [1, 0, 2, 0], 2, 1, [1, 1, 0]))  # 1/020/020
    out.append(Carrier([[1, 0, 1], [0, 1, 2], [1, 0, 1]], [0, 1], [1, 0], 4, 2, [1, 1]))  # 101/012/101
    out.append(Carrier([[1, 0, 1], [0, 2], [0, 2, 1]], [0, 1], [1, 0], 6, 2, [1, 1]))  # 101/02/021
    out.append(Carrier([[1, 0, 1], [0, 2, 0], [0, 2, 0]], [0, 2, 0, 1, 0, 1], [1, 0, 1, 0, 2, 0], 2, 1, [1, 1, 0]))  # 101/020/020
    out.append(Carrier([[1, 0, 2], [0, 2], [1, 0]], [0, 2, 1], [1, 0, 2], 6, 2, [1, 1]))  # 102/02/10
    out.append(Carrier([[1, 0, 2], [2, 1, 0], [0, 2, 1]], [0, 2, 1], [1, 0, 2], 3, 1, [1, 0, 0]))  # 102/210/021
    return out^


def _det3(P: List[List[Int]], a: Int, b: Int, c: Int) -> Int:
    return (P[0][a] * (P[1][b] * P[2][c] - P[2][b] * P[1][c])
            - P[0][b] * (P[1][a] * P[2][c] - P[2][a] * P[1][c])
            + P[0][c] * (P[1][a] * P[2][b] - P[2][a] * P[1][b]))


def _gcd(a: Int, b: Int) -> Int:
    var x = a if a >= 0 else -a
    var y = b if b >= 0 else -b
    while y != 0:
        var t = x % y
        x = y
        y = t
    return x


def _minor_gcd(P: List[List[Int]]) -> Int:
    """gcd of the 3 x 3 minors of a 3 x n integer matrix: the index of its
    column lattice in Z^3 (0 when the rank is below 3)."""
    var g = 0
    var n = len(P[0])
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                g = _gcd(g, _det3(P, a, b, c))
    return g


def _bare(states: List[Pair]) -> StrictClosure:
    """A hand-made state set with no child rows: not child-closed."""
    var rows = List[List[Int]]()
    for _ in range(len(states)):
        rows.append(List[Int]())
    return StrictClosure(states, rows, rows)


def _refuses(sigma: List[List[Int]], states: List[Pair], branch: String) -> Bool:
    """Whether `quotient_charpoly` refuses with the message of `branch`."""
    try:
        _ = quotient_charpoly(sigma, _bare(states))
    except e:
        return branch in String(e)
    return False


def test_proposition_q_on_all_carrier_classes() raises:
    var cs = carriers()
    assert_equal(len(cs), 28)
    var rank_counts: List[Int] = [0, 0, 0, 0]
    for k in range(len(cs)):
        var c = strict_closure(cs[k].sigma, Pair(cs[k].u, cs[k].v))
        assert_equal(c.size(), cs[k].size)
        assert_true(intertwines(cs[k].sigma, c))
        var basis = parikh_span_basis(c)
        assert_equal(len(basis), cs[k].rank)
        var poly = quotient_charpoly(cs[k].sigma, c)
        assert_equal(poly, cs[k].poly)
        assert_true(is_neutral(poly))
        rank_counts[len(basis)] += 1
    assert_equal(rank_counts, [0, 10, 17, 1])


def test_rank_three_strict_system_of_a_singular_incidence() raises:
    # 01/2/120: chi_M = x^2 (x - 2), det 0; a 20-state strict system with rank P = 3,
    # so full Parikh rank alone cannot be the obstruction for a PIP strict system.
    var sigma: List[List[Int]] = [[0, 1], [2], [1, 2, 0]]
    var c = strict_closure(sigma, Pair([0, 0, 1, 2], [2, 0, 0, 1]))
    assert_equal(c.size(), 20)
    assert_equal(len(parikh_span_basis(c)), 3)
    assert_equal(quotient_charpoly(sigma, c), [1])
    assert_equal(c.first_pair_mask(), 0b111)      # A(C) holds all three unordered pairs
    assert_equal(_minor_gcd(parikh_matrix(c)), 1)  # Parikh lattice index 1 in Z^3


def test_neutral_polynomials_and_refusals() raises:
    assert_true(is_neutral([1]))
    for c0 in [0, 1, -1]:
        assert_true(is_neutral([1, c0]))
    assert_false(is_neutral([1, -2]))
    assert_false(is_neutral([1, -2, -2]))     # x^2 - 2x - 2, the reducible control's Pisot factor
    assert_false(is_neutral([1, 0, -2]))
    assert_true(is_neutral([1, 1, 1]))        # cyclotomic Phi_3
    assert_true(is_neutral([1, 0, 1]))        # Phi_4
    var refused = False
    try:
        _ = is_neutral([2, 1])
    except:
        refused = True
    assert_true(refused)
    # a unit PIP has no strict system: its swap seed meets a coincident factor
    refused = False
    try:
        _ = strict_closure([[0, 1], [1, 2], [0, 2, 1]], Pair([1, 0], [0, 1]))
    except:
        refused = True
    assert_true(refused)


def test_non_invariant_spans_refuse() raises:
    # sigma = 01/12/021, M = [[1,0,1],[1,1,1],[0,1,1]]; the state sets are not child-closed
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    # rank 1, p = (2,1,1), (Mp)_0 = 3: no integral eigenvalue
    assert_true(_refuses(sigma, [Pair([0, 0, 1, 2], [1, 2, 0, 0])], "not an integral eigenvector"))
    # rank 1, p = (1,1,0), Mp = (1,2,1): not an eigenvector
    assert_true(_refuses(sigma, [Pair([0, 1], [1, 0])], "Parikh vector is not an eigenvector"))
    # rank 2, n = (1,1,0) x (1,0,1) = (1,-1,-1), nM = (0,-2,-1): not a left eigenvector
    assert_true(_refuses(sigma, [Pair([0, 1], [1, 0]), Pair([0, 2], [2, 0])], "not a left eigenvector"))
    # rank 2, n = (0,1,1) x (1,0,2) = (2,1,-1), (nM)_0 = 3: no integral eigenvalue
    assert_true(_refuses(sigma, [Pair([1, 2], [2, 1]), Pair([0, 2, 2], [2, 2, 0])], "eigenvalue is not an integer"))


def main() raises:
    test_proposition_q_on_all_carrier_classes()
    test_rank_three_strict_system_of_a_singular_incidence()
    test_neutral_polynomials_and_refusals()
    test_non_invariant_spans_refuse()
    print("Proposition Q: 28 strict-carrier classes, ranks 10/17/1, every quotient spectrum neutral; rank-3 system of 01/2/120; four non-invariant spans refused.")
    require_contract("Proposition Q on a finite child-closed balanced-pair system: the Parikh span is M-invariant and its quotient characteristic polynomial is a product of x and cyclotomic factors, pinned on one strict system of each of the 28 strict-carrier classes with images of length at most three (ranks 1/2/3: 10/17/1) and on the rank-three system of 01/2/120 (20 states, lattice index 1, all three first-letter pairs); non-monic input refuses, and a non-invariant span refuses on each reachable branch (rank-1 non-integral or non-eigenvector, rank-2 non-integral or non-left-eigenvector normal)")
