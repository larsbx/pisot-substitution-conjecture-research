"""The literal fixed-tiling count against its closed form, and the nonunit
rank-two residue over the corpus."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import identity3
from psc.corpus import pip_corpus
from psc.rank_two_parity import er_graph_map
from psc.twin_fixed_points import fixed_tiling_count, residue_profile


def fixed_letters(f: List[Int], n: Int) -> Int:
    var c = 0
    for x in range(3):
        var y = x
        for _ in range(n):
            y = f[y]
        c += Int(y == x)
    return c


def main() raises:
    # Thue-Morse: the letter exchange is a free involution of Fix(Phi^n).
    var tm: List[List[Int]] = [[0, 1], [1, 0]]
    var two = 1
    for n in range(1, 9):
        two *= 2
        assert_equal(fixed_tiling_count(tm, n), two if n % 2 == 0 else two - 2)

    # Tribonacci (unit, pure discrete): tr(M^3) - 1 - 3 + 3 with 10, 20, 00 legal.
    var trib: List[List[Int]] = [[0, 1], [0, 2], [0]]
    assert_equal(fixed_tiling_count(trib, 1), 0)
    assert_equal(fixed_tiling_count(trib, 2), 2)
    assert_equal(fixed_tiling_count(trib, 3), 6)

    var corpus = pip_corpus()
    var nonunit = 0
    var theorem_e = 0
    var tree = 0
    var either = 0
    var parity = 0
    var after = 0
    var survivors = 0
    var survivors_e2_odd = 0
    for s in range(len(corpus)):
        var m = corpus[s].incidence.copy()
        var det = m.det()
        if det == 1 or det == -1:
            continue
        nonunit += 1
        var sigma = corpus[s].sigma.copy()
        var g = [sigma[a][0] for a in range(3)]
        var gr = [sigma[a][len(sigma[a]) - 1] for a in range(3)]
        var er = er_graph_map(sigma)

        # Lemma N: the literal count is tr(M^n) - Fix(g^n) - Fix(g_R^n) + fixed edges of ER.
        var power = identity3()
        var all_even = True
        for n in range(1, 7):
            power = power * m
            var closed = power.trace() - fixed_letters(g, n) - fixed_letters(gr, n) + er.fixed_edges(n)
            var literal = fixed_tiling_count(sigma, n)
            assert_equal(literal, closed)
            all_even = all_even and literal % 2 == 0

        var r = residue_profile(sigma)
        assert_equal(r.edges, er.edge_count())
        assert_equal(r.tree, er.betti() == 0)
        theorem_e += Int(r.theorem_e)
        tree += Int(r.tree)
        either += Int(r.theorem_e or r.tree)
        parity += Int(r.odd_power != 0)
        if r.theorem_e or r.tree:
            continue
        after += 1
        # Theorem R(1): past Theorems E and H3 the eventual range is K_{2,2}.
        assert_true(r.complete_bipartite())
        # Theorem R(2): there the count is even for all n iff tr M is even, and n = 1 decides.
        assert_equal(r.odd_power == 0, m.trace() % 2 == 0)
        assert_equal(r.odd_power == 0, all_even)
        assert_true(r.odd_power <= 1)
        assert_true(det % 2 == 0)
        if r.survives():
            survivors += 1
            survivors_e2_odd += Int(m.charpoly()[1] % 2 != 0)

    assert_equal(nonunit, 1926)
    assert_equal(theorem_e, 840)
    assert_equal(tree, 1362)
    assert_equal(either, 1794)
    assert_equal(parity, 1338)
    assert_equal(after, 132)
    assert_equal(survivors, 72)
    assert_equal(survivors_e2_odd, 48)
    # Theorem R(4) keeps chi_M = t^3 mod 2: the K_{2,2} row of the even-residue shape table.
    assert_equal(survivors - survivors_e2_odd, 24)

    # A unit member is outside the theorem, and the profile is still computed.
    assert_false(residue_profile(trib).survives())

    require_contract("fixed-tiling count: literal words agree with tr(M^n) - Fix(g^n) - Fix(g_R^n) + fixed ER edges; past Theorems E and H3 the eventual range is K_{2,2} and the count is even iff tr M is; 72 nonunit corpus classes pass, 24 of them with nilpotent incidence modulo two")
