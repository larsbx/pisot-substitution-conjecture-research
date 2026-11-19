"""Exact corpus and long-image controls for the even stack residue.

The corpus filter intersects nilpotent parity with positive eventual-range
cycle rank. On the retained specimens an existing exact strong-coincidence
automaton gives shortest left witnesses. Literal words replay the positive
answers with explicit depth and word caps. This test decides no coincidence
rank and checks no tiling-space argument.
"""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, substitution_incidence
from psc.c4_cut_attractor import left_witness
from psc.c4_geometric_f import chi_mod2_code, principal_minor_sum
from psc.coincidence_formula import coincidence_level
from psc.corpus import pip_corpus
from psc.h1_census import eventual_range, h1_profile, legal_two_words
from psc.histogram import Histogram
from psc.pisot import is_pip
from psc.words import parikh

comptime WITNESS_DEPTH = 12
comptime WORD_CAP = 531441  # 3^12 for the standing corpus


def test_even_corpus() raises:
    var corpus = pip_corpus()
    var even = 0
    var positive_range = 0
    var nilpotent = Histogram(8)
    var levels = Histogram(WITNESS_DEPTH + 1)
    for specimen in corpus:
        ref m = specimen.incidence
        var determinant = m.det()
        if determinant % 2 != 0:
            continue
        even += 1
        var h = h1_profile(specimen.sigma)
        assert_equal(h.eventual_rank, 3)
        assert_equal(h.components, 1)
        positive_range += Int(h.dimension > 3)
        if chi_mod2_code(determinant, m.trace(), principal_minor_sum(m)) != 0:
            continue
        nilpotent.record(h.dimension)
        if h.dimension == 3:
            continue
        for a in range(3):
            for b in range(a + 1, 3):
                var depth = coincidence_level(specimen.sigma, a, b)
                if depth < 1 or depth > WITNESS_DEPTH:
                    raise Error("left witness outside the replay domain for " + specimen.label())
                var witness = left_witness(specimen.sigma, a, b, depth, WORD_CAP)
                assert_equal(witness[0], depth)
                levels.record(depth)
    assert_equal(len(corpus), 4554)
    assert_equal(even, 1926)
    assert_equal(positive_range, 564)
    assert_equal(nilpotent.line("dim H1"), "dim H1 3:336 4:36 5:48 7:12")
    assert_equal(levels.total(), 288)
    assert_equal(levels.maximum(), 7)
    print("even-det corpus", even, "positive ER rank", positive_range, "residue", levels.total() // 3)
    print(nilpotent.line("nilpotent by dim H1"))
    print(levels.line("literal left witness levels"))


def test_long_image_control() raises:
    var sigma: List[List[Int]] = [[1], [2], [1, 0, 0, 2, 2, 2, 2, 1]]
    var m = Mat3(substitution_incidence(sigma))
    assert_true(is_pip(m))
    assert_equal(m.charpoly(), [-2, -2, -4, 1])
    assert_equal(chi_mod2_code(m.det(), m.trace(), principal_minor_sum(m)), 0)
    assert_equal(
        eventual_range(sigma, legal_two_words(sigma)),
        [False, False, False, False, True, True, False, True, True],
    )
    assert_equal(h1_profile(sigma).dimension, 4)
    var witness = left_witness(sigma, 1, 2, 3, 512)
    assert_equal(witness, [3, 16, 2])
    var top: List[Int] = [1]
    var bottom: List[Int] = [2]
    for _ in range(3):
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
    var top_prefix = [top[i] for i in range(16)]
    var bottom_prefix = [bottom[i] for i in range(16)]
    assert_equal(parikh(top_prefix), parikh(bottom_prefix))
    assert_equal(top[16], bottom[16])
    print("1/2/10022221", m.charpoly(), "K2,2", "literal left witness", witness,
          "prefix Parikh", parikh(top_prefix))


def main() raises:
    test_even_corpus()
    test_long_image_control()
    require_contract("Even stack residue: 96 of the 564 positive-ER-rank even determinant corpus specimens have nilpotent incidence modulo two. All 288 unordered letter pairs on those 96 have an exact shortest left coincidence witness confirmed by literal words. The PIP3 control 1/2/10022221 has the nilpotent parity and K2,2 eventual range beyond the corpus, and its periodic first letters coincide at level 3.")
