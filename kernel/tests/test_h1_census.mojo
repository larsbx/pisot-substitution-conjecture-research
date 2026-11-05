"""Rank of H^1 through the Barge-Diamond complex: classics, corpus specimens, the
corpus census, and refusals."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.corpus import pip_corpus
from psc.h1_census import eventual_rank, h1_census, h1_profile, legal_two_words


def check(sigma: List[List[Int]], dimension: Int, eventual: Int, edges: Int, vertices: Int, legal: Int) raises:
    var p = h1_profile(sigma)
    assert_equal(p.dimension, dimension)
    assert_equal(p.eventual_rank, eventual)
    assert_equal(p.edges, edges)
    assert_equal(p.vertices, vertices)
    assert_equal(p.components, 1)
    assert_equal(p.legal_words, legal)


def test_classics_with_published_ranks() raises:
    check([[0, 1], [0]], 2, 2, 2, 3, 3)              # Fibonacci
    check([[0, 1], [1, 0]], 2, 1, 4, 4, 4)           # Thue-Morse
    check([[0, 1], [0, 0]], 2, 2, 2, 3, 3)           # period doubling
    check([[0, 1], [0, 2], [0]], 3, 3, 3, 4, 5)      # Tribonacci


def test_corpus_specimens_across_the_strata() raises:
    check([[1], [2], [0, 2]], 3, 3, 3, 4, 5)
    check([[1, 0], [0, 2, 1], [0]], 4, 3, 4, 4, 6)
    check([[1], [2], [0, 1]], 5, 3, 6, 5, 7)            # the deep strong-coincidence class
    check([[1, 2], [0], [1]], 5, 3, 6, 5, 7)
    check([[1, 2], [0], [2, 1, 1]], 7, 3, 9, 6, 9)
    check([[1], [0, 2], [2, 2, 0]], 7, 3, 9, 6, 9)      # both endpoint maps permutations


def test_corpus_census() raises:
    var census = h1_census(pip_corpus())
    assert_equal(census.total, 4554)
    assert_equal(census.disconnected, 0)
    assert_equal(census.dimensions.count(3), 3102)
    assert_equal(census.dimensions.count(4), 552)
    assert_equal(census.dimensions.count(5), 720)
    assert_equal(census.dimensions.count(6), 0)
    assert_equal(census.dimensions.count(7), 180)
    assert_equal(census.dimensions.total(), 4554)
    assert_equal(census.unimodular.count(3), 1740)
    assert_equal(census.unimodular.count(4), 396)
    assert_equal(census.unimodular.count(5), 408)
    assert_equal(census.unimodular.count(7), 84)
    assert_equal(census.unimodular.total(), 2628)
    # (edges, vertices) of the eventual range, key 16 * edges + vertices
    assert_equal(census.shapes.count(16 * 1 + 2), 780)
    assert_equal(census.shapes.count(16 * 2 + 3), 1344)
    assert_equal(census.shapes.count(16 * 3 + 4), 918)
    assert_equal(census.shapes.count(16 * 4 + 4), 504)
    assert_equal(census.shapes.count(16 * 4 + 5), 60)
    assert_equal(census.shapes.count(16 * 5 + 5), 48)
    assert_equal(census.shapes.count(16 * 6 + 5), 708)
    assert_equal(census.shapes.count(16 * 7 + 6), 12)
    assert_equal(census.shapes.count(16 * 9 + 6), 180)
    assert_equal(census.shapes.total(), 4554)


def refuses(sigma: List[List[Int]]) -> Bool:
    try:
        _ = h1_profile(sigma)
        return False
    except:
        return True


def test_refusals() raises:
    var empty_image: List[List[Int]] = [[0, 1], List[Int]()]
    var out_of_range: List[List[Int]] = [[0, 2], [1]]
    var one_letter: List[List[Int]] = [[0]]
    assert_true(refuses(empty_image))
    assert_true(refuses(out_of_range))
    assert_true(refuses(one_letter))
    # a singular incidence has eventual rank below the alphabet size
    assert_equal(eventual_rank([[0, 1], [1, 0]]), 1)
    assert_equal(len(legal_two_words([[0, 1], [0]])), 4)


def main() raises:
    test_classics_with_published_ranks()
    test_corpus_specimens_across_the_strata()
    test_corpus_census()
    test_refusals()
    print("H^1 census: classics 2/2/2/3; corpus 3102/552/720/180, unimodular 1740/396/408/84.")
    require_contract("dim H^1 of a one-dimensional substitution tiling space through the Barge-Diamond complex: evrank(M^T) + E(ER) - V(ER) + 1, with the classics Fibonacci, Thue-Morse, period doubling and Tribonacci at 2, 2, 2, 3; corpus census 3102/552/720/180 and unimodular 1740/396/408/84; malformed input and a non-bijective eventual range refuse")
