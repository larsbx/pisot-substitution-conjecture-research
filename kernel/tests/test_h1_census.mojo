"""Rank of H^1 through the Barge-Diamond complex: published calibration
values, corpus specimens across the strata, the corpus census tables, and
refusals."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.corpus import pip_corpus
from psc.h1_census import eventual_rank, h1_census, h1_profile, legal_two_words


def check(sigma: List[List[Int]], dimension: Int, eventual: Int, edges: Int, vertices: Int, components: Int, legal: Int) raises:
    var p = h1_profile(sigma)
    assert_equal(p.dimension, dimension)
    assert_equal(p.eventual_rank, eventual)
    assert_equal(p.edges, edges)
    assert_equal(p.vertices, vertices)
    assert_equal(p.components, components)
    assert_equal(p.legal_words, legal)


def test_published_calibration_values() raises:
    check([[0, 1], [0]], 2, 2, 2, 3, 1, 3)                         # Fibonacci, Z^2
    check([[0, 1], [1, 0]], 2, 1, 4, 4, 1, 4)                      # Thue-Morse, Z[1/2] + Z
    check([[0, 1], [0, 0]], 2, 2, 2, 3, 1, 3)                      # period doubling, Z[1/2] + Z
    check([[0, 1], [0, 2], [0]], 3, 3, 3, 4, 1, 5)                 # Tribonacci, Z^3
    check([[1, 0, 0, 0, 1], [0, 1, 0]], 3, 2, 4, 4, 1, 4)          # BBJS 2012 intro, dim 3 with l = 1
    check([[0, 1], [1, 2], [2, 0, 0]], 7, 3, 9, 6, 1, 9)           # Gaehler-Maloney maximal rank n^2 - n + 1
    check([[0, 1], [1, 2], [2, 0]], 7, 3, 9, 6, 1, 9)
    # Barge-Diamond 2008 Example 8: two components in the eventual range (k = 2),
    # the H~^0 correction the corpus never exercises; dim 3 with evrank 4.
    check([[0, 1, 2, 3, 0], [0, 1], [2, 3, 1, 2], [3, 1]], 3, 4, 4, 6, 2, 7)


def test_corpus_specimens_across_the_strata() raises:
    # (sigma, det): one specimen per determinant in each stratum
    check([[1], [2], [0, 2]], 3, 3, 3, 4, 1, 5)                    # det 1
    check([[1], [0, 1, 2], [2, 1]], 3, 3, 4, 5, 1, 5)              # det -1
    check([[1], [2, 2], [0, 1, 2]], 3, 3, 3, 4, 1, 5)              # det 2
    check([[1], [1, 2], [2, 0, 1]], 4, 3, 4, 4, 1, 6)              # det 1
    check([[1], [0, 2, 1], [1, 2]], 4, 3, 4, 4, 1, 6)              # det -1
    check([[1], [0, 1, 2], [0, 0, 1]], 4, 3, 4, 4, 1, 7)           # det 2
    check([[1], [2], [0, 1]], 5, 3, 6, 5, 1, 7)                    # det 1, the deep strong-coincidence class
    check([[0, 1], [0, 2], [2, 1, 0]], 5, 3, 6, 5, 1, 8)           # det -1
    check([[1], [2, 2], [0, 2, 1]], 5, 3, 6, 5, 1, 7)              # det 2
    check([[1], [0, 2], [2, 0, 0]], 7, 3, 9, 6, 1, 9)              # det 1
    check([[1], [0, 2], [2, 2, 0]], 7, 3, 9, 6, 1, 9)              # det -1, both endpoint maps permutations
    check([[0, 1], [2, 2], [1, 0, 0]], 7, 3, 9, 6, 1, 9)           # det 2


def test_corpus_census_tables() raises:
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
    # determinant x dimension (det in {-1, 1, 2}: 648 / 1980 / 1926 specimens)
    var det_table: List[List[Int]] = [
        [-1, 3, 420], [-1, 4, 144], [-1, 5, 72], [-1, 7, 12],
        [1, 3, 1320], [1, 4, 252], [1, 5, 336], [1, 7, 72],
        [2, 3, 1362], [2, 4, 156], [2, 5, 312], [2, 7, 96],
    ]
    var det_total = 0
    for row in det_table:
        assert_equal(census.determinant_count(row[0], row[1]), row[2])
        det_total += row[2]
    assert_equal(det_total, 4554)
    assert_equal(census.determinant_dimension.total(), 4554)
    # endpoint-type cell (A..G = 0..6 for sigma_+, sigma_-) x dimension
    var endpoint_table: List[List[Int]] = [
        [0, 0, 3, 48], [0, 1, 3, 192], [0, 2, 3, 72], [0, 3, 3, 6], [0, 4, 3, 24], [0, 5, 3, 84], [0, 6, 3, 150],
        [1, 0, 3, 192], [1, 1, 3, 348], [1, 2, 3, 198], [1, 3, 3, 6], [1, 4, 3, 120], [1, 5, 3, 318], [1, 6, 3, 138],
        [2, 0, 3, 72], [2, 1, 3, 198], [2, 2, 3, 30], [2, 4, 3, 6], [2, 4, 4, 24], [2, 5, 4, 228], [2, 6, 5, 222],
        [3, 0, 3, 6], [3, 1, 3, 6], [3, 5, 5, 24], [3, 6, 7, 24],
        [4, 0, 3, 24], [4, 1, 3, 120], [4, 2, 3, 6], [4, 2, 4, 24], [4, 4, 5, 12], [4, 5, 3, 24], [4, 5, 5, 18], [4, 6, 7, 66],
        [5, 0, 3, 84], [5, 1, 3, 318], [5, 2, 4, 228], [5, 3, 5, 24], [5, 4, 3, 24], [5, 4, 5, 18], [5, 5, 4, 48], [5, 6, 5, 90],
        [6, 0, 3, 150], [6, 1, 3, 138], [6, 2, 5, 222], [6, 3, 7, 24], [6, 4, 7, 66], [6, 5, 5, 90],
    ]
    var endpoint_total = 0
    for row in endpoint_table:
        assert_equal(census.endpoint_count(row[0], row[1], row[2]), row[3])
        endpoint_total += row[3]
    assert_equal(endpoint_total, 4554)
    assert_equal(census.endpoint_dimension.total(), 4554)
    # (edges, vertices) of the eventual range, key 16 * edges + vertices
    var shape_table: List[List[Int]] = [
        [1, 2, 780], [2, 3, 1344], [3, 4, 918], [4, 4, 504], [4, 5, 60], [5, 5, 48], [6, 5, 708], [7, 6, 12], [9, 6, 180],
    ]
    for row in shape_table:
        assert_equal(census.shapes.count(16 * row[0] + row[1]), row[2])
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
    var not_primitive: List[List[Int]] = [[0, 0], [1, 1]]
    assert_true(refuses(empty_image))
    assert_true(refuses(out_of_range))
    assert_true(refuses(one_letter))
    assert_true(refuses(not_primitive))
    assert_equal(eventual_rank([[0, 1], [1, 0]]), 1)
    assert_equal(len(legal_two_words([[0, 1], [0]])), 4)


def main() raises:
    test_published_calibration_values()
    test_corpus_specimens_across_the_strata()
    test_corpus_census_tables()
    test_refusals()
    print("H^1 census: calibration 2/2/2/3, BD Ex. 8 k = 2; corpus 3102/552/720/180, unimodular 1740/396/408/84, det and endpoint tables.")
    require_contract("dim H^1 of a primitive aperiodic one-dimensional substitution tiling space through the Barge-Diamond complex, evrank(M^T) + E(ER) - V(ER) + 1, against published values including a two-component eventual range; corpus census 3102/552/720/180 with the determinant and endpoint-type tables; non-primitive and malformed input refuse")
