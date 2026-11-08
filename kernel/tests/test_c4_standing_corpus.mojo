"""C4 on the standing corpus: every letter pair of every specimen has an exact
left strong-coincidence witness, so by the cut-pair reduction (Theorem A(4) of
docs/c4-cut-pair-productivity-2026-11-04.md) no strict component exists and
C3-local holds vacuously for all 4,554 specimens.

The witnesses are decided by the affine coincidence automaton of
`psc.coincidence_formula`: `coincidence_level` returns `-1` only as a decided
negative, never as an exhausted budget. A pair merged by the first-letter map
is witnessed at the left end of `sigma^n` and is counted separately."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_claim
from psc.coincidence_formula import coincidence_level, first_letter_merge_level
from psc.corpus import pip_corpus
from psc.histogram import Histogram
from psc.words import ALPHABET


def test_every_pair_of_every_specimen_is_witnessed() raises:
    var corpus = pip_corpus()
    var residual_levels = Histogram(32)
    var merged_pairs = 0
    var residual_pairs = 0
    var specimens_with_residual = 0
    var unwitnessed = 0
    for s in range(len(corpus)):
        var has_residual = False
        for a in range(ALPHABET):
            for b in range(a + 1, ALPHABET):
                if first_letter_merge_level(corpus[s].sigma, a, b) >= 0:
                    merged_pairs += 1
                    continue
                var level = coincidence_level(corpus[s].sigma, a, b)
                if level < 0:
                    unwitnessed += 1
                    continue
                residual_pairs += 1
                has_residual = True
                residual_levels.record(level)
        if has_residual:
            specimens_with_residual += 1
    assert_equal(len(corpus), 4554)
    assert_equal(unwitnessed, 0)
    assert_equal(merged_pairs + residual_pairs, 3 * 4554)
    assert_equal(residual_pairs, 6360)
    assert_equal(specimens_with_residual, 2658)
    # residual pairs by least coincidence level (strong_coincidence_census.mojo)
    var expected: List[List[Int]] = [
        [2, 828], [3, 1956], [4, 1812], [5, 1200], [6, 384], [7, 132], [8, 18], [12, 6], [13, 6], [14, 12], [15, 6],
    ]
    for row in expected:
        assert_equal(residual_levels.count(row[0]), row[1])
    assert_equal(residual_levels.total(), 6360)
    assert_equal(residual_levels.maximum(), 15)


def test_witness_levels_on_named_specimens() raises:
    # the deep class 1/2/01 (plastic number): residual pairs at levels 13, 14, 12
    var deep: List[List[Int]] = [[1], [2], [0, 1]]
    assert_equal(first_letter_merge_level(deep, 0, 1), -1)
    assert_equal(coincidence_level(deep, 0, 1), 13)
    assert_equal(coincidence_level(deep, 0, 2), 14)
    assert_equal(coincidence_level(deep, 1, 2), 12)
    # unit PIP 01/12/021: {0,2} merged at the first letter, {0,1} and {1,2} at level 4
    var unit: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    assert_equal(first_letter_merge_level(unit, 0, 2), 1)
    assert_equal(coincidence_level(unit, 0, 1), 4)
    assert_equal(coincidence_level(unit, 1, 2), 4)
    # The reducible strict control 10/102/211 lies outside the domain: the exact
    # automaton needs an irreducible cubic and refuses it (test_c4_cut_attractor
    # pins its unwitnessed cut pair with the bounded search instead).
    assert_true(first_letter_merge_level([[1, 0], [1, 0, 2], [2, 1, 1]], 0, 1) >= 0)


def main() raises:
    test_every_pair_of_every_specimen_is_witnessed()
    test_witness_levels_on_named_specimens()
    print("C4 on the standing corpus: 13,662 letter pairs witnessed (6,360 residual, deepest level 15); no strict component exists on any of the 4,554 specimens.")
    require_claim("C4StandingCorpus")
    require_claim("C4FromStrongCoincidence")
