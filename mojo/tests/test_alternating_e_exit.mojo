"""Counter-calibration of the alternating-E interior-witness transport target."""

from std.testing import assert_equal, assert_true
from psc.claim_tests import require_contract
from psc.corpus import pip_corpus
from psc.alternating_e_exit import alternating_e_hub, hub_star_exit
from psc.overlap_seed_patch import build_seed_overlap_tables
from psc.perron_field3 import CubicElt


def test_named_specimen_leaves_the_hub_star_without_the_good_edge() raises:
    # 0 -> 1, 1 -> 02, 2 -> 220: hub 2 fixed, good edge {0,1} swapped.
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 2, 0]]
    assert_equal(alternating_e_hub(sigma), 2)
    var cache = Dict[CubicElt, Int]()
    var e = hub_star_exit(build_seed_overlap_tables(sigma), 2, cache)
    assert_true(not e.reaches_good_edge)
    assert_true(e.coincides_avoiding_good_edge)


def test_non_type_e_maps_have_no_alternating_hub() raises:
    var tribonacci: List[List[Int]] = [[0, 1], [0, 2], [0]]
    assert_equal(alternating_e_hub(tribonacci), -1)


def test_corpus_exit_census() raises:
    """294 corpus specimens carry the alternating-E endpoint map; in every one
    the hub star coincides along a path avoiding offset-zero G, and in 66 no
    offset-zero G vertex lies below the hub star at all."""
    var corpus = pip_corpus()
    var type_e = 0
    var reaches = 0
    var avoiding = 0
    for s in range(len(corpus)):
        ref sigma = corpus[s].sigma
        var hub = alternating_e_hub(sigma)
        if hub < 0:
            continue
        type_e += 1
        var cache = Dict[CubicElt, Int]()
        var e = hub_star_exit(build_seed_overlap_tables(sigma), hub, cache)
        if e.reaches_good_edge:
            reaches += 1
        if e.coincides_avoiding_good_edge:
            avoiding += 1
    assert_equal(type_e, 294)
    assert_equal(reaches, 228)
    assert_equal(avoiding, 294)


def main() raises:
    test_named_specimen_leaves_the_hub_star_without_the_good_edge()
    print("[PASS] test_named_specimen_leaves_the_hub_star_without_the_good_edge")
    test_non_type_e_maps_have_no_alternating_hub()
    print("[PASS] test_non_type_e_maps_have_no_alternating_hub")
    test_corpus_exit_census()
    print("[PASS] test_corpus_exit_census")
    print("3 alternating-E exit Mojo tests passed.")
    require_contract("alternating-E hub star exits without the good edge on 66 of 294 corpus specimens")
