"""The aligned obligation of one swap seed, censused over the standing corpus."""

from std.testing import assert_equal
from psc.claim_tests import require_contract
from psc.corpus import pip_corpus
from psc.overlap_seed_patch import build_seed_overlap_tables
from psc.perron_field3 import CubicElt
from psc.seed_aligned_cover import ALL_PAIRS, pair_bit, seed_aligned_pair_mask


def test_tribonacci_seeds_expose_every_pair() raises:
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var tables = build_seed_overlap_tables(sigma)
    var cache = Dict[CubicElt, Int]()
    assert_equal(seed_aligned_pair_mask(tables, 0, 1, cache), ALL_PAIRS)


def test_corpus_seed_cover_census() raises:
    """Per specimen: how many of its three swap seeds expose all three pairs,
    and how many expose only their own pair."""
    var corpus = pip_corpus()
    var full = List[Int](length=4, fill=0)
    var own_only = List[Int](length=4, fill=0)
    var masks = List[Int](length=8, fill=0)
    for s in range(len(corpus)):
        var tables = build_seed_overlap_tables(corpus[s].sigma)
        var cache = Dict[CubicElt, Int]()
        var nf = 0
        var no = 0
        for a in range(3):
            for b in range(a + 1, 3):
                var m = seed_aligned_pair_mask(tables, a, b, cache)
                masks[m] += 1
                if m == ALL_PAIRS:
                    nf += 1
                if m == pair_bit(a, b):
                    no += 1
        full[nf] += 1
        own_only[no] += 1
    assert_equal(full[0], 36)
    assert_equal(full[1], 1134)
    assert_equal(full[2], 120)
    assert_equal(full[3], 3264)
    assert_equal(own_only[0], 4452)
    assert_equal(own_only[1], 102)
    assert_equal(own_only[2] + own_only[3], 0)
    assert_equal(masks[ALL_PAIRS], 11166)


def main() raises:
    test_tribonacci_seeds_expose_every_pair()
    print("[PASS] test_tribonacci_seeds_expose_every_pair")
    test_corpus_seed_cover_census()
    print("[PASS] test_corpus_seed_cover_census")
    print("2 seed aligned-cover Mojo tests passed.")
    require_contract("every swap seed exposes all three pairs at offset zero on 3264 of 4554 corpus specimens")
