"""Reproducible finite occurrence-path control; no universal closure verdict."""
from psc.occurrence_path import (
    SwapOccurrence, search_overlap_path, certify_overlap_path,
    CERTIFIED_LIFTABLE_TARGET_PATH, matched_target,
)
from psc.words import Pair


def main() raises:
    var sigma: List[List[Int]] = [[0, 0, 0, 1, 2, 2], [0, 1], [0]]
    var seed = SwapOccurrence(0, 1, 0, 1)
    var result = search_overlap_path(sigma, seed, 2, 1000, 10000)
    if result.status != CERTIFIED_LIFTABLE_TARGET_PATH:
        raise Error("positive control search did not produce a replayed target")
    certify_overlap_path(sigma, seed, result.edges, 2)
    print("CERTIFIED_LIFTABLE_TARGET_PATH")
    print("sigma: 000122|01|0; seed: swap(0,1), heads(0,1)")
    print("budgets: depth=2 states=1000 choices=10000")
    print("states seen:", result.states_seen, "choices checked:", result.choices_checked)
    for i in range(len(result.edges)):
        var edge = result.edges[i]
        print("edge", i, "source", edge.source, "heads", edge.top_index, edge.bottom_index, "target", edge.target)
    var swap = Pair([0, 1], [1, 0])
    for q in range(3):
        if matched_target(swap, q):
            raise Error("12|21 negative control unexpectedly accepted")
    print("12|21: no matched target, including terminal zero")
    print("scope: one specified seed occurrence; universal child-closed exclusion NOT CHECKED")
