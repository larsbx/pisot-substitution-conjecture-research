"""Two-step overlap graphs justified by the common compact-attractor argument.

The period-aware constructor remains unchanged. This separate theorem-facing
entry point uses the written F^12 uniqueness lemma to authenticate F^2 for
period-three prefix words as well. The graph engine and finite inequality
verifier are shared with the period-aware implementation; no SC input.
"""
from finite_exact.rat_q import Q
from psc.c4_pair_overlap_graph import (
    PairGraph, source_class_images, _certify_source_box, _build_source_graph,
    verify_weights_at_rate,
)


def build_source_order_graph(index: Int, state_cap: Int = 16000) raises -> PairGraph:
    var images = source_class_images(index)
    if state_cap < 3 or state_cap > 16000:
        raise Error("two-step attractor graph budget")
    # Authenticate all prefix cycles; the written common-attractor lemma,
    # not an SC certificate, permits step two when a cycle has length three.
    for start in range(3):
        var seen: List[Int] = [-1,-1,-1]
        var letter = start
        var count = 0
        while seen[letter] < 0:
            seen[letter] = count
            count += 1
            letter = images[letter][0]
        var period = count-seen[letter]
        if period < 1 or 12 % period != 0:
            raise Error("unsupported attractor block/prefix period")
    _certify_source_box(images,[24,12],[Q(13,2),Q(4,1)])
    return _build_source_graph(images,index,2,[24,12],state_cap,40)


def verify_pair_weights(graph: PairGraph, weights: List[Int]) raises -> Int:
    return verify_weights_at_rate(graph,weights,102,2)


def construct_attractor_weights(graph: PairGraph, iteration_cap: Int = 4000) raises -> Tuple[List[Int],Int]:
    if iteration_cap < 1 or iteration_cap > 4000:
        raise Error("ordered weight sweep budget")
    var n = len(graph.states)
    if n < 1 or n > 16000 or len(graph.rows) != n:
        raise Error("graph dimensions before indexing")
    for row in graph.rows:
        if len(row) > 1024:
            raise Error("occurrence row budget")
        for j in row:
            if j < 0 or j >= n:
                raise Error("invalid target before weight indexing")
    var weights = List[Int]()
    for _ in range(n):
        weights.append(1)
    for sweep in range(1,iteration_cap+1):
        var unchanged = True
        for i in range(n):
            var total = 0
            for j in graph.rows[i]:
                total += weights[j]
            var value = 1+(20*total+101)//102
            if value > 1000000:
                raise Error("weight budget exhausted; inconclusive")
            if value < weights[i]:
                raise Error("nonmonotone ordered weight iteration")
            if value != weights[i]:
                unchanged = False
                weights[i] = value
        if unchanged:
            _ = verify_pair_weights(graph,weights)
            return (weights^,sweep)
    raise Error("iteration budget exhausted; inconclusive")
