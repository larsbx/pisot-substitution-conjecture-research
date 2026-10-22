"""Exact complete swap-seed graphs of a gap-one class-A line, and their export.

`survey(line, n)` builds the complete canonical seed graph of
`psc.class_a_line.ALine.member(n)` under the 20,000-state cap (an exhausted
cap raises and gives no verdict), and checks that every vertex has a finite
offset-zero descendant. With `export=True` it prints the graph in the record
format of `kernel/class_a_run_index.mojo export N`: `V n i top bottom k c y
depth`, `SEED n i`, `E n i j top_index bottom_index` and `SUMMARY`. These are
exact finite observations for one `n` each; nothing here is uniform in `n`.
"""
from std.collections import Dict
from psc.class_a_line import ALine
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapAutomaton, build_seed_overlap_tables_screened,
    build_seed_overlap_graph_from_tables, first_left_aligned_depths,
    seed_overlap_states,
)
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.overlap_zipper import ordered_child_occurrences
from psc.overlap_obstruction import recurrent_sccs


def survey(line: ALine, n: Int, export: Bool = False) raises -> List[Int]:
    """Returns `[vertices, maximum first-hit depth, recurrent vertices]`."""
    var tables = build_seed_overlap_tables_screened(line.member(n))
    var g = build_seed_overlap_graph_from_tables(tables, 20000)
    if g.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no hitting verdict")
    var ds = first_left_aligned_depths(g)
    var lm = length_matrix(tables)
    var maximum = 0
    for i in range(g.size()):
        if ds[i] < 0:
            raise Error("complete graph has a nonhitting state")
        maximum = max(maximum, ds[i])
        if export:
            var v = g.states[i]
            var w = offset_vector(lm, v.shift)
            print("V", n, i, v.top, v.bottom, w[0], w[1], w[2], ds[i])
    var recurrent = 0
    for c in recurrent_sccs(g):
        recurrent += len(c)
    if export:
        var index = Dict[OverlapState, Int]()
        for i in range(g.size()):
            index[g.states[i]] = i
        for seed in seed_overlap_states(tables):
            print("SEED", n, index[seed])
        for i in range(g.size()):
            if g.states[i].is_coincidence():
                continue
            for e in ordered_child_occurrences(tables, g.states[i]):
                print("E", n, i, index[e.state], e.top_index, e.bottom_index)
    print("SUMMARY", n, g.size(), maximum, recurrent)
    return [g.size(), maximum, recurrent]
