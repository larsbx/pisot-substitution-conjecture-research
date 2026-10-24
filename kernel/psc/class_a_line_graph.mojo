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
    build_overlap_graph_from_seeds, first_left_aligned_depths,
    seed_overlap_states_cached,
)
from psc.perron_field3 import CubicElt
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.overlap_zipper import ordered_child_occurrences_cached
from psc.overlap_obstruction import recurrent_sccs


def survey(line: ALine, n: Int, export: Bool = False) raises -> List[Int]:
    """Returns `[vertices, maximum first-hit depth, recurrent vertices]`."""
    var tables = build_seed_overlap_tables_screened(line.member(n))
    # One exact sign cache serves the seed scan, the graph closure and, under
    # `export`, every edge enumeration. The sign of a field element at the
    # Perron root depends on the element alone, so sharing it changes no
    # record, only the number of Sturm--Tarski evaluations.
    var sign_cache = Dict[CubicElt, Int]()
    var seeds = seed_overlap_states_cached(tables, sign_cache)
    var g = build_overlap_graph_from_seeds(tables, seeds, sign_cache, 20000)
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
        for seed in seeds:
            print("SEED", n, index[seed])
        for i in range(g.size()):
            if g.states[i].is_coincidence():
                continue
            for e in ordered_child_occurrences_cached(tables, sign_cache, g.states[i]):
                print("E", n, i, index[e.state], e.top_index, e.bottom_index)
    print("SUMMARY", n, g.size(), maximum, recurrent)
    return [g.size(), maximum, recurrent]


def residue_profile(d: Int, eps: Int, last: Int, l_min: Int = 2) raises -> List[List[Int]]:
    """Vertex counts of the exact complete graphs of `(n+d, n, n+eps)`, `n <= last`,
    fitted on each residue ray `n = d l + r` as `slope l + constant`.

    The fit takes the two largest members with `l >= l_min`; a residue with fewer
    than two such members is omitted. Returns `[r, slope, constant, members, affine]`
    per residue, with `affine = 1` iff every member with `l >= l_min` lies on the
    fitted line. Each line prints as `PROFILE`. A finite observation: nothing
    here is uniform in `l` or `d`.
    """
    var size = Dict[Int, Int]()
    for n in range(0, last + 1):
        if n + eps >= 0 and d <= 2 * n + 6 * eps + 5:
            size[n] = survey(ALine(d, eps, n % d), n)[0]
    var out = List[List[Int]]()
    for r in range(d):
        var members = List[Int]()
        for n in range(r + l_min * d, last + 1, d):
            if n in size:
                members.append(n)
        if len(members) < 2:
            continue
        var n1 = members[len(members) - 2]
        var n2 = members[len(members) - 1]
        var slope = (size[n2] - size[n1]) // ((n2 - n1) // d)
        var constant = size[n2] - slope * (n2 // d)
        var affine = 1
        for n in members:
            if size[n] != slope * (n // d) + constant:
                affine = 0
        print("PROFILE d=" + String(d), "eps=" + String(eps), "r=" + String(r), "slope", slope,
              "constant", constant, "members", len(members), "affine", affine)
        out.append([r, slope, constant, len(members), affine])
    return out^
