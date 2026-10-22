"""Finite common target spine for minus class-D a=2..8, b=0.

A spine is a lower subgraph, not a claimed equality of full parameter graphs.
The driver rebuilds every full seed graph before intersecting directed support.
Every retained edge is replayed as an ordered occurrence at every member.
No family exhaustion, parametric graph closure, or canonical run is implied.
"""
from std.collections import Dict
from psc.class_d_boundary import boundary_member
from psc.overlap_seed_patch import SeedOverlapAutomaton, build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, first_depths
from psc.overlap_zipper import ordered_child_occurrences
from psc.vertex_coincidence import length_matrix, offset_vector


def _key(top: Int, bottom: Int, w: List[Int]) -> String:
    return String(top) + ":" + String(bottom) + ":" + String(w[0]) + "," + String(w[1]) + "," + String(w[2])


def minus_common_spine(last: Int = 8) raises -> List[Int]:
    if last < 3 or last > 8:
        raise Error("declared comparison budget is a=2..last, 3<=last<=8")
    var tables = build_seed_overlap_tables_screened(boundary_member(-1, 2))
    var base = build_seed_overlap_graph_from_tables(tables, 20000)
    if base.capped:
        raise Error("capped graph: no coverage verdict")
    var lm = length_matrix(tables)
    var keys = List[String]()
    var index = Dict[String, Int]()
    var target = List[Bool]()
    for v in base.states:
        var key = _key(v.top, v.bottom, offset_vector(lm, v.shift))
        if key in index:
            raise Error("duplicate integral label")
        index[key] = len(keys)
        keys.append(key)
        target.append(v.shift.is_zero())
    # Adjacency stores occurrences; explicitly deduplicate directed support.
    var common = List[List[Int]]()
    for i in range(base.size()):
        var seen = Dict[Int, Bool]()
        var row = List[Int]()
        for j in base.adj[i]:
            if j not in seen:
                seen[j] = True
                row.append(j)
        common.append(row^)
    for a in range(2, last + 1):
        var current_tables = build_seed_overlap_tables_screened(boundary_member(-1, a))
        var graph = build_seed_overlap_graph_from_tables(current_tables, 20000)
        if graph.capped or graph.size() != base.size():
            raise Error("full seed graph coverage differs or is capped")
        var lengths = length_matrix(current_tables)
        var local_index = Dict[String, Int]()
        for i in range(graph.size()):
            var v = graph.states[i]
            var key = _key(v.top, v.bottom, offset_vector(lengths, v.shift))
            if key not in index or key in local_index:
                raise Error("full labelled vertex sets differ")
            local_index[key] = i
        for i in range(base.size()):
            var v = graph.states[local_index[keys[i]]]
            if target[i] != v.shift.is_zero():
                raise Error("target not reflected by label map")
            if v.is_coincidence():
                continue  # terminal in the seed graph
            var occurrences = ordered_child_occurrences(current_tables, v)
            var actual = Dict[Int, Bool]()
            for occurrence in occurrences:
                var child = occurrence.state
                var key = _key(child.top, child.bottom, offset_vector(lengths, child.shift))
                if key not in index:
                    raise Error("ordered occurrence escapes full cover")
                actual[index[key]] = True
            var kept = List[Int]()
            for j in common[i]:
                if j in actual:
                    kept.append(j)
            common[i] = kept^
    var spine = SeedOverlapAutomaton(base.states, common, False)
    var ranks = first_depths(spine, target)
    var maximum = 0
    var edges = 0
    var targets = 0
    for i in range(base.size()):
        if ranks[i] < 0:
            raise Error("common lower graph has a target-free vertex")
        maximum = max(maximum, ranks[i])
        edges += len(common[i])
        if target[i]:
            targets += 1
        else:
            var descent = False
            for j in common[i]:
                descent = descent or ranks[j] < ranks[i]
            if not descent:
                raise Error("no strict rank-decreasing actual edge")
    return [base.size(), edges, targets, maximum]
