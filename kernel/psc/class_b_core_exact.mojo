"""Exact bounded forward closure of step-2b's strict core; no uniform theorem.

Reuses the checked integral Perron-field and complete child generator. The
input domain and cap are resource guards, never mathematical cutoffs.
"""
from std.collections import Dict
from class_b_top_layer_profile import top_layer_member, in_open_top_layer
from a1_normal_form_census import CLASS_B, class_member
from psc.perron_field3 import CubicElt
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, SeedOverlapAutomaton, build_seed_overlap_tables_screened, interior_overlap_cached, build_overlap_graph_from_seeds, seed_overlap_states_cached, first_left_aligned_depths
from psc.class_b_segment_graph import segment_graph, root_box, fast_interior
from psc.vertex_coincidence import offset_of, offset_vector, length_matrix
from psc.class_a_gap_dataset import _less


def core_graph(plus: Bool, gap: Int, q: Int, cap: Int = 20000) raises -> SeedOverlapAutomaton:
    if gap < 1 or gap > 32 or q < 1 or q > 320 or cap < 1 or cap > 20000:
        raise Error("bounded exact core domain requires g<=32, q<=320, cap<=20000")
    var par = top_layer_member(plus, gap - 1, q)
    if not in_open_top_layer(plus, par[0], q):
        raise Error("outside open class-B top layer")
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_B, par[0], q, par[2]))
    var lengths = List[CubicElt]([tables.lengths.at(0), tables.lengths.at(1), tables.lengths.at(2)])
    var cache = Dict[CubicElt, Int]()
    var box = root_box(tables)
    var seeds = List[OverlapState]()
    for u in range(-3, 4):
        for d in range(-6, 7):
            for k in range(-2, 3):
                var shift = offset_of(lengths, [k, d + 3 * k, u - 6 * k - d])
                for top in range(3):
                    for bottom in range(3):
                        var state = OverlapState(top, bottom, shift)
                        if fast_interior(tables, cache, box, state):
                            seeds.append(state)
    # Every real canonical swap seed must be in the strict core. Closure then
    # gives seed-graph containment without fitting or comparing vertex counts.
    var present = Dict[OverlapState, Int]()
    for state in seeds:
        present[state] = 1
    for state in seed_overlap_states_cached(tables, cache):
        if state not in present:
            raise Error("canonical swap seed omitted from strict core")
    var graph = segment_graph(tables, seeds, cache, cap)
    if graph.capped:
        raise Error("CORE_CLOSURE_BUDGET_EXHAUSTED: no verdict")
    var depths = first_left_aligned_depths(graph)
    for depth in depths:
        if depth < 0:
            raise Error("exact core closure has a state without an offset-zero descendant")
    return graph^


def core_labels(plus: Bool, gap: Int, q: Int, cap: Int = 20000) raises -> String:
    var graph = core_graph(plus, gap, q, cap)
    var par = top_layer_member(plus, gap - 1, q)
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_B, par[0], q, par[2]))
    var lm = length_matrix(tables)
    var depths = first_left_aligned_depths(graph)
    var rows = List[List[Int]]()
    var deepest = 0
    for i in range(graph.size()):
        var state = graph.states[i]
        var w = offset_vector(lm, state.shift)
        deepest = max(deepest, depths[i])
        rows.append([state.top, state.bottom, w[0], w[1], w[2], depths[i]])
    for i in range(1, len(rows)):
        var row = rows[i].copy()
        var j = i
        while j > 0 and _less(row, rows[j - 1]):
            rows[j] = rows[j - 1].copy()
            j -= 1
        rows[j] = row^
    var out = "M " + String(q) + " " + String(graph.size()) + " " + String(deepest) + "\n"
    for row in rows:
        out += "V"
        for x in row:
            out += " " + String(x)
        out += "\n"
    return out^
