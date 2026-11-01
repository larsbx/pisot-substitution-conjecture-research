"""Exact class-B child support in nine segment pairs, rather than image pairs.

FIRST/RUN/LAST prefixes are (0,0,0), e_first + m e_y, and
 e_first + R e_y. The difference of two integer run intervals fills their
whole difference interval. For fixed segment types and displacement, child
start is strictly increasing in the run difference. Binary search finds the
first child ending after the top start; iterate until the top end is reached.
Duplicate occurrences are collapsed only for graph support. This is not an
occurrence-multiplicity exporter. All field arithmetic is checked.
"""
from std.collections import Dict
from finite_exact.closed_interval import IQ
from psc.perron_root_sign import perron_root_bracket
from psc.exact import interval_horner_int, strict_sign
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked, cubic_mul_beta, cubic_scale_checked
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, SeedOverlapAutomaton, cached_sign, interior_overlap_cached, seed_overlap_states_cached


def root_box(tables: SeedOverlapTables) raises -> IQ:
    return perron_root_bracket(tables.field.chi0, tables.field.chi1, tables.field.chi2, 24)


def fast_sign(tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int], box: IQ, value: CubicElt) raises -> Int:
    if value in cache:
        return cache[value]
    if value.is_zero():
        cache[value] = 0
        return 0
    var sign = strict_sign(interval_horner_int([value.a0, value.a1, value.a2], box))
    if sign == 0:
        return cached_sign(tables, cache, value)
    cache[value] = sign
    return sign


def fast_interior(tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int], box: IQ, state: OverlapState) raises -> Bool:
    return fast_sign(tables, cache, box, cubic_add_checked(state.shift, tables.lengths.at(state.bottom))) > 0 and fast_sign(tables, cache, box, cubic_sub_checked(state.shift, tables.lengths.at(state.top))) < 0


def check_class_b_images(tables: SeedOverlapTables) raises:
    for t in range(3):
        var word = tables.sigma[t].copy()
        if len(word) < 2 or word[0] != (0 if t == 0 else 1) or word[len(word) - 1] != 0:
            raise Error("not class-B FIRST/RUN/LAST images")
        for i in range(1, len(word) - 1):
            if word[i] != 2:
                raise Error("not class-B internal y run")


def segment_data(tables: SeedOverlapTables, t: Int, part: Int) raises -> List[Int]:
    var run = len(tables.sigma[t]) - 2
    if part == 0:
        return [0 if t == 0 else 1, 0, 0, 0, 0]
    var px = 1 if t == 0 else 0
    if part == 1:
        return [2, px, 1 - px, 0, run - 1]
    return [0, px, 1 - px, run, run]


def segment_children(tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int], box: IQ, state: OverlapState) raises -> List[OverlapState]:
    if not fast_interior(tables, cache, box, state):
        raise Error("cannot inflate a non-overlap state")
    var out = List[OverlapState]()
    var seen = Dict[OverlapState, Int]()
    var scaled = cubic_mul_beta(tables.field, state.shift)
    for pt in range(3):
        var a = segment_data(tables, state.top, pt)
        if a[3] > a[4]:
            continue
        for pb in range(3):
            var b = segment_data(tables, state.bottom, pb)
            if b[3] > b[4]:
                continue
            var base = cubic_add_checked(scaled, cubic_add_checked(cubic_scale_checked(tables.lengths.at(0), b[1] - a[1]), cubic_scale_checked(tables.lengths.at(1), b[2] - a[2])))
            var lo = b[3] - a[4]
            var hi = b[4] - a[3]
            var end = hi + 1
            while lo < end:
                var mid = lo + (end - lo) // 2
                var shift = cubic_add_checked(base, cubic_scale_checked(tables.lengths.at(2), mid))
                if fast_sign(tables, cache, box, cubic_add_checked(shift, tables.lengths.at(b[0]))) > 0:
                    end = mid
                else:
                    lo = mid + 1
            for dy in range(lo, hi + 1):
                var shift = cubic_add_checked(base, cubic_scale_checked(tables.lengths.at(2), dy))
                if fast_sign(tables, cache, box, cubic_sub_checked(shift, tables.lengths.at(a[0]))) >= 0:
                    break
                var child = OverlapState(a[0], b[0], shift)
                if child not in seen:
                    seen[child] = 1
                    out.append(child)
    return out^


def segment_graph(tables: SeedOverlapTables, seeds: List[OverlapState], mut cache: Dict[CubicElt, Int], cap: Int = 20000) raises -> SeedOverlapAutomaton:
    check_class_b_images(tables)
    if cap < 1 or cap > 20000:
        raise Error("class-B graph resource cap requires 1..20000")
    var box0 = root_box(tables)
    var states = List[OverlapState]()
    var adj = List[List[Int]]()
    var index = Dict[OverlapState, Int]()
    for seed in seeds:
        if not fast_interior(tables, cache, box0, seed):
            raise Error("non-strict seed")
        if seed not in index:
            if len(states) >= cap:
                raise Error("CLASS_B_GRAPH_CAP: no verdict")
            index[seed] = len(states)
            states.append(seed)
    var box = root_box(tables)
    var head = 0
    while head < len(states):
        var state = states[head]
        var edges = List[Int]()
        if not state.is_coincidence():
            for child in segment_children(tables, cache, box, state):
                if child not in index:
                    if len(states) >= cap:
                        raise Error("CLASS_B_GRAPH_CAP: no verdict")
                    index[child] = len(states)
                    states.append(child)
                edges.append(index[child])
        adj.append(edges^)
        head += 1
    return SeedOverlapAutomaton(states, adj, False)


def class_b_seed_graph(tables: SeedOverlapTables, cap: Int = 20000) raises -> SeedOverlapAutomaton:
    var cache = Dict[CubicElt, Int]()
    return segment_graph(tables, seed_overlap_states_cached(tables, cache), cache, cap)
