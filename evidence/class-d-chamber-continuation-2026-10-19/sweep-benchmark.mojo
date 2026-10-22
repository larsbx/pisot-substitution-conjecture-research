from std.time import perf_counter_ns
from std.testing import assert_equal
from std.collections import Dict
from symbolic_line_certificate import ClassLine
from a1_normal_form_census import CLASS_D
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, build_seed_overlap_tables_screened, overlap_children_cached, interior_overlap_cached, _child_at_prefixes
from psc.perron_field3 import CubicElt, cubic_mul_beta

def exhaustive(tables: SeedOverlapTables, state: OverlapState) raises -> List[OverlapState]:
    # Verbatim old production enumeration, including one scaled-shift build.
    var cache = Dict[CubicElt, Int]()
    if not interior_overlap_cached(tables, cache, state):
        raise Error("cannot inflate a non-overlap state")
    var out = List[OverlapState]()
    var scaled_shift = cubic_mul_beta(tables.field, state.shift)
    for i in range(len(tables.sigma[state.top])):
        var top_child = tables.sigma[state.top][i]
        var top_prefix = tables.prefix(state.top, i)
        for j in range(len(tables.sigma[state.bottom])):
            var bottom_child = tables.sigma[state.bottom][j]
            var bottom_prefix = tables.prefix(state.bottom, j)
            var child = _child_at_prefixes(top_child,bottom_child,scaled_shift,top_prefix,bottom_prefix)
            if interior_overlap_cached(tables, cache, child):
                out.append(child)
    return out^


def main() raises:
    var tables = build_seed_overlap_tables_screened(ClassLine(CLASS_D,[4,74,4,73,3,57],True).member(30))
    var state = OverlapState(0,1,CubicElt())
    var cache = Dict[CubicElt, Int]()
    var start = perf_counter_ns()
    var old = exhaustive(tables,state)
    var old_ns = perf_counter_ns()-start
    start = perf_counter_ns()
    var new = overlap_children_cached(tables,cache,state)
    var new_ns = perf_counter_ns()-start
    assert_equal(len(new),len(old))
    for i in range(len(new)):
        assert_equal(new[i],old[i])
    print("SWEEP_BENCH", "old_ns=",old_ns,"new_ns=",new_ns,"children=",len(new))
