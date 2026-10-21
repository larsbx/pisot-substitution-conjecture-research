from std.time import perf_counter_ns
from std.testing import assert_equal
from std.collections import Dict
from tests.test_overlap_child_sweep import exhaustive
from symbolic_line_certificate import ClassLine
from a1_normal_form_census import CLASS_D
from psc.overlap_seed_patch import OverlapState, build_seed_overlap_tables_screened, overlap_children_cached
from psc.perron_field3 import CubicElt

def main() raises:
    var tables = build_seed_overlap_tables_screened(ClassLine(CLASS_D,[4,74,4,73,3,57],True).member(30))
    var state = OverlapState(0,0,CubicElt())
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
