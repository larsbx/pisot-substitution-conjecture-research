"""Classification and actual occurrence controls, including non-seed cycles."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_minus_cycle_superset import CycleState
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_minus_recurrent_support import member, classify, state_of, exceptional_exit, recurrent_report, emit_counterexample
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, overlap_children


def main() raises:
    var rows = minus_spine_rows()
    assert_equal(classify(CycleState(0,0,0,0,0),rows),"coincidence")
    assert_equal(classify(CycleState(0,1,0,0,0),rows),"carrier")
    assert_equal(classify(CycleState(1,0,0,0,0),rows),"boundary_hit_noncoincidence")
    var empty = List[List[Int]]()
    assert_equal(classify(CycleState(0,1,0,0,0),empty),"unexplained")
    assert_equal(classify(CycleState(0,1,99,-99,0),rows),"unexplained")
    var exceptions = List[CycleState]()
    exceptions.append(CycleState(2,1,-2,4,-3))
    exceptions.append(CycleState(1,2,2,-4,3))
    exceptions.append(CycleState(2,1,3,-6,4))
    exceptions.append(CycleState(1,2,-3,6,-4))
    for b in [1,2]:
        var tables = build_seed_overlap_tables_screened(member(2,b))
        for i in range(4):
            var v = exceptions[i].copy()
            assert_equal(classify(v,rows),"exceptional")
            assert_equal(exceptional_exit(tables,v,2,b),1 if i<2 else 2)
            var children = overlap_children(tables,state_of(tables,v))
            var mirror = state_of(tables,exceptions[i+1 if i%2==0 else i-1])
            var found = False
            for child in children:
                found = found or child == mirror
            assert_true(found)
    # Force a known recurrent zero-offset noncoincidence through the replay
    # reporter, as if a broken carrier had omitted it.
    var tables = build_seed_overlap_tables_screened(member(2,1))
    var graph = build_seed_overlap_graph_from_tables(tables)
    var target = state_of(tables,CycleState(0,1,0,0,0))
    var replayed = False
    for i in range(graph.size()):
        if graph.states[i] == target:
            print("NEGATIVE_CONTROL forced_carrier_omission=0:1:0,0,0")
            emit_counterexample(tables,graph,i,2,1)
            replayed = True
    assert_true(replayed)
    var row = recurrent_report(2,1)
    assert_equal(row[0],139)
    assert_equal(row[1],129)
    assert_equal(row[6],0)
    assert_equal(row[7],1)
    var refused = False
    try:
        _ = recurrent_report(2,1,1)
    except:
        refused = True
    assert_true(refused)
    require_contract("minus positive-b exact recurrent support: complete swap-seed graph, coincidence requires equal letters, distinct-letter zero offsets are classified, four genuine exceptional cycles replay productive exits, unknown labels retain seed/cycle occurrence witnesses, caps refuse; finite calibration is not CycleSum")
