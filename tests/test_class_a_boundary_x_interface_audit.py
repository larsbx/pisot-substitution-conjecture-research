"""X first-choice full source inventory and conditional proof boundary."""
from pathlib import Path
import runpy
o=runpy.run_path(str(Path(__file__).resolve().parents[1]/
                     "oracles/python/class_a_boundary_x_interface_audit.py"))

def test_actual_x_stars_and_main_only_tail_replay():
    r=o["probe"]()
    assert r["members"]==117 and r["oriented_source_cells"]==234
    assert r["enumerated_pairs"]==297648
    assert r["indexed_children"]==6786
    assert r["distinct_base_labels"]==10
    assert r["conditional"]["mainline_registered_exits"]==4
    assert r["conditional"]["research_only_candidate_exits"]==6
    assert r["conditional"]["conditional_X_first_choice_depth"]==6
    assert r["not_universal_X_first_choice_proof"]

def test_exact_endpoint_inherits_only_nine_x_targets():
    Geometry=o["Geometry"]
    X=o["X"]
    g=Geometry(-1,0,0)
    assert g.n==3
    labels={w for i,j,w in g.edges(X)}
    assert len(labels)==9
    assert (2,2,1,-1,-2) not in labels
    h=Geometry(-1,1,0)
    assert len({w for i,j,w in h.edges(X)})==10
    assert (2,2,1,-1,-2) in {w for i,j,w in h.edges(X)}

def test_real_reversals_and_status_discipline():
    items=o["SOURCES"]
    assert len(items)==10
    assert len(set(items)|{o["reverse"](w) for w in items})==20
    assert {v[3] for v in items.values()} >= {0,375,376,377,378,380,412,420}
    assert all(status=="research-only" for _,_,status,pr in items.values() if pr in (375,376,377,378,380,420))
