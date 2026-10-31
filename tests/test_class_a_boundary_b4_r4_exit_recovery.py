"""B4/R4 all-cone selected exits, endpoint guards and independent Fraction replay."""
from pathlib import Path
import runpy
import pytest

P = Path(__file__).resolve().parents[1] / "oracles/python/class_a_boundary_b4_r4_exit_recovery.py"
m = runpy.run_path(str(P))


def test_exact_unbounded_occurrence_transport_and_strictness():
    r=m["symbolic_certificate"]()
    assert r["sources"]==2 and r["integer_chambers"]==3
    assert r["source_chamber_cases"]==6
    assert r["directed_symbolic_edge_checks"]==46
    assert r["oriented_labels"]==25 and r["strict_margins"]==50
    assert r["longest_path"]==5 and r["BH"] is False


def test_independent_literal_prefix_fraction_replay():
    r=m["literal_probe"](P.parent)
    assert r == dict(specimens=117,selected_actual_edge_replays=1846)


def test_small_endpoint_actually_last_and_t2_first_run_cases():
    geometry=runpy.run_path(str(P.parent/"class_a_boundary_children.py"))["Geometry"]
    for k,t in ((0,0),(1,0),(0,1),(0,2),(1,1),(1,2),(4,7)):
        g=geometry(-1,k,t)
        chamber=m["CHAMBERS"][min(t,2)]
        for source in m["SOURCES"]:
            path=m["paths"](source,chamber)
            state=source
            for aa,bb,target in path:
                i=aa.k*k+aa.t*t+aa.c if isinstance(aa,m["Aff"]) else aa
                j=bb.k*k+bb.t*t+bb.c if isinstance(bb,m["Aff"]) else bb
                assert g.child(state,i,j)==target
                assert g.interior(target)
                state=target
            assert state==m["C"]
    g=geometry(-1,0,1)
    assert g.child(m["B4"],0,2*g.n+4)==m["DXR"]
    assert g.words[0][2*g.n+4]==0  # actual LAST, not RUN
    h=geometry(-1,0,2)
    assert h.child(m["B4"],0,2*h.n+4)==m["F4"]
    assert h.words[0][2*h.n+4]==2  # genuine RUN


def test_wrong_word_type_and_unbounded_negative_index_slope_refused():
    with pytest.raises(AssertionError):
        m["certify_edge"](m["CHAMBERS"][0],m["B4"],0,m["A"]+1,m["F4"])
    with pytest.raises(AssertionError):
        m["CHAMBERS"][2].nonnegative(m["Aff"](k=-1,c=1000))
    with pytest.raises(AssertionError):
        m["certify_strict"]((0,0,0,0,100))
