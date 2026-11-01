"""Cross-check selected four-stage boundary path in exact-rational geometry."""
import importlib.util
from pathlib import Path

SRC=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_U_hit.py"
spec=importlib.util.spec_from_file_location("boundary_U_hit",SRC)
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_U_path_rational_realization():
    result=oracle.probe()
    assert result["members"]==60
    assert result["matched"]==60
    assert result["per_member_depth"]==4
    assert result["U_to_internal_hit_depth"]==2
    assert all(x["strictly_internal_newborn_start"] for x in result["rows"])
    for rec in result["rows"]:
        assert rec["steps"][-1]["target"]==(2,2,0,0,0)
        assert [(e["i"],e["j"]) for e in rec["steps"]]==[
            (1,2),(0,rec["t"]+1),(rec["d"]+3,0),(1,2)]


def test_wrong_last_run_address_is_not_a_target():
    g=oracle.Geometry(-1,0,0)
    V=(2,0,0,-1,1)
    wrong=g.child(V,1,1)
    assert wrong[:2]==(2,2)
    assert wrong!=(2,2,0,0,0)
