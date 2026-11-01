"""Exact affine transport and all-parameter word guards for CC choices."""
import importlib.util
from pathlib import Path
import sys
import pytest

SRC=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_cc_symbolic_transport.py"
spec=importlib.util.spec_from_file_location("cc_sym",SRC)
o=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=o
spec.loader.exec_module(o)


def test_all_eight_integer_chambers_x_four_first_choices():
    r=o.prove_all_affine_occurrences()
    assert r["chamber_cases"]==8
    assert r["source_cases"]==32
    assert r["max_tail_depth"]==5
    assert not r["universal_BH"]


def test_recession_and_corner_index_guards_refuse_invalid_indices():
    c=o.Chamber(3,1,False,False)
    with pytest.raises(AssertionError):
        c.nonnegative(o.Aff(-1,0,1000))
    with pytest.raises(AssertionError):
        c.nonnegative(o.Aff(0,0,-1))


def test_corrupt_selected_child_type_is_rejected_symbolically():
    label=o.every["XY2"]
    original=o.every["tail"]
    def corrupt(l,g):
        path=list(original(l,g))
        if l==label:
            i,j,_=path[0]
            path[0]=(i,j,(2,1,0,-1,1))
        return path
    o.every["tail"]=corrupt
    try:
        with pytest.raises(AssertionError):
            o.verify_one(o.CHAMBERS[-1],label)
    finally:
        o.every["tail"]=original
