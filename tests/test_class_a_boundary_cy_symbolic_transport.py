"""All-chamber exact affine coefficient/typed occurrence certification."""
import importlib.util
from pathlib import Path
import pytest

FILE=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_cy_symbolic_transport.py"
spec=importlib.util.spec_from_file_location("cy_sym",FILE)
m=importlib.util.module_from_spec(spec)
# dataclasses expects registered module
import sys
sys.modules[spec.name]=m
spec.loader.exec_module(m)


def test_all_ten_integer_chambers_certified_by_coefficients():
    result=m.prove_all_affine_occurrences()
    assert result["chamber_cases"]==10
    assert result["source_cases"]==60
    assert result["max_tail_depth"]==6
    assert not result["universal_BH"]


def test_affine_guard_rejects_unbounded_negative_slope():
    chamber=m.Chamber(3,2,False,False)
    with pytest.raises(AssertionError):
        chamber.nonnegative(m.Aff(-1,0,1000))
    with pytest.raises(AssertionError):
        chamber.nonnegative(m.Aff(0,0,-1))


def test_symbolic_transport_rejects_wrong_typed_target():
    label=m.every["B1"]
    original=m.every["tail"]
    def corrupt(l,g):
        path=list(original(l,g))
        if l==label:
            i,j,_=path[0]
            path[0]=(i,j,(2,1,0,-3,3))
        return path
    m.every["tail"]=corrupt
    try:
        with pytest.raises(AssertionError):
            m.verify_one(m.CHAMBERS[-1],label)
    finally:
        m.every["tail"]=original
