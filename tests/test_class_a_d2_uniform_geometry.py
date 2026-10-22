"""Independent integer polynomial tests for all-n d2 parity geometry."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "uniform_d2_geometry", ROOT/"oracles/python/class_a_d2_uniform_geometry.py")
g=importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


def test_uniform_candidate_geometry_and_seeds():
    e,o=g.certify(g.inferred(0),0),g.certify(g.inferred(1),1)
    assert (e["intervals"],e["strict_margins"],e["typed_slices"],e["seeds"])==(93,186,82,9)
    assert (o["intervals"],o["strict_margins"],o["typed_slices"],o["seeds"])==(87,174,80,9)
    assert (e["formal_size_slope_m"],e["formal_size_intercept"])==(40,105)
    assert (o["formal_size_slope_m"],o["formal_size_intercept"])==(40,111)
    assert o["n_floor"]==7 and e["n_floor"]==8


def test_coefficient_and_carrier_negative_controls():
    assert g.coefficients_positive((0,1,0,0),8)
    assert not g.coefficients_positive((0,0,0,0),8)
    assert not g.coefficients_positive((-1,0,0,0),9)
    source=g.inferred(0)
    broken=source.copy()
    row=list(broken[0])
    row[-1]+=20
    broken[0]=tuple(row)
    with pytest.raises(ValueError):
        g.certify(broken,0)
    with pytest.raises(ValueError):
        g.certify(source,1)
    with pytest.raises(ValueError):
        g.inferred(2)


def test_uniform_seed_certificate_not_just_n4_membership():
    for parity,n0 in [(0,8),(1,7)]:
        rows=g.inferred(parity)
        for seed in g.SEEDS:
            assert g.contains_seed_for_all_m(rows,n0//2,seed)
        # Removing a source slice destroys a seed's entire parity-ray membership.
        miss=[r for r in rows if r[:4]!=(2,2,-1,0)]
        assert not g.contains_seed_for_all_m(miss,n0//2,(2,2,0,-1,0))
