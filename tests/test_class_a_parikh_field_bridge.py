"""Exact integer-field intertwining, inverse lattice and actual word regressions."""
import importlib.util
from pathlib import Path
import sys
import pytest
FILE=Path(__file__).resolve().parents[1]/'reference/psc_research/class_a_parikh_field_bridge.py'
spec=importlib.util.spec_from_file_location('parikh_field',FILE)
b=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=b
spec.loader.exec_module(b)

def test_all_integer_displacement_conjugacy_large_grid():
    assert b.test_all_coefficients()==7020
    for k,t in ((0,0),(0,1),(3,0),(0,10),(30,50)):
        n,d,_=b.parameters(k,t)
        assert b.chi(n,d)==(2,-(t+3),-(k+t+5))
        assert b.parikh_shift(d,(1,0,0))==(-1,d,1)
        assert b.parikh_shift(d,(0,1,0))==(-1,0,1)
        assert b.parikh_shift(d,(0,0,1))==(0,-1,1)

def test_every_actual_ordered_occurrence_for_named_sources():
    sources=((0,0,1,0,-1),(0,0,0,1,0),(2,2,1,-1,-1),
             (1,2,0,-2,2),(1,1,0,-2,3))
    total=0
    for k in range(5):
        for t in range(5):
            ww=b.words(k,t)
            for w in sources:
                for i in range(len(ww[w[0]])):
                    for j in range(len(ww[w[1]])):
                        z=b.verify_field_transport(k,t,w,i,j)
                        assert z[:2]==(ww[w[0]][i],ww[w[1]][j])
                        total+=1
    assert total>10000

def test_reversed_exact_cubic_shift_and_child_transport():
    for k,t in ((0,0),(0,3),(3,0),(8,13)):
        n,d,_=b.parameters(k,t)
        w=(1,2,0,-2,2)
        rw=(w[1],w[0],-w[2],-w[3],-w[4])
        assert b.parikh_shift(d,rw[2:])==tuple(-v for v in b.parikh_shift(d,w[2:]))
        ww=b.words(k,t)
        for i in range(len(ww[w[0]])):
            for j in range(len(ww[w[1]])):
                z=b.verify_field_transport(k,t,w,i,j)
                rz=b.verify_field_transport(k,t,rw,j,i)
                assert rz==(z[1],z[0],-z[2],-z[3],-z[4])

def test_no_invalid_param_or_ordinal():
    for args in ((-1,0),(0,-1),(0.1,0)):
        with pytest.raises(ValueError): b.parameters(*args)
    with pytest.raises(ValueError): b.indexed_child(0,0,(0,1,0,0,0),100,0)
    with pytest.raises(ValueError): b.indexed_child(0,0,(3,1,0,0,0),0,0)

def test_exact_injective_lattice_and_typed_zero_equivalence():
    for k in range(13):
        for t in range(9):
            n,d,_=b.parameters(k,t)
            for p in (-5,-1,0,3):
                for q in (-4,0,2):
                    for r in (-2,0,1,7):
                        v=(p,q,r)
                        coeff=b.parikh_shift(d,v)
                        assert b.decode_parikh_shift(d,coeff)==v
                        assert (coeff==(0,0,0))==(v==(0,0,0))
            with pytest.raises(ValueError): b.decode_parikh_shift(d,(1,0,0))
    with pytest.raises(ValueError): b.decode_parikh_shift(0,(0,0,0))
