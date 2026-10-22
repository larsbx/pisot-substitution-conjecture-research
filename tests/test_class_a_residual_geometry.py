"""Independent general-normal-form identities and rejected carrier transplant."""
import importlib.util
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("a_geometry",ROOT/"oracles/python/class_a_residual_geometry.py")
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def test_both_signs_exact_polynomial_normal_form():
    for sign in (-1,1):
        F,L,M=mod.class_a(sign)
        assert F.terms and len(L)==3 and len(M)==3


def test_uniform_d2_nontransfer():
    evidence=mod.d2_witness()
    assert evidence["typed_row"]==(2,2,0,-2,-1,0,0,0)
    assert evidence["margin_upper_numerator"]==-76


def test_negative_controls():
    import pytest
    with pytest.raises(AssertionError):
        mod.class_a(0)
    F,L,M=mod.class_a(1)
    assert F != F + mod.h
    assert L[0]-L[1]!=2*mod.d*mod.h*(1+mod.h)
