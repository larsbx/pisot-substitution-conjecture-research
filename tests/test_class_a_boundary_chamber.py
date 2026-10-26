"""Independent rational oracle for class-A boundary chamber claims.

Finite spot-checks do not substitute for canonical Mojo symbolic cone proof.
"""
from fractions import Fraction
import importlib.util
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
ORACLE=ROOT/"oracles/python/class_a_boundary_probe.py"
spec=importlib.util.spec_from_file_location("boundary_probe",ORACLE)
bp=importlib.util.module_from_spec(spec)
spec.loader.exec_module(bp)


def test_rational_chamber_and_disjoint_run():
    for eps in (-1,1):
        for k in (0,1,3,10):
            floor=k+3 if eps==-1 else 2*(k+2)
            for n in (floor,floor+1,floor+15,floor+128):
                d=bp.params(n,eps,k)
                P=lambda x: bp.characteristic(n,d,eps,x)
                m=k+2
                z=Fraction(m,n)
                assert P(-1)<0<P(Fraction(-1)+z)
                lo,hi=(n+2,n+3) if eps==-1 else (n+4,n+6)
                assert P(lo)<0<P(hi)
                assert d>=hi-1
                # beta<hi entails d/(beta-1)>1 without assuming
                # any floating approximation or a uniform spectral gap.
                assert d>0 and n<d
                # Symbolic paired run-1 child from (x,c,0): y/y
                # with Parikh residual (-1,1,0), but no overlap:
                # |L_c-L_x|/L_y = d/(beta-1) > 1.


def test_negative_parameter_controls():
    import pytest
    with pytest.raises(AssertionError):
        bp.params(2,-1,0)
    with pytest.raises(AssertionError):
        bp.params(3,1,0)
