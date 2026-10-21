import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("shared",ROOT/"oracles/python/class_d_minus_shared_cycles.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_six_edge_exact_common_parameter_contradiction():
    forms = oracle.cycle_forms(oracle.NEGATIVE_STATES,oracle.NEGATIVE_SEGMENTS)
    assert forms == [(-7,-2,1),(7,2,-1),(2,1,-1),(-2,-1,1),
                     (11,2,2),(0,1,-1),(2,1,-1),(-2,-1,1),
                     (25,5,3),(-1,1,-1),(4,2,-1),(-4,-2,1)]
    for i,(u,v) in enumerate([(0,7),(0,2),(0,0),(0,2),(1,0),(0,4)]):
        assert all(c+a*u+b*v>=0 for c,a,b in forms[2*i:2*i+2])
    multipliers = [int(i in (0,5)) for i in range(12)]
    assert oracle.farkas_refutes(forms,multipliers)
    assert [sum(y*f[j] for y,f in zip(multipliers,forms)) for j in range(3)] == [-7,-1,0]
    assert not oracle.farkas_refutes(forms,[0]*12)
    assert not oracle.farkas_refutes(forms,[-1]*12)


def test_shared_integer_witness_for_genuine_u_cycle():
    forms = oracle.cycle_forms([(2,1,-2,4,-3),(1,2,2,-4,3)],[(2,1),(1,2)])
    assert all(c>=0 for c,_,_ in forms)  # a=2,b=1
    # a=2,b=3 lies outside b<=a, so this cycle really depends on parameters.
    assert any(c+2*b<0 for c,_,b in forms)


def test_closing_edge_and_budget_are_checked():
    pairs = oracle.NEGATIVE_SEGMENTS.copy()
    pairs[-1] = (0,0)
    with pytest.raises(ValueError,match="edge mismatch"):
        oracle.cycle_forms(oracle.NEGATIVE_STATES,pairs)
    with pytest.raises(ValueError,match="incomplete"):
        oracle.cycle_forms([],[])


@pytest.mark.parametrize("k", [2, 3, 7, 100, 100000])
def test_unbounded_family_independent_finite_calibration(k):
    states = oracle.negative_family(k)
    assert [sum(s[2:]) for s in states] == [-k,k-1,-k,k-1,-k,k]
    forms = oracle.cycle_forms(states,oracle.NEGATIVE_SEGMENTS)
    assert forms[0] == (2*k-11,-2,k-1)
    assert forms[5] == (4-2*k,1,1-k)
    assert tuple(a+b for a,b in zip(forms[0],forms[5])) == (-7,-1,0)
    assert oracle.farkas_refutes(forms,[int(i in (0,5)) for i in range(12)])
    if k == 2:
        assert states == oracle.NEGATIVE_STATES


@pytest.mark.parametrize("t", [1, 2, 17, 50000])
def test_even_family_has_individual_integer_edge_witnesses(t):
    forms = oracle.cycle_forms(oracle.negative_family(2*t),oracle.NEGATIVE_SEGMENTS)
    points = [(9*(t-1),7),(8*(t-1),2),(4*(t-1),0),
              (8*(t-1),2),(4*t-3,0),(6*(t-1),4)]
    for i,(u,v) in enumerate(points):
        assert u>=0 and v>=0
        assert all(c+a*u+b*v>=0 for c,a,b in forms[2*i:2*i+2])
