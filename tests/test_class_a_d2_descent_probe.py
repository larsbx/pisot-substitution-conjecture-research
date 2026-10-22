"""Independent exact ordered prefix edge replay for finite d2 descent."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "d2_descent",ROOT/"oracles/python/class_a_d2_descent_probe.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.mark.parametrize("n,states,deep",[
    (7,231,5),(8,265,5),(9,271,6),
    (10,305,6),(11,311,7),(12,345,7),
])
def test_complete_finite_descent_occurrence_packet(n,states,deep):
    r=oracle.build_finite(n)
    assert r["states"]==states
    assert r["targets"]==8
    assert r["actual_occurrence_witnesses"]==states-8
    assert r["max_first_hit"]==deep
    assert r["centered_slice"]["depths"]==[2,0,2]
    assert len(r["witness_sha256"])==64
    assert oracle.validate_witness(n,r)


def test_corrupt_actual_edge_indices_or_rank_refused():
    genuine=oracle.build_finite(8)
    tamper=dict(genuine)
    rows=genuine["_witness"].copy()
    parent,child,i,j,depth=rows[0]
    rows[0]=(parent,child,i+10000,j,depth)
    tamper["_witness"]=rows
    with pytest.raises(ValueError):
        oracle.validate_witness(8,tamper)
    rows=genuine["_witness"].copy()
    rows[0]=(parent,child,i,j,depth+1)
    tamper["_witness"]=rows
    with pytest.raises(ValueError):
        oracle.validate_witness(8,tamper)
    rows=genuine["_witness"][:-1]
    tamper["_witness"]=rows
    with pytest.raises(ValueError):
        oracle.validate_witness(8,tamper)


def test_zero_target_normalized_single_affine_rank_is_impossible():
    # On the row X(k)=A(n)+B(n)k, X(0)=0 forces A=0,
    # while X(-1)>=1 forces -B>=1 and X(1)>=1 forces B>=1.
    # Adding implies 0>=2. This argument is uniform wherever the
    # already-certified three-point typed slice is present (n>=7).
    for n in (7,8,9,10,11,12):
        g=oracle.graph(n)
        d=oracle.shortest_boundary_depths(g)
        table={lab:d[i] for i,lab in enumerate(oracle.labels(g))}
        assert [table[(0,0,k,-k,0)] for k in (-1,0,1)]==[2,0,2]
    for b in range(-30,31):
        assert not (-b>=1 and b>=1)


def test_finite_scope_is_fail_closed():
    for n in (3,25):
        with pytest.raises(ValueError):
            oracle.build_finite(n)
