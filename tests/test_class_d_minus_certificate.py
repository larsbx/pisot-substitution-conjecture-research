"""Independent finite verification of universal affine/polynomial obligations."""
import importlib.util
import json
from pathlib import Path
import sys
import pytest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT / 'oracles/python'))
import class_d_minus_certificate as cert
from class_d_boundary_probe import OverlapGraph


def rows():
    return json.loads(cert.DATA.read_text())['rows']


def test_parametric_certificate_and_native_data_agree():
    expected = dict(states=145,targets=6,seed_occurrences=9,closure_candidates=18779,max_rank=4)
    assert cert.verify(rows()) == expected
    source = (ROOT/'kernel/psc/class_d_minus_spine_data.mojo').read_text()
    native = [json.loads(line.strip().rstrip(',')) for line in source.splitlines()
              if line.startswith('        [')]
    assert native == rows()


@pytest.mark.parametrize('mutation',['false_target','self_loop','wrong_index','eventually_negative','missing_label','duplicate','empty'])
def test_countercontrols(mutation):
    data=rows()
    i=next(i for i,r in enumerate(data) if r[5]>0)
    if mutation=='false_target':data[i][5]=0
    if mutation=='self_loop':data[i][6]=i
    if mutation=='wrong_index':data[i][8]+=1
    if mutation=='eventually_negative':data[i][7:9]=[-1,9]
    if mutation=='missing_label':data.pop(i)
    if mutation=='duplicate':data.append(data[0][:])
    if mutation=='empty':data=[]
    with pytest.raises(ValueError):cert.verify(data)


def test_bounded_affine_fit_is_not_a_uniform_run_certificate():
    # The tempting top c-image index 9-a stays in its y-run at a=2..8,
    # but equals the first c at a=9 and becomes invalid at a=10.
    assert all(1<=9-a<=3*a+6 for a in range(2,9))
    with pytest.raises(ValueError,match='leaves its run'):
        cert.affine_prefix(1,-1,9)


def test_boundary_contact_and_unknown_sign_are_not_interior_proofs():
    assert not cert.interior((2,2,0,0,1))
    assert cert.impossible((2,2,0,0,1))
    # Mixed Bernstein signs certify neither strict positivity nor negativity.
    assert min(cert.bernstein100((0,1,-20)))<0<max(cert.bernstein100((0,1,-20)))


@pytest.mark.parametrize('a',[2,3,8])
def test_all_affine_choices_against_independent_full_exact_graph(a):
    p,q,r=3*a+5,3*a+6,2*a+4
    g=OverlapGraph({1:(1,)+(3,)*p+(2,),2:(2,)+(3,)*q+(1,),3:(2,)+(3,)*r+(2,)},20000)
    assert not g.capped
    F=g.F
    data=rows()
    states=[(v[0]+1,v[1]+1,tuple(sum(v[2+k]*g.l[k][j] for k in range(3)) for j in range(3))) for v in data]
    assert set(states)==set(g.states)
    for v,parent in zip(data,states):
        if v[5]==0:
            assert parent[2]==F.zero
            continue
        i,j=v[7]*a+v[8],v[9]*a+v[10]
        top,bot,t=parent
        child=(g.sigma[top][i],g.sigma[bot][j],F.sub(F.add(F.mul(F.beta,t),g.prefix[bot,j]),g.prefix[top,i]))
        assert child==states[v[6]] and g.overlaps(child)
        assert g.index[child] in g.adj[g.index[parent]]
    assert sum(v[5]==0 and not g.is_coincidence(s) for v,s in zip(data,states))>0
