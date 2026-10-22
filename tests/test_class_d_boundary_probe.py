"""Independent boundary calibration and refusal, without canonical execution credit."""
import importlib.util
import json
from pathlib import Path
import pytest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("class_d_boundary_probe", ROOT / "oracles/python/class_d_boundary_probe.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_recorded_eight_graphs_replay_exactly():
    expected=json.loads((ROOT / "evidence/class-d-boundary-2026-10-14/oracle.json").read_text())
    assert oracle.report()==expected


def test_capped_graph_refuses_a_verdict():
    with pytest.raises(RuntimeError,match="STATE_BUDGET_EXHAUSTED"):
        oracle.probe(1,0,1)

@pytest.mark.parametrize("s,a,cap",[(0,0,20000),(1,9,20000),(1,-1,20000),(1,0,20001),(1,0,0)])
def test_invalid_budget_is_rejected(s,a,cap):
    with pytest.raises(ValueError):
        oracle.probe(s,a,cap)


def test_equal_vertex_counts_do_not_certify_equal_support():
    actual=json.loads(json.dumps(oracle.support_report()))
    expected=json.loads((ROOT / "evidence/class-d-support-change-2026-10-14/oracle.json").read_text())
    assert actual==expected
    assert actual["vertices"]==[145,145]
    assert actual["vertex_labels_equal"]
    assert not actual["support_equal"]
    assert all(not w["present_at_a2"] and w["present_at_a3"] for w in actual["witnesses"])


@pytest.mark.parametrize("a",range(9))
def test_prescribed_seed_and_hitting_paths(a):
    """Independent exact recurrence/geometry check, not a family exhaustion."""
    p,q,r=3*a+5,3*a+6,2*a+4
    sigma={1:(1,)+(3,)*p+(2,),2:(2,)+(3,)*q+(1,),3:(2,)+(3,)*r+(2,)}
    g=oracle.OverlapGraph(sigma,20000)
    assert not g.capped
    F=g.F
    def state(top,bottom,w):
        shift=tuple(sum(w[k]*g.l[k][j] for k in range(3)) for j in range(3))
        return top,bottom,shift
    s=state(1,2,(0,0,0))
    pp=state(1,1,(0,0,1))
    qq=state(2,1,(-1,1,1))
    u=state(3,3,(0,2,-3))
    v=state(3,3,(1,1,-3))
    rr=state(2,3,(2,-3,1))
    t=state(3,2,(-1,1,0))
    z=state(2,3,(0,0,0))
    assert all(g.overlaps(x) for x in (s,pp,qq,u,v,rr,t,z))
    assert s in g.seeds() and pp in g.seeds()
    def prescribed(parent,child,i,j):
        top,bottom,shift=parent
        if not (0<=i<len(sigma[top]) and 0<=j<len(sigma[bottom])):
            return False
        shift=F.sub(F.add(F.mul(F.beta,shift),g.prefix[bottom,j]),g.prefix[top,i])
        actual=(sigma[top][i],sigma[bottom][j],shift)
        return actual==child and g.overlaps(actual)
    assert prescribed(s,qq,p+1,q+1)
    assert prescribed(pp,u,r+4,1)==(a>=3)
    assert prescribed(qq,v,r+5,1)==(a>=3)
    for parent,child,i,j in [(u,rr,0,2),(v,rr,0,3),(rr,t,a+1,r+1),(t,z,r+1,r)]:
        assert prescribed(parent,child,i,j)
        assert child in g.children(parent)
    assert not prescribed(t,z,r+1,r+1)
    assert z[2]==F.zero and not g.is_coincidence(z)
