"""Exact reconstruction and adversarial tests for the paired-prefix graphs."""
from copy import deepcopy
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import os
import pytest

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT/'oracles/python/c4_pair_overlap_graph.py'
spec = importlib.util.spec_from_file_location('pair_graph',PATH)
g = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = g
spec.loader.exec_module(g)


@pytest.mark.parametrize('fixture',[0,1])
def test_complete_graph_and_exact_weights(fixture):
    graph,w,it,gap = g.reference(fixture)
    assert len(graph.states) == (7150,7083)[fixture]
    assert sum(map(len,graph.rows)) == (34826,34853)[fixture]
    assert (it,gap) == ((856,99),(1695,101))[fixture]
    assert g.validate_weights(graph,w,g.RATE_NUMERATORS[fixture]) == gap
    assert not any(s[0]==s[1] and s[2:]==(0,0,0) for s in graph.states)
    assert any(len(set(row))<len(row) for row in graph.rows)
    assert g.certify_chart(fixture)['literal_digits'] == 55583
    for root in range(3):
        upper = Q(512*w[root])*Q(g.RATE_NUMERATORS[fixture],103)**1024
        assert upper < Q(1,10)


def test_independent_adjugate_enumeration_of_every_source_row():
    # No Gaussian inverse: directly use adj(M^2), checking its two products.
    adj = ((0,-2,6),(2,0,-2),(-2,2,0))
    m2 = g.power(g.M,2)
    target = ((4,0,0),(0,4,0),(0,0,4))
    assert g.mm(m2,adj) == g.mm(adj,m2) == target
    for fixture in (0,1):
        graph,_,_,_ = g.reference(fixture)
        lookup = {s:i for i,s in enumerate(graph.states)}
        words = []
        sigma = g.CONTROLS[fixture]
        for d in range(3):
            word = ''.join(sigma[int(x)] for x in sigma[d])
            words.append(word)
        digit_records = []
        for d,word in enumerate(words):
            for i,c in enumerate(word):
                mass = tuple(word[:i].count(str(t)) for t in range(3))
                digit_records.append((int(c),d,i,mass))
        residue_rejections = box_rejections = 0
        for i,(c,d,*z) in enumerate(graph.states):
            expected=[]
            for ca,a,pa,p in digit_records:
                if ca!=c: continue
                for cb,b,pb,q in digit_records:
                    if cb!=d: continue
                    x=tuple(z[k]+q[k]-p[k] for k in range(3))
                    y=tuple(sum(adj[r][k]*x[k] for k in range(3)) for r in range(3))
                    if any(v%4 for v in y):
                        residue_rejections+=1;continue
                    y=tuple(v//4 for v in y)
                    # Independently reproduce exact interval projection pruning.
                    xbounds=[Q(y[0])-Q(v,10**6)*y[1] for v in (828911,828912)]
                    ybounds=[Q(y[2])-Q(v,10**6)*y[1] for v in (440619,440620)]
                    reject=min(xbounds)>32 or max(xbounds)<-32 or min(ybounds)>16 or max(ybounds)<-16
                    if reject:
                        box_rejections+=1;continue
                    state=min((a,b,*y),(b,a,*(-v for v in y)))
                    assert state in lookup
                    expected.append(lookup[state])
            assert expected==graph.rows[i]
        assert (residue_rejections,box_rejections)==(graph.residue_rejections,graph.box_rejections)


def test_boundaries_canonicalization_and_unsupported_inputs():
    assert not g.outside_box((32,0,16))
    assert not g.outside_box((-32,0,-16))
    assert g.outside_box((33,0,0))
    assert g.outside_box((0,0,17))
    assert g.canonical(2,0,(1,-2,3))==(0,2,-1,2,-3)
    assert g.canonical(1,1,(1,0,0))==(1,1,-1,0,0)
    for fixture in (-1,2,True):
        with pytest.raises(g.InvalidCertificate):g.build_graph(fixture)
    with pytest.raises(g.InvalidCertificate):g.build_graph(0,state_cap=3)
    graph,_,_,_=g.reference(0)
    with pytest.raises(g.InvalidCertificate):g.construct_weights(graph,iteration_cap=1)


def test_missing_duplicate_occurrence_relabelled_state_and_false_weights():
    graph,w,_,_=g.reference(0)
    rows=deepcopy(graph.rows)
    victim=next(i for i,row in enumerate(rows) if len(set(row))<len(row))
    rows[victim]=list(dict.fromkeys(rows[victim]))
    with pytest.raises(g.InvalidCertificate):g.validate_supplied_graph(0,graph.states,rows,w)
    states=graph.states.copy();s=list(states[0]);s[2]=1;states[0]=tuple(s)
    with pytest.raises(g.InvalidCertificate):g.validate_supplied_graph(0,states,graph.rows,w)
    for value in (0,-1,True,10**7):
        bad=w.copy();bad[0]=value
        with pytest.raises(g.InvalidCertificate):g.validate_weights(graph,bad,99)
    with pytest.raises(g.InvalidCertificate):g.validate_weights(graph,w,103)
    with pytest.raises(g.InvalidCertificate):g.validate_weights(graph,[1]*len(w),99)


def test_native_packet_verification_and_omission_refusals():
    lines=['schema '+g.SCHEMA]
    for fixture in (0,1):
        graph,w,it,_=g.reference(fixture)
        lines.extend(g.graph_lines(graph,w,it))
    packet='\n'.join(lines)+'\n'
    assert g.verify_native(packet)==g.receipt()
    for bad in ('\n'.join(lines[:-1]), '\n'.join(lines+[lines[-1]]), packet.replace('row 0 0 ', 'row 0 1 ',1)):
        with pytest.raises(g.InvalidCertificate):g.verify_native(bad)
    # This self-generated packet is calibration, NOT evidence of a native run.


def test_committed_receipt_and_optional_native_input():
    receipt=ROOT/'evidence/c4-pair-overlap-graph-2026-11-05/receipt.json'
    assert json.loads(receipt.read_text())==g.receipt()
    native=os.environ.get('PSC_PAIR_GRAPH_NATIVE_OUTPUT')
    if native:
        assert g.verify_native(Path(native).read_text())==g.receipt()
    # No skip and no claim of native parity when the environment is absent.


def test_python_optimization_cannot_bypass_acceptance():
    script=f"import sys; sys.path.insert(0,{str(PATH.parent)!r}); import c4_pair_overlap_graph as g; g.verify_native('schema '+g.SCHEMA+'\\n'); print('CERTIFIED')"
    result=subprocess.run([sys.executable,'-O','-c',script],capture_output=True,text=True)
    assert result.returncode!=0
    assert not result.stdout
    assert 'mismatch' in result.stderr


def test_mass_scaling_is_lifted_not_euclidean():
    # abs(det B^2)=4/beta^2, compact Haar contributes 1/4.
    lo,hi=g.root_bracket()
    for n in (99,101):
        assert Q(n,20)/(lo*lo) < 1
        assert 4*Q(n,20)/(hi*hi) > 1
    # A fixed scalar cycle with six parallel edges cannot pass rate 101/20.
    synthetic=g.Graph(1,[(0,0,0,0,0)],[[0]*6],0,0)
    with pytest.raises(g.InvalidCertificate):g.validate_weights(synthetic,[1],101)
