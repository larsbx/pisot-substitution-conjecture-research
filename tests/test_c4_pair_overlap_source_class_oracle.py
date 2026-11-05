"""Full finite source-class replay plus independent adjugate edge reconstruction."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import importlib.util
import json
import os
import subprocess
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'oracles/python'))
import c4_pair_overlap_source_class as g


def adjugate(m):
    # Separate integer cofactor route, not the producer's Gaussian inverse.
    cofactors=[]
    for i in range(3):
        row=[]
        for j in range(3):
            rr=[r for r in range(3) if r!=i];cc=[c for c in range(3) if c!=j]
            minor=m[rr[0]][cc[0]]*m[rr[1]][cc[1]]-m[rr[0]][cc[1]]*m[rr[1]][cc[0]]
            row.append((-1)**(i+j)*minor)
        cofactors.append(row)
    return tuple(tuple(cofactors[j][i] for j in range(3)) for i in range(3))


def test_exact_complete_source_domain_and_fixed_point_powers():
    expected=tuple(product(('1',),tuple(''.join(w) for w in permutations('012')),('001','010','100')))
    assert g.SOURCES==expected and len(set(expected))==18
    periods=[]
    for i,sigma in enumerate(expected):
        letter,period,step=g.fixed_point_data(i)
        w=str(letter)
        for _ in range(period):w=''.join(sigma[int(c)] for c in w)
        assert w.startswith(str(letter)) and len(w)>1
        assert step%period==0
        periods.append(period)
    assert periods.count(1)==6 and periods.count(2)==8 and periods.count(3)==4
    for i in (12,13,15,16):
        with pytest.raises(g.InvalidCertificate):g.build_graph(i,step=2)


def test_all_eighteen_certificates_and_full_receipt():
    computed=g.receipt()
    path=ROOT/'evidence/c4-pair-overlap-source-class-2026-11-05/receipt.json'
    assert computed==json.loads(path.read_text())
    rows=computed['certificates']
    assert sum(r['states'] for r in rows)==288835
    assert sum(r['occurrence_edges'] for r in rows)==1862307
    assert all(r['zero_offset_diagonal_states']==0 for r in rows)
    assert max(r['maximum_weight'] for r in rows)==63257
    assert sum(r['literal_digits'] for r in rows)==1000494
    for index,r in enumerate(rows):
        graph,w,stats,gap=g.reference(index)
        assert g.validate_weights(graph,w)==gap>0
        num,den,lower=g.rate(index)
        assert g.base.root_bracket()[0]**graph.step>lower>Q(num,den)
        assert all(g.AREA*x*(Q(num,den)/lower)**8192<Q(1,10) for x in w[:3])


def test_every_edge_by_independent_literal_adjugate_reconstruction():
    for index in range(18):
        graph,_,_,_=g.reference(index)
        sigma=g.source(index)
        step=graph.step
        m=g.base.power(g.base.M,step)
        adj=adjugate(m); determinant=2**step
        expected=tuple(tuple(determinant*int(i==j) for j in range(3)) for i in range(3))
        assert g.base.mm(adj,m)==g.base.mm(m,adj)==expected
        records=[]
        for source in range(3):
            word=str(source)
            for _ in range(step):word=''.join(sigma[int(c)] for c in word)
            for pos,c in enumerate(word):
                records.append((int(c),source,tuple(word[:pos].count(str(j)) for j in range(3))))
        lookup={s:i for i,s in enumerate(graph.states)}
        # Group by endpoints only after the independent literal rescan.
        # Every paired occurrence remains a distinct list entry.
        paired={}
        for c in range(3):
            for d in range(3):
                paired[c,d]=[]
                for ca,a,p in records:
                    if ca!=c:continue
                    for cb,b,q in records:
                        if cb!=d:continue
                        delta=[q[k]-p[k] for k in range(3)]
                        transformed=tuple(sum(row[k]*delta[k] for k in range(3)) for row in adj)
                        paired[c,d].append((a,b,transformed))
        nr=nb=0
        for parent,(c,d,z0,z1,z2) in enumerate(graph.states):
            shift=[row[0]*z0+row[1]*z1+row[2]*z2 for row in adj]
            children=[]
            for a,b,delta in paired[c,d]:
                v0,v1,v2=shift[0]+delta[0],shift[1]+delta[1],shift[2]+delta[2]
                if v0%determinant or v1%determinant or v2%determinant:
                    nr+=1;continue
                x,y,z=(v0//determinant,v1//determinant,v2//determinant)
                xl,xh=10**6*x-828911*y,10**6*x-828912*y
                yl,yh=10**6*z-440619*y,10**6*z-440620*y
                if min(xl,xh)>48*10**6 or max(xl,xh)<-48*10**6 or min(yl,yh)>24*10**6 or max(yl,yh)<-24*10**6:
                    nb+=1;continue
                state=min((a,b,x,y,z),(b,a,-x,-y,-z))
                assert state in lookup
                children.append(lookup[state])
            assert children==graph.rows[parent]
        assert (nr,nb)==(graph.residue_rejections,graph.box_rejections)


def test_component_solver_equals_simple_synchronous_integer_recurrence():
    for index in (1,12):
        graph,w,_,_=g.reference(index)
        num,den,_=g.rate(index)
        current=[1]*len(w)
        for _ in range(1000):
            nxt=[1+(den*sum(current[j] for j in row)+num-1)//num for row in graph.rows]
            if nxt==current:break
            current=nxt
        else:raise AssertionError('synchronous budget')
        assert current==w
    rows=[[1,1],[0,2],[]]
    components=g.components_sink_first(rows)
    assert components==[[2],[0,1]]


def test_caps_missing_occurrences_false_weights_and_boundary_contact():
    assert not g.outside((48,0,24)) and g.outside((49,0,0))
    for bad in (-1,18,True):
        with pytest.raises(g.InvalidCertificate):g.build_graph(bad)
    with pytest.raises(g.InvalidCertificate):g.build_graph(0,state_cap=3)
    graph,w,_,_=g.reference(0)
    with pytest.raises(g.InvalidCertificate):g.construct_weights(graph,iteration_cap=1)
    rows=deepcopy(graph.rows)
    victim=next(i for i,row in enumerate(rows) if len(set(row))<len(row))
    rows[victim]=list(dict.fromkeys(rows[victim]))
    with pytest.raises(g.InvalidCertificate):g.verify_supplied_graph(0,graph.states,rows,w)
    for bad in (0,-1,True,10**9):
        weights=w.copy();weights[0]=bad
        with pytest.raises(g.InvalidCertificate):g.validate_weights(graph,weights)
    with pytest.raises(g.InvalidCertificate):g.validate_weights(graph,[1]*len(w))


def test_full_packet_replay_and_native_is_separate(tmp_path):
    path=tmp_path/'reference.txt'
    with path.open('w') as f:
        f.write('schema '+g.SCHEMA+'\n')
        for i in range(18):
            graph,w,_,_=g.reference(i)
            for line in g.graph_lines(graph,w):f.write(line+'\n')
    assert g.verify_native(path)==g.receipt()  # Calibration only, not a native run.
    with path.open('a') as f:f.write('extra\n')
    with pytest.raises(g.InvalidCertificate):g.verify_native(path)
    native=os.environ.get('PSC_PAIR_CLASS_NATIVE_OUTPUT')
    if native:assert g.verify_native(Path(native))==g.receipt()


def test_optimization_does_not_disable_admission():
    code=f"import sys;sys.path.insert(0,{str(ROOT/'oracles/python')!r});import c4_pair_overlap_source_class as g;g.build_graph(12,step=2);print('CERTIFIED')"
    p=subprocess.run([sys.executable,'-O','-c',code],capture_output=True,text=True)
    assert p.returncode!=0 and not p.stdout and 'fixed-point' in p.stderr
