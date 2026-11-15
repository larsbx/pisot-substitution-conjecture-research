"""Independent SCC, spectral, multiplicity and native-certificate controls."""
from copy import deepcopy
from dataclasses import replace
from fractions import Fraction as Q
from itertools import permutations
import gzip
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT=Path(__file__).resolve().parents[1]
ORACLES=ROOT/'oracles/python'
sys.path.insert(0,str(ORACLES))
g=importlib.import_module('c4_overlap_scc_obstruction')
EVIDENCE=ROOT/'evidence/c4-critical-overlap-components-2026-11-05'
COUNTS=(3518,3259,3518,3031,3564,3516,3057,3525,3492,3554,3256,3503)
LARGEST=(143,391,123,622,56,119,622,123,119,56,391,143)
SINGLETONS=(3516,3258,3516,3027,3561,3514,3053,3523,3490,3551,3255,3501)
OTHER_SIZES=((5,143),(391,),(28,123),(3,3,12,622),(15,21,56),(34,119),
             (3,3,12,622),(28,123),(34,119),(15,21,56),(391,),(5,143))


def rows(matrix):
    return [[j for j,value in enumerate(row) for _ in range(value)] for row in matrix]


def zeros(report):
    return {v:record['zero'] for record in report['components'] for v in record['members']}


def critical(weights=((Q(1),),)):
    return {'kind':2,'weights':weights}


def rational(kind,weights,rate):
    return {'kind':kind,'weights':weights,'rate':rate}


@pytest.mark.parametrize('index',range(12))
def test_all_complete_source_components_without_previous_weights(index):
    obj,report=g.reference(index)
    records=report['components']
    assert len(records)==COUNTS[index]
    assert max(len(r['members']) for r in records)==LARGEST[index]
    assert sum(r['exclusion']==1 for r in records)==SINGLETONS[index]
    assert sorted(len(r['members']) for r in records if len(r['members'])>1)==list(OTHER_SIZES[index])
    assert all(r['zero'] and not r['budget_refused'] and r['spectral']==0 for r in records)
    for record in records:
        if record['exclusion']==1:
            assert len(record['members'])==1 and not record['attempts']
        else:
            assert record['exclusion']==2
            assert len(record['attempts'])==1
            prime,rank,det=record['attempts'][0]
            assert prime==101 and rank==len(record['members']) and 0<det<prime
    assert report['zero_states']==len(obj.states)
    assert report['root_zero']==(True,True,True)
    g.require_zero_certificate(report)


def test_canonical_scc_partition_against_independent_reachability():
    graph=[[1,1],[0,2],[2,2],[],[3],[4]]
    reach=[]
    for start in range(len(graph)):
        seen={start}
        while True:
            enlarged=seen|{j for i in seen for j in graph[i]}
            if enlarged==seen:
                break
            seen=enlarged
        reach.append(seen)
    expected=[]
    unused=set(range(len(graph)))
    while unused:
        first=min(unused)
        block=tuple(j for j in sorted(unused) if j in reach[first] and first in reach[j])
        expected.append(block)
        unused.difference_update(block)
    assert g.components(graph)==tuple(expected)==((0,1),(2,),(3,),(4,),(5,))
    for supplied in (((0,),(1,),(2,),(3,),(4,),(5,)),
                     ((0,1,2),(3,),(4,),(5,)),((0,1),(2,),(3,),(4,)),
                     ((0,1),(2,),(3,),(4,),(4,5))):
        with pytest.raises(g.InvalidCertificate):
            g.authenticate_partition(graph,supplied)


def permutation_det(matrix):
    total=0
    for order in permutations(range(len(matrix))):
        sign=(-1)**sum(order[i]>order[j] for i in range(len(order)) for j in range(i+1,len(order)))
        term=sign
        for i,j in enumerate(order):
            term*=matrix[i][j]
        total+=term
    return total


def bareiss_det(matrix):
    matrix=deepcopy(matrix)
    sign,previous=1,1
    for k in range(len(matrix)-1):
        pivot=next((i for i in range(k,len(matrix)) if matrix[i][k]),None)
        if pivot is None:
            return 0
        if pivot!=k:
            matrix[k],matrix[pivot]=matrix[pivot],matrix[k]
            sign=-sign
        value=matrix[k][k]
        for i in range(k+1,len(matrix)):
            for j in range(k+1,len(matrix)):
                numerator=value*matrix[i][j]-matrix[i][k]*matrix[k][j]
                assert numerator%previous==0
                matrix[i][j]=numerator//previous
            matrix[i][k]=0
        previous=value
    return sign*matrix[-1][-1]


def test_actual_small_blocks_against_integer_determinants():
    # Exact integer fraction-free determinants are independent of modular
    # pivot arithmetic; permutation expansion also calibrates the smallest.
    checked=set()
    for index in (0,3,4):
        obj,report=g.reference(index)
        for record in report['components']:
            size=len(record['members'])
            if 1<size<=15:
                polynomial=g.polynomial_matrix(g.block_matrix(obj.rows,record['members']))
                determinant=bareiss_det(polynomial)
                assert determinant%101==record['attempts'][0][2]
                if size<=5:
                    assert determinant==permutation_det(polynomial)
                checked.add(size)
    assert checked=={3,5,12,15}


def test_noncritical_outgoing_forcing_does_not_imply_zero():
    graph=rows([[1,1],[0,2]])
    report=g.analyze(graph,(0,1),g.make_scale(0),
                     {0:rational(1,[1],(3,2)),1:critical()})
    assert [r['spectral'] for r in report['components']]==[1,2]
    assert report['components'][0]['exclusion']==2
    assert zeros(report)=={0:False,1:False}
    assert [sum(1 for _ in row) for row in graph]==[2,2]  # (1,1) is an exact ray.
    with pytest.raises(g.InvalidCertificate,match='inconclusive'):
        g.require_zero_certificate(report)


def test_critical_and_supercritical_ancestor_rules():
    two=g.make_scale(0)
    upper_critical=g.analyze(rows([[2,1],[0,2]]),(0,1),two,{0:critical(),1:critical()})
    assert zeros(upper_critical)=={0:False,1:True}
    upper_super=g.analyze(rows([[3,1],[0,2]]),(0,1),two,
                         {0:rational(3,[1],(3,1)),1:critical()})
    assert zeros(upper_super)=={0:True,1:True}
    # A supercritical child is zero; that alone does not kill a critical parent.
    lower_super=g.analyze(rows([[2,1],[0,3]]),(0,1),two,
                         {0:critical(),1:rational(3,[1],(3,1))})
    assert zeros(lower_super)=={0:False,1:True}


def test_unreachable_critical_component_and_discarded_incoming_equations():
    two=g.make_scale(0)
    report=g.analyze(rows([[2,0],[0,1]]),(1,),two,{0:critical()})
    assert report['root_zero']==(True,)
    full=rows([[0,1,0],[0,2,0],[0,1,2]])
    report=g.analyze(full,(0,),two,{1:critical(),2:critical()})
    assert zeros(report)=={0:True,1:True,2:False}
    restricted=rows([[0,1],[0,2]])
    smaller=g.analyze(restricted,(0,),two,{1:critical()})
    assert smaller['root_zero']==(False,)
    assert [sum(Q(1,2) if j==0 else Q(1) for j in row) for row in restricted]==[1,2]


def test_signed_theta_eigenvector_is_not_a_positive_critical_witness():
    matrix=[[3,1],[1,3]]
    two=g.make_scale(0)
    report=g.analyze(rows(matrix),(0,1),two)
    assert report['components'][0]['attempts']==((101,1,0),(103,1,0),(107,1,0))
    assert report['root_zero']==(False,False)
    report=g.analyze(rows(matrix),(0,1),two,{0:rational(3,[1,1],(4,1))})
    assert report['root_zero']==(True,True)
    for weights in (((Q(1),),(Q(-1),)),((Q(1),),(Q(1),))):
        with pytest.raises(g.InvalidCertificate):
            g.witness_status(matrix,two,critical(weights))


def test_actual_cubic_critical_block_and_nonperron_cubic_factor():
    scale=g.make_scale()
    square=[list(row) for row in g.source.mm(g.source.M,g.source.M)]
    perron=((Q(3,5),Q(-4,5),Q(1,5)),(Q(0),Q(1)),(Q(-2,5),Q(-4,5),Q(1,5)))
    report=g.analyze(rows(square),(0,1,2),scale,{0:critical(perron)})
    assert report['components'][0]['spectral']==2
    assert report['components'][0]['attempts']==((101,0,0),(103,0,0),(107,0,0))
    assert report['root_zero']==(False,False,False)
    doubled=[[square[i%3][j%3]+int(i==j) if i//3==j//3 else int(i%3==j%3)
              for j in range(6)] for i in range(6)]
    report=g.analyze(rows(doubled),(0,),scale,
                     {0:rational(3,[3,6,2,3,6,2],(7,1))})
    assert report['components'][0]['exclusion']==0
    assert all(rank<6 and det==0 for _,rank,det in report['components'][0]['attempts'])
    assert report['components'][0]['spectral']==3 and report['complete_zero_certificate']
    with pytest.raises(g.InvalidCertificate):
        g.witness_status(doubled,scale,critical(perron+tuple(tuple(-c for c in p) for p in perron)))


def test_bad_prime_multiplicity_and_minimal_polynomial_controls():
    polynomial=g.polynomial_matrix([[1]])
    assert polynomial==[[-5]]
    assert g.modular_rank_det(polynomial,5)==(0,0)
    assert g.modular_rank_det(polynomial,101)==(1,96)
    assert g.modular_rank_det(g.polynomial_matrix([[0]]),2)==(0,0)
    assert g.modular_rank_det(g.polynomial_matrix([[0]]),3)==(1,2)
    two=g.make_scale(0)
    assert g.analyze([[0,0]],(0,),two)['root_zero']==(False,)
    assert g.analyze([[0]],(0,),two)['root_zero']==(True,)
    # An annihilator that is not minimal cannot justify a degree shortcut.
    forged=replace(two,polynomial=(6,-5,1))
    with pytest.raises(g.InvalidCertificate,match='scale'):
        g.analyze([[0,0]],(0,),forged)
    with pytest.raises(g.InvalidCertificate):
        g.authenticate_scale(replace(g.make_scale(),lower=Q(0)))


def test_budget_refusal_stays_unresolved_without_weight_fallback():
    obj=g.graph(3)
    report=g.analyze(obj.rows,(0,1,2),block_budget=512)
    refused=[r for r in report['components'] if r['budget_refused']]
    assert len(refused)==1 and len(refused[0]['members'])==622
    assert not refused[0]['attempts'] and not report['complete_zero_certificate']
    with pytest.raises(g.InvalidCertificate,match='inconclusive'):
        g.require_zero_certificate(report)
    for cap in (0,769,True):
        with pytest.raises(g.InvalidCertificate):
            g.analyze([[0]],(0,),block_budget=cap)
    with pytest.raises(g.InvalidCertificate):
        g.analyze([[0]],(0,),primes=(101,))


def test_malformed_graph_matrix_and_witness_inputs_refuse():
    for graph in ([],[[1]],[[True]],[[0]*82],[[0],[-1]],[[0],[2]]):
        with pytest.raises(g.InvalidCertificate):
            g.analyze(graph,(0,))
    for matrix in ([[1,2]],[[True]],[[Q(1)]],[[1.0]],[]):
        with pytest.raises(g.InvalidCertificate):
            g.polynomial_matrix(matrix)
    for prime in (1,4,9,True,101.0):
        with pytest.raises(g.InvalidCertificate):
            g.modular_rank_det([[1]],prime)
    for witness in (rational(1,[0],(1,1)),rational(1,[True],(1,1)),
                    rational(1,[1],(0,1)),rational(1,[1],(1,0)),
                    rational(1,[1],(3,1)),rational(3,[1],(3,1)),
                    rational(True,[1],(1,1)),critical(((1.0,),))):
        with pytest.raises(g.InvalidCertificate):
            g.witness_status([[2]],g.make_scale(0),witness)


def test_complete_source_and_report_tampering_refuses():
    obj,report=g.reference(0)
    mutated=deepcopy(obj.rows)
    victim=next(i for i,row in enumerate(mutated) if len(set(row))<len(row))
    mutated[victim]=list(dict.fromkeys(mutated[victim]))
    with pytest.raises(g.InvalidCertificate,match='occurrence'):
        g.authenticate_source_report(0,obj.states,mutated,report)
    states=obj.states.copy()
    states[0]=(0,1,1,0,0)
    with pytest.raises(g.InvalidCertificate,match='occurrence'):
        g.authenticate_source_report(0,states,obj.rows,report)
    for key,value in (('zero',False),('members',(0,)),('dag',()),('attempts',((101,143,78),))):
        altered=deepcopy(report)
        altered['components'][0][key]=value
        with pytest.raises(g.InvalidCertificate,match='certificate mismatch'):
            g.authenticate_report(obj.rows,(0,1,2),altered)


def test_returned_graph_and_report_cannot_poison_authentication_cache():
    # This was a real review finding: mutable cached graphs previously made
    # the altered graph its own expected reference. Cache only immutable data.
    obj=g.graph(0)
    obj.rows=[[] for _ in obj.states]
    forged=g.analyze(obj.rows,(0,1,2))
    assert forged['complete_zero_certificate']
    with pytest.raises(g.InvalidCertificate,match='occurrence'):
        g.authenticate_source_report(0,obj.states,obj.rows,forged)
    expected_obj,report=g.reference(0)
    expected_obj.rows[0].clear()
    report['components'][0]['zero']=False
    report['root_zero']=(False,False,False)
    fresh,expected=g.reference(0)
    assert len(fresh.rows[0])>0 and expected['root_zero']==(True,True,True)
    assert expected['components'][0]['zero']
    assert sum(map(len,fresh.rows))==21151


def test_old_weight_constructors_are_never_consumed(monkeypatch):
    def forbidden(*args,**kwargs):
        raise AssertionError('earlier weight certificate was consumed')
    monkeypatch.setattr(g.source,'reference',forbidden)
    monkeypatch.setattr(g.source,'construct_weights',forbidden)
    obj=g.source.build_graph(0)
    report=g.analyze(obj.rows,(0,1,2))
    assert len(obj.states)==3664 and report['complete_zero_certificate']


def test_full_packet_authentication_and_committed_receipt():
    packet='\n'.join(g.packet_lines())+'\n'
    expected=g.receipt()
    assert expected['total_components']==40793
    assert expected['degree_exclusions']==40765 and expected['modular_exclusions']==28
    assert expected['zero_states']==43915 and expected['total_edges']==253395
    assert expected['previous_positive_weights_consumed'] is False
    assert g.verify_native(packet)==expected
    assert json.loads((EVIDENCE/'receipt.json').read_text())==expected
    for bad in (packet.rsplit('\n',2)[0]+'\n',packet+'dag 11 0 0\n',
                packet.replace('row 0 0 ','row 0 1 ',1),
                packet.replace('modtry 0 0 101 143 79','modtry 0 0 101 143 78',1),
                packet.replace('scale 1 -4 5 -7 1','scale 1 -3 5 -7 1',1)):
        with pytest.raises(g.InvalidCertificate):
            g.verify_native(bad)
    # The oracle-generated packet is parser calibration, not native evidence.


def test_actual_native_packet_when_supplied():
    path=os.environ.get('PSC_OVERLAP_SCC_NATIVE_OUTPUT')
    if not path:
        pytest.skip('native output not supplied; no new native parity claim')
    assert g.verify_native(Path(path).read_text())==g.receipt()


def test_archived_native_packet_is_complete_and_replayable():
    packet=gzip.decompress((EVIDENCE/'native-packet.txt.gz').read_bytes()).decode('ascii')
    assert g.verify_native(packet)==g.receipt()


def test_optimized_python_cannot_bypass_acceptance():
    script=(f'import sys;sys.path.insert(0,{str(ORACLES)!r});'
            "import c4_overlap_scc_obstruction as g;g.verify_native('schema '+g.SCHEMA+'\\n');print('CERTIFIED')")
    result=subprocess.run([sys.executable,'-O','-c',script],capture_output=True,text=True)
    assert result.returncode!=0 and not result.stdout
    assert 'record count mismatch' in result.stderr
