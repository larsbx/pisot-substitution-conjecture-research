"""Complete finite-class reconstruction. No SC witness or native pass assumed."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json
import subprocess
import sys
import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'oracles/python'))
import c4_pair_overlap_class as g

RECEIPT = json.loads((ROOT/'evidence/c4-pair-overlap-class-2026-11-05/receipt.json').read_text())


def independent_rows(index, graph, weights):
    # Independent adjugate versus producer's rational Gaussian inverse;
    # direct string-prefix counters versus producer's running counters.
    adj = ((0,-2,6),(2,0,-2),(-2,2,0))
    m2 = g.core.power(g.core.M, 2)
    assert g.core.mm(m2, adj) == g.core.mm(adj, m2) == ((4,0,0),(0,4,0),(0,0,4))
    sigma = g.source(index)
    digits = []
    for a in range(3):
        word = ''.join(sigma[int(c)] for c in sigma[a])
        for pos,c in enumerate(word):
            digits.append((int(c),a,tuple(word[:pos].count(str(i)) for i in range(3))))
    ids = {state:i for i,state in enumerate(graph.states)}
    residue_count = box_count = 0
    minimum_gap = None
    for row_id,(c,d,*offset) in enumerate(graph.states):
        targets = []
        for left,a,p in digits:
            if left != c: continue
            for right,b,q in digits:
                if right != d: continue
                vector = [offset[k]+q[k]-p[k] for k in range(3)]
                numer = [sum(adj[i][k]*vector[k] for k in range(3)) for i in range(3)]
                if any(v % 4 for v in numer):
                    residue_count += 1
                    continue
                x,y,z = [v//4 for v in numer]
                first = [Q(x)-Q(n,10**6)*y for n in (828911,828912)]
                second = [Q(z)-Q(n,10**6)*y for n in (440619,440620)]
                if min(first)>48 or max(first)<-48 or min(second)>24 or max(second)<-24:
                    box_count += 1
                    continue
                state = min((a,b,x,y,z),(b,a,-x,-y,-z))
                assert state in ids
                targets.append(ids[state])
        assert targets == graph.rows[row_id]
        gap = 102*weights[row_id]-20*sum(weights[j] for j in targets)
        assert gap > 0
        minimum_gap = gap if minimum_gap is None else min(minimum_gap,gap)
    assert (residue_count,box_count) == (graph.residue_rejections,graph.box_rejections)
    assert minimum_gap == 102


@pytest.mark.parametrize('index',range(18))
def test_complete_source_graph_receipt_and_independent_rows(index):
    graph,w,sweeps,gap = g.reference(index)
    assert g.summary(index) == RECEIPT['sources'][index]
    independent_rows(index,graph,w)
    assert not any(c==d and (x,y,z)==(0,0,0) for c,d,x,y,z in graph.states)
    assert any(len(row)>len(set(row)) for row in graph.rows)
    assert all(Q(1152*v)*Q(102,103)**2304 < Q(1,10) for v in w[:3])
    assert sweeps < 4000 and max(w) < 1000000 and gap == 102


def test_exact_domain_prefix_periods_and_enclosures():
    expected = {('1',''.join(p),tail) for p in permutations('012') for tail in ('001','010','100')}
    assert set(g.SOURCES) == expected and len(g.SOURCES) == 18
    assert [i for i in range(18) if g.prefix_periods(i)==[3]] == [12,13,15,16]
    assert all(12 % period == 0 for i in range(18) for period in g.prefix_periods(i))
    assert sum(row['chart']['literal_digits'] for row in RECEIPT['sources']) == 1000494
    assert sum(row['states'] for row in RECEIPT['sources']) == 285786
    assert sum(row['occurrence_edges'] for row in RECEIPT['sources']) == 1409729
    assert not g.outside((48,0,24)) and not g.outside((-48,0,-24))
    assert g.outside((49,0,0)) and g.outside((0,0,25))
    # Exact invariance margins, not decimal approximations.
    assert Q(13,2)+Q(473,1000)*24+Q(390,1000)*12 <= 24
    assert 4+Q(147,1000)*24+Q(344,1000)*12 <= 12


def test_false_graph_weights_and_budgets_refuse():
    for bad in (-1,18,True,0.0,'0'):
        with pytest.raises(g.core.InvalidCertificate): g.source(bad)
    with pytest.raises(g.core.InvalidCertificate): g.build_graph(0,state_cap=3)
    graph,w,_,_ = g.reference(0)
    with pytest.raises(g.core.InvalidCertificate): g.construct_weights(graph,iteration_cap=1)
    rows = deepcopy(graph.rows)
    row = next(i for i,r in enumerate(rows) if len(r)>len(set(r)))
    rows[row] = list(dict.fromkeys(rows[row]))
    with pytest.raises(g.core.InvalidCertificate):
        g.validate_supplied_graph(0,graph.states,rows,w)
    for bad in (0,-1,True,1000001):
        broken = w.copy();broken[0]=bad
        with pytest.raises(g.core.InvalidCertificate): g.core.validate_weights(graph,broken,102)
    with pytest.raises(g.core.InvalidCertificate): g.core.validate_weights(graph,w,103)
    with pytest.raises(g.core.InvalidCertificate): g.core.validate_weights(graph,[1]*len(w),102)


def test_optimized_python_and_missing_native_packet_refuse(tmp_path):
    # A missing native packet never becomes evidence, even under python -O.
    packet=tmp_path/'missing.txt';packet.write_text('wrong schema\n')
    with pytest.raises(g.core.InvalidCertificate):g.verify_native_file(packet)
    code=f"import sys;sys.path.insert(0,{str(ROOT/'oracles/python')!r});import c4_pair_overlap_class as g;g.source(True);print('CERTIFIED')"
    result=subprocess.run([sys.executable,'-O','-c',code],capture_output=True,text=True)
    assert result.returncode != 0 and not result.stdout


def test_chart_is_not_reused_outside_its_checked_box(monkeypatch):
    # Two of the new sources do not fit the old 16x8 certificate.
    g.certify_box.cache_clear()
    with monkeypatch.context() as m:
        m.setattr(g,'RADII',(16,8))
        with pytest.raises(g.core.InvalidCertificate):g.certify_box(5)
    g.certify_box.cache_clear()
    assert g.certify_box(5)['radii'] == [24,12]
