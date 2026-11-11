"""Independent literal reconstruction and adversarial certificate calibration."""
from copy import deepcopy
from fractions import Fraction as Q
from functools import lru_cache
import gzip
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT/'oracles/python/c4_pair_overlap_new_incidence.py'
spec = importlib.util.spec_from_file_location('new_incidence', PATH)
g = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = g
spec.loader.exec_module(g)

EXPECTED_STATES = (3664,3649,3667,3667,3653,3667,3693,3674,3643,3643,3646,3649)
EXPECTED_EDGES = (21151,21164,21103,21033,21186,21168,21144,21203,20976,21054,21095,21118)
EXPECTED_SWEEPS = (51,123,41,520,47,50,467,47,52,41,117,67)


@pytest.mark.parametrize('index', range(12))
def test_complete_new_source_graph_and_uniform_certificate(index):
    graph, weights, sweeps, gap = g.reference(index)
    model = g.certify_model(index)
    assert model['literal_digits'] == 178973
    assert model['carrier_capacity'] == 178002
    assert len(graph.states) == EXPECTED_STATES[index]
    assert sum(map(len, graph.rows)) == EXPECTED_EDGES[index]
    assert sweeps == EXPECTED_SWEEPS[index]
    assert gap == g.verify_weights(graph, weights) == 125
    assert graph.carrier_rejections == 0
    assert any(len(set(row)) < len(row) for row in graph.rows)
    assert not any(s[0] == s[1] and s[2:] == (0,0,0) for s in graph.states)
    assert max(weights) <= 1000000
    for w in weights[:3]:
        assert 256*w*Q(125,126)**3072 < Q(1,10)


def test_exact_chart_typed_carrier_and_all_retained_strips():
    assert g.certify_algebra() and g.certify_uniform_upper_tenth()
    assert len({g.source_images(i) for i in range(12)}) == 12
    assert list(g.carrier_boxes()) == [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
    assert all(box == ((-15,15),(-14,14),(-16,16)) for box in g.carrier_boxes().values())
    for value, floor, ceiling in ((Q(7,3),2,3),(Q(-7,3),-3,-2),(Q(-2),-2,-2),(Q(0),0,0)):
        assert (g.floor_q(value),g.ceil_q(value)) == (floor,ceiling)
    # The strict strip is verified on every distinct generated state, not
    # asserted as an emptiness rule for arbitrary shifted intersections.
    states = {state for index in range(12) for state in g.reference(index)[0].states}
    for c,d,*z in states:
        h = (Q(0),)*3
        for coefficient, value in zip(g.ELL,z):
            h = g.fadd(h,g.fscale(coefficient,value))
        assert g.interval(g.fadd(h,g.ELL[c]))[0] > 0
        assert g.interval(g.fadd(g.ELL[d],g.fscale(h,-1)))[0] > 0
        assert not g.outside_carrier((c,d,*z))


def test_independent_minors_rescanned_prefixes_and_every_occurrence_row():
    # A second reconstruction uses cofactors, rescanned literal prefixes and
    # Fraction interval pruning, independently of the Gaussian/running oracle
    # and Mojo's checked adjugate/streamed prefix implementation.
    square = g.mm(g.M,g.M)
    def minor(i,j):
        rows = [[square[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
        return rows[0][0]*rows[1][1]-rows[0][1]*rows[1][0]
    adj = tuple(tuple((-1)**(i+j)*minor(j,i) for j in range(3)) for i in range(3))
    det = sum(square[0][j]*(-1)**j*minor(0,j) for j in range(3))
    assert det == 4
    assert adj == ((1,-1,2),(4,0,-4),(-6,2,4))
    identity4 = tuple(tuple(4*int(i==j) for j in range(3)) for i in range(3))
    assert g.mm(square,adj) == g.mm(adj,square) == identity4
    @lru_cache(maxsize=None)
    def rejected(z):
        for coordinate,endpoints in ((0,(556693,556694)),(2,(398160,398161))):
            bounds = [Q(z[coordinate])-Q(v,1000000)*z[1] for v in endpoints]
            if min(bounds)>16 or max(bounds)<-16:
                return True
        return False
    for index in range(12):
        graph = g.reference(index)[0]
        lookup = {s:i for i,s in enumerate(graph.states)}
        sigma = g.source_images(index)
        digits = []
        for parent in range(3):
            word = ''.join(sigma[int(c)] for c in sigma[parent])
            for position, letter in enumerate(word):
                prefix = tuple(word[:position].count(str(c)) for c in range(3))
                digits.append((int(letter),parent,prefix))
        by_letter = [tuple(x for x in digits if x[0]==c) for c in range(3)]
        counts = [0,0,0]
        for row_id,(c,d,*z) in enumerate(graph.states):
            expected = []
            for _,parent,p in by_letter[c]:
                for _,other,r in by_letter[d]:
                    delta = tuple(z[k]+r[k]-p[k] for k in range(3))
                    nums = tuple(sum(adj[i][j]*delta[j] for j in range(3)) for i in range(3))
                    if any(n%det for n in nums):
                        counts[0] += 1
                        continue
                    shift = tuple(n//det for n in nums)
                    if rejected(shift):
                        counts[1] += 1
                        continue
                    child = min((parent,other,*shift),(other,parent,*(-v for v in shift)))
                    if any(abs(value)>radius for value,radius in zip(child[2:],(15,14,16))):
                        counts[2] += 1
                        continue
                    assert child in lookup
                    expected.append(lookup[child])
            assert expected == graph.rows[row_id]
        assert counts == [graph.residue_rejections,graph.box_rejections,graph.carrier_rejections]


def test_closed_boundaries_unsupported_sources_and_budget_refusals():
    assert not g.outside_box((16,0,16))
    assert not g.outside_box((-16,0,-16))
    assert g.outside_box((17,0,0)) and g.outside_box((0,0,-17))
    assert not g.outside_carrier((0,1,15,14,16))
    assert g.outside_carrier((0,1,16,14,16))
    assert g.canonical(2,0,(1,-2,3)) == (0,2,-1,2,-3)
    assert g.canonical(1,1,(1,0,0)) == (1,1,-1,0,0)
    for index in (-1,12,True):
        with pytest.raises(g.InvalidCertificate):
            g.build_graph(index)
    with pytest.raises(g.InvalidCertificate,match='inconclusive'):
        g.build_graph(0,state_cap=3)
    with pytest.raises(g.InvalidCertificate,match='inconclusive'):
        g.construct_weights(g.reference(0)[0],iteration_cap=1)
    for num,den in ((0,20),(-1,20),(125,0),(True,20),(126,20)):
        with pytest.raises(g.InvalidCertificate):
            g.construct_weights(g.reference(0)[0],num,den)


def test_failed_stronger_rate_is_preserved_as_inconclusive():
    for index in (3,6):
        with pytest.raises(g.InvalidCertificate,match='weight budget exhausted; inconclusive'):
            g.construct_weights(g.reference(index)[0],124,20)
        assert g.reference(index)[3] == 125


def test_omitted_multiplicity_mutated_state_and_false_weights_refuse():
    graph, weights, _, _ = g.reference(0)
    rows = deepcopy(graph.rows)
    victim = next(i for i,row in enumerate(rows) if len(set(row))<len(row))
    rows[victim] = list(dict.fromkeys(rows[victim]))
    with pytest.raises(g.InvalidCertificate,match='multiplicities'):
        g.validate_supplied_graph(0,graph.states,rows,weights)
    states = graph.states.copy()
    states[0] = (0,1,1,0,0)
    with pytest.raises(g.InvalidCertificate,match='inventory'):
        g.validate_supplied_graph(0,states,graph.rows,weights)
    for value in (0,-1,True,1000001):
        bad = weights.copy()
        bad[0] = value
        with pytest.raises(g.InvalidCertificate):
            g.verify_weights(graph,bad)
    with pytest.raises(g.InvalidCertificate):
        g.verify_weights(graph,[1]*len(weights))
    rows = deepcopy(graph.rows)
    rows[0] = [len(weights)]
    mutated = g.Graph(0,graph.states,rows,0,0,0)
    with pytest.raises(g.InvalidCertificate,match='target'):
        g.verify_weights(mutated,weights)


def test_diagonal_same_occurrence_block_cannot_pass_subcritical_weights():
    # Actual same-occurrence diagonal children have multiplicity M²[c,d].
    # This is a positive subgraph, not a claim that it exhausts all diagonal
    # paired occurrences. Any subcritical certificate for the full graph
    # would also bound this Perron-critical subgraph, which is impossible.
    square = g.power(g.M,2)
    rows = [[d for d in range(3) for _ in range(square[c][d])] for c in range(3)]
    diagonal = g.Graph(0,[(c,c,0,0,0) for c in range(3)],rows,0,0,0)
    with pytest.raises(g.InvalidCertificate,match='inconclusive'):
        g.construct_weights(diagonal)
    # Euclidean scaling alone would multiply the true lifted rate by four.
    assert Q(125,20)/g.root_bracket()[0]**2 < 1
    assert 4*Q(125,20)/g.root_bracket()[1]**2 > 1


def test_packet_authentication_and_committed_receipt():
    lines = list(g.packet_lines())
    packet = '\n'.join(lines)+'\n'
    expected = g.receipt()
    assert g.verify_native(packet) == expected
    for bad in ('\n'.join(lines[:-1]),'\n'.join(lines+[lines[-1]]),
                packet.replace('row 0 0 ','row 0 1 ',1),
                packet.replace('model 8 8 ','model 7 8 ',1)):
        with pytest.raises(g.InvalidCertificate):
            g.verify_native(bad)
    path = ROOT/'evidence/c4-pair-overlap-new-incidence-2026-11-05/receipt.json'
    assert json.loads(path.read_text()) == expected
    # This self-generated packet is parser calibration, never native evidence.


def test_actual_native_packet_when_supplied():
    path = os.environ.get('PSC_NEW_INCIDENCE_NATIVE_OUTPUT')
    if not path:
        pytest.skip('native output not supplied; no native parity claim')
    assert g.verify_native(Path(path).read_text()) == g.receipt()


def test_archived_native_packet_is_complete_and_replayable():
    path = ROOT/'evidence/c4-pair-overlap-new-incidence-2026-11-05/native-packet.txt.gz'
    packet = gzip.decompress(path.read_bytes()).decode('ascii')
    assert g.verify_native(packet) == g.receipt()


def test_optimized_python_cannot_bypass_acceptance():
    script = (f'import sys;sys.path.insert(0,{str(PATH.parent)!r});'
              "import c4_pair_overlap_new_incidence as g;g.verify_native('schema '+g.SCHEMA+'\\n');print('CERTIFIED')")
    result = subprocess.run([sys.executable,'-O','-c',script],capture_output=True,text=True)
    assert result.returncode != 0 and not result.stdout
    assert 'preamble mismatch' in result.stderr
