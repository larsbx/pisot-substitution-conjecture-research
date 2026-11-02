"""Independent finite certificate acceptance and adversarial controls."""
from copy import deepcopy
from pathlib import Path
import runpy
import pytest

m = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                      'oracles/python/class_a_finite_certificates.py'))
r = m['raw']


@pytest.fixture(scope='module')
def packet():
    # Independent generator used ONLY as calibration input for this checker.
    g = m['Geometry'](-1, 3, 0)
    _, seeds = r['swap_sources'](g)
    states, ids, adj = r['complete_graph'](g, seeds)
    reps = [v for v, w in enumerate(states) if v <= ids[r['reverse'](w)]]
    orbit = {v: orb for orb, rep in enumerate(reps)
             for v in (rep, ids[r['reverse'](states[rep])])}
    qa = [[(orbit[dst], i, j) for dst, i, j in adj[rep]] for rep in reps]
    roots = [v for v, w in enumerate(states) if r['coincidence'](w)]
    od, _ = r['backwards'](adj, roots)
    qd, _ = r['backwards'](qa, [orbit[v] for v in roots])
    vertices = {v: (w, orbit[v], od[v], 0 if v in roots else
                   len(g.words[w[0]]) * len(g.words[w[1]])) for v, w in enumerate(states)}
    edges = [(v, *edge) for v, row in enumerate(adj) for edge in row]
    orbits = {orb: (rep, qd[orb], next((e for e, (dst, _, _) in enumerate(qa[orb])
                  if qd[dst] == qd[orb] - 1), -1)) for orb, rep in enumerate(reps)}
    return dict(k=3, t=0, vertices=vertices, edges=edges, orbits=orbits,
                complete=(len(states), len(reps), len(edges), 20000000, 6000))


def test_independent_completed_specimen(packet):
    _, summary = m['verify_member'](**packet)
    assert (summary['vertices'], summary['quotient_orbits']) == (352, 177)
    assert summary['indexed_edges'] == summary['all_edge_orientation_lifts'] == 3252
    assert summary['max_terminal_distance'] == 4


def test_omitted_paired_edges_preserve_symmetry_but_fail_completeness(packet):
    bad = deepcopy(packet)
    v, dst, i, j = bad['edges'][0]
    ids = {row[0]: u for u, row in bad['vertices'].items()}
    rv = ids[r['reverse'](bad['vertices'][v][0])]
    rd = ids[r['reverse'](bad['vertices'][dst][0])]
    bad['edges'].remove((v, dst, i, j))
    bad['edges'].remove((rv, rd, j, i))
    # Earlier quotient checker still accepts this deliberately incomplete graph.
    q = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                          'oracles/python/class_a_reversal_quotient.py'))
    states = [row[0] for _, row in sorted(bad['vertices'].items())]
    adj = [[] for _ in states]
    for source, *edge in bad['edges']:
        adj[source].append(tuple(edge))
    q['quotient'](states, {w: u for u, w in enumerate(states)}, adj)
    with pytest.raises(ValueError, match='full literal occurrences'):
        m['verify_member'](**bad)


@pytest.mark.parametrize('mutation', ['original_distance', 'quotient_distance', 'fake_terminal',
    'fabricated_path', 'terminal_path', 'negative_index', 'huge_index', 'duplicate_edge',
    'wrong_target', 'pair_count', 'missing_seed', 'missing_orbit', 'cap_pair', 'cap_state'])
def test_refusals(packet, mutation):
    bad = deepcopy(packet)
    if mutation in ('original_distance', 'fake_terminal'):
        w, orb, d, pairs = bad['vertices'][0]
        bad['vertices'][0] = (w, orb, 0 if mutation == 'fake_terminal' else d+1, pairs)
    elif mutation == 'quotient_distance':
        rep, d, e = bad['orbits'][0]
        bad['orbits'][0] = (rep, d+1, e)
    elif mutation == 'fabricated_path':
        rep, d, _ = bad['orbits'][0]
        bad['orbits'][0] = (rep, d, 123456)
    elif mutation == 'terminal_path':
        orb = next(o for o, (_, d, _) in bad['orbits'].items() if d == 0)
        rep, d, _ = bad['orbits'][orb]
        bad['orbits'][orb] = (rep, d, 0)
    elif mutation in ('negative_index', 'huge_index', 'wrong_target'):
        v, dst, i, j = bad['edges'][0]
        bad['edges'][0] = (v, (dst+1) % len(bad['vertices']), i, j) if mutation == 'wrong_target' else (
            v, dst, -1 if mutation == 'negative_index' else 123456, j)
    elif mutation == 'duplicate_edge':
        bad['edges'].insert(0, bad['edges'][0])
    elif mutation == 'pair_count':
        w, orb, d, pairs = bad['vertices'][0]
        bad['vertices'][0] = (w, orb, d, pairs-1)
    elif mutation == 'missing_seed':
        del bad['vertices'][0]
    elif mutation == 'missing_orbit':
        del bad['orbits'][0]
    elif mutation == 'cap_pair':
        bad['pair_cap'] = 1
    else:
        bad['state_cap'] = 18
    with pytest.raises((ValueError, r['IncompleteGraph'])):
        m['verify_member'](**bad)


def test_truncated_and_fabricated_native_receipts_rejected():
    for data in (b'', b'RC_NEGATIVE_CONTROLS_PASS 16\n',
                 b'RC_NEGATIVE_CONTROLS_PASS 16\nRC_NEGATIVE_CONTROLS_PASS 16\n',
                 b'RC_FAKE 0 0 0\n'):
        with pytest.raises(ValueError):
            m['parse_native'](data)


def test_archived_packet_rejects_missing_or_duplicate_specimens():
    for packet in ({'schema': 'unknown', 'members': []},
                   {'schema': 'psc-class-a-finite-v1', 'members': []},
                   {'schema': 'psc-class-a-finite-v1', 'members': [{'k': 0, 't': 0}]*22}):
        with pytest.raises(ValueError):
            m['replay_certificate'](packet)
