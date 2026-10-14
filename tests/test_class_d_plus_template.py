"""Independent plus-line closure and finite-prefix replay with frozen sources."""
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-d-plus-template-2026-10-14'
spec = importlib.util.spec_from_file_location('plus_boundary_oracle', ROOT / 'oracles/python/class_d_boundary_template.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_complete_plus_replay_and_rank_certificate():
    actual = json.loads(json.dumps(oracle.report(1)))
    assert actual == json.loads((PACKET / 'oracle.json').read_text())
    assert (actual['symbolic_floor'], actual['symbolic_vertices'], actual['symbolic_directed_edges'], actual['max_half_depth']) == (7, 718, 4326, 6)
    assert [r['a'] for r in actual['finite_prefix']] == list(range(7))
    assert [r['states'] for r in actual['finite_prefix']] == [1026,977,887,868,746,726,718]
    assert all(r['missing'] == 0 and r['max_half_depth'] == 6 for r in actual['finite_prefix'])
    assert actual['finite_prefix'][0]['r'] == 0
    vertices, edges, ranks = actual['vertices'], actual['adjacency'], actual['depths']
    assert len({tuple(v) for v in vertices}) == len(vertices)
    assert [ranks.count(i) for i in range(7)] == [6,27,102,243,196,136,8]
    reached = set(actual['seeds'])
    pending = list(reached)
    while pending:
        for child in edges[pending.pop()]:
            if child not in reached:
                reached.add(child)
                pending.append(child)
    assert reached == set(range(len(vertices)))
    for i, vertex in enumerate(vertices):
        assert (ranks[i] == 0) == (vertex[2:] == [0, 0, 0])
        if ranks[i] > 0:
            assert any(ranks[j] == ranks[i]-1 for j in edges[i])


def test_branch_sign_empty_run_and_future_range_change():
    assert oracle.sign((1,-1,0),7,1) == 1
    assert oracle.sign((1,-1,0),7,-1) == -1
    with pytest.raises(ValueError, match='empty run'):
        oracle.build(0,s=1)
    with pytest.raises(oracle.Undecided):
        oracle.build(6,s=1)
    with pytest.raises(oracle.Undecided):
        oracle.geq((1,-7),6)
    assert oracle.geq((1,-7),7)
    with pytest.raises(RuntimeError, match='STATE_BUDGET_EXHAUSTED'):
        oracle.build(7,1,1)
    with pytest.raises(ValueError, match='branch'):
        oracle.build(7,s=0)


def test_plus_support_crosscheck_rejects_edge_deletion():
    graph = oracle.build(7,s=1)
    altered = copy.deepcopy(graph)
    parent = next(v for v in sorted(altered) if altered[v])
    altered[parent].remove(min(altered[parent]))
    assert set(altered) == set(graph)
    with pytest.raises(ValueError, match='directed support differs'):
        oracle.check_exact_support(altered,7,1)


def test_sealed_packet_and_frozen_source_bytes():
    for line in (PACKET / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ',1)
        assert hashlib.sha256((PACKET / name).read_bytes()).hexdigest() == digest
    pins = json.loads((PACKET / 'source-digests.json').read_text())
    sources = json.loads(gzip.decompress((PACKET / 'sources.json.gz').read_bytes()))['sources']
    assert set(pins) == set(sources)
    for name, digest in pins.items():
        assert hashlib.sha256(sources[name].encode()).hexdigest() == digest
