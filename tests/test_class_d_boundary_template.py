"""Independent complete-template replay, graph integrity and countercontrols."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-d-minus-template-2026-10-14'
spec = importlib.util.spec_from_file_location('boundary_template_oracle', ROOT / 'oracles/python/class_d_boundary_template.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_complete_symbolic_replay_and_finite_prefix():
    actual = json.loads(json.dumps(oracle.report()))
    assert actual == json.loads((PACKET / 'oracle.json').read_text())
    assert (actual['symbolic_floor'], actual['symbolic_vertices'], actual['symbolic_directed_edges'], actual['max_half_depth']) == (4, 145, 781, 4)
    assert [r['a'] for r in actual['finite_prefix']] == list(range(4))
    assert all(r['missing'] == 0 and r['max_half_depth'] == 4 for r in actual['finite_prefix'])
    vertices, edges, ranks = actual['vertices'], actual['adjacency'], actual['depths']
    assert len({tuple(v) for v in vertices}) == len(vertices)
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


def test_uniform_signs_refuse_a_future_change():
    assert oracle.sign((0, 0, 0), 4) == 0
    assert oracle.sign((1, 2, -4), 4) == 1
    assert oracle.sign((-1, -2, 4), 4) == -1
    with pytest.raises(oracle.Undecided):
        oracle.sign((1, 2, -4), 0)
    assert oracle.geq((1, -3), 3)
    assert not oracle.geq((-1, 2), 3)
    with pytest.raises(oracle.Undecided):
        oracle.geq((1, -3), 2)
    with pytest.raises(oracle.Undecided):
        oracle.geq((-1, 2), 1)


def test_lowered_floor_and_exhausted_budget_refuse():
    with pytest.raises(oracle.Undecided):
        oracle.build(3)
    with pytest.raises(RuntimeError, match='STATE_BUDGET_EXHAUSTED'):
        oracle.build(4, 1)
    for floor, cap in [(-1, 20000), (65, 20000), (4, 0), (4, 20001)]:
        with pytest.raises(ValueError):
            oracle.build(floor, cap)


def test_equal_vertices_do_not_let_altered_support_pass():
    graph = oracle.build()
    altered = copy.deepcopy(graph)
    parent = next(v for v in sorted(altered) if altered[v])
    altered[parent].remove(min(altered[parent]))
    assert set(altered) == set(graph)
    with pytest.raises(ValueError, match='directed support differs'):
        oracle.check_exact_support(altered, 4)


def test_packet_bytes_and_sources_are_pinned():
    for line in (PACKET / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        assert hashlib.sha256((PACKET / name).read_bytes()).hexdigest() == digest
    for name, digest in json.loads((PACKET / 'source-digests.json').read_text()).items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
