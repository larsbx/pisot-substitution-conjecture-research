from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_r3_children.py'))


def test_four_complete_stars_selected_exits_and_source_reconciliation():
    p = o['probe']()
    assert p['members'] == 117 and p['source_cells'] == 468
    assert p['pairs'] == 253188 and p['accepted'] == 14014 and p['path_edges'] == 1440
    assert p['image_labels'] == 36
    assert p['candidate39_not_forward_closed'] and p['candidate41_not_forward_closed']
    assert not p['all_direct_children_productivity_proved']
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal']) == (17, 19)
    assert r['after41_registered_including_terminal'] == 21 and r['after41_unregistered'] == 20
    image = o['envelope']()
    assert sum(o['interface'](w, True) is not None for w in image) == 16
    assert sum(o['registered_exit'](w, True) for w in image) == 14


def test_actual_endpoints_parameter_clips_and_carrier_escapes():
    for t in range(4):
        g = o['Geometry'](-1, 0, t)
        A, n = g.n+g.d, g.n
        assert g.child(o['X'], A+1, n) == o['R3']
        assert g.child(o['R3'], A+1, n) == o['D3'] not in o['candidate']()
        assert g.child(o['D3'], t+1, 1) == o['pp']['BASE'][0] not in o['candidate'](True)
        assert o['predicted'](2, g, 0, 0) == (t <= 1)
        assert o['predicted'](2, g, 0, 1) == (t == 0)
        if n == 3:
            assert g.child(o['p3']['BASE'][0], A+1, 0) == o['p3']['BASE'][2] != o['R3']
        else:
            assert g.child(o['p3']['BASE'][0], A+1, n-3) == o['R3']
    # T2's known complete star does not register a new uniform exit here.
    assert o['interface']((2, 2, -1, 1, 2)) == 'T2'
    assert not o['registered_exit']((2, 2, -1, 1, 2))


def test_every_native_registry_row_matches_independent_source_inventory():
    output = (ROOT/'evidence/class-a-boundary-r3-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    lines = [line for line in output.splitlines() if line.startswith('CLASS_A_R3_REGISTRY ')]
    assert len(lines) == 39
    for bad in ('\n'.join(lines[:-1]), '\n'.join(lines+[lines[0]])):
        with pytest.raises(ValueError):
            o['verify_native_registry'](bad)
    changed = list(lines)
    fields = changed[0].split()
    fields[-1] = '0' if fields[-1] == '1' else '1'
    changed[0] = ' '.join(fields)
    with pytest.raises(ValueError):
        o['verify_native_registry']('\n'.join(changed))


def test_invalid_indices_disjoint_pairs_wrong_interior_targets_and_false_coincidence():
    g = o['Geometry'](-1, 0, 0)
    for kind, i, j in [(4, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 10, 0), (2, 0, 5)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    plus = o['Geometry'](1, 0, 0)
    with pytest.raises(ValueError):
        o['predicted'](0, plus, 0, 0)
    with pytest.raises(ValueError):
        o['path'](0, plus)
    assert not o['predicted'](0, g, g.d-2, 0)
    assert not g.interior(g.child(o['R3'], g.d-2, 0))
    wrong = o['pp']['BASE'][1]
    assert g.interior(wrong) and wrong in o['envelope']()
    packet = o['path'](2, g)
    for changed in [0, 1, -1]:
        bad = list(packet)
        if changed == 0:
            bad[0] = (1, 1, wrong)
        elif changed == 1:
            bad[1] = (0, 2, (0, 2, 1, 2, -3))
        else:
            bad[-1] = (1, 2, (2, 0, 0, 0, 0))
        for want in (packet, bad):
            with pytest.raises(ValueError):
                o['verify_path'](o['D3'], g, bad, want)
    with pytest.raises(ValueError):
        o['verify_path'](o['D3'], g, packet[:-1], packet[:-1])
    # A duplicate actual pair cannot stand for a second occurrence.
    edges = list(g.edges(o['R3']))
    o['verify_star'](0, g, edges)
    for broken in (edges + [edges[0]], edges[:-1], [edges[0]] + edges[:-1]):
        with pytest.raises(ValueError):
            o['verify_star'](0, g, broken)
