from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_b3_children.py'))


def test_two_complete_stars_selected_exit_and_source_reconciliation():
    p = o['probe']()
    assert (p['members'], p['source_cells'], p['pairs']) == (117, 234, 122616)
    assert (p['accepted'], p['path_edges'], p['image_labels']) == (6760, 468, 20)
    assert p['typed_exit_two_edges'] and p['candidate41_escape_via_H1']
    assert not p['all_direct_children_productivity_proved']
    assert (p['outgoing_registered_stars'], p['outgoing_registered_exits']) == (10, 10)
    assert (p['old_R3_D3_outgoing_registered_stars'], p['old_R3_D3_outgoing_registered_exits']) == (18, 16)
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal']) == (21, 23)
    assert r['after_unregistered'] == 18


def test_endpoint_types_clips_and_uniform_ancestry_and_exit():
    for k in range(3):
        for t in range(4):
            g = o['Geometry'](-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            assert g.child(o['r3']['R3'], d+1, 0) == o['B3']
            assert g.child(o['B3'], 0, n+2) == o['eh']['BASE'][1] not in o['r3']['candidate'](True)
            assert o['predicted'](0, g, n-1, A+1) == (t == 0)
            assert o['predicted'](0, g, n, A+1) == (t <= 1)
            if t == 0:
                assert 2*n+3 == A+1
                assert g.child(o['B3'], n, 2*n+3) == (1, 0, -1, -1, 3)
                assert g.child(o['B3'], n-1, A+1) == (2, 0, -1, -1, 4)
                assert g.child(o['B3'], n-1, A+1) != (2, 2, -1, -1, 4)
            elif t == 1:
                assert 2*n+4 == A+1
                assert g.child(o['B3'], n, 2*n+4) == (1, 0, -1, -1, 4)
            else:
                assert g.child(o['B3'], n, 2*n+4) == (1, 2, -1, -1, 4)
    assert o['interface']((2, 2, -1, 1, 2), True) == 'T2'
    assert not o['registered_exit']((2, 2, -1, 1, 2), True)


def test_every_native_registry_row_matches_independent_source_inventory():
    output = (ROOT/'evidence/class-a-boundary-b3-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    lines = [line for line in output.splitlines() if line.startswith('CLASS_A_B3_REGISTRY ')]
    assert len(lines) == 41
    for bad in ('\n'.join(lines[:-1]), '\n'.join(lines+[lines[0]])):
        with pytest.raises(ValueError):
            o['verify_native_registry'](bad)
    changed = list(lines)
    fields = changed[0].split()
    fields[-1] = '0' if fields[-1] == '1' else '1'
    changed[0] = ' '.join(fields)
    with pytest.raises(ValueError):
        o['verify_native_registry']('\n'.join(changed))


def test_refuse_bad_parameters_pairs_offsets_stars_and_paths():
    g = o['Geometry'](-1, 0, 0)
    for kind, i, j in [(2, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 5, 0), (0, 0, 10)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    plus = o['Geometry'](1, 0, 0)
    for fn in (lambda: o['predicted'](0, plus, 0, 0), lambda: o['path'](0, plus)):
        with pytest.raises(ValueError):
            fn()
    # Legal but disjoint FR(n+1), not an overlap merely because it is indexed.
    assert not g.interior(g.child(o['B3'], 0, g.n+1))
    assert not o['predicted'](0, g, 0, g.n+1)
    wrong = o['eh']['BASE'][2]
    assert g.interior(wrong) and wrong in o['envelope']()
    packet = o['path'](0, g)
    for mode in range(4):
        bad = list(packet)
        if mode == 0:
            bad[0] = (0, g.n+2, wrong)
        elif mode == 1:
            bad[1] = (2, 1, o['C'])
        elif mode == 2:
            bad[1] = (1, 2, (2, 0, 0, 0, 0))
        else:
            bad.pop()
        for want in (packet, bad):
            with pytest.raises(ValueError):
                o['verify_path'](o['B3'], g, bad, want)
    edges = list(g.edges(o['B3']))
    o['verify_star'](0, g, edges)
    for broken in (edges + [edges[0]], edges[:-1], [edges[0]] + edges[:-1]):
        with pytest.raises(ValueError):
            o['verify_star'](0, g, broken)
