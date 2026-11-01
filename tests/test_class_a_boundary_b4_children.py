from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_b4_children.py'))


def test_two_complete_stars_three_case_exits_and_registry():
    p = o['probe']()
    assert (p['members'], p['source_cells'], p['path_source_cells']) == (117, 234, 702)
    assert (p['pairs'], p['accepted'], p['image_labels']) == (122616, 1690, 32)
    assert (p['b4_path_edges'], p['companion_path_edges'], p['path_edges']) == (1118, 1404, 2522)
    assert p['B4_typed_exit_at_most_five'] and p['image_disjoint_from_candidate41']
    assert p['all_direct_children_productive_on_t_le_1']
    assert not p['all_direct_children_productive_for_all_t_proved']
    assert not p['companion_complete_stars_proved']
    assert (p['outgoing_registered_stars'], p['outgoing_registered_exits']) == (2, 6)
    assert (p['old_R3_D3_outgoing_registered_stars'], p['old_R3_D3_outgoing_registered_exits']) == (20, 18)
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal']) == (23, 25)
    assert r['after_unregistered'] == 16


def test_actual_endpoint_types_and_singleton_child_productivity():
    for k in range(4):
        for t in range(4):
            g = o['Geometry'](-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            for flip in range(2):
                w = o['source'](flip)
                assert g.child(o['b3']['r3']['source'](flip), 0 if flip else d+2, d+2 if flip else 0) == w
                packet = o['path'](flip, g)
                o['verify_path'](w, g, packet, packet)
                if t <= 1:
                    assert set(g.edges(w)) == {packet[0]}
            if t == 0:
                assert 2*n+4 == A+2
                with pytest.raises(ValueError):
                    g.child(o['BASE'][0], 0, 2*n+4)
            elif t == 1:
                assert 2*n+4 == A+1
                assert g.child(o['BASE'][0], 0, 2*n+4) == o['reverse'](o['e2']['BASE'][1]) != o['BASE'][2]
            else:
                assert g.child(o['BASE'][0], 0, 2*n+4) == o['BASE'][2]


def test_exact_half_separator_changes_indices_not_total_count():
    for k, t, high in [(0, 0, False), (1, 1, False), (2, 2, True), (5, 4, False), (0, 4, True)]:
        g = o['Geometry'](-1, k, t)
        assert o['high'](k, t) == high
        assert g.sign((-2*g.n-5, 2, 0)) == (1 if high else -1)
        assert len(list(g.edges(o['BASE'][0]))) == max(1, 2*t-1)
        if t == 4:
            assert o['predicted'](0, g, 0, g.n+g.d+1) == high
    with pytest.raises(ValueError):
        o['high'](-1, 0)


def test_exit_certificates_do_not_register_companion_complete_stars():
    for kind in range(2, 6):
        w = o['source'](kind)
        assert o['interface'](w, True) is None
        assert o['exit_interface'](w, True) in ('D0', 'F4')
        g = o['Geometry'](-1, 0, 0)
        p = o['path'](kind, g)
        o['verify_path'](w, g, p, p)
        with pytest.raises(ValueError):
            o['predicted'](kind, g, 0, 0)
        with pytest.raises(ValueError):
            o['verify_star'](kind, g, [])
    assert o['interface']((2, 2, -1, 1, 2), True) == 'T2'
    assert o['exit_interface']((2, 2, -1, 1, 2), True) is None


def test_all_73_native_registry_rows_match_independent_interfaces():
    output = (ROOT/'evidence/class-a-boundary-b4-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix, count in [('CLASS_A_B4_CANDIDATE_REGISTRY ', 41), ('CLASS_A_B4_IMAGE_REGISTRY ', 32)]:
        lines = [line for line in output.splitlines() if line.startswith(prefix)]
        assert len(lines) == count
        changed = lines[0].split()
        changed[-1] = '0' if changed[-1] != '0' else '21'
        for bad in (output.replace(lines[0]+'\n', '', 1), output+'\n'+lines[0], output.replace(lines[0], ' '.join(changed), 1)):
            with pytest.raises(ValueError):
                o['verify_native_registry'](bad)


def test_invalid_pairs_wrong_interior_labels_broken_stars_and_paths_refused():
    g = o['Geometry'](-1, 0, 2)
    for kind, i, j in [(2, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 6, 0), (0, 0, 16)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    for kind in (-1, 6):
        with pytest.raises(ValueError):
            o['source'](kind)
    plus = o['Geometry'](1, 0, 0)
    for fn in (lambda: o['predicted'](0, plus, 0, 0), lambda: o['path'](0, plus)):
        with pytest.raises(ValueError):
            fn()
    assert not g.interior(g.child(o['BASE'][0], 0, 0))
    assert not o['predicted'](0, g, 0, 0)
    wrong = (0, 2, -1, -2, 5)
    assert g.interior(wrong) and wrong in o['envelope']()
    packet = o['path'](0, g)
    for mode in range(4):
        bad = list(packet)
        if mode == 0:
            bad[0] = (0, 2*g.n+4, wrong)
        elif mode == 1:
            bad[1] = (0, g.t+2, o['BASE'][2])
        elif mode == 2:
            bad[-1] = (2, 1, (2, 0, 0, 0, 0))
        else:
            bad.pop()
        for want in (packet, bad):
            with pytest.raises(ValueError):
                o['verify_path'](o['BASE'][0], g, bad, want)
    edges = list(g.edges(o['BASE'][0]))
    o['verify_star'](0, g, edges)
    for broken in (edges + [edges[0]], edges[:-1], [edges[0]] + edges[:-1]):
        with pytest.raises(ValueError):
            o['verify_star'](0, g, broken)
