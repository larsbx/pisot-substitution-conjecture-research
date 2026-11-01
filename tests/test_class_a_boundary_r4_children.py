from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_r4_children.py'))


def test_complete_stars_uniform_exits_and_separate_registries():
    p = o['probe']()
    assert (p['members'], p['source_cells'], p['path_source_cells']) == (117, 234, 1404)
    assert (p['pairs'], p['accepted'], p['image_labels']) == (122616, 1898, 20)
    assert (p['r4_path_edges'], p['companion_path_edges'], p['path_edges']) == (728, 3518, 4246)
    assert p['R4_typed_exit_at_most_four'] and p['image_disjoint_from_candidate41']
    assert p['all_direct_children_productive_on_t_le_1']
    assert not p['all_direct_children_productive_for_all_t_proved']
    assert not p['companion_complete_stars_proved']
    assert p['companion_exit_bounds'] == dict(E4=2, D4=7, Y4=2, E5=3, G5=5)
    assert (p['outgoing_registered_stars'], p['outgoing_registered_exits']) == (2, 10)
    assert (p['old_R3_D3_outgoing_registered_stars'], p['old_R3_D3_outgoing_registered_exits']) == (22, 20)
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal']) == (25, 27)
    assert (r['after_unregistered'], r['after_exits_including_terminal']) == (14, 27)


def test_t_faces_literal_clips_and_both_t1_children_productive():
    for k in range(4):
        for t in range(5):
            g = o['Geometry'](-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            for flip in range(2):
                w = o['source'](flip)
                assert g.child(o['b4']['b3']['r3']['source'](flip), n-1 if flip else A+1, A+1 if flip else n-1) == w
                p = o['path'](flip, g)
                o['verify_path'](w, g, p, p)
                if t <= 1:
                    children = {target for _, _, target in g.edges(w)}
                    want = {o['source'](2+flip)} if t == 0 else {o['source'](4+flip), o['source'](8+flip)}
                    assert children == want
                    for child in children:
                        kind = next(z for z in range(2, 12) if o['source'](z) == child)
                        suffix = o['path'](kind, g)
                        o['verify_path'](child, g, suffix, suffix)
            assert o['predicted'](0, g, 0, n) == (t <= 2)
            assert len(list(g.edges(o['BASE'][0]))) == max(1, 2*t)
            if t == 0:
                with pytest.raises(ValueError):
                    g.child(o['BASE'][0], 0, k+4)
            elif t == 1:
                assert g.child(o['BASE'][0], 0, k+4) == o['BASE'][4] != o['reverse'](o['h3']['BASE'][3])


def test_n3_companion_shortcut_has_wrong_actual_type_not_disjointness():
    g = o['Geometry'](-1, 0, 0)
    actual = g.child(o['BASE'][2], 0, 3)
    assert actual == (0, 1, 1, 0, -1) != o['BASE'][3]
    assert g.interior(actual)
    assert len(o['path'](4, g)) == 7
    short = [(0, 3, o['BASE'][3])] + o['path'](6, g)
    with pytest.raises(ValueError):
        o['verify_path'](o['BASE'][2], g, short, short)
    for k, t in [(1, 0), (0, 1), (3, 2)]:
        g = o['Geometry'](-1, k, t)
        assert g.child(o['BASE'][2], 0, 3) == o['BASE'][3]
        assert len(o['path'](4, g)) == 3


def test_all_five_companions_have_exits_without_complete_stars():
    for kind in range(2, 12):
        w = o['source'](kind)
        assert o['interface'](w, True) is None
        assert o['exit_interface'](w, True) in ('E4', 'D4', 'Y4', 'E5', 'G5')
        with pytest.raises(ValueError):
            o['predicted'](kind, o['Geometry'](-1, 0, 0), 0, 0)
        with pytest.raises(ValueError):
            o['verify_star'](kind, o['Geometry'](-1, 0, 0), [])
    # Y4 is in S41 but has no complete-star interface. T2 has the opposite flags.
    assert o['BASE'][3] in o['b4']['b3']['r3']['candidate'](True)
    assert o['interface']((2, 2, -1, 1, 2), True) == 'T2'
    assert o['exit_interface']((2, 2, -1, 1, 2), True) is None
    # The literal c-prefix in E5 RR changes both first Parikh coordinates.
    g = o['Geometry'](-1, 0, 0)
    assert g.child(o['BASE'][4], g.n, 1) == o['pp']['BASE'][3]
    assert g.child(o['BASE'][4], g.n, 1) != o['reverse'](o['pp']['BASE'][0])


def test_all_61_native_registry_rows_match_independent_interfaces():
    output = (ROOT/'evidence/class-a-boundary-r4-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix, count in [('CLASS_A_R4_CANDIDATE_REGISTRY ', 41), ('CLASS_A_R4_IMAGE_REGISTRY ', 20)]:
        lines = [line for line in output.splitlines() if line.startswith(prefix)]
        assert len(lines) == count
        changed = lines[0].split()
        changed[-1] = '0' if changed[-1] != '0' else '26'
        for bad in (output.replace(lines[0]+'\n', '', 1), output+'\n'+lines[0], output.replace(lines[0], ' '.join(changed), 1)):
            with pytest.raises(ValueError):
                o['verify_native_registry'](bad)


def test_invalid_pairs_wrong_interior_labels_and_malformed_packets_refused():
    g = o['Geometry'](-1, 0, 2)
    for kind, i, j in [(2, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 16, 0), (0, 0, 6)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    for kind in (-1, 12):
        with pytest.raises(ValueError):
            o['source'](kind)
    plus = o['Geometry'](1, 0, 0)
    for fn in (lambda: o['predicted'](0, plus, 0, 0), lambda: o['path'](0, plus)):
        with pytest.raises(ValueError):
            fn()
    assert not g.interior(g.child(o['BASE'][0], 0, 0))
    assert not o['predicted'](0, g, 0, 0)
    wrong = o['BASE'][2]
    assert g.interior(wrong) and wrong in o['envelope']()
    packet = o['path'](0, g)
    for mode in range(4):
        bad = list(packet)
        if mode == 0:
            bad[0] = (0, 4, wrong)
        elif mode == 1:
            bad[1] = (g.n-2, 0, o['BASE'][2])
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
