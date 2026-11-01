from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_y4_children.py'))


def test_complete_stars_and_every_indexed_child_has_a_bounded_typed_tail():
    p = o['probe']()
    assert (p['members'], p['source_cells'], p['path_source_cells']) == (117, 234, 1638)
    assert (p['pairs'], p['accepted'], p['image_labels']) == (122616, 6552, 18)
    assert (p['source_path_edges'], p['all_child_walk_edges'], p['max_walk']) == (6500, 39676, 8)
    assert p['all_direct_children_productive']
    assert (p['direct_child_tail_bound'], p['first_choice_walk_bound']) == (7, 8)
    assert p['T2_uniform_exit_bound'] == 7 and p['Y4_source_exit_bound'] == 2
    assert not p['new_companion_complete_stars_proved'] and not p['closed_carrier_proved']
    assert (p['outgoing_registered_stars'], p['outgoing_registered_exits']) == (14, 18)
    assert (p['old_R3_D3_outgoing_registered_stars'], p['old_R3_D3_outgoing_registered_exits']) == (22, 22)
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal']) == (27, 29)
    assert (r['after_unregistered'], r['after_exits_including_terminal']) == (12, 31)


def test_each_image_label_has_a_universal_tail_dispatch_in_both_orientations():
    for k, t in [(0, 0), (0, 1), (4, 0), (2, 3)]:
        g = o['Geometry'](-1, k, t)
        for w in o['envelope']():
            tail = o['tail'](w, g)
            assert 1 <= len(tail) <= 7
            o['verify_path'](w, g, tail, tail)
        for kind in (0, 1):
            for edge in g.edges(o['source'](kind)):
                walk = o['walk'](kind, g, edge)
                o['verify_walk'](kind, g, edge, walk)
                assert len(walk) <= 8
    with pytest.raises(ValueError):
        o['tail'](o['C'], o['Geometry'](-1, 0, 0))


def test_n3_second_rr_strip_is_a_real_last_run_edge_with_another_type():
    g = o['Geometry'](-1, 0, 0)
    actual = g.child(o['BASE'][0], g.d+4, 1)
    wrong = o['source'](7)
    assert actual == o['r4']['BASE'][0] != wrong
    assert actual[2:] == wrong[2:] and g.interior(actual) and g.interior(wrong)
    assert o['predicted'](0, g, g.d+4, 1)
    assert all(target not in (o['source'](6), wrong) for _, _, target in g.edges(o['BASE'][0]))
    g = o['Geometry'](-1, 0, 1)
    assert g.child(o['BASE'][0], g.d+4, 1) == wrong


def test_t2_endpoint_and_c_prefix_are_not_interchangeable_with_y_prefix():
    for k in range(3):
        for t in range(3):
            g = o['Geometry'](-1, k, t)
            target = o['BASE'][5] if t == 0 else o['BASE'][4]
            assert g.child(o['BASE'][3], k+3, 0) == target
            assert len(o['path'](6, g)) == (5 if t == 0 else 7)
            p = o['path'](6, g)
            o['verify_path'](o['BASE'][3], g, p, p)
            assert g.child(o['BASE'][4], 2, 0) == o['BASE'][6]
            assert g.child(o['BASE'][5], 2, 0) == o['V'] != o['BASE'][6]
            assert g.child(o['BASE'][1], t+1, 1) == o['reverse'](o['pp']['BASE'][3])
            assert g.child(o['BASE'][1], t+1, 1) != o['pp']['BASE'][0]
            assert g.child(o['BASE'][2], g.d+1, 1) == o['C']
    g = o['Geometry'](-1, 0, 0)
    bad = [(g.k+3, 0, o['BASE'][4])] + o['path'](8, g)
    with pytest.raises(ValueError):
        o['verify_path'](o['BASE'][3], g, bad, bad)


def test_uniform_t_cycle_and_both_candidate_escapes_remain_real():
    for k, t in [(0, 0), (0, 1), (3, 2)]:
        g = o['Geometry'](-1, k, t)
        for flip in (0, 1):
            y, T = o['source'](flip), o['p3']['source'](2+flip)
            assert g.child(T, 1 if flip else 0, 0 if flip else 1) == y
            assert g.child(y, 0 if flip else g.d+1, g.d+1 if flip else 0) == T
            assert g.child(y, g.n if flip else g.n+g.d+1, g.n+g.d+1 if flip else g.n) == o['source'](4+flip)
            assert o['source'](4+flip) not in o['b3']['r3']['candidate'](True)
        assert g.child(o['BASE'][1], t+1, 1) not in o['envelope']()


def test_star_and_exit_flags_preserve_inherited_t2_and_new_companion_scope():
    for flip in (0, 1):
        T2 = o['source'](6+flip)
        assert o['interface'](T2) == 'T2' and o['exit_interface'](T2) is None
        assert o['exit_interface'](T2, True) == 'T2'
        assert o['interface'](o['source'](flip)) is None
        assert o['interface'](o['source'](flip), True) == 'Y4'
    for kind in (2, 3, 4, 5, 8, 9, 10, 11, 12, 13):
        assert o['interface'](o['source'](kind), True) is None
        assert o['exit_interface'](o['source'](kind), True) is not None
    g = o['Geometry'](-1, 0, 0)
    with pytest.raises(ValueError):
        o['predicted'](6, g, 0, 0)
    with pytest.raises(ValueError):
        o['verify_star'](6, g, [])


def test_all_59_native_registry_rows_match_the_independent_interfaces():
    output = (ROOT/'evidence/class-a-boundary-y4-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix, count in [('CLASS_A_Y4_CANDIDATE_REGISTRY ', 41), ('CLASS_A_Y4_IMAGE_REGISTRY ', 18)]:
        lines = [line for line in output.splitlines() if line.startswith(prefix)]
        assert len(lines) == count
        changed = lines[0].split()
        changed[-1] = '0' if changed[-1] != '0' else '29'
        for bad in (output.replace(lines[0]+'\n', '', 1), output+'\n'+lines[0], output.replace(lines[0], ' '.join(changed), 1)):
            with pytest.raises(ValueError):
                o['verify_native_registry'](bad)


def test_invalid_inputs_wrong_interior_packets_and_malformed_stars_walks_refused():
    g = o['Geometry'](-1, 0, 0)
    for kind, i, j in [(2, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 10, 0), (0, 0, 4)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    for kind in (-1, 14):
        with pytest.raises(ValueError):
            o['source'](kind)
    plus = o['Geometry'](1, 0, 0)
    for fn in (lambda: o['predicted'](0, plus, 0, 0), lambda: o['path'](0, plus), lambda: o['tail'](o['V'], plus), lambda: o['seed_suffix'](0, 2, g)):
        with pytest.raises(ValueError):
            fn()
    assert not g.interior(g.child(o['BASE'][0], 0, 0))
    wrong = o['b3']['B3']
    assert g.interior(wrong) and wrong in o['envelope']()
    with pytest.raises(ValueError):
        o['walk'](0, g, (g.d+1, 0, wrong))
    edge = (g.n+g.d+1, g.n, o['BASE'][2])
    packet = o['walk'](0, g, edge)
    for mode in range(4):
        bad = list(packet)
        if mode == 0:
            bad[0] = (edge[0], edge[1], o['BASE'][1])
        elif mode == 1:
            bad[-1] = (g.d+1, 1, (2, 0, 0, 0, 0))
        elif mode == 2:
            bad.pop()
        else:
            bad.append(bad[-1])
        with pytest.raises(ValueError):
            o['verify_walk'](0, g, edge, bad)
    edges = list(g.edges(o['BASE'][0]))
    o['verify_star'](0, g, edges)
    for broken in (edges + [edges[0]], edges[:-1], [edges[0]] + edges[:-1]):
        with pytest.raises(ValueError):
            o['verify_star'](0, g, broken)
