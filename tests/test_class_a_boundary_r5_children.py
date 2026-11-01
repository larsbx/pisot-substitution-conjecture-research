from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_r5_children.py'))


def test_complete_indexed_stars_and_exact_chamber_image():
    p = o['probe']()
    assert (p['members'], p['source_cells'], p['pairs'], p['accepted']) == (117, 234, 122616, 6760)
    assert (p['source_path_edges'], p['reused_exit_edges'], p['source_exit_bound']) == (702, 1410, 3)
    assert (p['image_labels'], p['image_registered_stars'], p['image_registered_exits']) == (18, 6, 6)
    assert p['image_exit_gaps'] == 12
    assert (p['Y4_image_registered_stars'], p['Y4_image_registered_exits']) == (16, 18)
    assert (p['old_R3_D3_image_registered_stars'], p['old_R3_D3_image_registered_exits']) == (22, 22)
    r = p['reconciliation']
    assert (r['before_registered_including_terminal'], r['after_registered_including_terminal'], r['exits_including_terminal']) == (29, 31, 31)
    assert not p['all_direct_children_productive_proved'] and not p['closed_carrier_proved']
    assert p['S41_escape'] and p['image_escape_via_K']


def test_t1_clipped_run_is_a_real_first_first_edge_with_other_types():
    g = o['Geometry'](-1, 0, 1)
    actual = g.child(o['R5'], g.t-1, 0)
    wrong = o['h3']['BASE'][2]
    assert actual == (0, 0, 0, -2, 4) != wrong
    assert g.words[o['R5'][0]][g.t-1] == 0
    assert g.interior(actual) and g.interior(wrong)
    assert o['predicted'](0, g, 0, 0)
    with pytest.raises(ValueError):
        o['verify_star'](0, g, [(0, 0, wrong)] + [e for e in g.edges(o['R5']) if e[:2] != (0, 0)])
    g = o['Geometry'](-1, 0, 0)
    with pytest.raises(ValueError):
        o['predicted'](0, g, g.t-1, 0)
    assert g.child(o['R5'], 0, 0) == (0, 0, 0, -2, 3)
    for t in (2, 3):
        g = o['Geometry'](-1, 0, t)
        assert not o['predicted'](0, g, 0, 0)
        assert not g.interior(g.child(o['R5'], 0, 0))


def test_literal_y_prefix_cannot_be_replaced_by_d3_c_prefix():
    for k in range(3):
        for t in range(3):
            g = o['Geometry'](-1, k, t)
            target = g.child(o['R5'], t+1, 1)
            d3 = (0, 1, 1, -1, -1)
            assert target == o['reverse'](o['pp']['BASE'][3])
            assert g.child(d3, t+1, 1) == o['pp']['BASE'][0] != target
            assert o['R5'][2:] == d3[2:]
            for flip in (0, 1):
                packet = o['path'](flip, g)
                assert len(packet) == 3
                o['verify_path'](flip, g, packet)
                i, j = (g.n-1, g.n+g.d+1) if flip else (g.n+g.d+1, g.n-1)
                assert g.child(o['y4']['source'](flip), i, j) == o['source'](flip)


def test_reused_b2_b2h_k_interfaces_and_true_nonclosure():
    for g in (o['Geometry'](-1, 0, 0), o['Geometry'](-1, 2, 2)):
        for base, name in [(o['pp']['BASE'][2], 'B2'), (o['pp']['BASE'][3], 'B2h'),
                           (o['h3']['BASE'][2], 'K')]:
            for w in (base, o['reverse'](base)):
                assert w in o['envelope']()
                assert o['interface'](w) == name and o['exit_interface'](w) == name
        assert o['interface'](o['R5']) is None
        assert o['interface'](o['R5'], True) == 'R5'
        assert o['exit_interface'](o['R5']) == 'R5'
        assert o['y4']['interface'](o['R5'], True) is None
        assert o['y4']['exit_interface'](o['R5'], True) == 'R5'
        assert all(w not in o['y4']['b3']['r3']['candidate'](True) for w in o['envelope']())
        K = o['h3']['BASE'][2]
        edge = o['h3']['path'](4, g)[0]
        assert g.child(K, edge[0], edge[1]) == edge[2] not in o['envelope']()
        assert edge[2] == o['h3']['BASE'][3]
    assert len(o['pp']['path'](5, o['Geometry'](-1, 0, 0))) == 4
    assert len(o['pp']['path'](5, o['Geometry'](-1, 0, 1))) == 1


def test_all_59_native_registry_rows_and_bad_inventory_refusal():
    output = (ROOT/'evidence/class-a-boundary-r5-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix, count in [('CLASS_A_R5_CANDIDATE_REGISTRY ', 41), ('CLASS_A_R5_IMAGE_REGISTRY ', 18)]:
        lines = [line for line in output.splitlines() if line.startswith(prefix)]
        assert len(lines) == count
        changed = lines[0].split()
        changed[-1] = '0' if changed[-1] != '0' else '29'
        for bad in (output.replace(lines[0]+'\n', '', 1), output+'\n'+lines[0],
                    output.replace(lines[0], ' '.join(changed), 1)):
            with pytest.raises(ValueError):
                o['verify_native_registry'](bad)


def test_wrong_interior_packet_duplicate_star_path_terminal_and_inputs_refused():
    g = o['Geometry'](-1, 0, 0)
    actual = list(g.edges(o['R5']))
    o['verify_star'](0, g, actual)
    for bad in (actual[:-1], actual+[actual[0]], [actual[0]]+actual[:-1]):
        with pytest.raises(ValueError):
            o['verify_star'](0, g, bad)
    wrong = o['reverse'](o['pp']['BASE'][2])
    assert wrong in o['envelope']() and g.interior(wrong)
    assert g.child(o['R5'], 1, 1) != wrong
    bad = [(1, 1, wrong) if e[:2] == (1, 1) else e for e in actual]
    with pytest.raises(ValueError):
        o['verify_star'](0, g, bad)
    assert not g.interior(g.child(o['R5'], 0, 1))
    packet = o['path'](0, g)
    for bad in (packet[:-1], [(1, 1, o['pp']['BASE'][0])]+packet[1:],
                packet[:-1]+[(packet[-1][0], packet[-1][1], (2, 0, 0, 0, 0))],
                [(0, 1, packet[0][2])]+packet[1:]):
        with pytest.raises(ValueError):
            o['verify_path'](0, g, bad)
    for kind, i, j in [(-1, 0, 0), (2, 0, 0), (0, -1, 0), (0, 10, 0), (0, 0, 4)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    for k, t in [(-1, 0), (0, -1)]:
        with pytest.raises(ValueError):
            o['Geometry'](-1, k, t)
    plus = o['Geometry'](1, 0, 0)
    for fn in (lambda: o['predicted'](0, plus, 0, 0), lambda: o['path'](0, plus),
               lambda: o['verify_star'](0, plus, actual)):
        with pytest.raises(ValueError):
            fn()
