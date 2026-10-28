from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
o = runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_q3_children.py'))


def test_complete_two_stars_all_direct_child_tails_and_real_cycles():
    p = o['probe']()
    assert p['members'] == 117 and p['source_cells'] == 234
    assert p['pairs'] == 122616 and p['accepted'] == 234
    assert p['path_edges'] == 1170 and p['cycle_edges'] == 468
    assert p['image_labels'] == 2 and p['unresolved_direct_Q3_children'] == 0
    assert p['Q3_typed_exit_at_most_five'] and p['every_direct_child_typed_tail_at_most_four']
    assert not p['all_edge_descent'] and not p['forward_closure']


def test_invalid_orientation_parameters_indices_types_and_duplicate_star():
    g = o['Geometry'](-1, 0, 0)
    A = g.n+g.d
    for kind, i, j in [(2, 0, 0), (-1, 0, 0), (0, -1, 0), (0, A+2, 0), (1, g.n+1, 0)]:
        with pytest.raises(ValueError):
            o['predicted'](kind, g, i, j)
    for k, t in [(-1, 0), (0, -1)]:
        with pytest.raises(ValueError):
            o['Geometry'](-1, k, t)
    edge = (A+1, 0, o['X'])
    o['verify_star'](0, g, [edge])
    for star in [[], [edge, edge], [(A+1, 0, (0, 1, 1, 0, -1))], [(A, 0, o['X'])]]:
        with pytest.raises(ValueError):
            o['verify_star'](0, g, star)
    assert g.interior((0, 1, 1, 0, -1))  # wrong types, correct offset, still interior
    assert g.words[0][A+1] == 0 != 2  # never RUN, even at n=3


def test_disjoint_endpoint_and_false_coincidence_controls():
    g = o['Geometry'](-1, 0, 0)
    A = g.n+g.d
    assert not o['predicted'](0, g, A+1, 1)
    assert not g.interior(g.child(o['Q3'], A+1, 1))
    endpoint = g.child(o['Q'], 0, 2)
    assert endpoint == (0, 2, 1, 0, 0)
    assert g.shift(endpoint) == g.lengths[endpoint[0]]
    assert not g.interior(endpoint)
    for w in [o['Q3'], o['X'], (1, 2, 0, 0, 0)]:
        assert not o['typed_coincidence'](w)
    p = o['path'](0, g)
    for index, replacement in [(0, (A+1, 0, (0, 1, 1, 0, -1))),
                               (2, (g.n, 0, (1, 0, 0, 1, 0))),
                               (4, (1, 2, (2, 0, 0, 0, 0)))]:
        bad = list(p)
        bad[index] = replacement
        with pytest.raises(ValueError):
            o['verify_path'](o['Q3'], g, bad, p)
        with pytest.raises(ValueError):
            o['verify_path'](o['Q3'], g, bad, bad)
    with pytest.raises(ValueError):
        o['verify_path'](o['Q3'], g, p[:-1], p[:-1])
