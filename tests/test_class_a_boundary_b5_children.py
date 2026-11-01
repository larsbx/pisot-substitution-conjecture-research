from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_b5_children.py'))


def test_complete_stars_and_every_indexed_child_has_a_bounded_tail():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['pairs'],p['accepted'])==(117,234,122616,5850)
    assert (p['source_and_companion_path_edges'],p['all_child_walk_edges'],p['max_walk'])==(948,34884,8)
    assert p['image_labels']==24 and p['all_direct_children_productive']
    assert (p['source_exit_bound'],p['child_tail_bound'],p['walk_bound'])==(2,7,8)
    assert p['E7_tail_n4_only'] and not p['E7_uniform_exit_registered']
    assert (p['image_registered_stars'],p['image_uniform_exits'])==(18,22)
    r=p['reconciliation']
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(29,29)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(31,33)
    assert not p['closed_carrier_proved']


def test_small_first_last_endpoints_preserve_actual_types():
    for k,t in [(0,0),(1,0),(0,1)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        actual=g.child(o['source'](0),0,A+1)
        assert actual==o['source'](2 if g.n==3 else 4)
        wrong=(0,2,*actual[2:])
        assert g.interior(actual) and g.interior(wrong) and actual!=wrong
        assert o['predicted'](0,g,0,A+1)
        with pytest.raises(ValueError):
            o['verify_star'](0,g,[(0,A+1,wrong)]* (2*g.n-1))
    for k,t in [(1,0),(0,1)]:
        g=o['Geometry'](-1,k,t)
        for kind in (4,5):
            p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)
            assert len(p)==3
    for k,t in [(0,0),(2,0),(0,2)]:
        g=o['Geometry'](-1,k,t)
        assert g.interior(o['source'](4))
        with pytest.raises(ValueError):o['path'](4,g)
        with pytest.raises(ValueError):o['tail'](o['source'](4),g)
        assert o['exit_interface'](o['source'](4),True) is None


def test_clipped_rr_pair_is_a_real_run_last_edge():
    for k,t,delta in [(1,0,4),(2,0,5)]:
        g=o['Geometry'](-1,k,t);j=g.d+delta+1
        assert j==g.n+g.d+1
        actual=g.child(o['source'](0),1,j)
        wrong=(2,2,*actual[2:])
        assert actual[:2]==(2,0) and g.interior(actual) and g.interior(wrong)
        assert actual!=wrong and o['predicted'](0,g,1,j)


def test_every_actual_child_walk_and_guarded_uniform_E6_exit():
    for k,t in [(0,0),(1,0),(0,1),(2,1),(3,4)]:
        g=o['Geometry'](-1,k,t)
        for kind in (0,1):
            for edge in g.edges(o['source'](kind)):
                p=o['walk'](kind,g,edge);o['verify_walk'](kind,g,edge,p)
                assert len(p)<=8
        for kind in (2,3):
            p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)
            assert len(p)==2 and o['exit_interface'](o['source'](kind),True)=='E6'
            assert o['interface'](o['source'](kind),True) is None


def test_image_is_inside_S41_and_has_a_uniform_escape_to_W():
    assert o['envelope']()<=o['r3']['candidate'](True)
    for k,t in [(0,0),(0,1),(2,3)]:
        g=o['Geometry'](-1,k,t)
        V=o['y4']['V'];W=(1,0,0,1,-1)
        assert V in o['envelope']() and W not in o['envelope']()
        assert W not in o['r3']['candidate'](True)
        assert g.child(V,g.n,0)==W and g.interior(W)


def test_registry_flags_and_native_rows_match_without_a_uniform_E7_claim():
    output=(ROOT/'evidence/class-a-boundary-b5-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix,n in [('CLASS_A_B5_CANDIDATE_REGISTRY ',41),('CLASS_A_B5_IMAGE_REGISTRY ',24)]:
        lines=[x for x in output.splitlines() if x.startswith(prefix)]
        assert len(lines)==n
        changed=lines[0].split();changed[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
    for flip in (0,1):
        assert o['interface'](o['source'](flip)) is None
        assert o['interface'](o['source'](flip),True)=='B5'
        assert o['interface'](o['source'](4+flip),True) is None
        assert o['exit_interface'](o['source'](4+flip),True) is None


def test_invalid_parameters_targets_stars_and_walks_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,4,0),(0,0,11)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,6]:
        with pytest.raises(ValueError):o['source'](kind)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    edges=list(g.edges(o['source'](0)))
    for bad in [edges[:-1],edges+[edges[0]],edges[:-1]+[edges[0]]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    edge=(0,9,o['source'](2));packet=o['walk'](0,g,edge)
    for bad in [packet[:-1],packet+[packet[-1]],packet[:-1]+[(2,1,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_walk'](0,g,edge,bad)
    wrong=(0,8,(0,2,0,1,-2))
    assert g.interior(wrong[2])
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
