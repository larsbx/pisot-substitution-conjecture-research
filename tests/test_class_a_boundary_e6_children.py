from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_e6_children.py'))


def test_complete_stars_and_every_indexed_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['path_source_cells'])==(117,234,936)
    assert (p['pairs'],p['accepted'],p['image_labels'],p['every_member_image_labels'])==(297648,8658,16,16)
    assert (p['source_and_companion_path_edges'],p['all_child_walk_edges'],p['max_walk'])==(2582,34766,9)
    assert p['all_direct_children_productive'] and p['all_image_labels_uniform_exit']
    assert (p['source_exit_bound'],p['child_tail_bound'],p['walk_bound'])==(2,8,9)
    assert not p['companion_complete_stars_proved'] and not p['closed_carrier_proved']
    assert (p['image_registered_stars'],p['image_uniform_exits'],p['previous_B5_image_registered_stars'])==(10,16,20)
    r=p['reconciliation']
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(29,31)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(33,33)


def test_uniform_tails_cover_all_sixteen_labels_both_orientations():
    for k,t in [(0,0),(0,1),(1,0),(2,3),(17,12)]:
        g=o['Geometry'](-1,k,t)
        for w in o['envelope']():
            tail=o['tail'](w,g)
            assert 1<=len(tail)<=8
            o['verify_path'](w,g,tail,tail)
        for kind in range(8):
            p=o['path'](kind,g)
            o['verify_path'](o['source'](kind),g,p,p)
            assert len(p)==o['path_length'](kind,g)


def test_n3_D4_suffix_keeps_its_actual_types_and_nine_edge_walk():
    g=o['Geometry'](-1,0,0);A=g.n+g.d
    edge=(A+1,g.d-3,o['source'](2))
    p=o['walk'](0,g,edge)
    assert len(p)==9 and len(o['path'](2,g))==8
    assert p[1]==(0,1,o['r4']['source'](4))
    wrong=[edge,p[1],(0,3,o['r4']['source'](6))]+o['r4']['path'](6,g)
    with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,wrong,wrong)
    g=o['Geometry'](-1,0,1)
    assert len(o['path'](2,g))==4
    assert len(o['walk'](0,g,(g.n+g.d+1,g.d-3,o['source'](2))))==5


def test_small_member_three_cycle_and_uniform_candidate_escapes():
    g=o['Geometry'](-1,0,0)
    for flip in (0,1):
        swap=lambda i,j:(j,i) if flip else (i,j)
        assert g.child(o['source'](flip),*swap(9,3))==o['source'](4+flip)
        assert g.child(o['source'](4+flip),*swap(3,0))==o['b5']['source'](flip)
        assert g.child(o['b5']['source'](flip),*swap(0,9))==o['source'](flip)
    S=o['b5']['r3']['candidate'](True)
    for k,t in [(0,0),(0,1),(2,4)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        assert g.child(o['source'](0),A+1,g.d-2)==o['source'](4) not in S
        assert g.child(o['source'](4),g.t+3,0)==o['b5']['source'](0) not in o['envelope']()


def test_every_member_has_the_same_full_image_and_no_endpoint_loss():
    for k,t in [(0,0),(1,0),(0,1),(3,5)]:
        g=o['Geometry'](-1,k,t)
        image=set()
        for kind in (0,1):
            star=list(g.edges(o['source'](kind)))
            assert len(star)==2*g.d-1
            o['verify_star'](kind,g,star)
            image|={w for i,j,w in star}
        assert image==o['envelope']()
        assert not g.interior(g.child(o['source'](0),g.n+1,0))
        assert not g.interior(g.child(o['source'](0),g.n+g.d+1,g.d))


def test_new_flags_add_E6_stars_and_companion_exits_only():
    for flip in (0,1):
        E6=o['source'](flip)
        assert o['interface'](E6) is None and o['interface'](E6,True)=='E6'
        assert o['exit_interface'](E6)==o['exit_interface'](E6,True)=='E6'
    for kind in range(2,8):
        assert o['interface'](o['source'](kind),True) is None
        assert o['exit_interface'](o['source'](kind)) is None
        assert o['exit_interface'](o['source'](kind),True) is not None
    # E7's n=4-only contract is not silently upgraded by this packet.
    g=o['Geometry'](-1,0,0)
    with pytest.raises(ValueError):o['b5']['path'](4,g)


def test_all_native_registry_rows_match_and_corruption_is_refused():
    output=(ROOT/'evidence/class-a-boundary-e6-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix,n in [('CLASS_A_E6_CANDIDATE_REGISTRY ',41),('CLASS_A_E6_IMAGE_REGISTRY ',16),('CLASS_A_E6_B5_IMAGE_REGISTRY ',24)]:
        lines=[x for x in output.splitlines() if x.startswith(prefix)]
        assert len(lines)==n
        changed=lines[0].split();changed[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)


def test_invalid_ids_parameters_targets_stars_and_walks_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,8]:
        with pytest.raises(ValueError):o['source'](kind)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    wrong=(5,0,(2,0,0,1,-2));assert g.interior(wrong[2])
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
    edges=list(g.edges(o['source'](0)))
    for bad in [edges[:-1],edges+[edges[0]],edges[:-1]+[edges[0]]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    edge=(9,2,o['source'](2));packet=o['walk'](0,g,edge)
    for bad in [packet[:-1],packet+[packet[-1]],packet[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_walk'](0,g,edge,bad)
