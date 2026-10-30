from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_w9_children.py'))


def test_complete_stars_constant_member_image_and_every_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['pairs'],p['accepted'])==(117,234,297648,12402)
    assert (p['source_path_edges'],p['companion_path_edges'],p['all_child_walk_edges'],p['all_image_tail_edges'])==(936,4212,43992,5382)
    assert (p['image_labels'],p['image_registered_stars'],p['image_uniform_exits'],p['max_selected_walk'])==(16,2,16,6)
    assert p['constant_memberwise_image'] and p['all_direct_children_productivity_proved']
    assert not p['closed_carrier_proved'] and not p['new_companion_stars']


def test_nine_kinds_and_each_member_image_at_unbalanced_parameters():
    for k,t in [(0,0),(0,12),(1,11),(2,10),(17,0),(21,3),(12,19)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d;image=set()
        for kind in (0,1):
            actual=set(g.edges(o['source'](kind)))
            assert len(actual)==o['count'](k,t)==4*g.n+1
            chosen={(i,j,g.child(o['source'](kind),i,j)) for i in range(A+2) for j in range(A+2) if o['predicted'](kind,g,i,j)}
            assert actual==chosen;o['verify_star'](kind,g,list(actual));image.update(w for i,j,w in actual)
        assert image==o['envelope']()


def test_every_member_has_explicit_witnesses_for_all_eight_base_labels():
    for k,t in [(0,0),(1,0),(0,1),(2,3),(17,12)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        witnesses=[(t+3,0),(t+4,0),(t+5,0),(t+5,1),(t+6,1),(A+1,A-t-4),(A+1,A-t-3),(A+1,A-t-2)]
        targets={g.child(o['source'](0),i,j) for i,j in witnesses}
        assert len(targets)==8
        assert targets|{o['reverse'](w) for w in targets}==o['envelope']()
        assert all(o['predicted'](0,g,i,j) for i,j in witnesses)
        # Their source-dependent rectangles and index strips can still differ at fixed n.
    a=o['Geometry'](-1,0,3);b=o['Geometry'](-1,3,0)
    assert a.n==b.n and o['count'](0,3)==o['count'](3,0)
    assert set(a.edges(o['source'](0)))!=set(b.edges(o['source'](0)))


def test_all_six_new_companions_have_full_cone_typed_exits_and_no_stars():
    for k,t in [(0,0),(0,5),(1,0),(2,4),(15,3)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(12):
            w=o['companion'](kind);assert g.interior(w)
            p=o['companion_path'](kind,g);o['verify_path'](w,g,p,p)
            assert len(p)==(3,3,2,5,3,2)[kind//2]
            assert o['interface'](w,True) is None
            assert o['exit_interface'](w) is None
            assert o['exit_interface'](w,True)==('N9','X2','X3','X4','Y2','Y3')[kind//2]


def test_floor_zero_offset_has_actual_LAST_c_not_a_typed_coincidence():
    floor=o['Geometry'](-1,0,0)
    for kind in (2,8):
        w=o['companion'](kind);actual=floor.child(w,1,3)
        assert actual==(2,1,0,0,0) and actual!=o['C'] and floor.interior(actual)
        with pytest.raises(ValueError):o['verify_path'](w,floor,[(1,3,o['C'])],[(1,3,o['C'])])
        p=o['companion_path'](kind,floor)
        assert p[0][0:2]==(0,2) and len(p)==3
    for k,t in [(0,1),(1,0),(3,2)]:
        g=o['Geometry'](-1,k,t)
        for kind in (2,8):assert g.child(o['companion'](kind),1,3)==o['C']
    g=o['Geometry'](-1,2,1)
    X3,Y3=o['companion'](4),o['companion'](10)
    assert X3[2:]==Y3[2:] and X3!=Y3
    # Nominal top RUN n is genuine for x but actual LAST c for y.
    a=g.child(X3,g.n,0);b=g.child(Y3,g.n,0)
    assert a[2:]==b[2:] and a[:2]==(2,0) and b[:2]==(1,0)


def test_six_edge_bound_and_escape_are_attained_in_every_member():
    for k,t in [(0,0),(1,0),(0,3),(5,2)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        edge=(A+1,A-t-2,o['companion'](6))
        p=o['walk'](0,g,edge);o['verify_walk'](0,g,edge,p);assert len(p)==6
        tail=o['companion_path'](6,g)
        assert tail[0][2] not in o['envelope']()
        for kind in (0,1):
            p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p);assert len(p)==4


def test_registry_aliases_source_ancestry_and_old_H9_image_coverage():
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'],r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(33,33,35,35)
    assert sum(x['before'] is not None for x in r['previous_H9_image_rows'])==2
    assert sum(x['after'] is not None for x in r['previous_H9_image_rows'])==4
    assert sum(x['after_exit'] is not None for x in r['previous_H9_image_rows'])==20
    assert o['interface'](o['source'](0)) is None and o['interface'](o['source'](0),True)=='W9'
    assert o['exit_interface'](o['source'](0))==o['exit_interface'](o['source'](0),True)=='W9'
    for t in range(4):
        g=o['Geometry'](-1,0,t);A=g.n+g.d
        for kind in (0,1):
            assert g.child(o['h9']['source'](1-kind),0,0)==o['source'](kind)
            assert g.child(o['h9']['source'](1-kind),A+1,A+1)==o['source'](kind)


def test_bad_inputs_same_type_strict_wrong_targets_and_terminals_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    with pytest.raises(ValueError):o['count'](-1,0)
    with pytest.raises(ValueError):o['companion'](12)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    wrong=(3,0,o['p9']['companion'](2));assert g.interior(wrong[2])
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
    edges=list(g.edges(o['source'](0)))
    for bad in [[],edges[:-1]+[edges[0]]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    p=o['path'](0,g)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,p)


def test_91_actual_native_registry_rows_and_corruption_controls():
    output=(ROOT/'evidence/class-a-boundary-w9-2026-10-29/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,n in [('SOURCE',14),('CANDIDATE',41),('IMAGE',16),('H9_IMAGE',20)]:
        lines=[line for line in output.splitlines() if line.startswith('CLASS_A_W9_'+name+'_REGISTRY ')]
        assert len(lines)==n
        first=lines[0];parts=first.split();parts[-1]='999'
        for bad in [output.replace(first+'\n','',1),output+first+'\n',output.replace(first,' '.join(parts),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
