from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_h9_children.py'))


def test_complete_stars_and_selected_completion_after_every_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['pairs'],p['accepted'])==(117,234,297648,13302)
    assert (p['source_path_edges'],p['companion_path_edges'],p['all_child_walk_edges'],p['all_image_tail_edges'])==(1404,3042,78714,9170)
    assert (p['image_labels'],p['image_registered_stars'],p['image_uniform_exits'],p['max_selected_walk'])==(20,2,20,7)
    assert p['all_direct_children_productivity_proved'] and not p['closed_carrier_proved'] and not p['new_companion_stars']


def test_nine_kinds_at_unbalanced_members_and_all_count_boundaries():
    for k,t in [(0,11),(1,10),(2,9),(3,8),(17,0),(18,2),(13,17)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        for kind in (0,1):
            actual=set(g.edges(o['source'](kind)))
            assert len(actual)==o['count'](k,t)==(2*A+3 if k<=1 else 2*A-2*k+5)
            chosen={(i,j,g.child(o['source'](kind),i,j)) for i in range(A+2) for j in range(A+2) if o['predicted'](kind,g,i,j)}
            assert actual==chosen;o['verify_star'](kind,g,list(actual))


def test_equal_endpoint_targets_preserve_distinct_indexed_edges():
    for k in range(4):
        g=o['Geometry'](-1,k,1);A=g.n+g.d
        for kind in (0,1):
            w=o['source'](kind);edges=list(g.edges(w))
            assert g.child(w,0,0)==g.child(w,A+1,A+1)
            assert o['predicted'](kind,g,0,0)==o['predicted'](kind,g,A+1,A+1)==(k<=1)
            if k<=1:
                first=(0,0,g.child(w,0,0));last=(A+1,A+1,first[2]);assert first in edges and last in edges
                bad=[first if e==last else e for e in edges]
                assert len(bad)==len(edges)
                with pytest.raises(ValueError):o['verify_star'](kind,g,bad)


def test_equal_counts_do_not_identify_stars_or_member_images():
    a=o['Geometry'](-1,0,1);b=o['Geometry'](-1,2,0)
    sa=set(a.edges(o['source'](0)));sb=set(b.edges(o['source'](0)))
    assert len(sa)==len(sb)==25 and sa!=sb
    assert len({w for _,_,w in sa})==5 and len({w for _,_,w in sb})==8
    for k,want in [(0,10),(1,14),(2,16),(3,16)]:
        g=o['Geometry'](-1,k,0)
        image={w for kind in (0,1) for i,j,w in g.edges(o['source'](kind))}
        assert len(image)==want and image<o['envelope']()


def test_three_uniform_companion_exits_and_actual_floor_RUN_LAST_types():
    for k,t in [(0,0),(0,5),(1,0),(2,4),(17,3)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(6):
            w=o['companion'](kind);assert g.interior(w)
            p=o['companion_path'](kind,g);o['verify_path'](w,g,p,p)
            assert len(p)==(4,3,6)[kind//2]
            assert o['interface'](w,True) is None
            assert o['exit_interface'](w,True)==('K9','L9','M9')[kind//2]
        assert g.d+3<=g.n+g.d # genuine bottom RUN, including the floor
        assert g.child(o['companion'](0),0,g.d+3)==(0,2,0,1,-2)
    floor=o['Geometry'](-1,0,0);K=o['companion'](0);A=floor.n+floor.d
    actual=floor.child(K,0,floor.d+4);fake=(0,2,0,1,-1)
    assert floor.d+4==A+1 and actual==(0,0,0,1,-1)
    assert floor.interior(actual) and floor.interior(fake)
    bad=[(0,A+1,fake)]+o['j9']['e7']['b5']['r3']['p3']['path'](3,floor)
    with pytest.raises(ValueError):o['verify_path'](K,floor,bad,bad)


def test_bound_seven_and_guarded_D4_suffix_not_falsely_uniform_six():
    g=o['Geometry'](-1,0,0)
    # RR delta1 reaches S8 with its six-edge suffix.
    edge=(1,2,(2,2,-1,-3,6));p=o['walk'](0,g,edge)
    o['verify_walk'](0,g,edge,p);assert len(p)==7
    D=o['r4']['source'](4)
    assert len(o['tail'](D,g))==7 # valid source tail, but this is not a floor H9 child
    assert D not in {w for i,j,w in g.edges(o['source'](0))}
    for k,t in [(2,0),(3,1),(14,2)]:
        g=o['Geometry'](-1,k,t)
        assert D in {w for i,j,w in g.edges(o['source'](0))}
        assert len(o['tail'](D,g))==3


def test_ancestry_escape_and_registry_reconciliation():
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'],r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(33,33,35,35)
    assert sum(x['before'] is not None for x in r['previous_P9_image_rows'])==2
    assert sum(x['after'] is not None for x in r['previous_P9_image_rows'])==4
    assert sum(x['after_exit'] is not None for x in r['previous_P9_image_rows'])==20
    for k,t in [(0,0),(1,0),(2,1),(4,3)]:
        g=o['Geometry'](-1,k,t)
        assert (g.child(o['p9']['source'](0),0,0)==o['source'](0))==(k==0)
        p=o['companion_path'](0,g)
        assert p[0][2] not in o['envelope']()
    assert o['interface'](o['source'](0)) is None and o['interface'](o['source'](0),True)=='H9'
    assert o['exit_interface'](o['source'](0))==o['exit_interface'](o['source'](0),True)=='H9'


def test_bad_parameters_packets_typed_terminals_and_unknown_tails_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    with pytest.raises(ValueError):o['count'](-1,0)
    with pytest.raises(ValueError):o['companion'](6)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    wrong=(0,0,(0,0,-1,-3,4));assert g.interior(wrong[2])
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
    edges=list(g.edges(o['source'](0)))
    for bad in [[],edges[:-1]+[edges[0]]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    p=o['path'](0,g)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,p)


def test_actual_native_driver_93_rows_and_corruption_controls():
    output=(ROOT/'evidence/class-a-boundary-h9-2026-10-29/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,n in [('SOURCE',8),('CANDIDATE',41),('IMAGE',20),('P9_IMAGE',24)]:
        lines=[line for line in output.splitlines() if line.startswith('CLASS_A_H9_'+name+'_REGISTRY ')]
        assert len(lines)==n
        first=lines[0];parts=first.split();parts[-1]='999'
        for bad in [output.replace(first+'\n','',1),output+first+'\n',output.replace(first,' '.join(parts),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
