from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_e7_children.py'))


def test_complete_stars_and_uniform_source_exits():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['path_source_cells'])==(117,234,702)
    assert (p['pairs'],p['accepted'],p['image_labels'])==(297648,1690,32)
    assert (p['source_and_companion_path_edges'],p['registered_image_tail_edges'])==(2006,2362)
    assert p['source_exit_bound']==5 and (p['source_exit_tle1'],p['source_exit_tge2'])==(3,5)
    assert p['all_direct_children_productive_tle1'] and not p['all_direct_children_productive_all_t_proved']
    assert not p['closed_carrier_proved']
    assert (p['image_registered_stars'],p['image_uniform_exits'])==(6,8)
    assert (p['previous_B5_image_registered_stars'],p['previous_B5_image_uniform_exits'])==(22,24)
    r=p['reconciliation']
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(31,33)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(33,35)


def test_same_t4_count_has_different_chamber_edges_and_actual_targets():
    low=o['Geometry'](-1,5,4);high=o['Geometry'](-1,4,4)
    assert not o['high'](5,4) and o['high'](4,4)
    lo=list(low.edges(o['source'](0)));hi=list(high.edges(o['source'](0)))
    assert len(lo)==len(hi)==7
    low_rr=(2,2,2,2,-6);high_lf=(0,0,1,2,-7)
    assert low_rr in {w for i,j,w in lo} and high_lf not in {w for i,j,w in lo}
    assert high_lf in {w for i,j,w in hi} and low_rr not in {w for i,j,w in hi}
    assert low.interior(low_rr) and not high.interior(low_rr)
    assert high.interior(high_lf) and not low.interior(high_lf)
    high_rf=(2,0,1,2,-7)
    assert high.interior(high_rf) and not low.interior(high_rf)
    assert not o['high'](0,0) and not o['high'](1,1) and o['high'](2,2)


def test_t0_unavailable_run_and_t1_actual_LAST_x_preserve_true_types():
    for k in range(4):
        g=o['Geometry'](-1,k,0);i=2*g.n+4
        assert i>g.n+g.d+1
        with pytest.raises(ValueError):g.child(o['source'](0),i,0)
        g=o['Geometry'](-1,k,1);i=2*g.n+4
        assert i==g.n+g.d+1
        actual=g.child(o['source'](0),i,0);wrong=o['h3']['source'](2)
        assert actual==o['source'](4) and actual[2:]==wrong[2:]
        assert g.interior(actual) and g.interior(wrong) and actual!=wrong
        bad=[(i,0,wrong)]+o['h3']['path'](2,g)
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,bad)
    for k,t in [(0,0),(1,0),(0,1)]:
        g=o['Geometry'](-1,k,t)
        if g.n==4:
            for flip in (0,1):assert o['path'](flip,g)==o['b5']['path'](4+flip,g)


def test_companion_aliases_and_shortcut_keep_existing_Dxx_and_B2_exception():
    for flip in (0,1):
        assert o['source'](4+flip)==o['e2']['source'](2+flip)
        assert o['interface'](o['source'](4+flip),True)=='Dxx'
        assert o['exit_interface'](o['source'](4+flip),True)=='Dxx'
        g=o['Geometry'](-1,0,0)
        assert o['path'](4+flip,g)==o['e2']['path'](2+flip,g)
        assert len(o['path'](4+flip,g))==4
    g=o['Geometry'](-1,0,0);B2=o['pp']['source'](5)
    # RR to B2 is real, but its nominal one-edge terminal has LAST c at n=3.
    assert g.child(o['source'](4),5,1)==B2
    assert g.child(B2,1,3)!=(2,2,0,0,0)
    for k,t in [(1,0),(0,1),(2,3)]:
        g=o['Geometry'](-1,k,t)
        for kind in (4,5):assert len(o['path'](kind,g))==2
        for kind in (2,3):assert len(o['path'](kind,g))==2


def test_uniform_B5_image_tails_now_cover_all_twenty_four_labels():
    for k,t in [(0,0),(1,0),(0,1),(3,4),(15,10)]:
        g=o['Geometry'](-1,k,t)
        for w in o['b5']['envelope']():
            p=o['uniform_b5_tail'](w,g)
            assert 1<=len(p)<=7 and o['exit_interface'](w,True) is not None
            o['verify_path'](w,g,p,p)
        for kind in range(6):
            p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)


def test_singleton_child_productivity_and_union_escapes_do_not_claim_all_t():
    S=o['b5']['r3']['candidate'](True)
    assert not(o['envelope']()&S)
    for k,t in [(0,0),(0,1),(3,0),(3,1)]:
        g=o['Geometry'](-1,k,t)
        for flip in (0,1):
            edges=set(g.edges(o['source'](flip)));p=o['path'](flip,g)
            assert edges=={p[0]} and len(p)==3
    for k,t in [(0,0),(0,2),(2,4)]:
        g=o['Geometry'](-1,k,t);J=o['h3']['source'](2);K=o['h3']['source'](4)
        assert J in o['envelope']() and K not in o['envelope']()
        p=o['h3']['path'](2,g)
        assert g.child(J,p[0][0],p[0][1])==K and g.interior(K)
        unknown=(2,0,1,2,-5)
        assert g.interior(unknown)
        with pytest.raises(ValueError):o['registered_tail'](unknown,g)


def test_all_native_registry_rows_match_and_corrupt_rows_fail():
    output=(ROOT/'evidence/class-a-boundary-e7-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for prefix,n in [('CLASS_A_E7_CANDIDATE_REGISTRY ',41),('CLASS_A_E7_IMAGE_REGISTRY ',32),('CLASS_A_E7_B5_IMAGE_REGISTRY ',24)]:
        lines=[x for x in output.splitlines() if x.startswith(prefix)]
        assert len(lines)==n
        changed=lines[0].split();changed[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
    assert o['interface'](o['source'](2),True) is None
    assert o['exit_interface'](o['source'](2),True)=='D0'
    for flip in (0,1):
        assert o['source'](2+flip)==o['b4']['source'](3-flip)


def test_invalid_ids_parameters_targets_stars_and_paths_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,6]:
        with pytest.raises(ValueError):o['source'](kind)
    with pytest.raises(ValueError):o['registered_tail'](o['C'],g)
    with pytest.raises(ValueError):o['uniform_b5_tail'](o['C'],g)
    wrong=(9,0,o['source'](4));assert g.interior(wrong[2])
    edges=list(g.edges(o['source'](0)))
    for bad in [[],edges+[edges[0]],[wrong]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    p=o['path'](0,g)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,p)
