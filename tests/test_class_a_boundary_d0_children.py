from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_d0_children.py'))


def test_complete_stars_and_every_indexed_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['pairs'],p['accepted'])==(117,234,297648,5850)
    assert (p['source_path_edges'],p['all_child_walk_edges'],p['uniform_image_tail_edges'])==(468,34884,9880)
    assert (p['source_exit_bound'],p['child_tail_bound'],p['walk_bound'],p['max_walk'])==(2,7,8,8)
    assert p['all_direct_children_productive'] and p['image_equals_B5'] and p['surviving_indexed_stars_equal_reversed_B5']
    assert not p['sources_equal_B5'] and not p['new_companion_stars_or_exits'] and not p['closed_carrier_proved']
    assert (p['image_labels'],p['image_registered_stars'],p['image_uniform_exits'])==(24,22,24)
    assert (p['previous_E7_image_registered_stars'],p['previous_E7_image_uniform_exits'])==(8,8)


def test_small_LAST_first_targets_keep_types_and_clipped_RUN_strips():
    for k,t in [(0,0),(1,0),(0,1)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        actual=g.child(o['source'](0),A+1,0)
        expected=o['reverse'](o['b5']['source'](2) if g.n==3 else o['e7']['source'](0))
        assert actual==expected and g.interior(actual)
        fake=(2,0,*actual[2:])
        assert fake!=actual and g.interior(fake)
        edges=list(g.edges(o['source'](0)))
        bad=[(i,j,fake if (i,j)==(A+1,0) else w) for i,j,w in edges]
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
        assert len(edges)==2*g.n-1 and not o['predicted'](0,g,A,1)
    # At n=4, the nominal first RR pair is actual LAST/RUN, yielding R5.
    g=o['Geometry'](-1,1,0);A=g.n+g.d
    actual=g.child(o['source'](0),g.d+5,1)
    assert g.d+5==A+1 and actual==o['y4']['source'](2)
    fake=(2,2,*actual[2:]);assert g.interior(fake)
    edges=list(g.edges(o['source'](0)))
    with pytest.raises(ValueError):o['verify_star'](0,g,[(i,j,fake if (i,j)==(A+1,1) else w) for i,j,w in edges])
    for k,t in [(2,0),(0,2),(7,3)]:
        g=o['Geometry'](-1,k,t)
        assert not g.interior(g.child(o['source'](0),g.n+g.d+1,0))


def test_surviving_stars_equal_B5_without_identifying_sources_or_rectangles():
    for k,t in [(0,0),(1,0),(0,1),(2,4)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        for kind in (0,1):
            w=o['source'](kind);other=o['b5']['source'](1-kind)
            assert w!=other and w[2:]==other[2:]
            assert set(g.edges(w))==set(g.edges(other))
            i,j=(g.n,A+1) if kind else (A+1,g.n)
            extra,last=g.child(w,i,j),g.child(other,i,j)
            assert extra!=last and not g.interior(extra) and not g.interior(last)
            # The next x-parent run is real; the y-parent ordinal is unavailable.
            i,j=(g.n+1,A+1) if kind else (A+1,g.n+1)
            assert not g.interior(g.child(w,i,j))
            with pytest.raises(ValueError):g.child(other,i,j)


def test_full_image_uniform_tails_and_inherited_source_exits():
    assert o['envelope']()==o['b5']['envelope']()
    for k,t in [(0,0),(1,0),(0,1),(3,4),(17,12)]:
        g=o['Geometry'](-1,k,t)
        for w in o['envelope']():
            p=o['tail'](w,g)
            assert 1<=len(p)<=7
            o['verify_path'](w,g,p,p)
        for kind in (0,1):
            p=o['path'](kind,g)
            assert p==o['e7']['path'](2+kind,g) and len(p)==2
            o['verify_path'](o['source'](kind),g,p,p)


def test_four_cycle_has_exits_and_uniform_T_branch_leaves_image():
    g=o['Geometry'](-1,1,0);A=g.n+g.d
    w=o['source'](0);start=w
    for i,j in [(A+1,0),(0,A+1),(0,A+1),(A+1,0)]:
        w=g.child(w,i,j);assert g.interior(w)
    assert w==start
    for kind in (0,1):
        p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)
    for k,t in [(0,0),(0,1),(2,4)]:
        g=o['Geometry'](-1,k,t);T=o['p3']['source'](2);Y=o['y4']['source'](0)
        assert g.child(o['source'](0),g.d+3,0)==T in o['envelope']()
        assert g.child(T,0,1)==Y not in o['envelope']() and g.interior(Y)


def test_registry_reuses_D0_exit_id_and_preserves_predecessor_counts():
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(33,33)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(35,35)
    for row in r['source_rows']:
        assert row['before'] is None and row['after']=='D0'
        assert row['before_exit']==row['after_exit']=='D0'
    assert sum(row['before'] is not None for row in r['previous_E7_image_rows'])==6
    assert sum(row['after'] is not None for row in r['previous_E7_image_rows'])==8
    missing=[row for row in r['image_rows'] if row['after'] is None]
    assert len(missing)==2 and all(row['after_exit']=='R5' for row in missing)
    # R5/D5 are independent sibling PRs, not imported by this packet.


def test_all_native_registry_rows_match_and_corrupt_rows_fail():
    output=(ROOT/'evidence/class-a-boundary-d0-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,n in [('SOURCE',2),('CANDIDATE',41),('IMAGE',24),('E7_IMAGE',32)]:
        lines=[line for line in output.splitlines() if line.startswith('CLASS_A_D0_'+name+'_REGISTRY ')]
        assert len(lines)==n
        altered=lines[0].split();altered[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(altered),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)


def test_bad_parameters_wrong_interiors_duplicate_omissions_and_walks_refuse():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,2]:
        with pytest.raises(ValueError):o['source'](kind)
    with pytest.raises(ValueError):o['Geometry'](-1,-1,0)
    with pytest.raises(ValueError):o['Geometry'](-1,0,-1)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    edges=list(g.edges(o['source'](0)))
    wrong=(7,0,o['p3']['source'](2));assert g.interior(wrong[2])
    for bad in [[],edges[:-1]+[edges[0]],[wrong]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    edge=edges[0];p=o['walk'](0,g,edge)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_walk'](0,g,edge,bad)
    altered=[p[0],(0,0,o['C'])]+p[2:]
    with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,altered,altered)
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
