from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_j9_children.py'))


def test_complete_indexed_stars_and_uniform_selected_source_exits():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['path_source_cells'])==(117,234,702)
    assert (p['pairs'],p['accepted'],p['image_labels'])==(122616,5390,34)
    assert (p['source_and_companion_path_edges'],p['registered_image_tail_edges'])==(4482,1422)
    assert (p['source_exit_k0'],p['source_exit_kpositive'],p['P9_exit_k0'],p['P9_exit_kpositive'],p['H9_exit'])==(8,7,7,6,6)
    assert not p['all_direct_children_productivity_proved'] and not p['new_companion_stars'] and not p['closed_carrier_proved']
    assert (p['image_registered_stars'],p['image_uniform_exits'])==(0,2)
    assert (p['previous_E7_image_registered_stars'],p['previous_E7_image_uniform_exits'])==(12,12)


def test_exact_half_separator_and_every_piecewise_count_boundary():
    for k,t in [(0,0),(1,0),(2,0),(3,0),(4,1),(3,1),(2,1),(1,1),(1,2),(1,3),(1,4),(22,4),(4,21)]:
        g=o['Geometry'](-1,k,t);q=(2,-2*g.n-5,2);g4=(4,-g.n-3,1)
        assert tuple(a+b for a,b in zip(g.times_beta(g4),g4))==(2,1-k,0)
        assert g.times_beta(q)==(-4,g.n+t-k+5,-1)
        assert g.sign(q)==(1 if t>=k-2 else -1)
        for flip in (0,1):
            edges=list(g.edges(o['source'](flip)))
            assert len(edges)==o['count'](k,t)
    for t in range(5):
        assert o['count'](t+2,t)==o['count'](t+3,t)==4*t+9


def test_equal_counts_do_not_identify_opposite_half_targets():
    for t in range(4):
        high=o['Geometry'](-1,t+2,t);low=o['Geometry'](-1,t+3,t)
        hi=list(high.edges(o['source'](0)));lo=list(low.edges(o['source'](0)))
        assert len(hi)==len(lo)==4*t+9
        fr=(0,2,-1,-4,9);rr=(2,2,-2,-4,8)
        assert fr in {w for i,j,w in hi} and fr not in {w for i,j,w in lo}
        assert rr in {w for i,j,w in lo} and rr not in {w for i,j,w in hi}
        assert high.interior(fr) and not low.interior(fr)
        assert low.interior(rr) and not high.interior(rr)


def test_actual_endpoint_types_and_E7_ancestry_only_tge4():
    for k in range(4):
        for t in range(6):
            g=o['Geometry'](-1,k,t);i=2*g.n+6;A=g.n+g.d
            if t<=2:
                assert i>A+1
                with pytest.raises(ValueError):g.child(o['e7']['source'](0),i,0)
            elif t==3:
                actual=g.child(o['e7']['source'](0),i,0)
                assert i==A+1 and actual[:2]==(0,0) and actual[2:]==o['source'](0)[2:]
                assert actual!=o['source'](0) and g.interior(actual)
            else:assert g.child(o['e7']['source'](0),i,0)==o['source'](0)
    for t in range(5):
        g=o['Geometry'](-1,0,t);P=o['source'](2);H=o['source'](4);fake=o['r4']['source'](11)
        assert g.child(P,0,0)==H and H!=fake and g.interior(H) and g.interior(fake)
        # A fictitious RUN at ordinal zero has both the wrong type and prefix.
        bad=[(0,0,fake)]+o['r4']['path'](11,g)
        with pytest.raises(ValueError):o['verify_path'](P,g,bad,bad)


def test_source_and_companion_paths_are_full_cone_but_companion_stars_absent():
    for k,t in [(0,0),(0,4),(1,0),(2,1),(3,5),(17,12)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(6):
            p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)
            assert len(p)==o['path_length'](kind,g)
            if kind<2:assert p[0] in set(g.edges(o['source'](kind)))
        for kind in range(2,6):
            assert o['interface'](o['source'](kind),True) is None
            assert o['exit_interface'](o['source'](kind),True) in ('P9','H9')
        for flip in (0,1):
            p=o['registered_tail'](o['source'](2+flip),g)
            assert p[0][2] not in o['envelope']()


def test_image_is_chamber_wide_and_unknown_tail_refuses_despite_interior_source():
    g=o['Geometry'](-1,0,0)
    image={w for kind in (0,1) for i,j,w in g.edges(o['source'](kind))}
    assert len(image)==14 and image<o['envelope']()
    g=o['Geometry'](-1,3,0)
    image={w for kind in (0,1) for i,j,w in g.edges(o['source'](kind))}
    assert len(image)==16 and image<o['envelope']()
    for k,t in [(0,0),(1,2),(3,0)]:
        g=o['Geometry'](-1,k,t);unknown=(0,2,-1,-4,8)
        assert unknown in o['envelope']() and g.interior(unknown)
        with pytest.raises(ValueError):o['registered_tail'](unknown,g)


def test_all_113_native_registry_rows_match_and_corrupt_rows_fail():
    output=(ROOT/'evidence/class-a-boundary-j9-2026-10-29/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,n in [('SOURCE',6),('CANDIDATE',41),('IMAGE',34),('E7_IMAGE',32)]:
        lines=[x for x in output.splitlines() if x.startswith('CLASS_A_J9_'+name+'_REGISTRY ')]
        assert len(lines)==n
        changed=lines[0].split();changed[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(33,33)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(35,35)
    assert sum(x['before'] is not None for x in r['previous_E7_image_rows'])==10
    assert sum(x['after'] is not None for x in r['previous_E7_image_rows'])==12


def test_bad_parameters_wrong_interiors_stars_and_paths_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,4,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,6]:
        with pytest.raises(ValueError):o['source'](kind)
    for f in ('high','count'):
        with pytest.raises(ValueError):o[f](-1,0)
    with pytest.raises(ValueError):o['registered_tail'](o['C'],g)
    edges=list(g.edges(o['source'](0)))
    wrong=(0,6,(0,2,-1,-4,8));assert g.interior(wrong[2])
    for bad in [[],edges[:-1]+[edges[0]],[wrong]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    p=o['path'](0,g)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,p)
