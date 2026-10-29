from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_j8_children.py'))


def test_complete_stars_and_every_actual_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['path_source_cells'])==(117,234,2628)
    assert (p['pairs'],p['accepted'],p['image_labels'])==(122616,6804,18)
    assert (p['source_and_companion_path_edges'],p['all_child_walk_edges'],p['guarded_image_tail_edges'])==(11502,39762,7532)
    assert (p['source_exit_k0'],p['source_exit_kpositive'],p['child_tail_bound'],p['walk_bound'],p['max_walk'])==(6,4,8,9,9)
    assert p['all_actual_direct_children_productive'] and p['conditional_L8_k0_only']
    assert not p['all_image_labels_full_cone_uniform_sources'] and not p['new_companion_stars'] and not p['closed_carrier_proved']
    assert (p['image_registered_stars'],p['image_uniform_exits'])==(2,16)
    assert (p['previous_E7_image_registered_stars'],p['previous_E7_image_uniform_exits'])==(10,10)


def test_exact_k0_separator_and_conditional_source_geometry():
    for k,t in [(0,0),(0,7),(1,0),(1,7),(9,2),(19,11)]:
        g=o['Geometry'](-1,k,t);q=(3,-g.n-3,1)
        # Independent integer coefficient reduction of (beta+1)*q.
        lhs=tuple(a+b for a,b in zip(g.times_beta(q),q))
        assert lhs==(1,-k,0)
        assert g.sign(q)==(1 if k==0 else -1)
        for flip in (0,1):
            w=o['source'](26+flip)
            assert g.interior(w)==(k==0)
            assert o['exit_interface'](w,True) is None
            if k:
                with pytest.raises(ValueError):o['tail'](w,g)
            else:
                p=o['tail'](w,g);assert len(p)==7;o['verify_path'](w,g,p,p)


def test_member_images_are_sixteen_or_fourteen_not_chamber_union():
    for k,t in [(0,0),(0,5),(1,0),(3,4)]:
        g=o['Geometry'](-1,k,t);seen=set()
        for kind in (0,1):
            edges=list(g.edges(o['source'](kind)))
            assert len(edges)==2*g.n+3+(k==0)
            seen|={w for i,j,w in edges}
        assert len(seen)==(16 if k==0 else 14) and seen<o['envelope']()
        assert (o['source'](2) in seen)==(k==0)
        assert (o['r4']['source'](4) in seen)==(k>=1)
        assert (o['source'](26) in seen)==(k==0)


def test_reused_L_G5_aliases_and_guarded_helpers_are_distinct():
    for flip in (0,1):
        assert o['source'](4+flip)==o['h3']['source'](7-flip)
        assert o['source'](16+flip)==o['r4']['source'](11-flip)
        assert o['interface'](o['source'](4+flip),True)=='L'
        assert o['exit_interface'](o['source'](16+flip),True)=='G5'
    for k,t in [(0,0),(0,3),(1,2),(2,3),(17,12)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(28):
            group=kind//2
            if group in (11,13) and k!=0 or group==12 and k!=1:
                with pytest.raises(ValueError):o['path'](kind,g)
                if group!=13:assert g.interior(o['source'](kind))
            else:
                p=o['path'](kind,g);o['verify_path'](o['source'](kind),g,p,p)
                assert len(p)==o['path_length'](kind,g)
        for kind in range(22,28):assert o['exit_interface'](o['source'](kind),True) is None


def test_E7_ancestry_only_tge3_and_xc_cc_small_types_are_not_aliases():
    for k in range(4):
        for t in range(5):
            g=o['Geometry'](-1,k,t);i=2*g.n+5;A=g.n+g.d
            if t<2:
                assert i>A+1
                with pytest.raises(ValueError):g.child(o['e7']['source'](0),i,0)
            elif t==2:
                w=g.child(o['e7']['source'](0),i,0)
                assert i==A+1 and w[:2]==(0,0) and w[2:]==o['source'](0)[2:]
                assert g.interior(w)
            else:assert g.child(o['e7']['source'](0),i,0)==o['source'](0)
    for t in range(4):
        g=o['Geometry'](-1,0,t);R=o['source'](6);C=o['source'](14);Q=o['source'](18)
        assert g.child(R,0,g.n)==C and C[2:]==Q[2:] and C!=Q
        assert g.interior(C) and g.interior(Q)
        bad=[(0,g.n,Q)]+o['path'](18,g)
        with pytest.raises(ValueError):o['verify_path'](R,g,bad,bad)
        g=o['Geometry'](-1,1,t);A=o['source'](10);D=o['source'](24)
        actual=g.child(A,0,g.n);other=o['e7']['source'](4)
        assert actual==D and D[2:]==other[2:] and D!=other
        bad=[(0,g.n,other)]+o['e7']['path'](4,g)
        with pytest.raises(ValueError):o['verify_path'](A,g,bad,bad)


def test_uniform_two_cycle_has_exits_and_image_escapes():
    for k,t in [(0,0),(0,3),(1,0),(3,4)]:
        g=o['Geometry'](-1,k,t)
        for flip in (0,1):
            w=o['source'](flip);B=o['source'](12+flip)
            i,j=(g.n+k+2,g.n) if flip else (g.n,g.n+k+2)
            assert g.child(w,i,j)==B in o['envelope']()
            assert g.child(B,0 if flip else k+1,k+1 if flip else 0)==w not in o['envelope']()
            p=o['path'](flip,g);o['verify_path'](w,g,p,p)
            assert p[0][2] not in o['e7']['envelope']()
            p=o['walk'](flip,g,(i,j,B));o['verify_walk'](flip,g,(i,j,B),p)


def test_native_registry_all_119_rows_and_uniform_conditional_separation():
    output=(ROOT/'evidence/class-a-boundary-j8-2026-10-29/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,n in [('SOURCE',28),('CANDIDATE',41),('IMAGE',18),('E7_IMAGE',32)]:
        lines=[x for x in output.splitlines() if x.startswith('CLASS_A_J8_'+name+'_REGISTRY ')]
        assert len(lines)==n
        changed=lines[0].split();changed[-1]='999'
        for bad in [output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'])==(33,33)
    assert (r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(35,35)
    assert sum(x['before'] is not None for x in r['previous_E7_image_rows'])==8
    assert sum(x['after'] is not None for x in r['previous_E7_image_rows'])==10


def test_bad_parameters_interiors_corrupt_stars_and_walks_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,4,0),(0,0,10)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    for kind in [-1,28]:
        with pytest.raises(ValueError):o['source'](kind)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    with pytest.raises(ValueError):o['Geometry'](-1,-1,0)
    edges=list(g.edges(o['source'](0)))
    wrong=(0,1,o['r4']['source'](10));assert g.interior(wrong[2])
    for bad in [[],edges[:-1]+[edges[0]],[wrong]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
    edge=edges[0];p=o['walk'](0,g,edge)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_walk'](0,g,edge,bad)
