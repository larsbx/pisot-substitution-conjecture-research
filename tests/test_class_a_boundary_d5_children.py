from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_d5_children.py'))


def test_all_pairs_indexed_first_choices_and_six_label_union():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['path_source_cells'])==(117,234,1053)
    assert (p['pairs'],p['accepted'],p['source_path_edges'],p['all_child_walk_edges'])==(130572,3744,2457,5850)
    assert (p['image_labels'],p['max_walk'],p['first_choice_walk_bound'],p['child_tail_bound'])==(6,7,7,6)
    assert p['all_direct_children_productive'] and p['source_exit_bound']==1
    assert (p['image_typed_terminals'],p['image_classified_nonterminal_stars'],p['image_registered_exits'])==(2,0,6)
    assert not p['closed_carrier_proved'] and p['S43_escape'] and p['image_escape']


def test_exact_touching_neighbors_are_excluded_without_epsilon():
    for k,t in [(0,0),(0,1),(3,0),(2,3)]:
        g=o['Geometry'](-1,k,t);d,n,A=g.d,g.n,g.n+g.d
        for i,j,w in [(d+1,0,(2,1,0,-1,0)),(d,1,(2,2,0,0,1)),
                      (d+2,1,(2,2,0,0,-1)),(A,n+1,(2,0,0,0,1)),
                      (A+1,n,(0,2,0,0,-1))]:
            assert g.child(o['BASE'][0],i,j)==w
            assert not g.interior(w) and not o['predicted'](0,g,i,j)
            assert not o['predicted'](1,g,j,i)
            assert not g.interior(g.child(o['source'](1),j,i))
        assert g.interior(g.child(o['BASE'][0],d,0))
        assert g.interior(g.child(o['BASE'][0],d+1,1))


def test_xx_terminal_is_retained_and_normalization_is_an_actual_edge():
    for k,t in [(0,0),(1,0),(0,2)]:
        g=o['Geometry'](-1,k,t);A=g.n+g.d
        assert g.child(o['BASE'][0],A+1,g.n+1)==o['X0']!=o['C']
        assert g.child(o['X0'],1,1)==o['C']
        assert o['interface'](o['X0'],True)=='X0_terminal'
        assert o['tail'](o['C'],g)==[]
        edge=(A+1,g.n+1,o['X0'])
        assert len(o['walk'](0,g,edge))==2
        for wrong in [o['C'],(0,1,0,0,0)]:
            with pytest.raises(ValueError):o['walk'](0,g,(edge[0],edge[1],wrong))
        assert g.interior((0,1,0,0,0))
        with pytest.raises(ValueError):o['tail']((0,1,0,0,0),g)


def test_all_uniform_companion_exits_but_no_new_companion_stars():
    for k,t in [(0,0),(0,1),(3,2)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(9):
            p=o['path'](kind,g)
            o['verify_path'](kind,g,p)
            assert len(p)==(1,6,2,1,1)[kind//2]
        for kind in range(2,8):
            assert o['interface'](o['source'](kind),True) is None
            assert o['exit_interface'](o['source'](kind),True) is not None
        for kind in (0,1):
            for edge in g.edges(o['source'](kind)):
                p=o['walk'](kind,g,edge);o['verify_walk'](kind,g,edge,p)
                assert len(p)<=7
        with pytest.raises(ValueError):o['verify_star'](8,g,[])


def test_current_r5_b5_union_inventory_and_remaining_escapes():
    r=o['reconciliation']()
    assert (r['S41']['after_registered_including_terminals'],r['S41']['after_exits'])==(31,33)
    assert (r['S43']['after_registered_including_terminals'],r['S43']['after_exits'])==(33,35)
    assert (r['Y4_IMAGE']['after_registered_including_terminals'],r['Y4_IMAGE']['after_exits'])==(18,18)
    assert (r['R5_IMAGE']['after_registered_including_terminals'],r['R5_IMAGE']['after_exits'])==(8,8)
    assert (r['B5_IMAGE']['after_registered_including_terminals'],r['B5_IMAGE']['after_exits'])==(20,22)
    assert r['IMAGE']['typed_terminals']==2
    for k,t in [(0,0),(2,1)]:
        g=o['Geometry'](-1,k,t)
        assert g.child(o['BASE'][0],g.d,0)==o['BASE'][1] not in o['candidate'](True)
        assert g.child(o['BASE'][1],1,3)==o['y4']['T1'] not in o['envelope']()
    # Earlier scoped registries retain their historical coverage unchanged.
    assert o['r5']['interface'](o['BASE'][0],True) is None
    assert o['b5']['interface'](o['r5']['R5'],True) is None


def test_all_150_native_inventory_rows_match_and_corruption_is_refused():
    output=(ROOT/'evidence/class-a-boundary-d5-2026-10-28/driver.log').read_text()
    o['verify_native_registry'](output)
    for name,rec in o['reconciliation']().items():
        prefix='CLASS_A_D5_'+name+'_REGISTRY '
        lines=[line for line in output.splitlines() if line.startswith(prefix)]
        assert len(lines)==rec['labels']
        changed=lines[0].split();changed[-1]='0' if changed[-1]!='0' else '39'
        for bad in (output.replace(lines[0]+'\n','',1),output+'\n'+lines[0],output.replace(lines[0],' '.join(changed),1)):
            with pytest.raises(ValueError):o['verify_native_registry'](bad)


def test_bad_inputs_wrong_interior_targets_and_malformed_stars_walks():
    g=o['Geometry'](-1,0,0)
    for kind,i,j in [(-1,0,0),(2,0,0),(0,-1,0),(0,10,0),(0,0,5)]:
        with pytest.raises(ValueError):o['predicted'](kind,g,i,j)
    for kind in (-1,9):
        with pytest.raises(ValueError):o['source'](kind)
    plus=o['Geometry'](1,0,0)
    with pytest.raises(ValueError):o['predicted'](0,plus,0,0)
    with pytest.raises(ValueError):o['path'](0,plus)
    actual=list(g.edges(o['source'](0)))
    for bad in (actual[:-1],actual+[actual[0]],[actual[0]]+actual[:-1]):
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    assert g.interior(o['source'](4)) and o['source'](4) in o['envelope']()
    with pytest.raises(ValueError):o['walk'](0,g,(5,0,o['source'](4)))
    edge=(5,0,o['source'](2));p=o['walk'](0,g,edge)
    for bad in (p[:-1],p+[p[-1]],[(5,0,o['source'](4))]+p[1:],
                p[:-1]+[(p[-1][0],p[-1][1],(2,0,0,0,0))]):
        with pytest.raises(ValueError):o['verify_walk'](0,g,edge,bad)
