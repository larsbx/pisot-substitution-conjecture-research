from pathlib import Path
import runpy
import pytest
ROOT=Path(__file__).resolve().parents[1]
o=runpy.run_path(str(ROOT/'oracles/python/class_a_boundary_p9_children.py'))


def test_complete_stars_selected_exits_and_every_actual_first_choice():
    p=o['probe']()
    assert (p['members'],p['source_cells'],p['pairs'],p['accepted'])==(117,234,122616,6750)
    assert (p['source_path_edges'],p['companion_path_edges'],p['all_child_walk_edges'])==(1422,1746,39618)
    assert (p['image_labels'],p['image_registered_stars'],p['image_uniform_exits'],p['image_guarded_tail_labels'])==(24,2,20,4)
    assert p['all_direct_children_productivity_proved'] and p['max_selected_walk']==9
    assert not p['closed_carrier_proved'] and not p['new_companion_stars']


def test_all_nine_kinds_and_count_thresholds_at_unbalanced_members():
    for k,t in [(0,9),(1,8),(2,7),(3,6),(17,0),(17,2),(21,13)]:
        g=o['Geometry'](-1,k,t)
        for kind in (0,1):
            actual=set(g.edges(o['source'](kind)))
            assert len(actual)==2*g.n+2+(k>=2)
            assert len(actual)==o['count'](k,t)
            chosen={(i,j,g.child(o['source'](kind),i,j)) for i in range(len(g.words[o['source'](kind)[0]])) for j in range(len(g.words[o['source'](kind)[1]])) if o['predicted'](kind,g,i,j)}
            assert actual==chosen
            o['verify_star'](kind,g,list(actual))


def test_chamber_image_is_not_constant_and_all_labels_are_witnessed():
    for k,want in [(0,14),(1,12),(2,14),(3,14),(4,14)]:
        g=o['Geometry'](-1,k,0)
        image={w for kind in (0,1) for i,j,w in g.edges(o['source'](kind))}
        assert len(image)==want and image<o['envelope']()
    g=o['Geometry'](-1,0,0)
    packet=o['walk'](0,g,(g.n-1,g.n,(2,1,1,3,-5)))
    o['verify_walk'](0,g,(g.n-1,g.n,(2,1,1,3,-5)),packet)
    assert len(packet)==9


def test_uniform_companions_and_actual_LAST_x_conditional_helper():
    for k,t in [(0,0),(0,6),(1,0),(2,4),(11,3)]:
        g=o['Geometry'](-1,k,t)
        for kind in range(4):
            p=o['companion_path'](kind,g);o['verify_path'](o['companion'](kind),g,p,p)
            assert len(p)==(4 if kind<2 else 3)
            assert o['interface'](o['companion'](kind),True) is None
            assert o['exit_interface'](o['companion'](kind),True)==('W9' if kind<2 else 'B9')
        X=o['companion'](4)
        assert g.interior(X) # uniform overlap does not make its chosen k0 path uniform
        assert o['exit_interface'](X,True) is None
        actual=g.child(X,g.n+g.d+1,0)
        assert actual[:2]==(0,0) and actual[2:]==(0,-3,5-k)
        if k==0:
            p=o['companion_path'](4,g);o['verify_path'](X,g,p,p);assert len(p)==6
            assert p[0][2]==o['j9']['j8']['source'](20)
        else:
            for kind in (4,5):
                with pytest.raises(ValueError):o['companion_path'](kind,g)
                with pytest.raises(ValueError):o['tail'](o['companion'](kind),g)
    g=o['Geometry'](-1,0,0);X=o['companion'](4)
    bad=[(g.n+g.d+1,0,(2,0,0,-3,5))]+o['j9']['j8']['path'](20,g)
    with pytest.raises(ValueError):o['verify_path'](X,g,bad,bad)


def test_L8_is_reused_only_where_strict_and_never_gets_uniform_exit():
    for k in range(4):
        g=o['Geometry'](-1,k,1);w=o['j9']['j8']['source'](27)
        assert w in o['envelope']() and g.interior(w)==(k==0)
        assert o['exit_interface'](w,True) is None
        if k==0:
            p=o['tail'](w,g);assert len(p)==7;o['verify_path'](w,g,p,p)
        else:
            with pytest.raises(ValueError):o['tail'](w,g)


def test_uniform_ancestry_and_image_escape():
    for k,t in [(0,0),(1,0),(4,3)]:
        g=o['Geometry'](-1,k,t)
        for kind in (0,1):
            assert g.child(o['j9']['source'](kind),g.n+k+3 if kind else 0,0 if kind else g.n+k+3)==o['source'](kind)
        W=o['companion'](0);B=o['companion'](2)
        assert W in o['envelope']() and B not in o['envelope']()
        assert g.child(W,g.t+4,0)==B and g.interior(B)
        assert o['path'](0,g)[0][2] not in o['j9']['envelope']()


def test_registry_changes_are_separate_and_preserve_old_aliases():
    r=o['reconciliation']()
    assert (r['before_registered_including_terminal'],r['after_registered_including_terminal'],r['before_exits_including_terminal'],r['after_exits_including_terminal'])==(33,33,35,35)
    assert sum(x['before'] is not None for x in r['previous_J9_image_rows'])==0
    assert sum(x['after'] is not None for x in r['previous_J9_image_rows'])==2
    assert sum(x['after_exit'] is not None for x in r['previous_J9_image_rows'])==2
    assert o['interface'](o['source'](0)) is None and o['interface'](o['source'](0),True)=='P9'
    assert o['exit_interface'](o['source'](0))==o['exit_interface'](o['source'](0),True)=='P9'
    assert (o['interface']((2,0,0,3,-4),True),o['exit_interface']((2,0,0,3,-4),True))==('L','L')


def test_parameters_wrong_strict_targets_stars_and_paths_fail_closed():
    g=o['Geometry'](-1,0,0)
    for args in [(2,0,0),(-1,0,0),(0,-1,0),(0,10,0),(0,0,4)]:
        with pytest.raises(ValueError):o['predicted'](args[0],g,*args[1:])
    with pytest.raises(ValueError):o['predicted'](0,o['Geometry'](1,0,0),0,0)
    with pytest.raises(ValueError):o['count'](-1,0)
    with pytest.raises(ValueError):o['companion'](6)
    with pytest.raises(ValueError):o['tail'](o['C'],g)
    edges=list(g.edges(o['source'](0)));wrong=(0,0,o['companion'](0));assert g.interior(wrong[2])
    for bad in [[],edges[:-1]+[edges[0]],[wrong]]:
        with pytest.raises(ValueError):o['verify_star'](0,g,bad)
    with pytest.raises(ValueError):o['walk'](0,g,wrong)
    p=o['path'](0,g)
    for bad in [p[:-1],p+[p[-1]],p[:-1]+[(1,2,(2,0,0,0,0))]]:
        with pytest.raises(ValueError):o['verify_path'](o['source'](0),g,bad,p)



def test_registry_parser_refuses_omissions_duplicates_and_corruption():
    import ast
    code=(ROOT/'oracles/python/class_a_boundary_j9_children.py').read_text()
    fn=next(n for n in ast.parse(code).body if isinstance(n,ast.FunctionDef) and n.name=='verify_native_registry')
    ids=ast.literal_eval(fn.body[0].value);ids.update(W9=64,B9=65)
    rec=o['reconciliation']();lines=[]
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('J9_IMAGE','previous_J9_image_rows')]:
        for r in rec[key]:
            lines.append('CLASS_A_P9_'+name+'_REGISTRY '+' '.join(map(str,r['label']+[ids[r[k]] for k in ('before','after','before_exit','after_exit')])))
    output='\n'.join(lines)+'\n'
    assert len(lines)==107 # synthetic parser contract, NOT a native receipt
    o['verify_native_registry'](output)
    for line in [lines[0],lines[8],lines[49],lines[73]]:
        parts=line.split();parts[-1]='999'
        for bad in [output.replace(line+'\n','',1),output+line+'\n',output.replace(line,' '.join(parts),1)]:
            with pytest.raises(ValueError):o['verify_native_registry'](bad)
