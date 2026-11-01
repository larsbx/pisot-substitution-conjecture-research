"""Uniform oriented-X SCC bridge and reversal-invariant descendant closure."""
from pathlib import Path
import runpy
import pytest
from collections import deque

m=runpy.run_path(str(Path(__file__).resolve().parents[1]/
                     'oracles/python/class_a_x_reversal_hub.py'))


def test_unbounded_affine_transport_and_exact_rational_physical_proof():
    r=m['symbolic_certificate']()
    assert r['X_to_reverse_X_depth']==4
    assert r['reverse_X_to_X_depth']==4
    assert r['directed_symbolic_occurrence_checks']==8
    assert r['oriented_path_states']==8
    assert r['strict_physical_margins']==16
    assert r['forward_X_closure_reversal_invariant']
    assert not r['implies_all_X_descendants_productive']
    assert r['no_universal_BH']


def test_exact_literal_geometry_117_members_both_orientations():
    r=m['independent_literal_probe']()
    assert r['specimens']==117
    assert r['actual_oriented_bridge_edges']==936
    assert r['all_chosen_source_stars_reverse_consistent']


def test_actual_last_and_run_indices_in_smallest_chamber():
    g=m['Geometry'](-1,0,0)
    assert g.n==3 and g.d==5
    path=m['actual_steps'](0,0)
    assert [(i,j) for i,j,_ in path]==[(7,0),(0,5),(3,3),(0,4)]
    assert g.words[2][g.n]==1             # actual LAST c in y-image
    assert g.words[1][g.n+1]==0           # actual LAST x in c-image
    assert g.child(m['H1'],g.n,g.n)==m['Z']
    assert g.child(m['Z'],0,g.n+1)==m['RX']


def test_lift_every_chosen_path_by_universal_reversal_bridge():
    for k,t in ((0,0),(1,0),(0,3),(3,3)):
        g=m['Geometry'](-1,k,t)
        X,Q,C=m['X'],(2,0,0,-1,1),m['C']
        path=[(g.d+1,0,Q),(1,2,C)]
        assert m['verify'](g,X,path)==C
        lifted=m['lifted_reversal_path'](k,t,path)
        assert len(lifted)==6
        assert m['verify'](g,X,lifted)==C
        # One intermediate prefix from X -> Q also lifts to X -> R(Q).
        prefix=m['lifted_reversal_path'](k,t,path[:1])
        assert m['verify'](g,X,prefix)==m['reverse'](Q)


def test_finite_complete_x_closure_is_reversal_closed():
    for k,t in ((0,0),(1,1),(3,0)):
        g=m['Geometry'](-1,k,t)
        seen={m['X']};todo=deque([m['X']])
        while todo:
            w=todo.popleft()
            if w[0]==w[1] and w[2:]==(0,0,0):continue
            for i in range(len(g.words[w[0]])):
                for j in range(len(g.words[w[1]])):
                    v=g.child(w,i,j)
                    if g.interior(v) and v not in seen:
                        seen.add(v);todo.append(v)
                        assert len(seen)<6000
        assert m['RX'] in seen
        assert all(m['reverse'](w) in seen for w in seen)


def test_bad_typed_target_and_nonconical_indices_fail_closed():
    with pytest.raises(AssertionError):
        m['certify_edge'](m['X'],m['D']+2,0,m['H1'])
    with pytest.raises(AssertionError):
        m['nonnegative'](m['Aff'](k=-1,c=1000))
    with pytest.raises(AssertionError):
        m['certify_strict']((0,0,0,0,100))
    with pytest.raises((AssertionError,IndexError)):
        g=m['Geometry'](-1,0,0)
        m['verify'](g,m['X'],[(g.d+2,0,m['Z'])])
