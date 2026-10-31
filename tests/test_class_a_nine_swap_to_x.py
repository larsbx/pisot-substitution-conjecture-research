"""All nine literal swapped-patch seed exits; no all-descendant promotion."""
import pytest
from collections import deque
from pathlib import Path
import runpy
source=runpy.run_path(str(Path(__file__).resolve().parents[1]/
    'oracles/python/class_a_nine_swap_to_x.py'))
(symbolic_certificate,literal_probe,swapped_seed_candidates,
 certified_transport,strict,nonnegative,Aff,SEEDS,paths,Geometry,
 X,S1,N,Q,C,reverse)=(source[name] for name in (
    'symbolic_certificate','literal_probe','swapped_seed_candidates',
    'certified_transport','strict','nonnegative','Aff','SEEDS','paths',
    'Geometry','X','S1','N','Q','C','reverse'))

def test_nine_seed_uniform_affine_paths_and_strict_margin_certificates():
    r=symbolic_certificate()
    assert r['strict_swap_seeds']==9
    assert r['seed_candidates']==12
    assert r['symbolic_oriented_edges_to_X']==68
    assert r['max_seed_to_X_depth']==5
    assert r['max_seed_to_C_depth']==7
    assert r['oriented_path_states']==32
    assert r['strict_physical_margins']==64
    assert r['universal_BH'] is False

def test_original_exact_Fraction_word_oracle_and_both_reversals():
    r=literal_probe()
    assert r==dict(exact_Fraction_specimens=117,real_oriented_selected_edges=7956)

def test_all_swapped_patches_have_three_strict_of_four_pairs():
    selected,excluded=swapped_seed_candidates()
    assert len(selected)==9 and selected==set(SEEDS)
    assert len(excluded)==3
    for k,t in ((0,0),(0,3),(3,0),(2,2)):
        g=Geometry(-1,k,t)
        assert all(g.interior(w) for w in selected)
        assert all(not g.interior(w) for w in excluded)
        assert g.child(X,g.d+1,0)==Q
        assert g.child(Q,1,2)==C

def test_reverse_reachability_does_not_imply_reverse_graph_coverage():
    # At this concrete completed parameter member, the valid swapped
    # seed S1=(x,x,0,1,0) has a 3-edge path TO X, but is NOT reachable
    # FROM the four named sources X,Y0,CY,CC. The two claims differ.
    g=Geometry(-1,3,0)
    four=((0,0,1,0,-1),(2,2,1,-1,-1),(1,2,0,-2,2),(1,1,0,-2,3))
    seen=set(four)
    q=deque(four)
    while q:
        w=q.popleft()
        if w[0]==w[1] and w[2:]==(0,0,0):continue
        for i in range(len(g.words[w[0]])):
            for j in range(len(g.words[w[1]])):
                nxt=g.child(w,i,j)
                if g.interior(nxt) and nxt not in seen:
                    seen.add(nxt);q.append(nxt)
                    assert len(seen)<6000
    assert len(seen)==350
    assert S1 not in seen
    current=S1
    for aa,bb,target in paths()[S1]:
        i=aa.k*3+aa.t*0+aa.c if isinstance(aa,Aff) else aa
        j=bb.k*3+bb.t*0+bb.c if isinstance(bb,Aff) else bb
        assert g.child(current,i,j)==target
        current=target
    assert current==X

def test_bad_indices_and_forged_targets_rejected():
    with pytest.raises(AssertionError):
        certified_transport(S1,N+2,0,(2,0,0,1,0))
    with pytest.raises(AssertionError):
        nonnegative(Aff(k=-1,c=1000))
    with pytest.raises(AssertionError):
        strict((0,0,0,0,100))
    for w in SEEDS:
        assert reverse(reverse(w))==w
