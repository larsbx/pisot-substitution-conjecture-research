"""Universal paths from X to eight of nine strict swapped-patch seeds.

Uses mainline exact class-A Geometry and the pending #428 seed->X
certificate (as stacked dependency). No descendant productivity/BH/PSC.
"""
from pathlib import Path
import runpy
ROOT=Path(__file__).resolve().parent
base=runpy.run_path(str(ROOT/'class_a_nine_swap_to_x.py'))
X=base['X']; S1=base['S1']; SEEDS=base['SEEDS']
Aff=base['Aff']; reverse=base['reverse']; Geometry=base['Geometry']
EIGHT=tuple(w for w in SEEDS if w!=S1)
EDGE_AFFINE={
    ((0, 0, 1, 0, -1),(2, 0, 0, -1, 0)): (Aff(1,2,7), Aff(0,0,0)),
    ((0, 0, 1, 0, -1),(2, 0, 0, -1, 1)): (Aff(1,2,6), Aff(0,0,0)),
    ((0, 1, 1, -1, 0),(2, 1, 0, -1, 1)): (Aff(1,2,5), Aff(0,0,0)),
    ((0, 1, 1, -1, 0),(2, 1, 0, -1, 2)): (Aff(1,2,4), Aff(0,0,0)),
    ((0, 2, 0, -1, 1),(2, 1, 0, 0, 0)): (Aff(1,1,2), Aff(1,1,3)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -1)): (Aff(1,1,3), Aff(0,0,0)),
    ((0, 2, 1, 0, -1),(0, 1, 1, -1, 0)): (Aff(2,3,9), Aff(1,1,3)),
    ((1, 1, 0, 1, -1),(0, 2, 0, 0, 0)): (Aff(1,1,4), Aff(1,1,3)),
    ((1, 1, 0, 1, -1),(1, 1, 0, 0, 1)): (Aff(0,0,0), Aff(0,0,0)),
    ((2, 0, 0, -1, 0),(0, 2, 0, -1, 1)): (Aff(0,0,0), Aff(1,1,5)),
    ((2, 0, 0, -1, 0),(0, 2, 0, -1, 2)): (Aff(0,0,0), Aff(1,1,6)),
    ((2, 0, 0, -1, 1),(0, 2, 1, 0, -1)): (Aff(0,0,0), Aff(0,0,1)),
    ((2, 0, 0, -1, 1),(1, 2, 0, 0, 0)): (Aff(1,1,3), Aff(1,1,4)),
    ((2, 0, 0, 1, -1),(0, 0, 0, 0, 1)): (Aff(0,0,0), Aff(0,0,0)),
    ((2, 0, 0, 1, -1),(2, 0, -1, 0, 1)): (Aff(0,0,1), Aff(0,0,0)),
    ((2, 1, 0, -1, 1),(1, 0, -1, 1, 0)): (Aff(1,1,3), Aff(1,1,4)),
    ((2, 1, 0, -1, 2),(1, 1, 0, 1, -1)): (Aff(1,1,3), Aff(0,0,0)),
    ((2, 1, 0, 0, 0),(0, 1, 0, 0, 0)): (Aff(0,0,0), Aff(0,0,0)),
}

PATH_TARGETS={
    (0, 1, 0, 0, 0): ((2, 0, 0, -1, 0), (0, 2, 0, -1, 1), (2, 1, 0, 0, 0), (0, 1, 0, 0, 0)),
    (1, 0, -1, 1, 0): ((2, 0, 0, -1, 1), (0, 2, 1, 0, -1), (0, 1, 1, -1, 0), (2, 1, 0, -1, 1), (1, 0, -1, 1, 0)),
    (0, 2, 0, 0, 0): ((2, 0, 0, -1, 1), (0, 2, 1, 0, -1), (0, 1, 1, -1, 0), (2, 1, 0, -1, 2), (1, 1, 0, 1, -1), (0, 2, 0, 0, 0)),
    (0, 0, 0, 0, 1): ((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -1), (0, 0, 0, 0, 1)),
    (2, 0, -1, 0, 1): ((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -1), (2, 0, -1, 0, 1)),
    (1, 2, 0, 0, 0): ((2, 0, 0, -1, 1), (1, 2, 0, 0, 0)),
    (1, 1, 0, 0, 1): ((2, 0, 0, -1, 1), (0, 2, 1, 0, -1), (0, 1, 1, -1, 0), (2, 1, 0, -1, 2), (1, 1, 0, 1, -1), (1, 1, 0, 0, 1)),
    (2, 1, 0, -1, 1): ((2, 0, 0, -1, 1), (0, 2, 1, 0, -1), (0, 1, 1, -1, 0), (2, 1, 0, -1, 1)),
}


def path(seed):
    if seed not in PATH_TARGETS:
        raise ValueError('no uniform forward-X path for this source')
    current=X;out=[]
    for target in PATH_TARGETS[seed]:
        i,j=EDGE_AFFINE[(current,target)]
        out.append((i,j,target))
        current=target
    assert current==seed
    return out

def symbolic_certificate():
    assert set(PATH_TARGETS)==set(EIGHT)
    assert len(EDGE_AFFINE)==18
    states={X};edges=0
    for seed in EIGHT:
        current=X;steps=path(seed)
        for i,j,target in steps:
            base['certified_transport'](current,i,j,target)
            base['certified_transport'](reverse(current),j,i,reverse(target))
            states.add(target);current=target;edges+=2
        assert current==seed
        assert base['paths']()[seed][-1][2]==X
    allstates=states|{reverse(w) for w in states}
    for w in allstates:
        base['strict'](w)
    assert edges==70 and max(len(path(seed)) for seed in EIGHT)==6
    return dict(eight_swap_seeds=len(EIGHT),exception=S1,
                unique_affine_transitions=len(EDGE_AFFINE),
                exact_symbolic_oriented_path_edges=edges,
                base_path_states=len(states),oriented_path_states=len(allstates),
                strict_physical_margins=2*len(allstates),
                max_X_to_seed_depth=6,
                eight_seeds_in_X_SCC_conditioned_on_base_seed_to_X=True,
                S1_in_X_SCC_unproved=True,
                all_descendants_reach_X_unproved=True,
                universal_BH=False)

def literal_probe():
    specimens=edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            for seed in EIGHT:
                for flip in (0,1):
                    current=reverse(X) if flip else X
                    for ii,jj,target in path(seed):
                        i=ii.k*k+ii.t*t+ii.c
                        j=jj.k*k+jj.t*t+jj.c
                        if flip:i,j,target=j,i,reverse(target)
                        assert g.child(current,i,j)==target,(k,t,seed,current,i,j,target)
                        assert g.interior(target)
                        current=target;edges+=1
                    assert current==(reverse(seed) if flip else seed)
            specimens+=1
    assert specimens==117 and edges==8190
    return dict(exact_Fraction_specimens=specimens,
                actual_oriented_forward_edges=edges)

if __name__=='__main__':
    import json
    print(json.dumps(symbolic_certificate(),indent=2,sort_keys=True))
    print(json.dumps(literal_probe(),indent=2,sort_keys=True))
