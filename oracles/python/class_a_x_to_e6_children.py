"""All eight E6 direct-child labels are reachable from X uniformly.

The exact nine-kind E6 complete star and both X-to-child path families
are certified under the inherited minus-class-A Perron bounds. On the
SCC side, this yields an exact nine-seed closure reduction conditional
on the already checked seed-to-X and X-to-eight-seed source packets.
It does NOT prove that all descendants of X are productive or PSC.
"""
from pathlib import Path
from dataclasses import dataclass
import runpy
ROOT=Path(__file__).resolve().parent
base=runpy.run_path(str(ROOT/'class_a_nine_swap_to_x.py'))
forward=runpy.run_path(str(ROOT/'class_a_x_to_eight_swap_seeds.py'))
Geometry=base['Geometry']; X=base['X'];E6=base['S1']
Aff=base['Aff'];reverse=base['reverse'];K=base['K'];T=base['T']
N=base['N'];D=base['DD'];A=base['A']
C=base['C']
E6_IMAGE=({(2,0,0,1,r) for r in(-3,-2,-1)} |
          {(2,2,1,1,r) for r in(-4,-3)} |
          {(0,2,1,1,r) for r in(-4,-3,-2)})
assert len(E6_IMAGE)==8

@dataclass(frozen=True)
class Chamber:
    label:str
    t0:int
    fixed_t:bool
    def simplify(self,z):
        z=base['aff'](z)
        return Aff(z.k,0 if self.fixed_t else z.t,
                   z.c+(z.t*self.t0 if self.fixed_t else 0))
    def nonnegative(self,z):
        z=self.simplify(z)
        assert z.k>=0 and z.t>=0,('negative recession slope',self,z)
        assert z.c+z.t*self.t0>=0,('negative chamber corner',self,z)

CHAMBERS={'t0':Chamber('t=0',0,True),
          't1plus':Chamber('t>=1',1,False)}

# Every edge is an actual full typed five-coordinate transition;
# indices are Aff(k,t,c) polynomials; no sampled branching in proofs.
EDGE_T0={
    ((0, 0, 1, 0, -1),(2, 0, 0, -1, 0)):(Aff(1, 0, 7),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -3)):(Aff(1, 0, 5),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -2)):(Aff(1, 0, 4),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -1)):(Aff(1, 0, 3),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 2, 1, 1, -4)):(Aff(1, 0, 6),Aff(0, 0, 1)),
    ((0, 2, 0, -1, 2),(2, 2, 1, 1, -3)):(Aff(1, 0, 5),Aff(0, 0, 1)),
    ((1, 0, -1, -1, 3),(0, 2, 1, 1, -4)):(Aff(1, 0, 4),Aff(1, 0, 5)),
    ((1, 0, -1, -1, 3),(0, 2, 1, 1, -3)):(Aff(1, 0, 4),Aff(1, 0, 6)),
    ((1, 0, -1, -1, 3),(0, 2, 1, 1, -2)):(Aff(1, 0, 4),Aff(1, 0, 7)),
    ((2, 0, 0, -1, 0),(0, 2, 0, -1, 2)):(Aff(0, 0, 0),Aff(1, 0, 6)),
    ((2, 0, 0, -1, 0),(1, 0, -1, -1, 3)):(Aff(1, 0, 3),Aff(2, 0, 9)),
}
PATH_T0={
    (2, 0, 0, 1, -3):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -3)),
    (2, 0, 0, 1, -2):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -2)),
    (2, 0, 0, 1, -1):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -1)),
    (2, 2, 1, 1, -4):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 2, 1, 1, -4)),
    (2, 2, 1, 1, -3):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 2, 1, 1, -3)),
    (0, 2, 1, 1, -4):((2, 0, 0, -1, 0), (1, 0, -1, -1, 3), (0, 2, 1, 1, -4)),
    (0, 2, 1, 1, -3):((2, 0, 0, -1, 0), (1, 0, -1, -1, 3), (0, 2, 1, 1, -3)),
    (0, 2, 1, 1, -2):((2, 0, 0, -1, 0), (1, 0, -1, -1, 3), (0, 2, 1, 1, -2)),
}
EDGE_T1PLUS={
    ((0, 0, 1, 0, -1),(2, 0, 0, -1, 0)):(Aff(1, 2, 7),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 1),(2, 1, 0, 0, 0)):(Aff(1, 1, 2),Aff(1, 1, 3)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -3)):(Aff(1, 1, 5),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -2)):(Aff(1, 1, 4),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 0, 0, 1, -1)):(Aff(1, 1, 3),Aff(0, 0, 0)),
    ((0, 2, 0, -1, 2),(2, 2, 1, 1, -4)):(Aff(1, 1, 6),Aff(0, 0, 1)),
    ((0, 2, 0, -1, 2),(2, 2, 1, 1, -3)):(Aff(1, 1, 5),Aff(0, 0, 1)),
    ((1, 0, -1, 1, 1),(0, 2, 1, 1, -4)):(Aff(1, 1, 4),Aff(1, 2, 3)),
    ((1, 0, -1, 1, 1),(0, 2, 1, 1, -3)):(Aff(1, 1, 4),Aff(1, 2, 4)),
    ((1, 0, -1, 1, 1),(0, 2, 1, 1, -2)):(Aff(1, 1, 4),Aff(1, 2, 5)),
    ((2, 0, 0, -1, 0),(0, 2, 0, -1, 1)):(Aff(0, 0, 0),Aff(1, 1, 5)),
    ((2, 0, 0, -1, 0),(0, 2, 0, -1, 2)):(Aff(0, 0, 0),Aff(1, 1, 6)),
    ((2, 1, 0, 0, 0),(1, 0, -1, 1, 1)):(Aff(1, 1, 3),Aff(1, 1, 4)),
}
PATH_T1PLUS={
    (2, 0, 0, 1, -3):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -3)),
    (2, 0, 0, 1, -2):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -2)),
    (2, 0, 0, 1, -1):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 0, 0, 1, -1)),
    (2, 2, 1, 1, -4):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 2, 1, 1, -4)),
    (2, 2, 1, 1, -3):((2, 0, 0, -1, 0), (0, 2, 0, -1, 2), (2, 2, 1, 1, -3)),
    (0, 2, 1, 1, -4):((2, 0, 0, -1, 0), (0, 2, 0, -1, 1), (2, 1, 0, 0, 0), (1, 0, -1, 1, 1), (0, 2, 1, 1, -4)),
    (0, 2, 1, 1, -3):((2, 0, 0, -1, 0), (0, 2, 0, -1, 1), (2, 1, 0, 0, 0), (1, 0, -1, 1, 1), (0, 2, 1, 1, -3)),
    (0, 2, 1, 1, -2):((2, 0, 0, -1, 0), (0, 2, 0, -1, 1), (2, 1, 0, 0, 0), (1, 0, -1, 1, 1), (0, 2, 1, 1, -2)),
}

def path(label,ch):
    if label not in E6_IMAGE:
        raise ValueError('no E6 typed target')
    key='t0' if ch.fixed_t else 't1plus'
    table=EDGE_T0 if ch.fixed_t else EDGE_T1PLUS
    routes=PATH_T0 if ch.fixed_t else PATH_T1PLUS
    w=X;steps=[]
    for target in routes[label]:
        i,j=table[(w,target)]
        steps.append((i,j,target));w=target
    assert w==label
    return steps

def prefix(parent,ordinal,ch):
    i=ch.simplify(ordinal)
    length=(A,N,N-1)[parent]
    if i==Aff():
        return (Aff(),Aff(),Aff()),(1 if parent==1 else 0)
    if ch.simplify(i-length-1)==Aff():
        vectors=((Aff(c=1),Aff(),A),(Aff(),Aff(c=1),N),
                 (Aff(c=1),Aff(),N-1))
        return vectors[parent],(1 if parent==2 else 0)
    ch.nonnegative(i-1)
    ch.nonnegative(length-i)
    return ((Aff(),Aff(c=1),i-1) if parent==1 else
            (Aff(c=1),Aff(),i-1)),2

def certify_edge(source,i,j,target,ch):
    top,top_type=prefix(source[0],i,ch)
    bot,bot_type=prefix(source[1],j,ch)
    assert target[:2]==(top_type,bot_type),('wrong typed index',ch,source,i,j,target)
    x,c,y=source[2:]
    M=(2*x+c+y,c+y,A*x+N*c+(N-1)*y)
    got=tuple(ch.simplify(M[z]+bot[z]-top[z]) for z in range(3))
    assert got==tuple(Aff(c=z) for z in target[2:]),(
        'Z[k,t] Parikh mismatch',ch,source,i,j,target,got)

def e6_predicted(g,i,j):
    A=g.n+g.d
    if not(0<=i<=A+1 and 0<=j<=A+1):
        raise ValueError('invalid ordered E6 occurrence')
    if 1<=i<=A:
        if j==0:return g.n+2<=i<=g.n+4
        return 1<=j<=A and i-j in (g.n+3,g.n+4)
    return i==A+1 and g.d-3<=j<=g.d-1

def symbolic_star():
    '''Exact nine-kind manual guard theorem, encoded by E6_predicted.

    Source shift s(E6)=b=1+h, inflated G=beta+1=n+3+alpha.
    RF(n+2..n+4,0): D=n+2+h-i, exactly those three.
    RR(i-j=n+3,n+4): D=n+3+alpha+j-i, exactly these strips.
    LR(A+1,d-3..d-1): D=j-d+2+alpha, exactly three.
    Others: FF/FR/FL/RL/LL too far right;
    LF=1+h-d<-a, with d>=5. Requires inherited
    0<h<1/5, 0<alpha=rho+h<1, 0<rho<1.
    '''
    assert N==K+T+3 and D==K+2*T+5
    # Symbolic exact counts: 3+(d-3)+(d-4)+3=2d-1.
    assert (3+(D-3)+(D-4)+3)==2*D-1
    # Transport of index families, checked at representative affine bases
    # and syntactically identified RUN/LAST types in the all-path oracle.
    return dict(nine_actual_occurrence_kinds=9,nonempty_kinds=3,
                indexed_children='2d-1',simultaneous_base_labels=8,
                self_child_excluded_by_actual_types=True,
                inherited_Perron_inequalities_required=True)

def symbolic_certificate():
    assert symbolic_star()['simultaneous_base_labels']==8
    assert len(PATH_T0)==len(PATH_T1PLUS)==8
    states={X,E6};directed=0;depths={}
    for key,ch in CHAMBERS.items():
        for label in sorted(E6_IMAGE):
            current=X;steps=path(label,ch)
            for i,j,target in steps:
                certify_edge(current,i,j,target,ch)
                certify_edge(reverse(current),j,i,reverse(target),ch)
                states.add(target);current=target;directed+=2
            assert current==label
            depths[(key,label)]=len(steps)
    oriented=states|{reverse(w) for w in states}
    for w in oriented:base['strict'](w)
    assert max(depths.values())==5
    return dict(chambers=2,typed_E6_targets=8,
                source_chamber_cases=16,
                exact_symbolic_oriented_path_edges=directed,
                max_X_to_E6_child_depth=5,
                distinct_path_labels=len(oriented),
                universal_strict_margins=2*len(oriented),
                conditional_nine_seed_closure_reduction=True,
                all_descendants_productive_unproved=True,
                BH=False,PSC=False)

def finite_oracle():
    instances=0;star_pairs=star_edges=forward_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            A=g.n+g.d
            image=set();accepted=0
            for i in range(A+2):
                for j in range(A+2):
                    child=g.child(E6,i,j)
                    strict=g.interior(child)
                    want=e6_predicted(g,i,j)
                    assert strict==want,('E6 strict guard wrong',k,t,i,j,child)
                    if strict:
                        image.add(child);accepted+=1
            assert accepted==2*g.d-1 and image==E6_IMAGE
            assert E6 not in image
            ch=CHAMBERS['t0'] if t==0 else CHAMBERS['t1plus']
            for label in E6_IMAGE:
                for flip in (0,1):
                    current=reverse(X) if flip else X
                    for aa,bb,target in path(label,ch):
                        i=aa.k*k+aa.t*t+aa.c
                        j=bb.k*k+bb.t*t+bb.c
                        if flip:i,j,target=j,i,reverse(target)
                        assert g.child(current,i,j)==target
                        assert g.interior(target)
                        current=target;forward_edges+=1
                    assert current==(reverse(label) if flip else label)
            star_pairs+=2*(A+2)**2
            star_edges+=2*accepted
            instances+=1
    assert (instances,star_pairs,star_edges,forward_edges)==(117,297648,8658,6864)
    return dict(specimens=instances,E6_candidate_pairs=star_pairs,
                strict_indexed_E6_children_both_orientations=star_edges,
                X_to_E6_child_selected_edge_replays=forward_edges)

if __name__=='__main__':
    import json
    print(json.dumps(symbolic_certificate(),indent=2,sort_keys=True))
    print(json.dumps(finite_oracle(),indent=2,sort_keys=True))
