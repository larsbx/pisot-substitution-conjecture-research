"""Independent literal-prefix/Fraction replay of four oriented E2/Dxx stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((0,0,0,0,2),(0,0,1,2,-4))
J=(2,0,1,2,-4);K=(2,0,-1,-2,5);L=(2,0,0,3,-4);H1=(0,2,0,-1,1);C=(2,2,0,0,0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<4:raise ValueError('unknown oriented packet')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def high(k,t):return t>k or(t==k and k>=2)


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[0]) and 0<=j<len(g.words[0])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else(i,j)
    n,A,t=g.n,g.n+g.d,g.t
    if kind//2==0:
        e=int(high(g.k,t))
        if 1<=a<=A:
            if b==0:return 2*n+3<=a<=2*n+5+e
            if 1<=b<=A:return a-b in(2*n+4+e,2*n+5+e)
        if a==A+1:
            if b==0:return t<=2 or(t==3 and e==1)
            return max(1,t-2-e)<=b<=t
        return False
    if 1<=a<=A:
        if b==0:return t+2<=a<=t+4
        return 1<=b<=A and a-b in(t+3,t+4)
    return a==A+1 and 2*n-1<=b<=2*n+1


def envelope():
    b=({(2,0,1,2,y) for y in range(-7,-3)}|
       {(2,2,2,2,y) for y in range(-8,-5)}|
       {(0,0,1,2,y) for y in range(-7,-3)}|
       {(0,2,2,2,y) for y in range(-8,-4)}|
       {(2,0,-1,-2,y) for y in(3,4,5)}|
       {(2,2,0,-2,y) for y in(2,3)}|
       {(0,2,0,-2,y) for y in(2,3,4)})
    assert len(b)==23 and not(b&{reverse(w) for w in b})
    return b|{reverse(w) for w in b}


def path(kind,g):
    out=[]
    if kind//2==0:
        if g.t==0:out.append((g.n+g.d+1,0,BASE[1]))
        else:out.append((2*g.n+3,0,J))
    out.append((g.t+2,0,K)) # Dxx and J have the same actual next pair
    out.extend(((g.k+1,0,L),(0,g.n-2,H1),(1,2,C)))
    return[(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_path(kind,g,packet):
    if packet!=path(kind,g):raise ValueError('path differs from intended packet')
    w=source(kind)
    for i,j,target in packet:
        if not(g.interior(w) and g.interior(target) and g.child(w,i,j)==target):
            raise ValueError('literal occurrence/geometry/full transport refused')
        w=target
    if w!=C:raise ValueError('wrong typed terminal')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=0;by_kind=[0]*4
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);A=g.n+g.d;counts=[]
            assert g.sign((-2*g.n-5,2,0))==(1 if high(k,t) else -1)
            for kind in range(4):
                w=source(kind);assert g.interior(w)
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==selected
                assert len(actual)==(2*t+1 if kind//2==0 else 4*g.n+3)
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                packet=path(kind,g);verify_path(kind,g,packet)
                assert len(packet)==(5 if kind//2==0 else 4)
                counts.append(len(actual));pairs+=(A+2)**2;accepted+=len(actual);by_kind[kind]+=len(actual);path_edges+=len(packet)
            if t==0:
                assert set(g.edges(BASE[0]))=={(A+1,0,BASE[1])}
                assert 2*g.n+3==A+1 and g.words[0][2*g.n+3]==0
            # Same shift, different child lengths: the y/y version is disjoint,
            # the last x/y version is a genuine outgoing edge.
            bad=g.child(BASE[1],t+3,1)
            good=g.child(BASE[1],A+1,2*g.n+1)
            assert bad==(2,2,0,-2,4) and not g.interior(bad)
            assert good==(0,2,0,-2,4) and g.interior(good)
            if k>=2:
                cycle=((L,1,g.n,(2,2,-1,-1,3)),
                       ((2,2,-1,-1,3),1,t+4,(2,2,0,2,-2)),
                       ((2,2,0,2,-2),0,0,BASE[0]))
                for w,i,j,target in cycle:
                    assert g.interior(w) and g.child(w,i,j)==target and g.interior(target)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,alpha_high=high(k,t),counts=counts))
    assert len(envelope())==46 and set(witnesses)==envelope()
    return dict(scope='finite independent replay; symbolic chamber proof separate; four minus packets, not universal BH',
                members=len(rows),source_cells=4*len(rows),pairs=pairs,accepted=accepted,accepted_by_kind=by_kind,
                path_edges=path_edges,image_labels=len(witnesses),all_four_sources_typed_coincident_within_five_steps=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
