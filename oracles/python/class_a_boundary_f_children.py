"""Independent literal-word/Fraction replay of eight F-family stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((0,2,1,-3,3),(2,0,1,0,-2),(0,0,-1,0,3),(0,2,2,0,-3))
G=(2,0,0,-3,3);L=(2,0,0,3,-4);H1=(0,2,0,-1,1);B=(2,2,0,-2,3);C=(2,2,0,0,0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<8:raise ValueError('unknown oriented F packet')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else(i,j)
    A,N,k,t=g.n+g.d,g.n-1,g.k,g.t;group=kind//2
    if group==0:return(a==A and b==0) or(a==A+1 and b in(0,1))
    if group==1:
        if a==0:return b==0 and t==0
        if 1<=a<=N:
            if b==0:return max(1,t)<=a<=t+2
            return 1<=b<=A and a-b in(t+1,t+2)
        return a==g.n and k+1<=b<=k+2
    if group==2:
        if 1<=a<=A:
            if b==0:return k+2<=a<=k+4
            return 1<=b<=A and a-b in(k+3,k+4)
        return a==A+1 and A-k-3<=b<=A-k-1
    q=A-k;e=int(t>=2)
    if 1<=a<=A:
        if b==0:return q-1<=a<=q+1+e
        return 1<=b<=N and a-b in(q+e,q+1+e)
    if a==A+1:
        return k==0 or(k==1 and e==1) if b==0 else max(1,k-e)<=b<=k+2
    return False


def envelope():
    base=({BASE[1],reverse(BASE[2]),BASE[3],(0,0,0,-2,4)}|
          {(2,0,-1,-2,y) for y in(3,4,5)}|
          {(2,2,0,-2,y) for y in(2,3)}|
          {(1,2,0,-2,y) for y in(2,3)}|
          {(2,0,0,3,y) for y in(-5,-4,-3)}|
          {(2,2,1,3,y) for y in(-6,-5)}|
          {(0,2,1,3,y) for y in(-6,-5,-4)}|
          {(2,0,0,-3,y) for y in range(1,5)}|
          {(2,2,1,-3,y) for y in range(3)}|
          {(0,0,0,-3,y) for y in(1,2)}|
          {(0,2,1,-3,y) for y in range(4)})
    assert len(base)==32 and not(base&{reverse(w) for w in base})
    return base|{reverse(w) for w in base}


def path(kind,g):
    group=kind//2;A=g.n+g.d
    if group==0:out=[(A+1,1,BASE[3]),(A-g.k,0,G),(1,4,C)]
    elif group==1:out=[(g.t+2,1,B),(g.n-1,0,reverse(H1)),(2,1,C)]
    elif group==2:out=[(g.k+3,0,L),(0,g.n-2,H1),(1,2,C)]
    else:out=[(A-g.k,0,G),(1,4,C)]
    return[(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def child_exit(flip,branch,g):
    if flip not in(0,1) or branch not in(0,1,2):raise ValueError('bad F child branch')
    A=g.n+g.d;kind=(2,5,6)[branch]
    out=[(A if branch==0 else A+1,1 if branch==2 else 0,source(kind))]+path(kind,g)
    return[(j,i,reverse(w)) for i,j,w in out] if flip else out


def verify_packet(w,g,packet,want):
    if packet!=want:raise ValueError('different intended packet')
    for i,j,target in packet:
        if not(g.interior(w) and g.child(w,i,j)==target and g.interior(target)):
            raise ValueError('actual occurrence/full transport/strict geometry failed')
        w=target
    if w!=C:raise ValueError('wrong typed terminal')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=child_exit_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);A=g.n+g.d;counts=[]
            for kind in range(8):
                w=source(kind);assert g.interior(w)
                R,D=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(D) if predicted(kind,g,i,j)}
                assert actual==selected and len(actual)==(3,2*k+6,2*A-2*k-1,2*k+5)[kind//2]
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                p=path(kind,g);verify_packet(w,g,p,p)
                path_edges+=len(p);pairs+=R*D;accepted+=len(actual);counts.append(len(actual))
            for flip in(0,1):
                first=set()
                for branch in range(3):
                    p=child_exit(flip,branch,g);verify_packet(source(flip),g,p,p)
                    first.add(p[0]);child_exit_edges+=len(p)
                assert first==set(g.edges(source(flip)))
            assert g.child(BASE[3],A+1,k+2)==BASE[0]
            h5=(0,2,2,2,-5)
            if k>=1:assert g.child(h5,A+1,k)==BASE[0]
            else:assert g.child(h5,A+1,0)!=BASE[0] # a real FIRST x, not RUN y
            assert not g.interior(g.child(BASE[0],A-1,0))
            assert g.child(BASE[0],A,0)==BASE[1]
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and len(witnesses)==64
    return dict(scope='finite independent replay; universal inequalities separate; eight minus packets, not global BH',
                members=len(rows),source_cells=8*len(rows),pairs=pairs,accepted=accepted,path_edges=path_edges,
                direct_F_child_exit_edges=child_exit_edges,image_labels=len(witnesses),every_direct_F_child_has_typed_tail_within_three=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
