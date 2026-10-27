"""Independent literal-prefix/Fraction replay; canonical implementation is Mojo."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((2,2,-1,-1,3),(2,2,-1,-1,4),(2,2,0,2,-2),(2,2,0,2,-3),(0,2,1,2,-4))
K=(2,0,-1,-2,5);L=(2,0,0,3,-4);H1=(0,2,0,-1,1);C=(2,2,0,0,0)


def reverse(w):return (w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<10:raise ValueError('unknown packet')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else(i,j)
    n,N,k,t=g.n,g.n-1,g.k,g.t
    group=kind//2
    if group==0:
        if a==0:return k==0 if b==n else t+1<=b<=min(N,t+3)
        if 1<=a<=N:
            if 1<=b<=N:return b-a in(t+2,t+3)
            return b==n and max(1,k)<=a<=k+1
        return False
    if group==1:
        if 1<=a<=N:
            if b==0:return k+1<=a<=k+3
            return 1<=b<=N and a-b in(k+2,k+3)
        if a==n:return t==0 if b==0 else max(1,t)<=b<=min(N,t+1)
        return False
    if group==2:
        if a==0:return b==0
        if 1<=a<=N:return a<=2 if b==0 else 1<=b<=N and a-b==2
        return a==n and b in(n-2,n-1)
    if group==3:return a==0 and b in(n-1,n)
    if 1<=a<=n+g.d:
        if b==0:return t+2<=a<=t+4
        if 1<=b<=N:return a-b in(t+3,t+4)
        return b==n and a in(n+t+3,n+t+4)
    return False


def envelope():
    base=({(0,2,1,2,y) for y in(-5,-4,-3)}|
          {(0,1,1,2,-3)}|
          {(2,2,0,2,y) for y in(-3,-2)}|
          {(2,1,0,2,y) for y in(-3,-2)}|
          {(2,0,0,3,y) for y in(-5,-4,-3)}|
          {(2,2,1,3,y) for y in(-6,-5)}|
          {(1,0,0,3,-5)}|
          {(1,2,1,3,y) for y in(-6,-5)}|
          {(0,0,0,0,2),(2,2,0,0,0)}|
          {(2,0,-1,0,y) for y in(1,2)}|
          {(1,2,0,0,y) for y in(0,1)}|
          {(0,2,0,-1,1),(0,1,0,-1,2)}|
          {(2,0,-1,-2,y) for y in(3,4,5)}|
          {(2,2,0,-2,y) for y in(2,3)}|
          {(2,1,0,-2,y) for y in(2,3)})
    assert len(base)==31
    return base|{reverse(w) for w in base}


def path(kind,g):
    group=kind//2;n,k,t=g.n,g.k,g.t
    tail=[(k+1,0,L),(0,n-2,H1),(1,2,C)]
    small=[(0,n-1,H1),(1,2,C)]
    if group==0:
        out=[(0,t+2,BASE[4]),(t+2,0,K)]+tail if k==0 else[(1,t+3,BASE[3])]+small
    elif group==1:out=[(k+2,0,L)]+tail[1:]
    elif group==2:
        out=[(3,1,C)] if n>=4 else[(1,0,(2,0,-1,0,2)),(1,2,BASE[3])]+small
    elif group==3:out=small
    else:out=[(t+2,0,K)]+tail
    return [(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_path(kind,g,packet):
    if packet!=path(kind,g):raise ValueError('packet differs from intended targets')
    w=source(kind)
    for i,j,target in packet:
        if not(g.interior(w) and g.interior(target) and g.child(w,i,j)==target):
            raise ValueError('actual occurrence/geometry/transport failed')
        w=target
    if w!=C:raise ValueError('wrong typed terminal')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=0;by_kind=[0]*10
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);counts=[]
            # Strict inherited margins checked by the independent Perron signs.
            assert g.sign(g.shift((2,2,1,0,-2)))>0 # alpha-h
            assert g.sign(g.shift((2,2,-1,-3,6)))>0 # 1-alpha-2h
            for kind in range(10):
                w=source(kind);assert g.interior(w)
                R,B=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(B) if predicted(kind,g,i,j)}
                assert actual==selected
                assert len(actual)==(2*k+4,2*t+4,g.n+2,2,2*g.n+3)[kind//2]
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                packet=path(kind,g);verify_path(kind,g,packet)
                assert len(packet)<=5
                path_edges+=len(packet);pairs+=R*B;accepted+=len(actual);by_kind[kind]+=len(actual);counts.append(len(actual))
            # A geometrically genuine zero-offset c/y child is not typed C.
            half=g.child(BASE[2],g.n,g.n-2)
            assert half==(1,2,0,0,0) and g.interior(half) and half!=C
            assert not g.interior(g.child(BASE[2],1,1)) # run/run shift exactly +2
            assert not g.interior(g.child(BASE[2],2,1)) # contact exactly +1
            if k==0:
                assert g.words[2][t+3]==1 # actual last c, not a run y
                assert g.child(BASE[0],1,t+3)!=BASE[3]
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert len(envelope())==51 and set(witnesses)==envelope()
    return dict(scope='finite independent replay, symbolic chamber proof separate; ten minus packets, no universal BH',
                members=len(rows),source_cells=10*len(rows),pairs=pairs,accepted=accepted,
                accepted_by_kind=by_kind,path_edges=path_edges,image_labels=len(witnesses),
                all_ten_sources_typed_coincident_within_five_steps=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
