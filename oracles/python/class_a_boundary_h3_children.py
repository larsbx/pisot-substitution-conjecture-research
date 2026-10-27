"""Independent literal-word/Perron replay of eight oriented H3-chain packets."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((0,2,0,-1,3),(2,0,1,2,-4),(2,0,-1,-2,5),(2,0,0,3,-4))
H1=(0,2,0,-1,1)
C=(2,2,0,0,0)


def reverse(w):return (w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<8:raise ValueError('unknown packet')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def high(k,t):return t>k or (t==k and k>=2)


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else (i,j)
    n,A,N=g.n,g.n+g.d,g.n-1
    group=kind//2
    if group==0:
        h=int(high(g.k,g.t)); t=g.t
        if 1<=a<=A:
            if b==0:return 2*n+2<=a<=2*n+4+h
            if 1<=b<=N:return a-b in (2*n+3+h,2*n+4+h)
        if a==A+1:
            if b==0:return t<=1 or(t==2 and h)
            return max(1,t-1-h)<=b<=t+1
        return False
    if group==1:
        if 1<=a<=N:
            if b==0:return g.t+2<=a<=g.t+4
            if 1<=b<=A:return a-b in (g.t+3,g.t+4)
        if a==n:return g.k<=1 if b==0 else max(1,g.k-1)<=b<=g.k
        return False
    if group==2:
        if a==0:return b==0 and g.k==0
        if 1<=a<=N:
            if b==0:return max(1,g.k)<=a<=g.k+2
            if 1<=b<=A:return a-b in(g.k+1,g.k+2)
        return a==n and g.t+1<=b<=g.t+2
    if a==0:return n-2<=b<=n
    if 1<=a<=N and 1<=b<=A:return a-b in(-n,1-n)
    return a==n and 2*n-1<=b<=2*n


def envelope():
    p=({(2,0,1,2,y) for y in range(-7,-3)} |
       {(2,2,2,2,y) for y in range(-8,-5)} |
       {(0,0,1,2,y) for y in range(-7,-4)} |
       {(0,2,2,2,y) for y in range(-8,-4)} |
       {(2,0,-1,-2,y) for y in range(3,6)} |
       {(2,2,0,-2,y) for y in (2,3)} |
       {(1,0,-1,-2,y) for y in (3,4)} |
       {(1,2,0,-2,y) for y in (2,3)} |
       {(0,0,1,3,-4)} |
       {(2,0,0,3,y) for y in (-5,-4,-3)} |
       {(2,2,1,3,y) for y in (-6,-5)} |
       {(1,2,1,3,y) for y in (-6,-5)} |
       {(0,2,0,-1,y) for y in (1,2,3)} |
       {(2,2,-1,-1,y) for y in (3,4)} |
       {(1,2,-1,-1,y) for y in (3,4)})
    assert len(p)==38
    return p|{reverse(w) for w in p}


def path(kind,g):
    flip=kind%2; out=[]
    for group in range(kind//2,4):
        i,j=((2*g.n+2,0),(g.t+2,0),(g.k+1,0),(0,g.n-2))[group]
        target=BASE[group+1] if group<3 else H1
        out.append((j,i,reverse(target)) if flip else(i,j,target))
    out.append((2,1,C) if flip else(1,2,C))
    return out


def verify_path(kind,g,packet):
    if packet!=path(kind,g):raise ValueError('path mismatch')
    current=source(kind)
    for i,j,target in packet:
        if not(g.interior(current) and g.interior(target) and g.child(current,i,j)==target):
            raise ValueError('intermediate occurrence/geometry/target failed')
        current=target
    if current!=C:raise ValueError('wrong typed terminal')


def probe():
    witnesses={};rows=[];pairs=accepted=path_edges=0;by_kind=[0]*8
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            # Independent exact algebraic separator sign; no rounded root.
            s=g.sign((-2*g.n-5,2,0))
            assert s==(1 if high(k,t) else -1)
            assert 4*k*k+20*k-4*t*t-24*t+5!=0
            counts=[]
            for kind in range(8):
                w=source(kind)
                assert g.interior(w)
                R,B=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(B) if predicted(kind,g,i,j)}
                assert selected==actual
                expected=(2*t+3,2*k+2,2*t+6,2*g.n+3)[kind//2]
                assert len(actual)==expected
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                packet=path(kind,g);verify_path(kind,g,packet)
                pairs+=R*B;accepted+=len(actual);by_kind[kind]+=len(actual);counts.append(len(actual));path_edges+=len(packet)
            bad=list(path(0,g));i,j,target=bad[1];bad[1]=(0,0,target)
            try:verify_path(0,g,bad)
            except ValueError:pass
            else:raise AssertionError('broken intermediate accepted')
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,alpha_high=high(k,t),counts=counts))
    assert set(witnesses)==envelope() and len(witnesses)==76
    return dict(scope='finite independent replay; symbolic chamber proof separate; eight minus sources, not universal BH',
                members=len(rows),source_cells=8*len(rows),pairs=pairs,accepted=accepted,
                accepted_by_kind=by_kind,path_edges=path_edges,image_labels=len(witnesses),
                all_sources_typed_coincident_within_five_steps=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
