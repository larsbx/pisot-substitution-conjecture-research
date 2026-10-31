"""Independent literal-word/Fraction replay of six P3-family stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((0,2,1,3,-4),(2,0,0,-1,1),(0,0,0,-1,1))
C=(2,2,0,0,0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<6:raise ValueError('unknown oriented P3 packet')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else(i,j)
    A,N,n,d=g.n+g.d,g.n-1,g.n,g.d
    if kind//2==0:
        if 1<=a<=A:
            if b==0:return d+3<=a<=d+6
            return 1<=b<=N and a-b in(d+5,d+6)
        if a==A+1:return n<=5 if b==0 else max(1,n-5)<=b<=n-2
        return False
    if a==0:return b in(0,1)
    R=N if kind//2==1 else A
    if 1<=a<=R:
        return (1<=b<=A and b==a+1) or(kind//2==2 and a==A and b==A+1)
    return n+1<=b<=n+2 if kind//2==1 else b==A+1


def envelope():
    base=({(2,0,0,-1,y) for y in range(-1,3)}|
          {(2,2,1,-1,y) for y in(-2,-1)}|
          {(0,0,0,-1,y) for y in(-1,0,1)}|
          {(0,2,1,-1,y) for y in range(-2,2)}|
          {(0,0,0,0,-1),(0,2,1,0,-1),(1,2,0,0,0),(1,2,0,0,1),(2,0,0,0,0),C})
    out=base|{reverse(w) for w in base}
    assert len(out)==37
    return out


def path(kind,g):
    out=[]
    if kind//2==0:
        out.append((g.n+g.d+1,0,BASE[2]) if g.n==3 else(g.d+4,0,BASE[1]))
    out.append((1,2,C))
    return[(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_packet(w,g,packet,want):
    if packet!=want:raise ValueError('different intended packet')
    for i,j,target in packet:
        if not(g.interior(w) and g.child(w,i,j)==target and g.interior(target)):
            raise ValueError('actual occurrence/full transport/strict geometry failed')
        w=target
    if w!=C:raise ValueError('wrong typed terminal')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);A=g.n+g.d;counts=[]
            for kind in range(6):
                w=source(kind);assert g.interior(w)
                R,D=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(D) if predicted(kind,g,i,j)}
                assert actual==selected and len(actual)==(2*g.n-3,g.n+3,A+3)[kind//2]
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                p=path(kind,g);verify_packet(w,g,p,p)
                path_edges+=len(p);pairs+=R*D;accepted+=len(actual);counts.append(len(actual))
            e3=(0,0,-1,0,3)
            assert g.child(e3,A+1,A-k-1)==BASE[0]
            assert g.interior(BASE[0]) and g.interior(reverse(BASE[0]))
            assert g.child(BASE[0],A+1,g.n-2)==(0,2,1,-1,1)
            # Same y/x types as a real RF edge, but disjoint.
            assert not g.interior(g.child(BASE[0],g.d+2,0))
            if g.n==3:
                assert g.d+4==A+1 and g.words[0][g.d+4]==0
                assert g.child(BASE[0],g.d+4,0)!=BASE[1]
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope()
    return dict(scope='finite independent replay; universal inequalities separate; six minus packets, not global BH',
                members=len(rows),source_cells=6*len(rows),pairs=pairs,accepted=accepted,path_edges=path_edges,
                image_labels=len(witnesses),P3_typed_exit_at_most_two=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
