"""Independent literal words and Fraction geometry for the six T/X/Y0 stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
T=(0,2,1,-1,1);X=(0,0,1,0,-1);Y0=(2,2,1,-1,-1)
Q=(2,0,0,-1,1);B=(2,2,0,-2,3);RH=(2,0,0,1,-1);C=(2,2,0,0,0)
BASE=(T,X,Y0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<6:raise ValueError('unknown T/X/Y0 orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def predicted(kind,g,i,j):
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else(i,j)
    n,A,N,d,k,t=g.n,g.n+g.d,g.n-1,g.d,g.k,g.t
    if kind//2==0:return a==A+1 and b==0
    if kind//2==1:
        if 1<=a<=A:
            if b==0:return d<=a<=d+3
            return 1<=b<=A and a-b in(d+2,d+3)
        return a==A+1 and n-2<=b<=n+1
    if a==0:return b==0 and t<=1
    if a<=N:
        if b==0:return max(1,t-1)<=a<=t+1
        return 1<=b<=N and a-b in(t,t+1)
    if b==n:return t==0
    return k+2<=b<=min(N,k+3)


def envelope():
    base=({X}|{(2,0,0,-1,y) for y in range(-1,3)}|
          {(2,2,1,-1,y) for y in(-2,-1)}|{(0,2,1,-1,y) for y in range(-2,2)}|
          {(0,0,0,-2,y) for y in(3,4)}|{(2,0,-1,-2,y) for y in(3,4,5)}|
          {(2,2,0,-2,y) for y in(2,3)}|{(1,2,0,-2,y) for y in(2,3)}|
          {(1,1,0,-2,3)})
    assert len(base)==21 and not(base&{reverse(w) for w in base})
    return base|{reverse(w) for w in base}


def path(kind,g):
    source(kind)
    if kind//2==0:out=[(g.n+g.d+1,0,X),(g.d+1,0,Q),(1,2,C)]
    elif kind//2==1:out=[(g.d+1,0,Q),(1,2,C)]
    else:out=[(g.t+1,1,B),(g.n-1,0,RH),(2,1,C)]
    return[(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_packet(kind,g,packet):
    if packet!=path(kind,g):raise ValueError('different intended path')
    w=source(kind)
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
                assert actual==selected and len(actual)==(1,2*g.n+3,2*k+8-(t==0))[kind//2]
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                p=path(kind,g);verify_packet(kind,g,p)
                pairs+=R*D;accepted+=len(actual);path_edges+=len(p);counts.append(len(actual))
            assert g.child((0,2,1,3,-4),A+1,g.n-2)==T
            assert g.child(X,A+1,g.n+1)==T and g.interior(T)
            assert g.child(X,g.d+3,1)==Y0 and g.interior(Y0)
            assert not g.interior(g.child(T,A,0))
            assert g.interior(g.child(Y0,g.n,g.n))==(t==0)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and len(witnesses)==42
    return dict(scope='finite independent replay; universal inequalities separate; T/X/Y0 and real reversals, not global BH',
                members=len(rows),source_cells=6*len(rows),pairs=pairs,accepted=accepted,path_edges=path_edges,
                image_labels=len(witnesses),max_path_length=3,real_T_X_cycle_with_exit=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
