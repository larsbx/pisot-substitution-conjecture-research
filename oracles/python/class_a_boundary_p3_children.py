"""Independent literal-word and Fraction replay of the two P3 stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
P3=(0,2,1,3,-4);E3=(0,0,-1,0,3)
V=(2,0,0,-1,2);W=(1,0,0,1,-1);Q=(2,0,0,-1,1);C=(2,2,0,0,0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(flip):
    if flip not in(0,1):raise ValueError('unknown P3 orientation')
    return reverse(P3) if flip else P3


def predicted(flip,g,i,j):
    w=source(flip)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if flip else(i,j)
    A,N,n,q=g.n+g.d,g.n-1,g.n,g.d+5
    if 1<=a<=A:
        if b==0:return q-2<=a<=q+1
        return 1<=b<=N and a-b in(q,q+1)
    if a==A+1:return n<=5 if b==0 else max(1,n-5)<=b<=n-2
    return False


def envelope():
    base=({(2,0,0,-1,y) for y in range(-1,3)}|
          {(2,2,1,-1,y) for y in(-2,-1)}|
          {(0,0,0,-1,y) for y in(-1,0,1)}|
          {(0,2,1,-1,y) for y in range(-2,2)})
    assert len(base)==13 and not(base&{reverse(w) for w in base})
    return base|{reverse(w) for w in base}


def path(flip,g):
    source(flip)
    if g.n>=4:out=[(g.d+4,0,Q),(1,2,C)]
    else:out=[(g.d+3,0,V),(g.n,0,W),(1,0,Q),(1,2,C)]
    return[(j,i,reverse(w)) for i,j,w in out] if flip else out


def verify_packet(flip,g,packet):
    if packet!=path(flip,g):raise ValueError('different intended path')
    w=source(flip)
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
            for flip in(0,1):
                w=source(flip);assert g.interior(w)
                R,D=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(D) if predicted(flip,g,i,j)}
                assert actual==selected and len(actual)==2*g.n-3
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,flip=flip,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                p=path(flip,g);verify_packet(flip,g,p)
                pairs+=R*D;accepted+=len(actual);path_edges+=len(p);counts.append(len(actual))
            assert g.child(E3,A+1,A-k-1)==P3
            # A real same-typed RF candidate, immediately below the admissible strip.
            assert not g.interior(g.child(P3,g.d+2,0))
            assert predicted(0,g,A+1,0)==(g.n<=5)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and len(witnesses)==26
    return dict(scope='finite independent replay; universal inequalities separate; P3 and reversal, not global BH',
                members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,path_edges=path_edges,
                image_labels=len(witnesses),max_path_length=4,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
