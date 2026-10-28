"""Independent literal-word/Fraction oracle for both complete H5 child stars."""
from pathlib import Path
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
H=(0,2,2,2,-5);C=(2,2,0,0,0)


def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))


def source(flip):
    if flip not in (0,1):raise ValueError('unknown orientation')
    return reverse(H) if flip else H


def predicted(flip,g,i,j):
    w=source(flip)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if flip else(i,j)
    A,N=g.n+g.d,g.n-1;q=A+2-g.k;e=int(g.t>=2)
    if 1<=a<=A:
        if b==0:return q-1<=a<=q+1+e
        return 1<=b<=N and a-b in(q+e,q+1+e)
    if a==A+1:
        if b==0:return g.k<=2 or(g.k==3 and e==1)
        return max(1,g.k-2-e)<=b<=g.k
    return False


def envelope():
    base=({(2,0,0,-3,y) for y in range(1,5)}|
          {(0,0,0,-3,y) for y in range(1,5)}|
          {(2,2,1,-3,y) for y in range(3)}|
          {(0,2,1,-3,y) for y in range(4)})
    assert len(base)==15 and not(base&{reverse(w) for w in base})
    return base|{reverse(w) for w in base}


def path(flip,g):
    A=g.n+g.d
    if g.k==0:out=[(A+1,0,(0,0,0,-3,4)),(g.t+1,0,(2,0,0,1,-1)),(2,1,C)]
    elif g.k==1:out=[(A+1,0,(0,0,0,-3,3)),(1,4,C)]
    else:out=[(A+2-g.k,0,(2,0,0,-3,3)),(1,4,C)]
    return[(j,i,reverse(w)) for i,j,w in out] if flip else out


def verify_path(flip,g,packet):
    if packet!=path(flip,g):raise ValueError('wrong intended packet')
    w=source(flip)
    for i,j,target in packet:
        if not(g.interior(w) and g.child(w,i,j)==target and g.interior(target)):
            raise ValueError('actual occurrence/typed transport/geometry failed')
        w=target
    if w!=C:raise ValueError('wrong typed terminal')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);counts=[]
            assert g.sign(g.shift((2,2,1,-3,1)))==(1 if t>=2 else -1)
            for flip in (0,1):
                w=source(flip);assert g.interior(w)
                R,B=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                predicted_edges={(i,j,g.child(w,i,j)) for i in range(R) for j in range(B) if predicted(flip,g,i,j)}
                assert actual==predicted_edges and len(actual)==2*k+1
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,flip=flip,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target) and g.interior(reverse(target))
                packet=path(flip,g);verify_path(flip,g,packet)
                counts.append(len(actual));pairs+=R*B;accepted+=len(actual);path_edges+=len(packet)
            if k==0:assert set(g.edges(H))=={(g.n+g.d+1,0,(0,0,0,-3,4))}
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,eta_positive=t>=2,counts=counts))
    assert set(witnesses)==envelope() and len(witnesses)==30
    return dict(scope='finite independent replay; universal guard proof separate; H5 and real reversal, not global BH',
                members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,path_edges=path_edges,
                image_labels=len(witnesses),occurrences_each='2k+1',selected_typed_paths_at_most_three=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
