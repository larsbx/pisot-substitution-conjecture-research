"""Independent literal word/Perron geometry replay, separate from uniform proof."""
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
SOURCES = ((1,0,0,1,-1),(1,0,0,0,1),(0,0,1,0,-1),(2,0,0,-1,1))
LABELS = ((0,1,0,0,0),(2,2,-1,1,1),(0,2,1,2,-3),(2,0,0,-1,2),SOURCES[0],SOURCES[3],(2,2,0,0,0))


def predicted(kind,g,i,j):
    n,d,A = g.n,g.d,g.n+g.d
    R = A if kind==2 else (n-1 if kind==3 else n)
    if not (0<=i<=R+1 and 0<=j<=A+1):
        raise ValueError('unavailable occurrence')
    if kind==1:
        return (i,j)==(n+1,0)
    if kind==3:
        if i==0: return j<=1
        if i==n: return j in (n+1,n+2)
        return j==i+1
    if kind==0 and i==0: return j==0
    if i==R+1: return n-2<=j<=n+1
    if 1<=i<=R:
        if j==0: return i<=3 if kind==0 else d<=i<=d+3
        if j<=A: return i-j in ((2,3) if kind==0 else (d+2,d+3))
    return False


def envelope():
    return ({(2,0,0,-1,y) for y in range(-1,3)} |
            {(2,2,1,-1,y) for y in (-2,-1)} |
            {(0,2,1,-1,y) for y in range(-2,2)} |
            {SOURCES[1],SOURCES[2],(0,0,0,0,-1),(0,2,1,0,-1),
             (2,2,0,0,0),(1,2,0,0,0),(1,2,0,0,1)})


def path(g):
    indices=((1,2),(0,g.t+1),(g.d+2,0),(g.n,0),(1,0),(1,2))
    return [(LABELS[z],i,j,LABELS[z+1]) for z,(i,j) in enumerate(indices)]


def typed_coincidence(label):
    return label[0]==label[1] and label[2:]==(0,0,0)


def verify_path(g,packet):
    if packet!=path(g):
        raise ValueError('path packet mismatch')
    for source,i,j,target in packet:
        if not (g.interior(source) and g.interior(target) and g.child(source,i,j)==target):
            raise ValueError('invalid intermediate occurrence/geometry/target')
    if not typed_coincidence(packet[-1][3]):
        raise ValueError('not typed coincidence')


def probe():
    witnesses, rows = {}, []
    pairs=accepted=0
    by_kind=[0]*4
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            verify_path(g,path(g))
            # Actual all-chamber cycle and a distinct certified coincidence exit.
            cyc=[(LABELS[3],g.n,0,SOURCES[0]),(SOURCES[0],0,0,SOURCES[1]),
                 (SOURCES[1],g.n+1,0,SOURCES[2]),(SOURCES[2],g.d,0,LABELS[3])]
            for source,i,j,target in cyc:
                assert g.child(source,i,j)==target and g.interior(target)
            counts=[]
            for kind,source in enumerate(SOURCES):
                assert g.interior(source)
                actual=set(g.edges(source))
                R=len(g.words[source[0]])
                B=len(g.words[source[1]])
                selected={(i,j,g.child(source,i,j)) for i in range(R) for j in range(B)
                          if predicted(kind,g,i,j)}
                assert selected==actual
                expected=1 if kind==1 else (g.n+3 if kind==3 else 2*g.n+3)
                assert len(actual)==expected
                counts.append(len(actual)); pairs+=R*B; accepted+=len(actual)
                by_kind[kind]+=len(actual)
                for i,j,target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
            # A zero-offset c/y child exists but fails the coincidence type guard.
            false=(1,2,0,0,0)
            assert g.child(SOURCES[3],g.n,g.n+1)==false and g.interior(false)
            assert not typed_coincidence(false)
            # First/run at (0,2) touches an endpoint and has no interior overlap.
            assert not g.interior(g.child(SOURCES[3],0,2))
            broken=list(path(g)); source,i,j,target=broken[2]
            broken[2]=(source,1,1,target)
            try: verify_path(g,broken)
            except ValueError: pass
            else: raise AssertionError('broken intermediate accepted')
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope()
    return dict(scope='finite independent replay; uniform symbolic proof is separate; one minus seed only, not universal BH',
                members=len(rows),source_cells=4*len(rows),pairs=pairs,accepted=accepted,
                accepted_by_kind=by_kind,image_labels=len(witnesses),path_edges=6*len(rows),
                every_seed_path_typed_coincident=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
