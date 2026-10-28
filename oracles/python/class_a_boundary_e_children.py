"""Independent exact literal-word replay of six oriented E/H child stars."""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
BASE=((0,0,0,0,1),(0,2,0,-1,1),(0,2,0,-1,2))
C=(2,2,0,0,0)


def reverse(w):
    return (w[1],w[0],*(-x for x in w[2:]))


def source(kind):
    if not 0<=kind<6: raise ValueError('unknown packet')
    w=BASE[kind//2]
    return reverse(w) if kind%2 else w


def predicted(kind,g,i,j):
    w=source(kind)
    if not (0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind%2 else (i,j)
    n,d,A=g.n,g.d,g.n+g.d
    group=kind//2
    if group==0:
        if 1<=a<=A:
            if b==0: return n+1<=a<=n+3
            if 1<=b<=A: return a-b in (n+2,n+3)
        return a==A+1 and d-2<=b<=d
    if group==1:
        if a==0: return b<=1
        if 1<=b<=n-1 and 1<=a<=A: return b==a+1
        return b==n and a in (n-1,n)
    if 1<=a<=A:
        if b==0: return n<=a<=n+2
        if 1<=b<=n-1: return a-b in (n+1,n+2)
        return b==n and a in (2*n+1,2*n+2)
    return False


def envelope():
    p=({(2,0,0,1,y) for y in (-3,-2,-1)} |
       {(2,2,1,1,y) for y in (-4,-3)} |
       {(2,1,1,1,y) for y in (-4,-3)} |
       {(0,2,1,1,y) for y in (-4,-3,-2)} |
       {(0,0,0,0,-1),(0,2,1,0,-1),C,(2,1,0,0,0),(2,1,0,0,-1)})
    return p | {reverse(w) for w in p}


def short_path(kind,g):
    if kind//2==1:
        return [(2,1,C)] if kind%2 else [(1,2,C)]
    i=g.n+1 if kind//2==0 else g.n
    return [(0,i,source(2)),(1,2,C)] if kind%2 else [(i,0,source(3)),(2,1,C)]


def verify_path(kind,g,packet):
    if packet!=short_path(kind,g): raise ValueError('path packet mismatch')
    current=source(kind)
    for i,j,target in packet:
        if not(g.interior(current) and g.interior(target) and g.child(current,i,j)==target):
            raise ValueError('actual occurrence, transport or geometry failed')
        current=target
    if current!=C: raise ValueError('wrong typed coincidence terminal')


def probe():
    rows=[]; witnesses={}; pairs=accepted=path_edges=0; by_kind=[0]*6
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t); labels=set(); counts=[]
            for kind in range(6):
                w=source(kind)
                assert g.interior(w)
                R,B=len(g.words[w[0]]),len(g.words[w[1]])
                actual=set(g.edges(w))
                selected={(i,j,g.child(w,i,j)) for i in range(R) for j in range(B)
                          if predicted(kind,g,i,j)}
                assert selected==actual
                expected=2*g.d+1 if kind//2==0 else (g.n+2 if kind//2==1 else 2*g.n+3)
                assert len(actual)==expected
                for i,j,target in sorted(actual):
                    labels.add(target)
                    witnesses.setdefault(target,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target)
                    assert g.interior(reverse(target))
                packet=short_path(kind,g); verify_path(kind,g,packet)
                path_edges+=len(packet); pairs+=R*B; accepted+=len(actual)
                by_kind[kind]+=len(actual); counts.append(len(actual))
            assert labels==envelope() and len(labels)==29
            unequal=(2,1,0,0,0)
            assert g.child(source(2),g.n-1,g.n)==unequal and g.interior(unequal)
            assert unequal[:2]!=(2,2) # real offset-zero edge, not typed C
            assert not g.interior(g.child(source(2),0,2))
            assert not g.interior(g.child(source(4),2*g.n+3,g.n))
            bad=list(short_path(1,g)); i,j,target=bad[0]; bad[0]=(0,0,target)
            try: verify_path(1,g,bad)
            except ValueError: pass
            else: raise AssertionError('broken intermediate path accepted')
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts,image_labels=len(labels)))
    assert set(witnesses)==envelope()
    return dict(scope='finite independent replay; uniform symbolic tables/path proof separate; six minus packets only; no universal BH',
                members=len(rows),source_cells=6*len(rows),pairs=pairs,accepted=accepted,
                accepted_by_kind=by_kind,path_edges=path_edges,every_member_image_labels=29,
                all_six_sources_typed_coincident_in_at_most_two_steps=True,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
