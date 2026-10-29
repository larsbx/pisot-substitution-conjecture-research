"""Independent exact rational first/run/last classification of H4's children.

Uses the existing literal-word/Fraction Perron oracle, not the Mojo
classifier. Finite probes cannot imply universal BH or a closed carrier.
"""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]


def high_half(k,t):
    if k<0 or t<0:raise ValueError("invalid boundary chamber")
    return t>k or (t==k and k>=2)


def expected(k,t,i,j):
    if k<0 or t<0:raise ValueError("negative boundary parameter")
    n=k+t+3
    d=2*n-1-k
    A=n+d
    N=n-1
    if not (0<=i<=A+1 and 0<=j<=N+1):
        raise ValueError("unavailable ordered occurrence")
    high=high_half(k,t)
    if i==0:return False
    if 1<=i<=A:
        if j==0:return 2*n+1<=i<=min(A,2*n+(4 if high else 3))
        if j==N+1:return False
        return i-j in ((2*n+3,2*n+4) if high else (2*n+2,2*n+3))
    if j==0:return t==0 or (t==1 and high)
    if j==N+1:return False
    return max(1,t-(1 if high else 0))<=j<=t+2


def envelope(w):
    top,bottom,x,c,y=w
    return (
        (top,bottom,x,c)==(2,0,1,2) and -7<=y<=-4 or
        (top,bottom,x,c)==(2,2,2,2) and -8<=y<=-6 or
        (top,bottom,x,c)==(0,0,1,2) and -7<=y<=-6 or
        (top,bottom,x,c)==(0,2,2,2) and -8<=y<=-5
    )



def selected_path(g):
    """Five literal H4 child occurrences to genuine y/y zero-offset C.

    Does not prove H4 is reached from a seed in every member, and does
    not imply all H4 children are productive.
    """
    n=g.n
    k=g.k
    t=g.t
    parent=(0,2,0,-2,4)
    addresses=((2*n+1,0),(t+2,0),(k+1,0),(0,n-2),(1,2))
    targets=((2,0,1,2,-4),(2,0,-1,-2,5),(2,0,0,3,-4),
             (0,2,0,-1,1),(2,2,0,0,0))
    assert g.interior(parent)
    out=[]
    for (i,j),want in zip(addresses,targets):
        actual=g.child(parent,i,j)
        assert actual==want,(k,t,i,j,actual,want)
        assert g.interior(actual),(k,t,i,j,want)
        out.append(dict(parent=parent,i=i,j=j,target=actual))
        parent=actual
    assert parent==(2,2,0,0,0)
    return out


def probe():
    members=pairs=accepted=0
    selected_edges=0
    witnesses={}
    rows=[]
    for k in range(10):
        for t in range(10):
            g=Geometry(-1,k,t)
            members+=1
            n,d=g.n,g.d
            A=n+d
            N=n-1
            source=(0,2,0,-2,4)
            assert g.interior(source)
            path=selected_path(g)
            assert len(path)==5
            selected_edges+=len(path)
            hits=0
            for i in range(A+2):
                for j in range(N+2):
                    pairs+=1
                    target=g.child(source,i,j)
                    actual=g.interior(target)
                    want=expected(k,t,i,j)
                    assert actual==want,(k,t,i,j,target,actual,want)
                    if actual:
                        assert envelope(target),(k,t,i,j,target)
                        witnesses.setdefault(target,(k,t,i,j))
                        hits+=1
                        accepted+=1
            assert hits==2*t+5,(k,t,hits)
            if k in (0,1,2,3,4,5,9) and t in (0,1,2,3,4,9):
                rows.append(dict(k=k,t=t,n=n,d=d,edges=hits,
                                 alpha_high=high_half(k,t)))
    assert len(witnesses)==13
    return dict(scope="bounded independent actual-word Perron check; no global closure",
                members=members,pairs=pairs,accepted=accepted,
                image_labels=len(witnesses),selected_edges=selected_edges,
                witnesses=[dict(target=label,k=k,t=t,i=i,j=j)
                           for label,(k,t,i,j) in sorted(witnesses.items())],
                rows=rows)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
