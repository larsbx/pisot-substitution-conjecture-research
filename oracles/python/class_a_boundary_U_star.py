"""Independent exact finite U child star oracle using literal words and Q roots."""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]


def expected(k,t,i,j):
    if k<0 or t<0:
        raise ValueError("invalid chamber")
    n=k+3+t
    d=2*n-1-k
    if not (0<=i<=n+d+1 and 0<=j<=n):
        raise ValueError("unavailable occurrence")
    if i==0:
        return False
    if i<n+d+1:
        if j==0:
            return d+2<=i<=d+5
        if j==n:
            return False
        return i-j in (d+4,d+5)
    if j==0:
        return n<=4
    if j==n:
        return False
    return j>=max(1,n-4)


def envelope(target):
    a,b,x,c,y=target
    return ((a,b,x,c)==(2,0,0,-1) and -1<=y<=2 or
            (a,b,x,c)==(2,2,1,-1) and -2<=y<=-1 or
            (a,b,x,c)==(0,0,0,-1) and -1<=y<=0 or
            (a,b,x,c)==(0,2,1,-1) and -2<=y<=1)


def probe():
    members=pairs=accepted=0
    targets={}
    results=[]
    for k in range(12):
        for t in (0,1,2,3,5,10):
            g=Geometry(-1,k,t)
            n,d=g.n,g.d
            members+=1
            U=(0,2,1,2,-3)
            assert g.interior(U)
            actual=[]
            for i in range(n+d+2):
                for j in range(n+1):
                    pairs+=1
                    child=g.child(U,i,j)
                    hit=g.interior(child)
                    want=expected(k,t,i,j)
                    assert hit==want,(k,t,i,j,child,hit,want)
                    if hit:
                        accepted+=1
                        assert envelope(child),(k,t,i,j,child)
                        targets.setdefault(child,(k,t,i,j))
                        actual.append((i,j))
            assert len(actual)==2*n-1,(k,t,n,len(actual))
            if k in (0,1,3,8,11) and t in (0,1,2,10):
                results.append(dict(k=k,t=t,n=n,edges=len(actual)))
    assert len(targets)==12,len(targets)
    return dict(scope="finite oracle, no BH",members=members,pairs=pairs,
                accepted=accepted,labels=len(targets),
                witnesses=[dict(target=v,k=k,t=t,i=i,j=j)
                           for v,(k,t,i,j) in sorted(targets.items())],
                results=results)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
