"""Independent finite exact-rational replay of both T_m run/first stars.

A finite control, not an infinite classifier proof or a BH receipt.
"""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]


def expected(eps,k,t,m,n):
    r=2 if eps==1 and k<=3 else 1
    if m not in (r,r+1):
        raise ValueError("invalid source")
    if m==r:
        return set()
    if eps==-1:
        return set(range(k+3,min(k+5,n+eps)+1))
    if k<=3:
        return set(range(3*k+t+3,n+eps+1))
    return set(range(max(1,k-6),k-2))


def probe():
    members=cells=ordinals=accepted=0
    rows=[]
    for eps in (-1,1):
        for k in range(16):
            for t in list(range(8))+[16,40]:
                g=Geometry(eps,k,t)
                members+=1
                r=2 if eps==1 and k<=3 else 1
                for m in (r,r+1):
                    cells+=1
                    parent=(2,2,-1,1,m)
                    assert g.interior(parent)
                    real=set()
                    for i in range(1,g.n+eps+1):
                        ordinals+=1
                        child=g.child(parent,i,0)
                        assert child==(2,0,m-1,m+1,m*(g.n+eps)-g.d-i+1)
                        if g.interior(child):
                            real.add(i)
                            accepted+=1
                    want=expected(eps,k,t,m,g.n)
                    assert want==real,(eps,k,t,m,want,real)
                    if t in (0,1,2,7,40) and k in (0,2,3,4,5,6,7,8,15):
                        rows.append(dict(eps=eps,k=k,t=t,m=m,indices=sorted(real)))
    return dict(scope="finite ordered word/geometry oracle; no BH",
                members=members,cells=cells,ordinals=ordinals,
                accepted=accepted,rows=rows)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
