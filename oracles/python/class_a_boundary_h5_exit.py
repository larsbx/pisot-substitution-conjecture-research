"""Independent literal-word exact-rational H5 typed exit oracle.

The beta sign routine is a bounded Fraction root enclosure and fails closed.
Only finitely many k,t are replayed, not a universal BH proof.
"""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]


def H5_path(k,t):
    if k<0 or t<0:
        raise ValueError("invalid minus boundary parameter")
    g=Geometry(-1,k,t)
    n,d=g.n,g.d
    A=n+d
    source=(0,2,2,2,-5)
    assert g.interior(source)
    H4=(0,2,0,-2,4)
    assert g.interior(H4)
    assert g.child(H4,A+1,t+2)==source
    if k==0:
        sequence=((A+1,0,(0,0,0,-3,4)),
                  (t+1,0,(2,0,0,1,-1)),
                  (2,1,(2,2,0,0,0)))
    elif k==1:
        sequence=((A+1,0,(0,0,0,-3,3)),
                  (1,4,(2,2,0,0,0)))
    else:
        sequence=((2*d-n+3,0,(2,0,0,-3,3)),
                  (1,4,(2,2,0,0,0)))
    steps=[]
    for i,j,target in sequence:
        actual=g.child(source,i,j)
        assert actual==target,(k,t,i,j,actual,target)
        assert g.interior(actual),(k,t,i,j,target)
        steps.append(dict(parent=source,i=i,j=j,target=target))
        source=target
    assert steps[-1]["target"]==(2,2,0,0,0)
    return dict(k=k,t=t,n=n,d=d,steps=steps,depth=len(steps))


def probe():
    rows=[H5_path(k,t) for k in range(12) for t in range(9)]
    return dict(scope="bounded exact Fraction oracle, not a closed carrier or global BH",
                members=len(rows),k0_three_steps=9,
                other_two_steps=len(rows)-9,rows=rows)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
