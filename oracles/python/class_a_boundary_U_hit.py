"""Independent exact rational oracle for the uniform selected boundary-U hit.

Checks literal four-step word occurrence addresses, Parikh transport, true
Perron interval geometry, and that the last common y/y start is *interior*
to the inflated V overlap. Finite replay only, not universal BH.
"""
from pathlib import Path
import runpy

base=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))
Geometry=base["Geometry"]
add=base["add"]
sub=base["sub"]


def witness(k,t):
    g=Geometry(-1,k,t)
    n,d=g.n,g.d
    parent=(0,1,0,0,0)
    path=((1,2),(0,t+1),(d+3,0),(1,2))
    targets=((2,2,-1,1,1),(0,2,1,2,-3),
             (2,0,0,-1,1),(2,2,0,0,0))
    assert g.interior(parent)
    steps=[]
    for (i,j),goal in zip(path,targets):
        assert i<len(g.words[parent[0]]) and j<len(g.words[parent[1]])
        target=g.child(parent,i,j)
        assert target==goal,(k,t,i,j,target,goal)
        assert g.interior(target),(k,t,i,j,target)
        steps.append(dict(parent=parent,i=i,j=j,target=target))
        parent=target
    # The selected final common start is not the outer top boundary.
    # In the positive shared length scale its top start is Lx,
    # the final selected tile end is Lx+Ly, and its parent image
    # [0,beta*Ly] strictly contains both.
    ly=g.lengths[2]
    lx=g.lengths[0]
    assert g.sign(lx)>0
    assert g.sign(sub(g.times_beta(ly),add(lx,ly)))>0
    V=targets[2]
    bottom_prefix=g.prefixes[V[1]][2]
    bottom_prefix_physical=g.shift((0,0,*bottom_prefix))
    bottom_child_start=add(g.times_beta(g.shift(V)),bottom_prefix_physical)
    assert bottom_child_start==lx
    # The earlier same-letter branch at bottom j=1 is nonzero-offset:
    assert g.child(V,1,1)!=(2,2,0,0,0)
    return dict(k=k,t=t,n=n,d=d,steps=steps,
                terminal=targets[-1],
                strictly_internal_newborn_start=True)


def probe():
    rows=[witness(k,t) for k in range(12) for t in (0,1,2,4,8)]
    return dict(scope="finite oracle of one infinite-family selected path; not all-state BH, not BPA packet closure",
                members=len(rows),matched=len(rows),per_member_depth=4,
                U_to_internal_hit_depth=2,rows=rows)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
