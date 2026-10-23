"""Independent integer-polynomial all-n central d2 two-step paths.

This uniform lemma establishes the two specific paths, not hitting across
the d2 carrier. Finite differential replay below separately checks actual
Q(beta) child indices on selected complete graphs.
"""
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
from class_a_d2_parity_carrier import graph, integral_coordinates

L=((1,2,2),(1,0,0),(1,1,0))
PATHS=(
    ((0,0,-1,1,0), ((0,2),(1,2)),
     ((0,2,0,1,-1),(2,2,0,0,0))),
    ((0,0,1,-1,0), ((2,0),(2,1)),
     ((2,0,0,-1,1),(2,2,0,0,0))),
)


def prefix(i):
    if i==0:return (0,0,0)
    if i==1:return (1,0,0)
    if i==2:return (1,0,1)
    raise ValueError("index outside uniformly valid low prefixes")


def symbolic_child(parent,ti,bi):
    t,b,k,c,y=parent
    if t not in (0,2) or b not in (0,2):
        raise ValueError("only x/y parents")
    s=k+c+y
    if s:
        raise ValueError("uncancelled n coefficient: no uniform identity")
    pt,pb=prefix(ti),prefix(bi)
    return (
        0 if ti==0 else 2,
        0 if bi==0 else 2,
        k+s+pb[0]-pt[0],
        s-k+pb[1]-pt[1],
        2*k+y+pb[2]-pt[2],
    )


def positive_coeffs(v):
    return len(v)==3 and v[0]>0 and all(c>=0 for c in v)


def strict_real_all_positive_h(vertex):
    top,bottom,k,c,y=vertex
    if top not in range(3) or bottom not in range(3):
        raise ValueError("invalid child tile")
    shift=(k+c+y,2*k+y,2*k)
    lo=tuple(a+b for a,b in zip(shift,L[bottom]))
    hi=tuple(a-b for a,b in zip(L[top],shift))
    if not (positive_coeffs(lo) and positive_coeffs(hi)):
        raise ValueError(("insufficient exact strict geometry",vertex,lo,hi))
    return (lo,hi)


def prove_uniform():
    result=[]
    for start,indices,children in PATHS:
        current=start
        for (i,j),child in zip(indices,children):
            strict_real_all_positive_h(current)
            if symbolic_child(current,i,j)!=child:
                raise ValueError("n-independent child identity failed")
            current=child
        strict_real_all_positive_h(current)
        if current!=(2,2,0,0,0):
            raise ValueError("two-step path did not hit zero shift")
        result.append({"start":start,"indices":indices,
                       "terminal":current,"all_n_ge_4":True})
    return result


def finite_replay(n):
    if not 4<=n<=24:
        raise ValueError("finite differential replay only 4<=n<=24")
    g=graph(n)
    labels={}
    for state in g.states:
        t,b,shift=state
        k,c,y=integral_coordinates(g,shift)
        key=(t-1,b-1,k,c,y)
        if key in labels:
            raise ValueError("duplicate integral label")
        labels[key]=state
    for start,indices,children in PATHS:
        current=start
        for (i,j),child_label in zip(indices,children):
            t,b,shift=labels[current]
            if not (0<=i<len(g.sigma[t]) and 0<=j<len(g.sigma[b])):
                raise ValueError("actual index absent")
            constructed=(
                g.sigma[t][i],g.sigma[b][j],
                g.F.sub(g.F.add(g.F.mul(g.F.beta,shift),g.prefix[b,j]),
                        g.prefix[t,i]),
            )
            if constructed!=labels[child_label] or not g.overlaps(constructed):
                raise ValueError("chosen ordered child disagrees with exact Q(beta)")
            current=child_label
    return {"n":n,"two_explicit_paths_replayed":True,"uniform_evidence":False}


if __name__=="__main__":
    import json
    print(json.dumps({"all_n_uniform_paths":prove_uniform(),
                      "finite_differential":[finite_replay(n) for n in (4,7,8,9,12)],
                      "scope":"two centered configurations only"},indent=2))
