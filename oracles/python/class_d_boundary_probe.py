"""Independent replay via the existing Q(beta) graph oracle; canonical Mojo companion.
Run from repository root: python3 oracles/python/class_d_boundary_probe.py
"""
from pathlib import Path
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "reference"))
from psc_research.overlap_graph import OverlapGraph, first_left_aligned_depths


def probe(s, a, cap=20000):
    if s not in (1, -1) or not 0 <= a <= 8 or not 1 <= cap <= 20000:
        raise ValueError("outside declared parameter/state budget")
    p,q,r = 4+3*a-s, 4+3*a-2*s, 2+2*a-2*s
    sigma = {1:(1,)+(3,)*p+(2,),2:(2,)+(3,)*q+(1,),3:(2,)+(3,)*r+(2,)}
    g=OverlapGraph(sigma,cap)
    if g.capped:
        raise RuntimeError("STATE_BUDGET_EXHAUSTED: no verdict")
    k=first_left_aligned_depths(g)
    return dict(s=s,a=a,b=0,p=p,q=q,r=r,states=len(g.states),max_half_depth=max(k),missing=sum(d<0 for d in k))


def report():
    return dict(status="BOUNDED_CALIBRATION_COMPLETE",authority="independent-python-oracle",canonical_replay="kernel/class_d_boundary_probe.mojo",canonical_execution="NOT_RUN_LOCALLY",domain="s in {+1,-1}, a in {0,1,2,3}, b=0",state_cap_per_graph=20000,rng="NONE",family_exhaustion=False,rows=[probe(s,a) for s in (1,-1) for a in range(4)])




def labelled_support(a):
    """Independently recover integral Parikh offsets by exact Gauss inversion."""
    from fractions import Fraction
    if not 0 <= a <= 8:
        raise ValueError("outside declared parameter budget")
    p,q,r=5+3*a,6+3*a,4+2*a
    g=OverlapGraph({1:(1,)+(3,)*p+(2,),2:(2,)+(3,)*q+(1,),3:(2,)+(3,)*r+(2,)},20000)
    if g.capped:
        raise RuntimeError("STATE_BUDGET_EXHAUSTED")
    matrix=[[g.l[j][i] for j in range(3)]+[Fraction(i==j) for j in range(3)] for i in range(3)]
    for col in range(3):
        pivots=[i for i in range(col,3) if matrix[i][col]]
        if not pivots:
            raise ValueError("singular length basis")
        pivot=pivots[0]
        matrix[col],matrix[pivot]=matrix[pivot],matrix[col]
        scale=matrix[col][col]
        matrix[col]=[v/scale for v in matrix[col]]
        for i in range(3):
            if i != col:
                scale=matrix[i][col]
                matrix[i]=[x-scale*y for x,y in zip(matrix[i],matrix[col])]
    labels=[]
    for top,bottom,t in g.states:
        w=[sum(matrix[k][3+j]*t[j] for j in range(3)) for k in range(3)]
        if any(x.denominator != 1 for x in w):
            raise ValueError("nonintegral offset")
        if any(sum(w[k]*g.l[k][j] for k in range(3)) != t[j] for j in range(3)):
            raise ValueError("offset inverse replay failed")
        labels.append((top-1,bottom-1,*map(int,w)))
    return {label:set(labels[j] for j in g.adj[i]) for i,label in enumerate(labels)}


def support_report():
    left,right=labelled_support(2),labelled_support(3)
    parents=[(0,0,0,0,1),(1,0,-1,1,1)]
    children=[(2,2,0,2,-3),(2,2,1,1,-3)]
    return dict(scope="s=-1, b=0, a=2 versus a=3",authority="independent-python-oracle",canonical_execution="NOT_RUN_LOCALLY",state_cap_per_graph=20000,vertices=[len(left),len(right)],vertex_labels_equal=set(left)==set(right),support_equal=left==right,witnesses=[dict(parent=p,child=c,present_at_a2=c in left[p],present_at_a3=c in right[p]) for p,c in zip(parents,children)],family_exhaustion=False)

if __name__ == "__main__":
    if sys.argv[1:] not in ([],["--support"]):
        raise ValueError("usage: class_d_boundary_probe.py [--support]")
    print(json.dumps(support_report() if sys.argv[1:] else report(),indent=2))
