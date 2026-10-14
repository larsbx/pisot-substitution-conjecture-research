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

if __name__ == "__main__":
    print(json.dumps(report(),indent=2))
