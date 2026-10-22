"""Independent Fraction-field calibration of finite class-A d=2 parity profiles.

This oracle directly constructs the complete exact seed-patch graph in
reference.psc_research.overlap_graph, extracts the unique integral shift
coordinates in its own left-eigenlength basis and compares every typed label
to the canonical Mojo D2_INTERVAL export. No finite sample proves an all-n
template or a pure-discreteness theorem.
"""
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"reference"))
from psc_research.overlap_graph import OverlapGraph,first_left_aligned_depths


def substitution(n):
    if n<4 or n>32:
        raise ValueError("finite-only, 4<=n<=32")
    return {1:(1,)+(3,)*(n+2)+(1,),
            2:(2,)+(3,)*n+(1,),
            3:(1,)+(3,)*(n+1)+(2,)}


@lru_cache(maxsize=4)
def graph(n):
    g=OverlapGraph(substitution(n),20000)
    if g.capped:
        raise RuntimeError("STATE_BUDGET_EXHAUSTED, no verdict")
    return g


def integral_coordinates(g,t):
    """Solve the 3x3 rational length-coordinate system exactly."""
    mat=[[g.l[j][i] for j in range(3)]+[t[i]] for i in range(3)]
    for j in range(3):
        pivot=next((r for r in range(j,3) if mat[r][j]),None)
        if pivot is None:
            raise ValueError("lengths do not span a rational 3-space")
        mat[j],mat[pivot]=mat[pivot],mat[j]
        divisor=mat[j][j]
        mat[j]=[a/divisor for a in mat[j]]
        for i in range(3):
            if i!=j:
                multiple=mat[i][j]
                mat[i]=[x-multiple*y for x,y in zip(mat[i],mat[j])]
    result=[mat[i][3] for i in range(3)]
    if any(v.denominator!=1 for v in result):
        raise ValueError("nonintegral shift coordinate in exact graph")
    return tuple(int(v) for v in result)


def typed_labels(g):
    labels=set()
    for t,b,shift in g.states:
        k,c,y=integral_coordinates(g,shift)
        label=(t-1,b-1,k,c,y)
        if label in labels:
            raise ValueError("duplicate typed vertex")
        labels.add(label)
    return labels


def profile_from_labels(labels):
    parts=defaultdict(list)
    for t,b,k,c,y in labels:
        parts[(t,b,k+c+y,y)].append(k)
    out=[]
    for key,values in sorted(parts.items()):
        values.sort()
        lo=hi=values[0]
        for value in values[1:]:
            if value==hi+1:
                hi=value
            else:
                out.append((*key,lo,hi))
                lo=hi=value
        out.append((*key,lo,hi))
    return out


def reference_profile(n):
    g=graph(n)
    labels=typed_labels(g)
    distances=first_left_aligned_depths(g)
    if len(labels)!=len(g.states) or any(d<0 for d in distances):
        raise RuntimeError("incomplete or nonhitting finite graph")
    return {
        "n":n,"states":len(labels),"intervals":profile_from_labels(labels),
        "max_hit":max(distances),"edges":sum(map(len,g.adj)),
        "seeds":len(g.seeds()),
    }


def read_profile(path):
    header=None
    rows=[]
    for line in Path(path).read_text().splitlines():
        parts=line.split()
        if not parts:
            continue
        if parts[0]=="D2_FINITE_SUMMARY":
            if header is not None:
                raise ValueError("duplicate profile completion")
            if len(parts)!=12 or parts[2]!="states" or parts[4]!="intervals" or parts[6]!="max_first_hit":
                raise ValueError("malformed finite profile summary")
            if parts[8]!="all_states_hitting=true" or parts[9]!="universal=false":
                raise ValueError("truncated or dishonest finite status")
            header=(int(parts[1]),int(parts[3]),int(parts[5]),int(parts[7]))
        elif parts[0]=="D2_INTERVAL":
            if len(parts)!=8:
                raise ValueError("invalid interval")
            n,*row=map(int,parts[1:])
            rows.append((n,tuple(row)))
    if header is None:
        raise ValueError("missing exact complete-graph receipt")
    n,states,number,deep=header
    if len(rows)!=number or any(v!=n for v,_ in rows):
        raise ValueError("inconsistent typed interval export")
    if len(set(x for _,x in rows))!=len(rows):
        raise ValueError("duplicate interval")
    return n,states,deep,[x for _,x in rows]


def calibrate(path):
    n,reported_states,reported_depth,observed=read_profile(path)
    expected=reference_profile(n)
    if expected["states"]!=reported_states or expected["max_hit"]!=reported_depth:
        raise ValueError("summary disagrees with independent exact graph")
    if observed!=expected["intervals"]:
        raise ValueError("typed profiles differ from independent exact graph")
    return {"n":n,"states":reported_states,"intervals":len(observed),
            "max_hit":reported_depth,"ordered_typed_intervals_equal":True,
            "arithmetic":"independent exact Q(beta) over Fraction",
            "scope":"one finite complete graph, not all-n carrier certification"}


if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit(__doc__)
    print(json.dumps(calibrate(sys.argv[1]),indent=2))
