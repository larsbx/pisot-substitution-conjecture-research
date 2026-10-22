"""Independent exact selected-occurrence descent witnesses on finite d2 graphs.

The authoritative uniform target remains a parity-indexed affine rank and
ordered-occurrence certificate for *every* n. A complete finite graph supplies
only evidence/proof targets, never the quantified hitting theorem.
"""
from collections import deque, Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"oracles/python"))
from class_a_d2_parity_carrier import graph,integral_coordinates


def shortest_boundary_depths(g):
    incoming=[[] for _ in g.states]
    distance=[-1]*len(g.states)
    todo=deque()
    for i,vertex in enumerate(g.states):
        if not any(vertex[2]):
            distance[i]=0
            todo.append(i)
        for child_id in g.adj[i]:
            incoming[child_id].append(i)
    while todo:
        child=todo.popleft()
        for parent in incoming[child]:
            if distance[parent]<0:
                distance[parent]=distance[child]+1
                todo.append(parent)
    if any(d<0 for d in distance):
        raise ValueError("complete finite d2 graph contains a nonhitting state")
    return distance


def labels(g):
    out=[]
    seen=set()
    for a,b,t in g.states:
        k,c,y=integral_coordinates(g,t)
        label=(a-1,b-1,k,c,y)
        if label in seen:
            raise ValueError("duplicated exact typed label")
        seen.add(label)
        out.append(label)
    return out


def find_occurrence(g,parent,child):
    t,b,shift=parent
    for i,ti in enumerate(g.sigma[t]):
        pi=g.prefix[t,i]
        for j,bj in enumerate(g.sigma[b]):
            if (ti,bj)!=(child[0],child[1]):
                continue
            pj=g.prefix[b,j]
            candidate=(ti,bj,g.F.sub(g.F.add(g.F.mul(g.F.beta,shift),pj),pi))
            if candidate==child and g.overlaps(candidate):
                return i,j
    raise ValueError("chosen child lacks exact positive-interior ordered occurrence")


def build_finite(n):
    if not 4<=n<=24:
        raise ValueError("finite-only n budget 4<=n<=24")
    g=graph(n)
    if g.capped:
        raise ValueError("STATE_BUDGET_EXHAUSTED: no evidence verdict")
    d=shortest_boundary_depths(g)
    labs=labels(g)
    if len(labs)!=len(g.states):
        raise ValueError("partial label inversion")
    witness=[]
    zero=0
    for i,(s,depth) in enumerate(zip(g.states,d)):
        if depth==0:
            if any(s[2]):
                raise ValueError("zero-depth state has nonzero shift")
            zero+=1
            continue
        child_id=next((ch for ch in g.adj[i] if d[ch]==depth-1),None)
        if child_id is None:
            raise ValueError("state lacks one-step decreasing actual child")
        ti,bi=find_occurrence(g,s,g.states[child_id])
        witness.append((i,child_id,ti,bi,depth))
    if zero!=8 or len(witness)+zero!=len(g.states):
        raise ValueError("d2 target count changed")
    by_label={lab:d[i] for i,lab in enumerate(labs)}
    centered=[by_label.get((0,0,k,-k,0)) for k in (-1,0,1)]
    if centered!=[2,0,2]:
        raise ValueError("central typed row depth 2,0,2 regression")
    return {
        "n":n,
        "states":len(g.states),
        "targets":zero,
        "max_first_hit":max(d),
        "centered_slice":{"typed":(0,0,0,0),"k":(-1,0,1),"depths":centered},
        "actual_occurrence_witnesses":len(witness),
        "witness_sha256":sha256(json.dumps(witness,separators=(",",":")).encode()).hexdigest(),
        "_witness":witness,
    }


def validate_witness(n,proof):
    """Reject a forged destination, depth, or proper-prefix pair."""
    g=graph(n)
    d=shortest_boundary_depths(g)
    if proof["n"]!=n or proof["states"]!=len(g.states):
        raise ValueError("wrong specimen or incomplete graph")
    selected=proof["_witness"]
    if len(selected)!=len(g.states)-proof["targets"]:
        raise ValueError("truncated witness list")
    actual_digest=sha256(json.dumps(selected,separators=(",",":")).encode()).hexdigest()
    if actual_digest!=proof["witness_sha256"]:
        raise ValueError("exact ordered-edge witness digest changed")
    covered=set()
    for parent,child,ti,bi,depth in selected:
        if parent in covered or not 0<=parent<len(g.states) or not 0<=child<len(g.states):
            raise ValueError("duplicate or missing source")
        covered.add(parent)
        if depth!=d[parent] or d[parent]<=0 or d[child]!=d[parent]-1:
            raise ValueError("rank does not decrease on actual child")
        t,b,shift=g.states[parent]
        if not 0<=ti<len(g.sigma[t]) or not 0<=bi<len(g.sigma[b]):
            raise ValueError("invalid occurrence index")
        expected=(g.sigma[t][ti],g.sigma[b][bi],
                  g.F.sub(g.F.add(g.F.mul(g.F.beta,shift),g.prefix[b,bi]),
                          g.prefix[t,ti]))
        if expected!=g.states[child] or not g.overlaps(expected):
            raise ValueError("ordered occurrence does not produce exact child")
    if covered != {i for i,val in enumerate(d) if val>0}:
        raise ValueError("some source lacks an actual descent occurrence")
    return True


def report(n):
    packet=build_finite(n)
    assert validate_witness(n,packet)
    return {k:v for k,v in packet.items() if not k.startswith("_")}


if __name__=="__main__":
    ns=[int(x) for x in sys.argv[1:]] or [7,8,9,10,11,12]
    print(json.dumps({"scope":"complete finite exact graphs only; no all-n descent proof",
                      "profiles":[report(n) for n in ns]},indent=2))
