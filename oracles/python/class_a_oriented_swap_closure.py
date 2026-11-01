"""Exact finite 18-orientation swap-seed graph and conditional closure theorem.

The universal set identity follows algebraically from three *external*
scoped certificates: Reach(nine swaps)=Reach(X) U {E6}, reversal
invariance of Reach(X), and an edge automorphism under reversal.
This module does not promote the external certificates or global BH/PSC.
"""
from collections import deque
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
X=(0,0,1,0,-1)
E6=(0,0,0,1,0)
S9=((0,1,0,0,0),E6,(1,0,-1,1,0),
    (0,2,0,0,0),(0,0,0,0,1),(2,0,-1,0,1),
    (1,2,0,0,0),(1,1,0,0,1),(2,1,0,-1,1))

def reverse(w):return(w[1],w[0],*(-z for z in w[2:]))
R_E6=reverse(E6)
S18=tuple(dict.fromkeys(S9+tuple(reverse(s) for s in S9)))
assert len(S9)==9 and len(S18)==18

class IncompleteGraph(RuntimeError):pass

def coincidence(w):return w[0]==w[1] and w[2:]==(0,0,0)

def closure(g,initial,cap=5000):
    """All literal strict indexed children; terminalize typed coincidence.

    Refuse a cap before concluding anything about a partial graph.
    """
    if cap<1:raise ValueError('invalid cap')
    states=[];ids={};adj=[]
    for w in initial:
        if not g.interior(w):raise ValueError(('not strict source',w))
        if w not in ids:
            if len(states)>=cap:raise IncompleteGraph('initial vertices exceed cap')
            ids[w]=len(states);states.append(w)
    cursor=0
    while cursor<len(states):
        parent=states[cursor];out=[]
        if not coincidence(parent):
            for i in range(len(g.words[parent[0]])):
                for j in range(len(g.words[parent[1]])):
                    child=g.child(parent,i,j)
                    if not g.interior(child):continue
                    if child not in ids:
                        if len(states)>=cap:raise IncompleteGraph('incomplete strict closure')
                        ids[child]=len(states);states.append(child)
                    out.append((ids[child],i,j))
        adj.append(out);cursor+=1
    return states,ids,adj

def forward(adj,ids,starts):
    found=set(starts);q=deque(starts)
    while q:
        v=q.popleft()
        for w,_,_ in adj[v]:
            if w not in found:found.add(w);q.append(w)
    return found

def oriented_closure_identity(U,nine,Rnine,S18set):
    """Exact finite-set witness of the abstract graph equality.

    The universally quantified theorem needs three external facts:
    Reach(S9)=U U {E6}, Reach(R(S9))=R(Reach(S9)), and R(U)=U.
    Their union yields Reach(S18)=U U {E6,R(E6)}.
    """
    assert nine<=S18set and Rnine<=S18set
    assert nine|Rnine==S18set
    if nine!=U|{E6} and nine!=U:
        raise AssertionError('nine-seed closure premise missing')
    if Rnine!={reverse(s) for s in nine}:
        raise AssertionError('actual reversal automorphism premise missing')
    if {reverse(s) for s in U}!=U:
        raise AssertionError('forward-X reversal closure premise missing')
    assert S18set==U|{E6,R_E6}
    return dict(nine_equals_x_or_one_exception=True,
                x_closed_under_reversal=True,
                eighteen_equals_x_plus_two_exceptions=True,
                new_theorem_unconditional=False)

def probe(k,t,cap=5000):
    if min(k,t)<0:raise ValueError('invalid minus parameters')
    g=Geometry(-1,k,t)
    states,ids,adj=closure(g,S18,cap)
    full=set(states)
    U={states[z] for z in forward(adj,ids,[ids[X]])}
    nine={states[z] for z in forward(adj,ids,[ids[s] for s in S9])}
    rnine={states[z] for z in forward(adj,ids,[ids[reverse(s)] for s in S9])}
    assert all(reverse(v) in full for v in full)
    assert {reverse(v) for v in U}==U
    identities=oriented_closure_identity(U,nine,rnine,full)
    assert len(full-U) in (0,2)
    assert full-U in (set(),{E6,R_E6})
    return dict(k=k,t=t,n=g.n,d=g.d,
                full_oriented_seed_graph=len(full),
                nine_seed_graph=len(nine),forward_X_graph=len(U),
                exceptional_labels=sorted(full-U),
                source_orientation_count=18,
                root_locality='minus class A only',
                finite_graph_complete=True,
                conditional_set_identity=identities,
                all_descendants_productive_unproved=True,
                universal_BH=False)

def census():return [probe(k,t) for k in range(4) for t in range(4)]

if __name__=='__main__':
    import json
    print(json.dumps(census(),sort_keys=True,indent=2))
