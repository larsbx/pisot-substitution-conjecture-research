"""Exact finite SCC audit of four named minus class-A strict overlap seeds.

Uses original literal-word/Fraction Geometry. Stops all typed coincidences,
which is sound for *existential* coincidence reachability only.
Every state has all indexed strict children recorded, including duplicates.
An incomplete or capped graph is never assigned a productivity verdict.
No universal claim, no seed-to-literature realization transfer.
"""
from collections import deque
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    'class_a_boundary_children.py')))['Geometry']
X=(0,0,1,0,-1)
Y0=(2,2,1,-1,-1)
CY=(1,2,0,-2,2)
CC=(1,1,0,-2,3)
Q=(2,0,0,-1,1)
C=(2,2,0,0,0)
SEEDS=(X,Y0,CY,CC)

class IncompleteGraph(RuntimeError):
    pass

def coincidence(w):
    return w[0]==w[1] and w[2:]==(0,0,0)

def build(k,t,cap=6000):
    if min(k,t)<0 or cap<1:
        raise ValueError('outside audited chamber or invalid cap')
    g=Geometry(-1,k,t)
    ids={}; states=[]; adj=[]
    for w in SEEDS:
        if not g.interior(w):
            raise ValueError(('seed not strict',k,t,w))
        if w not in ids:
            ids[w]=len(states);states.append(w)
            if len(states)>cap:raise IncompleteGraph('initial seeds exceed cap')
    cursor=0
    while cursor<len(states):
        w=states[cursor]
        pairs=[]
        if not coincidence(w):
            for i in range(len(g.words[w[0]])):
                for j in range(len(g.words[w[1]])):
                    child=g.child(w,i,j)
                    if not g.interior(child):continue
                    if child not in ids:
                        if len(states)>=cap:
                            raise IncompleteGraph('strict closure reaches state cap; verdict undefined')
                        ids[child]=len(states);states.append(child)
                    pairs.append((ids[child],i,j))
        adj.append(pairs)
        cursor+=1
    return states,adj,ids,g

def backwards(adj, targets):
    reverse=[[] for _ in adj]
    for v,edges in enumerate(adj):
        for w,_,_ in edges:reverse[w].append(v)
    depths={v:0 for v in targets}
    queue=deque(targets)
    while queue:
        v=queue.popleft()
        for w in reverse[v]:
            if w not in depths:
                depths[w]=depths[v]+1
                queue.append(w)
    return depths,reverse

def components(adj,reverse):
    # Iterative Kosaraju; no recursion-size assumptions.
    finished=[];seen=set()
    for root in range(len(adj)):
        if root in seen:continue
        seen.add(root);stack=[(root,0)]
        while stack:
            v,i=stack[-1]
            if i<len(adj[v]):
                w=adj[v][i][0]
                stack[-1]=(v,i+1)
                if w not in seen:
                    seen.add(w);stack.append((w,0))
            else:
                stack.pop();finished.append(v)
    assigned=set();groups=[];which={}
    for root in reversed(finished):
        if root in assigned:continue
        assigned.add(root);todo=[root];group=[]
        while todo:
            v=todo.pop();which[v]=len(groups);group.append(v)
            for w in reverse[v]:
                if w not in assigned:
                    assigned.add(w);todo.append(w)
        groups.append(group)
    return groups,which

def forward(adj,root):
    seen={root};todo=[root]
    while todo:
        v=todo.pop()
        for w,_,_ in adj[v]:
            if w not in seen:
                seen.add(w);todo.append(w)
    return seen

def audit_graph(states,adj,ids,complete=True):
    if not complete:raise IncompleteGraph('cannot infer SCC productivity from partial graph')
    if len(states)!=len(adj) or len(states)!=len(ids) or len(states)==0:
        raise ValueError('malformed finite adjacency')
    for edges in adj:
        for w,i,j in edges:
            if not(0<=w<len(states) and i>=0 and j>=0):
                raise ValueError('malformed directed occurrence edge')
    term={v for v,w in enumerate(states) if coincidence(w)}
    if not term or X not in ids:
        raise ValueError('missing coincidence or canonical X source')
    if any(adj[v] for v in term):
        raise ValueError('typed coincidences must be terminalized for this audit')
    dist,rev=backwards(adj,term)
    to_x,_=backwards(adj,[ids[X]])
    comps,component_id=components(adj,rev)
    # Independent reachability characterization of X's SCC.
    x_scc=set(comps[component_id[ids[X]]])
    assert x_scc==forward(adj,ids[X]) & set(to_x)
    cyclic=[];closed=[];bad_sinks=[]
    for group in comps:
        members=set(group)
        cycle=(len(group)>1 or any(w==v for v in group for w,_,_ in adj[v]))
        sink=all(w in members for v in group for w,_,_ in adj[v])
        if cycle:cyclic.append(group)
        if sink:
            closed.append(group)
            if not any(v in dist for v in group):bad_sinks.append(group)
    nonterm={i for i,w in enumerate(states) if not coincidence(w)}
    all_to_x=nonterm<=set(to_x)
    all_productive=len(dist)==len(states)
    return dict(states=len(states),indexed_edges=sum(len(v) for v in adj),
                sccs=len(comps),nonterminal_x_scc=len(x_scc),
                other_nonterminal=len(nonterm-x_scc),
                recurrent_sccs=len(cyclic),sink_sccs=len(closed),
                bad_sink_sccs=len(bad_sinks),typed_terminals=len(term),
                all_nonterminal_reach_X=all_to_x,
                all_states_productive=all_productive,
                max_depth_to_X=max(to_x.values()),
                max_depth_to_coincidence=max(dist.values()) if dist else None)

def probe(k,t,cap=6000):
    states,adj,ids,g=build(k,t,cap)
    # Existing accepted W/X certificate: X(d+1,0)->Q(1,2)->C.
    assert g.child(X,g.d+1,0)==Q and g.interior(Q)
    assert g.child(Q,1,2)==C and g.interior(C)
    data=audit_graph(states,adj,ids)
    assert data['typed_terminals']==2
    assert data['all_nonterminal_reach_X']
    assert data['all_states_productive']
    assert data['recurrent_sccs']==1 and data['bad_sink_sccs']==0
    return dict(k=k,t=t,**data,
                seed_scope='X,Y0,CY,CC only; not all class-A seeds or literature overlaps',
                finite_graph_complete=True,universal_BH=False)

def census():
    specimens=[]
    for k in range(4):
        for t in range(4):specimens.append(probe(k,t))
    return specimens

if __name__=='__main__':
    import json
    print(json.dumps(census(),indent=2,sort_keys=True))
