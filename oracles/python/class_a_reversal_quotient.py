"""Exact quotient of complete class-A overlap graphs by actual reversal.

Every quotient edge records a genuine zero-based ordered occurrence of its
canonical representative. Lifting from the reversed representative swaps
indices and applies the full five-coordinate state reversal. This is a
finite graph certificate, NOT a universal X-descendant productivity proof.
"""
from collections import deque
from pathlib import Path
import runpy

HERE=Path(__file__).resolve().parent
raw=runpy.run_path(str(HERE/'class_a_oriented_swap_closure.py'))
Geometry=raw['Geometry'];X=raw['X'];E6=raw['E6'];S18=raw['S18']
reverse=raw['reverse'];coincidence=raw['coincidence']
IncompleteGraph=raw['IncompleteGraph']

class InvalidReversalGraph(ValueError): pass

def canonical(w):
    return min(w,reverse(w))

def quotient(states,ids,edges):
    """Require a COMPLETE reversal-invariant typed-terminalized graph.

    The caller must supply all strict child occurrences (not a capped graph).
    Reversal invariance is verified edgewise, including index pairs and the
    full Parikh target. It is not inferred from opposite tile types.
    """
    if len(states)!=len(ids) or len(states)!=len(edges) or not states:
        raise InvalidReversalGraph('incomplete or malformed state/edge table')
    if len(set(states))!=len(states) or any(ids.get(w)!=v for v,w in enumerate(states)):
        raise InvalidReversalGraph('duplicate state or corrupt state IDs')
    if any(reverse(w) not in ids for w in states):
        raise InvalidReversalGraph('graph not closed under real reversal')
    edge_sets=[]
    for v,w in enumerate(states):
        seen=set()
        for target,i,j in edges[v]:
            if not 0<=target<len(states) or min(i,j)<0:
                raise InvalidReversalGraph('bad occurrence or target')
            if (i,j) in seen:
                raise InvalidReversalGraph('duplicate occurrence address')
            seen.add((i,j))
        if coincidence(w) and seen:
            raise InvalidReversalGraph('coincidence is not terminalized')
        if w==reverse(w) and not coincidence(w):
            raise InvalidReversalGraph('nonterminal reversal-fixed source')
        edge_sets.append(set(edges[v]))
    for v,w in enumerate(states):
        rv=ids[reverse(w)]
        for target,i,j in edges[v]:
            if (ids[reverse(states[target])],j,i) not in edge_sets[rv]:
                raise InvalidReversalGraph('missing actual reversed occurrence')
    labels=sorted({canonical(w) for w in states})
    qid={w:i for i,w in enumerate(labels)}
    orbit_of=[qid[canonical(w)] for w in states]
    qedges=[]
    for label in labels:
        v=ids[label]
        qedges.append([(orbit_of[target],i,j) for target,i,j in edges[v]])
    originals=sum(len(es) for es in edges)
    compressed=sum(len(es) for es in qedges)
    if originals!=2*compressed:
        raise InvalidReversalGraph('unpaired indexed edges or fixed source')
    fixed={w for w in states if reverse(w)==w}
    if not all(coincidence(w) for w in fixed):
        raise InvalidReversalGraph('fixed orbit is not typed coincidence')
    if len(states)!=2*(len(labels)-len(fixed))+len(fixed):
        raise InvalidReversalGraph('incorrect quotient orbit sizes')
    return dict(labels=labels,ids=qid,adj=qedges,orbit_of=orbit_of,
                original_edges=originals,quotient_edges=compressed,
                fixed_typed_states=sorted(fixed),
                original_vertices=len(states),quotient_vertices=len(labels))

def reverse_distances(adj,terminals):
    reverse_graph=[[] for _ in adj]
    for v,children in enumerate(adj):
        for w,*_ in children:
            reverse_graph[w].append(v)
    dist={v:0 for v in terminals}
    chosen={}
    queue=deque(terminals)
    while queue:
        w=queue.popleft()
        for v in reverse_graph[w]:
            if v not in dist:
                dist[v]=dist[w]+1
                chosen[v]=next((edge for edge in adj[v] if edge[0]==w))
                queue.append(v)
    return dist,chosen

def lift(g,quotient_graph,start,selected):
    """Lift *any* path with valid quotient occurrence witnesses.

    A quotient edge selected from its canonical source can be lifted from
    either member of that source orbit, using reversal index transport.
    All actual child coordinates/strictness are verified after each lift.
    """
    q=quotient_graph
    state=start
    out=[]
    for source_id,edge in selected:
        if not 0<=source_id<len(q['labels']) or edge not in q['adj'][source_id]:
            raise InvalidReversalGraph('edge is not a recorded quotient witness')
        rep=q['labels'][source_id]
        if canonical(state)!=rep:
            raise InvalidReversalGraph('quotient witness has wrong source orbit')
        target_id,i,j=edge
        if state==rep:
            child=g.child(state,i,j)
            aa,bb=i,j
        else:
            assert state==reverse(rep)
            aa,bb=j,i
            child=g.child(state,aa,bb)
        if not g.interior(child) or canonical(child)!=q['labels'][target_id]:
            raise InvalidReversalGraph('lift does not yield intended strict orbit')
        out.append((aa,bb,child))
        state=child
    return out

def target_path(q,from_orbit,chosen):
    steps=[];current=from_orbit
    while current in chosen:
        e=chosen[current]
        steps.append((current,e))
        current=e[0]
    return steps

def strongly_connected_components(adj):
    """Iterative Kosaraju, without treating any quotient SCC as an X SCC."""
    visited=set();finished=[]
    for root in range(len(adj)):
        if root in visited: continue
        visited.add(root)
        stack=[(root,0)]
        while stack:
            v,j=stack[-1]
            if j<len(adj[v]):
                w=adj[v][j][0]
                stack[-1]=(v,j+1)
                if w not in visited:
                    visited.add(w);stack.append((w,0))
            else:
                stack.pop();finished.append(v)
    reverse_edges=[[] for _ in adj]
    for v,es in enumerate(adj):
        for w,_,_ in es:reverse_edges[w].append(v)
    seen=set();comps=[]
    for root in reversed(finished):
        if root in seen:continue
        group=[];todo=[root];seen.add(root)
        while todo:
            v=todo.pop();group.append(v)
            for w in reverse_edges[v]:
                if w not in seen:seen.add(w);todo.append(w)
        comps.append(group)
    return comps

def analyze(k,t,scope='X',cap=5000,verify_all_lifts=True):
    if min(k,t)<0 or scope not in ('X','S18'):
        raise ValueError('unknown minus chamber or scope')
    g=Geometry(-1,k,t)
    seeds=[X] if scope=='X' else S18
    states,ids,edges=raw['closure'](g,seeds,cap=cap)
    q=quotient(states,ids,edges)
    terminals=[i for i,w in enumerate(q['labels']) if coincidence(w)]
    qdist,chosen=reverse_distances(q['adj'],terminals)
    odist,_=reverse_distances(edges,[i for i,w in enumerate(states) if coincidence(w)])
    # This is an exact finite instantiation of the quotient hitting lemma:
    # symmetry-invariant accepting sets yield the same shortest distance.
    assert all(odist.get(v)==qdist.get(q['orbit_of'][v]) for v in range(len(states)))
    comps=strongly_connected_components(q['adj'])
    cyclic=[gr for gr in comps if len(gr)>1 or any(e[0]==gr[0] for e in q['adj'][gr[0]])]
    x_orbit=q['ids'][canonical(X)]
    x_component=next(gr for gr in comps if x_orbit in gr)
    exception=q['ids'].get(canonical(E6))
    if scope=='X':
        assert exception is None or exception in x_component
    if verify_all_lifts:
        # Every shortest quotient path is independently lifted from BOTH
        # members of its source orbit. Fixed terminals are lifted once.
        for v,w in enumerate(states):
            if v not in odist:continue
            path=target_path(q,q['orbit_of'][v],chosen)
            walk=lift(g,q,w,path)
            end=walk[-1][2] if walk else w
            assert coincidence(end) and len(walk)==odist[v]
    bad=len(states)-len(odist)
    return dict(k=k,t=t,scope=scope,actual_vertices=len(states),
                quotient_vertices=q['quotient_vertices'],
                actual_indexed_edges=q['original_edges'],
                quotient_indexed_edges=q['quotient_edges'],
                fixed_typed_terminals=len(q['fixed_typed_states']),
                quotient_sccs=len(comps),quotient_recurrent_sccs=len(cyclic),
                x_quotient_scc=len(x_component),
                quotient_nonproductive_orbits=len(q['labels'])-len(qdist),
                actual_nonproductive_vertices=bad,
                max_exact_coincidence_distance=max(qdist.values()) if qdist else None,
                all_states_productive=(bad==0),
                graph_complete=True,universal_X_productivity=False,
                carried_source_reversal_theorem_requires_PR432=True)

def census():
    return [analyze(k,t,scope='X') for k in range(4) for t in range(4)]

if __name__=='__main__':
    import json
    print(json.dumps(census(),sort_keys=True,indent=2))
