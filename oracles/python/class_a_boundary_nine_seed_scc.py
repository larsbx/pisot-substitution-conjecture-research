"""Exact FINITE nine-swapped-seed SCC and X-closure comparison.

Uncapped complete literal-word graph only; a cap raises instead of
producing a claim. Coincidences are terminalized for existential
reachability. This does NOT prove all-parameter boundary hitting.
"""
from collections import deque
from pathlib import Path
from types import SimpleNamespace
import runpy

ROOT = Path(__file__).resolve().parents[2]
Geometry = runpy.run_path(str(ROOT / 'oracles/python/class_a_boundary_children.py'))['Geometry']
SCC = runpy.run_path(str(ROOT / 'reference/psc_research/overlap_obstruction.py'))
X = (0, 0, 1, 0, -1)
S1 = (0, 0, 0, 1, 0)
SEEDS = (
    (0, 1, 0, 0, 0), S1, (1, 0, -1, 1, 0),
    (0, 2, 0, 0, 0), (0, 0, 0, 0, 1), (2, 0, -1, 0, 1),
    (1, 2, 0, 0, 0), (1, 1, 0, 0, 1), (2, 1, 0, -1, 1),
)
class IncompleteGraph(RuntimeError):
    pass

def coincidence(w):
    return w[0] == w[1] and w[2:] == (0, 0, 0)

def build(k, t, cap=6000):
    if min(k,t)<0 or cap<1:
        raise ValueError('invalid parameter or cap')
    g=Geometry(-1,k,t)
    ids={}; states=[]; edges=[]
    for w in SEEDS:
        if not g.interior(w):
            raise ValueError(('non-strict swap source',w,k,t))
        if w not in ids:
            if len(states)>=cap:
                raise IncompleteGraph('initial seed cap exceeded')
            ids[w]=len(states);states.append(w)
    cursor=0
    while cursor<len(states):
        w=states[cursor];out=[]
        if not coincidence(w):
            for i in range(len(g.words[w[0]])):
                for j in range(len(g.words[w[1]])):
                    v=g.child(w,i,j)
                    if not g.interior(v):continue
                    if v not in ids:
                        if len(states)>=cap:
                            raise IncompleteGraph('full graph exceeds state cap')
                        ids[v]=len(states);states.append(v)
                    out.append((ids[v],i,j))
        edges.append(out);cursor+=1
    return states,edges,ids,g

def traverse(graph,starts):
    reached=set(starts);todo=list(starts)
    while todo:
        v=todo.pop()
        for w in graph[v]:
            if w not in reached:
                reached.add(w);todo.append(w)
    return reached

def backwards(graph,starts):
    rev=[[] for _ in graph]
    for v,children in enumerate(graph):
        for w in children:
            if not 0<=w<len(graph):raise ValueError('malformed graph edge')
            rev[w].append(v)
    dist={v:0 for v in starts};q=deque(starts)
    while q:
        v=q.popleft()
        for w in rev[v]:
            if w not in dist:
                dist[w]=dist[v]+1;q.append(w)
    return dist,rev

def hub_extension_criterion(adj,seeds,hub,exception):
    """Exact graph implication, independent of finiteness/SCC.

    If all seeds but possible exception lie in Reach(hub), and the
    exception's every child stays in Reach(hub) U {exception}, then
    their entire forward closure lies in that union. Contrapositive
    negative tests must fail when either hypothesis fails.
    """
    if not 0<=hub<len(adj) or not 0<=exception<len(adj):
        raise ValueError('unknown designated vertex')
    x=traverse(adj,[hub]);candidate=x|{exception}
    seed_good=all(s in candidate for s in seeds)
    exception_closed=all(w in candidate for w in adj[exception])
    if seed_good and exception_closed:
        actual=traverse(adj,seeds)
        assert actual <= candidate
    return dict(seed_hypothesis=seed_good,
                exception_children_hypothesis=exception_closed,
                sufficient_criterion=seed_good and exception_closed)

def audit(states,edges,ids,complete=True):
    if not complete:raise IncompleteGraph('cannot audit capped graph')
    if not states or len(states)!=len(edges) or len(states)!=len(ids):
        raise ValueError('malformed complete graph')
    graph=[[w for w,_,_ in row] for row in edges]
    typed={i for i,s in enumerate(states) if coincidence(s)}
    if not typed or X not in ids or any(graph[v] for v in typed):
        raise ValueError('missing hub/coincidence or unterminated coincidence')
    to_c,_=backwards(graph,typed)
    to_x,_=backwards(graph,[ids[X]])
    x_forward=traverse(graph,[ids[X]])
    other=set(range(len(states)))-x_forward
    sccs=SCC['sccs'](SimpleNamespace(states=states,adj=graph,capped=False))
    recurrent=[];sinks=[];x_scc=None
    for comp in sccs:
        member=set(comp)
        if ids[X] in member:x_scc=member
        if len(comp)>1 or any(v in graph[v] for v in comp):recurrent.append(member)
        if all(w in member for v in comp for w in graph[v]):sinks.append(member)
    assert x_scc==x_forward & set(to_x), 'X SCC and mutual reachability disagree'
    nonproductive=set(range(len(states)))-set(to_c)
    bad_sinks=[comp for comp in sinks if comp<=nonproductive]
    # Cross-check against the already-mainline obstruction oracle,
    # independently of the local condensation/SCC bookkeeping.
    canonical_bad=SCC['nonproductive_sink_sccs'](SimpleNamespace(
        states=states,adj=graph,capped=False,
        nonproductive=lambda: sorted(nonproductive)))
    assert {frozenset(v) for v in bad_sinks}=={frozenset(v) for v in canonical_bad}
    hub_rule=hub_extension_criterion(graph,[ids[s] for s in SEEDS],ids[X],ids[S1])
    return dict(states=len(states),indexed_edges=sum(map(len,edges)),
        x_forward=len(x_forward),extra_from_nine=sorted(states[v] for v in other),
        extra_nonterminal=sorted(states[v] for v in other if v not in typed),
        x_recurrent_size=len(x_scc),sccs=len(sccs),recurrent_sccs=len(recurrent),
        typed_terminals=len(typed),nonproductive_states=len(nonproductive),
        nonproductive_sink_sccs=len(bad_sinks),all_nonterminal_reach_x=all(
            i in to_x for i in range(len(states)) if i not in typed),
        max_depth_to_x=max(to_x.values()),
        max_depth_to_coincidence=max(to_c.values()),
        exception_criterion=hub_rule)

def probe(k,t,cap=6000):
    states,edges,ids,g=build(k,t,cap=cap)
    result=audit(states,edges,ids)
    return dict(k=k,t=t,**result,complete=True,
        finite_specimen_only=True,all_seed_boundary_hitting=False)

def census():
    return [probe(k,t) for k in range(4) for t in range(4)]

if __name__=='__main__':
    import json
    print(json.dumps(census(),indent=2,sort_keys=True))
