"""Finite proof-carrying coincidence ranks on exact reversal-orbit quotients.

Producer uses shortest-path BFS; independent checker does NOT use BFS.
Each nonterminal representative carries a genuine indexed successor with
rank decreased by one. Lifting verifies the original word/Parikh/geometry.
Valid ONLY after complete exact overlap closure, never from a capped graph.
"""
import hashlib
import json
from pathlib import Path
import runpy

qmod=runpy.run_path(str(Path(__file__).with_name('class_a_reversal_quotient.py')))
X=qmod['X']; S18=qmod['S18']; Geometry=qmod['Geometry']

class UnproductiveQuotient(RuntimeError): pass
class InvalidRankCertificate(ValueError): pass

def build_complete(k,t,scope='X',cap=5000):
    if scope not in ('X','S18') or min(k,t)<0:
        raise ValueError('unknown scope or negative parameter')
    g=Geometry(-1,k,t)
    initial=[X] if scope=='X' else S18
    states,ids,edges=qmod['raw']['closure'](g,initial,cap=cap)
    q=qmod['quotient'](states,ids,edges)
    return g,states,q

def produce(q):
    terminals=[i for i,w in enumerate(q['labels']) if qmod['coincidence'](w)]
    dist,chosen=qmod['reverse_distances'](q['adj'],terminals)
    if len(dist)!=len(q['labels']):
        raise UnproductiveQuotient('a complete quotient orbit cannot reach typed coincidence')
    rows=[]
    for v,label in enumerate(q['labels']):
        edge=chosen.get(v)
        witness=None if edge is None else [edge[1],edge[2],list(q['labels'][edge[0]])]
        rows.append(dict(label=list(label),rank=dist[v],edge=witness))
    return rows

def verify_rank(q,rows):
    """A BFS-INDEPENDENT verifier of finite well-founded chosen-edge rank.

    No graph search or heuristic: simply check every vertex exactly once,
    typed terminal iff rank zero, and a genuine edge to rank minus one.
    An absent row, false typed terminal or an invented child fails closed.
    """
    if len(rows)!=len(q['labels']):
        raise InvalidRankCertificate('incomplete orbit certificate')
    expected=set(q['labels']);rank={};choice={}
    for row in rows:
        try:
            w=tuple(row['label']);d=row['rank'];edge=row['edge']
        except (KeyError,TypeError):
            raise InvalidRankCertificate('malformed row') from None
        if w not in expected or w in rank or type(d) is not int or d<0:
            raise InvalidRankCertificate('unknown, duplicate or invalid rank')
        rank[w]=d
        terminal=qmod['coincidence'](w)
        if terminal:
            if d!=0 or edge is not None:
                raise InvalidRankCertificate('typed terminal rank/edge mismatch')
            continue
        if d==0 or not isinstance(edge,list) or len(edge)!=3:
            raise InvalidRankCertificate('nonterminal must have positive rank and child')
        i,j,dest=edge
        if type(i) is not int or type(j) is not int or min(i,j)<0:
            raise InvalidRankCertificate('bad ordered occurrence index')
        target=tuple(dest)
        if target not in q['ids']:
            raise InvalidRankCertificate('unknown child orbit')
        e=(q['ids'][target],i,j)
        if e not in q['adj'][q['ids'][w]]:
            raise InvalidRankCertificate('child is not a genuine indexed quotient edge')
        choice[w]=(target,e)
    if set(rank)!=expected:
        raise InvalidRankCertificate('missing state')
    for w,(target,_) in choice.items():
        if rank[target]!=rank[w]-1:
            raise InvalidRankCertificate('chosen edge does not decrease integer rank')
    return dict(orbits=len(q['labels']),selected_edges=len(choice),
                typed_terminals=len(q['labels'])-len(choice),
                max_rank=max(rank.values()),rank_by_label=rank,choice_by_label=choice)

def verify_actual_lifts(g,states,q,rows):
    """Check a selected decreasing chain against actual words for EVERY state."""
    check=verify_rank(q,rows)
    rank=check['rank_by_label'];choice=check['choice_by_label'];edges=0
    for state in states:
        current=state
        remaining=rank[qmod['canonical'](current)]
        while remaining:
            rep=qmod['canonical'](current)
            target,e=choice[rep]
            lifted=qmod['lift'](g,q,current,[(q['ids'][rep],e)])
            assert len(lifted)==1
            current=lifted[0][2]
            if rank[qmod['canonical'](current)]!=remaining-1:
                raise InvalidRankCertificate('actual child fails rank descent')
            edges+=1;remaining-=1
        if not qmod['coincidence'](current):
            raise InvalidRankCertificate('actual path did not hit typed coincidence')
    return dict(actual_source_states=len(states),actual_indexed_lift_edges=edges,
                all_states_hit_typed_coincidence=True)

def digest(rows):
    data=json.dumps(rows,sort_keys=True,separators=(',',':')).encode()
    return hashlib.sha256(data).hexdigest()

def certify(k,t,scope='X',cap=5000,verify_all=True):
    g,states,q=build_complete(k,t,scope,cap)
    rows=produce(q)
    v=verify_rank(q,rows)
    lifts=verify_actual_lifts(g,states,q,rows) if verify_all else None
    return dict(k=k,t=t,scope=scope,actual_vertices=len(states),
                quotient_vertices=v['orbits'],chosen_occurrence_edges=v['selected_edges'],
                terminal_orbits=v['typed_terminals'],maximum_rank=v['max_rank'],
                manifest_sha256=digest(rows),actual_lifts=lifts,
                complete_finite_specimen=True,universal_parameterized_rank=False)

def export(k,t,scope='X',cap=5000):
    g,states,q=build_complete(k,t,scope,cap)
    rows=produce(q)
    check=verify_rank(q,rows)
    return dict(k=k,t=t,scope=scope,complete_finite_graph=True,
                original_vertices=len(states),quotient_vertices=len(rows),
                terminal_orbits=check['typed_terminals'],max_rank=check['max_rank'],
                manifest_sha256=digest(rows),rows=rows)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('--k',type=int,default=3)
    p.add_argument('--t',type=int,default=0)
    p.add_argument('--scope',choices=['X','S18'],default='X')
    p.add_argument('--full',action='store_true',help='emit full proof-carrying rows')
    args=p.parse_args()
    obj=export(args.k,args.t,args.scope) if args.full else certify(args.k,args.t,args.scope)
    print(json.dumps(obj,sort_keys=True,indent=2))
