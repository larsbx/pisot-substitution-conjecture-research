"""Independent exact all-child physical-overlap closure for the #487 specimen.

This reuses only the independent Python literal return coding, never Mojo
outputs or a supplied graph. Saturation must exhaust its entire queue. The
rational Perron enclosure is isolated here independently by 60 bisections.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import argparse
import hashlib
import json
from pathlib import Path

import pytest
from test_c4_return_boundary_carrier_oracle import (
    SIGMA, RETURNS, STATES, edge, parikh, add, subtract, m_times, apply,
)


def polynomial(x):
    return x*x*x-4*x*x+4*x-2


def root_enclosure():
    lo, hi = Fraction(14, 5), Fraction(3)
    assert polynomial(lo) < 0 < polynomial(hi)
    # f' is positive throughout this interval: f''=6x-8>0 and f'(14/5)>0.
    assert 3*lo*lo-8*lo+4 > 0 and 6*lo-8 > 0
    for _ in range(60):
        mid = (lo+hi)/2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


BETA_LO, BETA_HI = root_enclosure()
# g(x)=x^2-3x+2 is increasing throughout the enclosure.
ELL = ((Fraction(1), Fraction(1)),
       (BETA_LO-1, BETA_HI-1),
       (BETA_LO**2-3*BETA_LO+2, BETA_HI**2-3*BETA_HI+2))
E = ((1,0,0), (0,1,0), (0,0,1))
ZERO = (0,0,0)


def perron_sign(vector):
    if len(vector) != 3 or any(type(x) is not int or abs(x)>1000 for x in vector):
        raise ValueError('invalid or over-budget exact vector')
    if vector == ZERO:
        return 0
    lo = sum(x*(a if x>=0 else b) for x,(a,b) in zip(vector,ELL))
    hi = sum(x*(b if x>=0 else a) for x,(a,b) in zip(vector,ELL))
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    raise ValueError('root enclosure insufficient; no sign verdict')


def overlaps(physical):
    x,y,delta = physical
    if type(x) is not int or type(y) is not int or not (0<=x<3 and 0<=y<3):
        raise ValueError('bad next letter')
    # Top interval: [ell.delta, ell.delta+ell[x]]. Bottom: [0,ell[y]].
    return (perron_sign(subtract(delta,E[y])) < 0 and
            perron_sign(add(delta,E[x])) > 0)


POINT_INDEX = {point:i for i,point in enumerate(STATES)}
NEXT = tuple(int(RETURNS[j][d]) for j,d in STATES)
MASS = tuple(parikh(RETURNS[j][:d]) for j,d in STATES)
CHILD = tuple(tuple(POINT_INDEX[edge(j,d,t).target]
                    for t in range(len(SIGMA[NEXT[i]])))
              for i,(j,d) in enumerate(STATES))
DIGIT = tuple(tuple(parikh(w[:t]) for t in range(len(w))) for w in SIGMA)


def physical(state):
    top,bottom,a,b,c = state
    return NEXT[top],NEXT[bottom],(a,b,c)


def children(state):
    top,bottom,*d = state
    x,y = NEXT[top],NEXT[bottom]
    expanded = m_times(d)
    for t in range(len(SIGMA[x])):
        for u in range(len(SIGMA[y])):
            delta = add(expanded,subtract(DIGIT[x][t],DIGIT[y][u]))
            target = (CHILD[top][t],CHILD[bottom][u],*delta)
            if overlaps(physical(target)):
                yield t,u,target


def initial_states():
    result=[]
    for top,bottom in product(range(28),repeat=2):
        state=(top,bottom,*subtract(MASS[top],MASS[bottom]))
        if overlaps(physical(state)):
            result.append(state)
    return result


def build(cap=2048):
    if type(cap) is not int or not 1<=cap<=2048:
        raise ValueError('explicit complete-saturation resource budget')
    states=[]
    index={}
    predecessor=[]
    def intern(state,parent=None):
        if state not in index:
            if len(states)>=cap:
                raise ValueError('cap exhausted: no closure or productivity verdict')
            index[state]=len(states)
            states.append(state)
            predecessor.append(parent)
        return index[state]
    for state in initial_states():
        intern(state)
    initial_count=len(states)
    adjacency=[]
    for i,state in enumerate(states):  # Python visits newly appended queue entries.
        adjacency.append(tuple((t,u,intern(target,(i,t,u)))
                               for t,u,target in children(state)))
    assert len(adjacency)==len(states)
    distance=[0 if physical(s)[0]==physical(s)[1] and tuple(s[2:])==ZERO else -1
              for s in states]
    changed=True
    while changed:
        changed=False
        new=distance.copy()
        for i,row in enumerate(adjacency):
            candidates=[distance[j]+1 for t,u,j in row if distance[j]>=0]
            if candidates:
                best=min(candidates)
                if new[i]<0 or best<new[i]:
                    new[i]=best
                    changed=True
        distance=new
    return states,adjacency,distance,initial_count,predecessor


def verify_complete(graph):
    states,adj,distance,initial_count,_=graph
    if len(states)!=len(set(states)) or len(adj)!=len(states) or len(distance)!=len(states):
        raise ValueError('malformed graph dimensions or duplicate states')
    if states[:initial_count]!=initial_states():
        raise ValueError('a genuine initial overlap was omitted or altered')
    index={s:i for i,s in enumerate(states)}
    for i,state in enumerate(states):
        if not overlaps(physical(state)):
            raise ValueError('non-overlap admitted')
        expected=[]
        for t,u,target in children(state):
            if target not in index:
                raise ValueError('actual overlapping child outside supplied graph')
            expected.append((t,u,index[target]))
        if tuple(expected)!=tuple(adj[i]):
            raise ValueError('ordered child occurrence omitted, duplicated or altered')
        goal=physical(state)[0]==physical(state)[1] and tuple(state[2:])==ZERO
        if (distance[i]==0)!=goal or distance[i]<0:
            raise ValueError('coincidence distance misclassified or unproductive state')
        if not goal:
            if not any(distance[j]==distance[i]-1 for t,u,j in adj[i]):
                raise ValueError('no decreasing actual occurrence witness')
            best=1+min(distance[j] for t,u,j in adj[i])
            if distance[i]!=best:
                raise ValueError('claimed minimum distance is not a shortest distance')
    return True


def quotient(graph):
    states,adj,distance,_,_=graph
    types={physical(s) for s in states}
    output={}
    for x,y,delta in sorted(types):
        row=[]
        for t,z in enumerate(SIGMA[x]):
            for u,w in enumerate(SIGMA[y]):
                d=add(m_times(delta),subtract(DIGIT[x][t],DIGIT[y][u]))
                child=(int(z),int(w),d)
                if overlaps(child):
                    assert child in types
                    row.append((t,u,child))
        output[(x,y,delta)]=tuple(row)
    # Every quotient path lifts at every decorated state over its source.
    by_type={}
    for i,state in enumerate(states):
        kind=physical(state)
        lifted=tuple((t,u,physical(states[j])) for t,u,j in adj[i])
        assert lifted==output[kind]
        by_type.setdefault(kind,set()).add(distance[i])
    assert all(len(values)==1 for values in by_type.values())
    return output, {kind:next(iter(v)) for kind,v in by_type.items()}


def receipt(graph):
    states,adj,distance,initial_count,_=graph
    q,qd=quotient(graph)
    payload={'states':states,'edges':adj,'distance':distance,'initial_count':initial_count}
    digest=hashlib.sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()
    return {'initial_decorated_overlaps':initial_count,
            'decorated_states':len(states),'occurrence_edges':sum(map(len,adj)),
            'coincidence_states':distance.count(0),'maximum_minimum_depth':max(distance),
            'distance_histogram':dict(sorted(Counter(distance).items())),
            'physical_types':len(q),'physical_occurrence_edges':sum(map(len,q.values())),
            'physical_distance_histogram':dict(sorted(Counter(qd.values()).items())),
            'largest_actual_register_coordinate':max(max(map(abs,s[2:])) for s in states),
            'graph_sha256':digest}


def test_root_signs_and_strict_overlap_boundaries():
    assert polynomial(Fraction(2839286,10**6))<0<polynomial(Fraction(2839287,10**6))
    for x,y in product(range(3),repeat=2):
        assert overlaps((x,y,ZERO))
        assert not overlaps((x,y,E[y]))  # endpoint contact only
        assert not overlaps((x,y,tuple(-v for v in E[x])))
        assert perron_sign(E[x])==1
    assert perron_sign(ZERO)==0
    with pytest.raises(ValueError): perron_sign((1001,0,0))


def test_full_decorated_saturation_and_exact_distance_distribution():
    g=build();assert verify_complete(g)
    r=receipt(g)
    assert (r['initial_decorated_overlaps'],r['decorated_states'],r['occurrence_edges'])==(118,1134,3106)
    assert r['coincidence_states']==120
    assert r['maximum_minimum_depth']==5
    assert r['distance_histogram']=={0:120,1:90,2:278,3:286,4:256,5:104}
    assert r['largest_actual_register_coordinate']==2


def test_physical_quotient_is_occurrence_complete_and_path_lifting():
    q,d=quotient(build())
    assert len(q)==87 and sum(map(len,q.values()))==230
    assert Counter(d.values())=={0:3,1:6,2:16,3:28,4:26,5:8}
    # Small register size is an OUTCOME of full saturation, not a pruning rule.


def test_every_registered_state_has_a_real_root_occurrence_and_witness():
    g=build();states,adj,dist,n0,parents=g
    actual=[]
    for i,state in enumerate(states):
        if i<n0:
            top,bottom,*_=state;j,d=STATES[top];k,e=STATES[bottom]
            a,b=RETURNS[j][:d],RETURNS[k][:e]
            x,y=RETURNS[j][d],RETURNS[k][e]
        else:
            parent,t,u=parents[i]
            pa,pb,px,py=actual[parent]
            a=apply(SIGMA,pa)+SIGMA[int(px)][:t]
            b=apply(SIGMA,pb)+SIGMA[int(py)][:u]
            x,y=SIGMA[int(px)][t],SIGMA[int(py)][u]
        actual.append((a,b,x,y))
        assert subtract(parikh(a),parikh(b))==tuple(state[2:])
        assert (int(x),int(y))==physical(state)[:2]
        current=i
        # Replay literal descendants INSIDE the two next-letter images.
        # Transport the already-certified exterior mass by M^n instead of
        # materializing million-character exterior prefixes unnecessarily.
        exterior=tuple(state[2:]);pa=pb=""
        for step in range(dist[i]):
            t,u,nxt=next(e for e in adj[current] if dist[e[2]]==dist[current]-1)
            pa,pb=apply(SIGMA,pa)+SIGMA[int(x)][:t],apply(SIGMA,pb)+SIGMA[int(y)][:u]
            x,y=SIGMA[int(x)][t],SIGMA[int(y)][u]
            exterior=m_times(exterior)
            current=nxt
        assert add(exterior,subtract(parikh(pa),parikh(pb)))==ZERO and x==y


def test_incomplete_occurrence_tables_or_false_distances_are_rejected():
    states,adj,d,n0,parents=build()
    truncated=list(adj);truncated[0]=truncated[0][:-1]
    with pytest.raises(ValueError): verify_complete((states,truncated,d,n0,parents))
    bad=list(d);bad[next(i for i,v in enumerate(d) if v==5)]=4
    with pytest.raises(ValueError): verify_complete((states,adj,bad,n0,parents))


def test_caps_are_failure_not_a_finite_closure_receipt():
    for cap in (0,1,117,1133,2049):
        with pytest.raises(ValueError): build(cap)


def test_unrestricted_two_track_product_is_not_bounded_even_from_zero():
    # Start at the same first letter 0. Choose t=1,u=0 once: delta=e0.
    # Thereafter choose inherited cuts on both tracks: delta grows as M^n e0.
    d=E[0];sizes=[]
    for _ in range(12):
        sizes.append(sum(d));d=m_times(d)
    assert all(a<b for a,b in zip(sizes,sizes[1:]))
    assert max(d)>1000
    # The first divergent pair already has only endpoint contact, not an
    # actual positive-length overlap, so it is correctly excluded here.
    assert not overlaps((1,0,E[0]))


def compare_native(log):
    got_states=[];got_rows={};got_dist=[]
    for line in Path(log).read_text().splitlines():
        fields=line.split()
        if not fields:continue
        if fields[0]=='RCO_STATE':
            values=list(map(int,fields[1:]));i,*state=values
            assert i==len(got_states);got_states.append(tuple(state))
        elif fields[0]=='RCO_EDGE':
            i,t,u,target=map(int,fields[1:]);got_rows.setdefault(i,[]).append((t,u,target))
        elif fields[0]=='RCO_DIST':
            i,d=map(int,fields[1:]);assert i==len(got_dist);got_dist.append(d)
    expected=build()
    assert got_states==expected[0], 'native full ordered state table differs'
    assert [tuple(got_rows.get(i,[])) for i in range(len(got_states))]==expected[1], 'native complete occurrence table differs'
    assert got_dist==expected[2], 'native exact distances differ'
    print('Native/oracle full state, occurrence and distance parity passed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--native-log');parser.add_argument('--receipt')
    args=parser.parse_args()
    g=build();verify_complete(g)
    if args.native_log:compare_native(args.native_log)
    result=receipt(g)
    if args.receipt:Path(args.receipt).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
