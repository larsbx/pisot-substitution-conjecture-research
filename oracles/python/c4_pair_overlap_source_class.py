"""Complete 18-source extension of #496, preserving each fixed-point period.

No SC witness is an input. All edges and all positive integer inequalities
are checked. The compact set equations and Haar argument remain written
proof dependencies, not conclusions of this finite arithmetic alone.
"""
from dataclasses import dataclass
from functools import lru_cache
from fractions import Fraction as Q
from itertools import permutations, product, zip_longest
from math import lcm
from pathlib import Path
import argparse
import hashlib
import json
import c4_pair_overlap_graph as base

SCHEMA = 'c4-pair-overlap-source-class-v1'
SOURCES = tuple(product(('1',), tuple(''.join(w) for w in permutations('012')),
                        ('001', '010', '100')))
RADII = (24, 12)
AREA = 1152
STATE_CAP = 20000
COORD_CAP = 64
WEIGHT_CAP = 1000000
require = base.require
InvalidCertificate = base.InvalidCertificate


def source(index):
    require(type(index) is int and 0 <= index < 18, 'unsupported source index')
    return SOURCES[index]


def fixed_point_data(index):
    sigma = source(index)
    seen, c = [], 0
    while c not in seen:
        seen.append(c)
        c = int(sigma[c][0])
    period = len(seen) - seen.index(c)
    step = 2 if period in (1, 2) else 3
    require(step % period == 0, 'step is not a fixed-point power')
    return c, period, step


def rate(index):
    step = fixed_point_data(index)[2]
    return (102, 20, Q(103, 20)) if step == 2 else (233, 20, Q(292, 25))


def literal_digits(index, depth):
    sigma = source(index)
    require(type(depth) is int and 0 <= depth <= 12, 'literal depth budget')
    words = ('0', '1', '2')
    for _ in range(depth):
        words = tuple(''.join(sigma[int(c)] for c in w) for w in words)
        require(all(len(w) <= 100000 for w in words), 'word budget; inconclusive')
    for d, word in enumerate(words):
        prefix = [0, 0, 0]
        for position, c in enumerate(word):
            yield d, position, int(c), tuple(prefix)
            prefix[int(c)] += 1


@lru_cache(maxsize=18)
def certify_chart(index):
    sigma = source(index)
    require(tuple(tuple(w.count(str(i)) for w in sigma) for i in range(3)) == base.M,
            'incidence mismatch')
    lo, _ = base.root_bracket()
    require(lo**2 > Q(103, 20) and lo**3 > Q(292, 25), 'spectral lower bound')
    a = base.interval((Q(0), Q(3, 2), Q(-1, 2)))
    b = base.interval((Q(-1), Q(-1, 2), Q(1, 2)))
    for endpoints, exact in zip(base.COEFFICIENTS, (a, b)):
        require(Q(endpoints[0], base.GRID) <= exact[0] <= exact[1] <= Q(endpoints[1], base.GRID),
                'coarse projection interval')
    block = base.stable_block()
    bound = ((Q(473, 1000), Q(390, 1000)), (Q(147, 1000), Q(344, 1000)))
    for i in range(2):
        for j in range(2):
            require(max(map(abs, base.interval(block[i][j]))) <= bound[i][j], 'block entry')
    maxima, count = [0, 0], 0
    for _, _, _, p in literal_digits(index, 12):
        count += 1
        for i, coordinate in enumerate((0, 2)):
            maxima[i] = max(maxima[i], *(abs(base.GRID*p[coordinate]-e*p[1])
                                        for e in base.COEFFICIENTS[i]))
    digits = (Q(13, 2), Q(4))
    require(count == 55583, 'incomplete block occurrence list')
    for i in range(2):
        require(Q(maxima[i], base.GRID) <= digits[i], 'digit enclosure')
        linear = sum(bound[i][j]*RADII[j] for j in range(2))
        require(linear < RADII[i] and linear+digits[i] <= RADII[i], 'noninvariant common box')
    first, period, step = fixed_point_data(index)
    return {'literal_digits': count, 'digit_maximum_numerators': maxima,
            'digit_denominator': base.GRID, 'radii': list(RADII),
            'fixed_letter': first, 'fixed_point_period': period, 'graph_step': step}


def outside(z):
    for i, coord in enumerate((0, 2)):
        endpoints = [base.GRID*z[coord]-a*z[1] for a in base.COEFFICIENTS[i]]
        limit = 2*RADII[i]*base.GRID
        if min(endpoints) > limit or max(endpoints) < -limit:
            return True
    return False


@dataclass
class ClassGraph:
    source_index: int
    step: int
    states: list
    rows: list
    residue_rejections: int
    box_rejections: int


def build_graph(index, *, step=None, state_cap=STATE_CAP):
    chart = certify_chart(index)
    actual_step = chart['graph_step']
    require(step is None or (type(step) is int and step == actual_step), "fixed-point step outside the period-aware route's premise; see the common-attractor route")
    step = actual_step
    require(type(state_cap) is int and 3 <= state_cap <= STATE_CAP, 'state budget domain')
    digits = [[] for _ in range(3)]
    for d, pos, c, p in literal_digits(index, step):
        digits[c].append((d, pos, p))
    inverse = base.inverse(base.power(base.M, step))
    denominator = lcm(*(x.denominator for row in inverse for x in row))
    numerator = tuple(tuple(int(denominator*x) for x in row) for row in inverse)
    require(denominator > 0 and 2**step % denominator == 0, 'inverse denominator')
    states = [(0,1,0,0,0), (0,2,0,0,0), (1,2,0,0,0)]
    ids, rows = {s:i for i,s in enumerate(states)}, []
    residue_rejections = box_rejections = 0
    for c, d, x, y, z in states:
        targets = []
        for a, _, p in digits[c]:
            for b, _, q in digits[d]:
                dx, dy, dz = x+q[0]-p[0], y+q[1]-p[1], z+q[2]-p[2]
                candidate = tuple(r[0]*dx+r[1]*dy+r[2]*dz for r in numerator)
                if any(v % denominator for v in candidate):
                    residue_rejections += 1
                    continue
                translated = tuple(v//denominator for v in candidate)
                if outside(translated):
                    box_rejections += 1
                    continue
                require(max(map(abs,translated)) <= COORD_CAP, 'coordinate budget; inconclusive')
                child = base.canonical(a,b,translated)
                if child not in ids:
                    require(len(states) < state_cap, 'state budget; inconclusive')
                    ids[child] = len(states)
                    states.append(child)
                targets.append(ids[child])
        rows.append(targets)
    return ClassGraph(index,step,states,rows,residue_rejections,box_rejections)


def components_sink_first(rows):
    """Iterative Kosaraju. This accelerates construction, never acceptance."""
    n = len(rows)
    reverse = [[] for _ in rows]
    for i,row in enumerate(rows):
        for j in row:
            reverse[j].append(i)
    seen, order = set(), []
    for root in range(n):
        if root in seen: continue
        seen.add(root)
        stack = [(root, iter(rows[root]))]
        while stack:
            v,it = stack[-1]
            w = next(it,None)
            if w is None:
                order.append(v); stack.pop()
            elif w not in seen:
                seen.add(w); stack.append((w,iter(rows[w])))
    seen, components = set(), []
    for root in reversed(order):
        if root in seen: continue
        seen.add(root); pending=[root]; component=[]
        while pending:
            v=pending.pop();component.append(v)
            for w in reverse[v]:
                if w not in seen: seen.add(w);pending.append(w)
        components.append(sorted(component))
    return list(reversed(components))


def validate_weights(graph, weights):
    numerator,denominator,lower=rate(graph.source_index)
    require(graph.step == fixed_point_data(graph.source_index)[2], 'graph step mismatch')
    require(Q(numerator,denominator) < lower, 'missing strict margin')
    require(len(weights) == len(graph.states) == len(graph.rows), 'weight dimensions')
    require(all(type(w) is int and 0 < w <= WEIGHT_CAP for w in weights), 'positive bounded weights')
    minimum=10**18
    for i,row in enumerate(graph.rows):
        require(all(type(j) is int and 0 <= j < len(weights) for j in row), 'target index')
        gap=numerator*weights[i]-denominator*sum(weights[j] for j in row)
        require(gap>=0, 'false subinvariance')
        minimum=min(minimum,gap)
    return minimum


def construct_weights(graph, iteration_cap=4000):
    require(type(iteration_cap) is int and 1<=iteration_cap<=4000,'iteration budget')
    num,den,_=rate(graph.source_index)
    weights=[1]*len(graph.rows)
    components=components_sink_first(graph.rows)
    done=set(); maximum_iterations=0
    for comp in components:
        local=set(comp)
        require(all(j in local or j in done for i in comp for j in graph.rows[i]), 'component order')
        for iteration in range(1,iteration_cap+1):
            values=[1+(den*sum(weights[j] for j in graph.rows[i])+num-1)//num for i in comp]
            require(max(values)<=WEIGHT_CAP,'weight budget; inconclusive')
            if all(weights[i]==v for i,v in zip(comp,values)):
                maximum_iterations=max(maximum_iterations,iteration);break
            for i,v in zip(comp,values):weights[i]=v
        else: raise InvalidCertificate('iteration budget; inconclusive')
        done.update(comp)
    gap=validate_weights(graph,weights)
    stats={'components':len(components),'largest_component':max(map(len,components)),
           'maximum_local_iterations':maximum_iterations}
    return weights,stats,gap


def graph_lines(graph, weights):
    f=graph.source_index
    num,den,_=rate(f)
    yield f'graph {f} {graph.step} {len(graph.states)} {sum(map(len,graph.rows))} {graph.residue_rejections} {graph.box_rejections} {num} {den}'
    for i,(state,row,w) in enumerate(zip(graph.states,graph.rows,weights)):
        yield 'node '+' '.join(map(str,(f,i,*state,w)))
        yield 'row '+' '.join(map(str,(f,i,len(row),*row)))


def verify_supplied_graph(index, states, rows, weights):
    actual=build_graph(index)
    require(actual.states==states and actual.rows==rows,'incomplete or relabelled occurrence graph')
    validate_weights(actual,weights)
    return actual


@lru_cache(maxsize=18)
def reference(index):
    graph=build_graph(index)
    weights,stats,gap=construct_weights(graph)
    return graph,weights,stats,gap


def summary(index):
    graph,w,stats,gap=reference(index)
    num,den,lower=rate(index); ratio=Q(num,den)/lower
    require(all(AREA*x*ratio**8192<Q(1,10) for x in w[:3]),'rational upper-bound check')
    digest=hashlib.sha256()
    for line in graph_lines(graph,w):digest.update((line+'\n').encode())
    return {'source_index':index,'sigma':list(source(index)),**certify_chart(index),
            'states':len(graph.states),'occurrence_edges':sum(map(len,graph.rows)),
            'residue_rejections':graph.residue_rejections,'box_rejections':graph.box_rejections,
            'root_weights':w[:3],'maximum_weight':max(w),'minimum_weight':min(w),
            'minimum_integer_gap':gap,'rate':str(Q(num,den)), 'beta_power_lower':str(lower),
            'ratio_upper':str(ratio),'all_roots_below_one_tenth_at_8192_blocks':True,
            'zero_offset_diagonal_states':sum(s[0]==s[1] and s[2:]==(0,0,0) for s in graph.states),
            'canonical_graph_sha256':digest.hexdigest(),'construction':stats}


def receipt():
    return {'schema':SCHEMA,'source_count':18,'scope':'all 18 source orders with the fixed determinant-two incidence; not general PSC',
            'base_pr_head':'d5833e3ad2908cec847002b797d12c73d48045a4',
            'area_bound':AREA,'certificates':[summary(i) for i in range(18)]}


def verify_native(path):
    path=Path(path)
    require(path.stat().st_size<=60_000_000,'native packet budget')
    with path.open() as f:
        require(f.readline().rstrip('\n')=='schema '+SCHEMA,'native schema')
        def expected():
            for i in range(18):
                g,w,_,_=reference(i)
                yield from graph_lines(g,w)
        for actual,want in zip_longest(f,expected()):
            require(actual is not None and want is not None and actual.rstrip('\n')==want,'native complete graph mismatch')
    return receipt()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native',type=Path)
    parser.add_argument('--emit-packet',action='store_true')
    args=parser.parse_args()
    if args.native:out=verify_native(args.native)
    elif args.emit_packet:
        print('schema '+SCHEMA)
        for i in range(18):
            graph,w,_,_=reference(i)
            for line in graph_lines(graph,w):print(line)
        return
    else:out=receipt()
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()
