"""Independent SCC obstruction oracle for authenticated paired-overlap graphs.

Canonical implementation: kernel/psc/c4_overlap_scc_obstruction.mojo.
The pre-implementation literature gate is recorded in docs/.  This oracle
does not consume the earlier positive weight certificates.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from collections import Counter
from math import isqrt
from itertools import zip_longest
from io import StringIO
import argparse
import hashlib
import json
from pathlib import Path

import c4_pair_overlap_new_incidence as source

PRIMES = (101,103,107)
BLOCK_BUDGET = 768
G = (-4,5,-7,1)
SCHEMA = 'c4-overlap-scc-obstruction-v1'
InvalidCertificate = source.InvalidCertificate
require = source.require


def validate_rows(rows):
    require(type(rows) is list and 0 < len(rows) <= 20000, 'bounded nonempty graph')
    require(all(type(row) is list and len(row) <= 81 and
                all(type(j) is int and 0 <= j < len(rows) for j in row) for row in rows),
            'bounded integer targets before graph traversal')
    require(sum(map(len,rows)) <= 2000000, 'edge budget exhausted; inconclusive')


def components(rows):
    """Independent iterative Kosaraju; canonicalized independently of DFS order."""
    validate_rows(rows)
    reverse = [[] for _ in rows]
    for i,row in enumerate(rows):
        for j in row:
            reverse[j].append(i)
    seen, finish = set(), []
    for root in range(len(rows)):
        if root in seen:
            continue
        seen.add(root)
        stack = [(root,0)]
        while stack:
            vertex,position = stack[-1]
            if position == len(rows[vertex]):
                finish.append(vertex)
                stack.pop()
            else:
                target = rows[vertex][position]
                stack[-1] = (vertex,position+1)
                if target not in seen:
                    seen.add(target)
                    stack.append((target,0))
    seen, out = set(), []
    for root in reversed(finish):
        if root in seen:
            continue
        seen.add(root)
        todo, block = [root], []
        while todo:
            vertex = todo.pop()
            block.append(vertex)
            for target in reverse[vertex]:
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        out.append(tuple(sorted(block)))
    require(len(out)**2<=20000000, 'condensation scan budget exhausted; inconclusive')
    return tuple(sorted(out,key=lambda block:block[0]))


def authenticate_partition(rows, supplied):
    expected = components(rows)
    require(tuple(tuple(c) for c in supplied) == expected, 'complete canonical SCC partition mismatch')
    return expected


def condensation(rows, blocks):
    owner = {vertex:i for i,block in enumerate(blocks) for vertex in block}
    require(len(owner) == len(rows), 'component inventory must cover every vertex')
    return tuple(tuple(sorted({owner[j] for i in block for j in rows[i] if owner[j] != k}))
                 for k,block in enumerate(blocks))


def block_matrix(rows, block, cap=BLOCK_BUDGET):
    require(type(cap) is int and 1 <= cap <= BLOCK_BUDGET, 'matrix budget must be supported')
    require(len(block) <= cap, 'matrix size budget exhausted; inconclusive')
    local = {v:i for i,v in enumerate(block)}
    require(len(local) == len(block) and len(block)>0, 'distinct nonempty block')
    matrix=[]
    for v in block:
        counts=Counter(rows[v])
        matrix.append([counts[t] for t in block])
    return matrix


def imatmul(left,right):
    # Integer polynomial construction precedes reduction; zero entries skipped.
    n=len(left)
    out=[[0]*n for _ in range(n)]
    for i,row in enumerate(left):
        for k,value in enumerate(row):
            if value:
                for j,other in enumerate(right[k]):
                    if other:
                        out[i][j]+=value*other
    return out


def validate_integer_matrix(matrix,nonnegative=False):
    require(type(matrix) in (list,tuple) and 0<len(matrix)<=BLOCK_BUDGET,
            'bounded nonempty square integer matrix')
    require(all(type(row) in (list,tuple) and len(row)==len(matrix) and
                all(type(value) is int and (not nonnegative or value>=0) for value in row)
                for row in matrix), 'square exact integer matrix required')


def polynomial_matrix(matrix, polynomial=G):
    validate_integer_matrix(matrix)
    require(type(polynomial) in (list,tuple) and len(polynomial)>0 and
            all(type(value) is int for value in polynomial), 'nonempty exact integer polynomial')
    n=len(matrix)
    require(n>0 and all(len(row)==n for row in matrix), 'square polynomial matrix')
    identity=[[int(i==j) for j in range(n)] for i in range(n)]
    out=[[polynomial[0]*int(i==j) for j in range(n)] for i in range(n)]
    term=identity
    # Direct powers, independent of the native Horner construction.
    for coefficient in polynomial[1:]:
        term=imatmul(term,matrix)
        for i in range(n):
            for j in range(n):
                out[i][j]+=coefficient*term[i][j]
    return out


def modular_rank_det(matrix,prime):
    validate_integer_matrix(matrix)
    require(type(prime) is int and 2<=prime<2**31 and all(prime%d for d in range(2,isqrt(prime)+1)),
            'prime modulus required')
    n=len(matrix)
    require(n>0 and all(len(row)==n for row in matrix), 'square rank matrix')
    # Eliminate columns of the original matrix by row operations on its
    # transpose. Rank and determinant are unchanged by transposition.
    rows=[[matrix[j][i]%prime for j in range(n)] for i in range(n)]
    rank,det=0,1
    for col in range(n):
        pivot=next((i for i in range(rank,n) if rows[i][col]),None)
        if pivot is None:
            continue
        if pivot!=rank:
            rows[pivot],rows[rank]=rows[rank],rows[pivot]
            det=-det
        value=rows[rank][col]
        det=det*value%prime
        inv=pow(value,-1,prime)
        for i in range(rank+1,n):
            factor=rows[i][col]*inv%prime
            if factor:
                rows[i]=[(x-factor*y)%prime for x,y in zip(rows[i],rows[rank])]
        rank+=1
    return rank,(det%prime if rank==n else 0)


@dataclass(frozen=True)
class Scale:
    kind: int
    polynomial: tuple
    lower: Q
    upper: Q


def make_scale(kind=1):
    require(type(kind) is int and kind in (0,1), 'unsupported authenticated scale')
    if kind==0:
        return Scale(0,(-2,1),Q(3,2),Q(5,2))
    source.certify_algebra()
    require(source.poly(source.root_bracket()[0])<0<source.poly(source.root_bracket()[1]),
            'authenticated beta interval')
    require(Q(63,10)<source.root_bracket()[0]**2<source.root_bracket()[1]**2<Q(32,5),
            'authenticated theta interval')
    # Irreducible cubic with no rational integer root; g(beta²)=0 below.
    require(all(sum(G[i]*Q(k)**i for i in range(4)) for k in (-4,-2,-1,1,2,4)),
            'minimal cubic rational-root exclusion')
    composed=[Q(0)]*7
    for i,value in enumerate(G):
        composed[2*i]=Q(value)
    require(not reduce_polynomial(composed,source.P), 'g(beta squared) must vanish')
    return Scale(1,G,Q(63,10),Q(32,5))


def authenticate_scale(scale):
    require(isinstance(scale,Scale) and scale==make_scale(scale.kind), 'scale metadata mismatch')


def trim(polynomial):
    out=list(map(Q,polynomial))
    while out and out[-1]==0:
        out.pop()
    return tuple(out)


def reduce_polynomial(polynomial,modulus):
    out=list(trim(polynomial))
    modulus=trim(modulus)
    require(len(modulus)>=2, 'nonconstant polynomial modulus')
    while len(out)>=len(modulus):
        factor=out[-1]/modulus[-1]
        offset=len(out)-len(modulus)
        for i,value in enumerate(modulus):
            out[i+offset]-=factor*value
        out=list(trim(out))
    return tuple(out)


def polynomial_interval(polynomial,scale):
    if scale.kind==0:
        value=sum(Q(coefficient)*2**i for i,coefficient in enumerate(polynomial))
        return value,value
    beta_lo,beta_hi=source.root_bracket()
    theta=(beta_lo**2,beta_hi**2)
    out=Q(0),Q(0)
    for value in reversed(polynomial):
        out=source.iadd(source.imul(out,theta),(Q(value),Q(value)))
    return out


def witness_status(matrix,scale,witness):
    """Validate evidence before assigning a spectral status; no bare labels."""
    authenticate_scale(scale)
    validate_integer_matrix(matrix,nonnegative=True)
    require(type(witness) is dict and type(witness.get('kind')) is int and
            witness['kind'] in (1,2,3), 'spectral witness kind')
    kind=witness['kind']
    weights=witness.get('weights')
    require(type(weights) in (list,tuple) and len(weights)==len(matrix), 'witness dimensions')
    if kind in (1,3):
        require(all(type(w) is int and 1<=w<=1000000 for w in weights), 'positive bounded rational weights')
        numerator,denominator=witness.get('rate',(0,0))
        require(type(numerator) is int and type(denominator) is int and numerator>0 and denominator>0,
                'positive exact witness rate')
        rate=Q(numerator,denominator)
        boundary=Q(2) if scale.kind==0 else (scale.lower if kind==1 else scale.upper)
        require(rate<boundary if kind==1 else rate>boundary, 'strict spectral comparison')
        for i,row in enumerate(matrix):
            value=sum(a*w for a,w in zip(row,weights))
            require(denominator*value<=numerator*weights[i] if kind==1 else
                    denominator*value>=numerator*weights[i], 'false spectral weight inequality')
    else:
        degree=len(scale.polynomial)-1
        require(all(type(p) in (tuple,list) and len(p)<=degree and
                    all(type(c) in (int,Q) for c in p) for p in weights), 'reduced exact field vector')
        require(all(polynomial_interval(p,scale)[0]>0 for p in weights), 'strictly positive critical vector')
        for i,row in enumerate(matrix):
            residual=[Q(0)]*(degree+1)
            for j,value in enumerate(row):
                for k,coefficient in enumerate(weights[j]):
                    residual[k]+=value*Q(coefficient)
            for k,coefficient in enumerate(weights[i]):
                residual[k+1]-=Q(coefficient)
            require(not reduce_polynomial(residual,scale.polynomial), 'false critical field eigenvector')
    return kind


def zero_closure(dag,exclusions,spectral):
    require(len(dag)==len(exclusions)==len(spectral), 'component flag dimensions')
    require(all(x in (0,1,2) for x in exclusions) and all(x in (0,1,2,3) for x in spectral),
            'supported authenticated component flags')
    # This helper consumes flags only from authenticated analysis below; it
    # is an algebraic rule kernel, not a certificate entry point.
    zero=[False]*len(dag)
    for i,kind in enumerate(spectral):
        if kind==3:
            zero[i]=True
        if kind in (2,3):
            for j in dag[i]:
                zero[j]=True
    changed=True
    while changed:
        changed=False
        for i,targets in enumerate(dag):
            if zero[i]:
                for j in targets:
                    if not zero[j]:
                        zero[j]=True
                        changed=True
            elif (exclusions[i]!=0 or spectral[i] in (1,3)) and all(zero[j] for j in targets):
                zero[i]=True
                changed=True
    return tuple(zero)


def analyze(rows,roots,scale=None,witnesses=None,block_budget=BLOCK_BUDGET,primes=PRIMES):
    scale=make_scale() if scale is None else scale
    authenticate_scale(scale)
    validate_rows(rows)
    require(type(block_budget) is int and 1<=block_budget<=BLOCK_BUDGET, 'supported block budget')
    require(tuple(primes)==PRIMES, 'supported deterministic prime budget')
    require(len(roots)>0 and all(type(r) is int and 0<=r<len(rows) for r in roots), 'valid declared roots')
    blocks=components(rows)
    dag=condensation(rows,blocks)
    witnesses={} if witnesses is None else witnesses
    require(type(witnesses) is dict and all(type(k) is int and 0<=k<len(blocks) for k in witnesses),
            'spectral witness component inventory')
    records=[]
    for index,block in enumerate(blocks):
        size=len(block)
        exclusion=0
        attempts=[]
        budget_refused=False
        spectral=0
        if size<len(scale.polynomial)-1:
            exclusion=1
        elif size>block_budget:
            budget_refused=True
        else:
            matrix=block_matrix(rows,block,block_budget)
            polynomial=polynomial_matrix(matrix,scale.polynomial)
            for prime in primes:
                rank,det=modular_rank_det(polynomial,prime)
                attempts.append((prime,rank,det))
                if rank==size:
                    exclusion=2
                    break
        if index in witnesses:
            require(size<=block_budget, 'spectral witness matrix budget exhausted; inconclusive')
            spectral=witness_status(block_matrix(rows,block,block_budget),scale,witnesses[index])
        require(not(exclusion and spectral==2), 'contradictory critical and excluded certificate')
        records.append({'members':block,'dag':dag[index],'exclusion':exclusion,'spectral':spectral,
                        'budget_refused':budget_refused,'attempts':tuple(attempts)})
    zeros=zero_closure(dag,[x['exclusion'] for x in records],[x['spectral'] for x in records])
    for i,record in enumerate(records):
        record['zero']=zeros[i]
    owner={v:i for i,block in enumerate(blocks) for v in block}
    return {'components':tuple(records),'zero_states':sum(len(blocks[i]) for i,z in enumerate(zeros) if z),
            'root_zero':tuple(zeros[owner[r]] for r in roots),
            'complete_zero_certificate':all(zeros)}


@lru_cache(maxsize=12)
def _reference_json(index):
    obj=graph(index)
    # Cache only immutable data. A public graph/report must not alias the
    # expected graph against which a later supplied certificate is checked.
    return json.dumps(analyze(obj.rows,(0,1,2)),sort_keys=True)


def reference(index):
    report=json.loads(_reference_json(index))
    report['root_zero']=tuple(report['root_zero'])
    for record in report['components']:
        record['members']=tuple(record['members'])
        record['dag']=tuple(record['dag'])
        record['attempts']=tuple(tuple(attempt) for attempt in record['attempts'])
    report['components']=tuple(report['components'])
    return graph(index),report


def require_zero_certificate(report):
    require(report['complete_zero_certificate'], 'unresolved components; inconclusive')


def authenticate_report(rows,roots,supplied,scale=None,witnesses=None,block_budget=BLOCK_BUDGET):
    expected=analyze(rows,roots,scale,witnesses,block_budget)
    require(supplied==expected, 'complete component certificate mismatch')
    return expected


def authenticate_source_report(index,states,rows,supplied):
    expected=graph(index)
    require(states==expected.states and rows==expected.rows, 'actual complete occurrence graph mismatch')
    report=authenticate_report(rows,(0,1,2),supplied)
    require_zero_certificate(report)
    return report


def graph_lines(index,obj,report):
    records=report['components']
    yield ' '.join(map(str,('graph',index,len(obj.states),sum(map(len,obj.rows)),
        obj.residue_rejections,obj.box_rejections,obj.carrier_rejections,len(records),
        max(len(r['members']) for r in records),sum(r['exclusion']==1 for r in records),
        sum(r['exclusion']==2 for r in records),sum(r['exclusion']==0 for r in records),
        report['zero_states'],*(int(z) for z in report['root_zero']))))
    for vertex,(state,row) in enumerate(zip(obj.states,obj.rows)):
        yield ' '.join(map(str,('node',index,vertex,*state)))
        yield ' '.join(map(str,('row',index,vertex,len(row),*row)))
    for cid,record in enumerate(records):
        yield ' '.join(map(str,('component',index,cid,len(record['members']),record['exclusion'],
            record['spectral'],int(record['zero']),int(record['budget_refused']),len(record['attempts']))))
        yield ' '.join(map(str,('members',index,cid,len(record['members']),*record['members'])))
        yield ' '.join(map(str,('dag',index,cid,len(record['dag']),*record['dag'])))
        for prime,rank,det in record['attempts']:
            yield ' '.join(map(str,('modtry',index,cid,prime,rank,det)))


def packet_lines():
    yield 'schema '+SCHEMA
    yield 'scale 1 -4 5 -7 1 63 10 32 5'
    yield 'budget 768 101 103 107'
    for index in range(12):
        obj,report=reference(index)
        require_zero_certificate(report)
        yield from graph_lines(index,obj,report)


def digest(lines):
    result=hashlib.sha256()
    for line in lines:
        result.update((line+'\n').encode('ascii'))
    return result.hexdigest()


def receipt():
    summaries=[]
    for index in range(12):
        obj,result=reference(index)
        require_zero_certificate(result)
        records=result['components']
        summaries.append({'source':index,'images':list(source.source_images(index)),
            'states':len(obj.states),'edges':sum(map(len,obj.rows)),'scc_count':len(records),
            'max_scc_size':max(len(r['members']) for r in records),
            'degree_exclusions':sum(r['exclusion']==1 for r in records),
            'modular_exclusions':sum(r['exclusion']==2 for r in records),
            'unresolved':sum(r['exclusion']==0 for r in records),
            'zero_states':result['zero_states'],'root_zero':list(result['root_zero']),
            'modular_blocks':[{'component':cid,'size':len(r['members']),
                               'attempts':[list(a) for a in r['attempts']]}
                              for cid,r in enumerate(records) if r['attempts']],
            'certificate_sha256':digest(graph_lines(index,obj,result))})
    return {'schema':SCHEMA,'canonical_language':'Mojo','source_count':12,'root_count':36,
        'minimal_polynomial':list(G),'scale_bracket':[[63,10],[32,5]],
        'matrix_budget':BLOCK_BUDGET,'prime_budget':list(PRIMES),
        'total_states':sum(r['states'] for r in summaries),'total_edges':sum(r['edges'] for r in summaries),
        'total_components':sum(r['scc_count'] for r in summaries),
        'degree_exclusions':sum(r['degree_exclusions'] for r in summaries),
        'modular_exclusions':sum(r['modular_exclusions'] for r in summaries),
        'unresolved':sum(r['unresolved'] for r in summaries),
        'zero_states':sum(r['zero_states'] for r in summaries),
        'previous_positive_weights_consumed':False,'sources':summaries,
        'normalized_packet_sha256':digest(packet_lines()),
        'scope':'complete source graphs, exact component exclusions, and zero propagation; the written measure equality supplies the geometric interpretation',
        'non_claims':['general C4','SC','BPA termination','geometric positivity from an eigencone','PDS','PSC']}


def verify_native(packet):
    require(isinstance(packet,str), 'native packet must be text')
    lines=(line.split() for line in StringIO(packet) if line.strip())
    require(next(lines,None)==['schema',SCHEMA], 'native packet preamble mismatch')
    expected=iter(packet_lines())
    next(expected)
    missing=object()
    for number,(actual,wanted) in enumerate(zip_longest(lines,expected,fillvalue=missing),2):
        require(actual is not missing and wanted is not missing, 'complete native record count mismatch')
        require(actual==wanted.split(), 'native component packet mismatch at record '+str(number))
    return receipt()


@lru_cache(maxsize=12)
def _graph_snapshot(index):
    obj=source.build_graph(index)
    return (tuple(tuple(state) for state in obj.states),
            tuple(tuple(row) for row in obj.rows),obj.residue_rejections,
            obj.box_rejections,obj.carrier_rejections)


def graph(index):
    states,rows,residue,box,carrier=_graph_snapshot(index)
    return source.Graph(index,list(states),[list(row) for row in rows],residue,box,carrier)


def inspect_components():
    for index in range(12):
        obj=graph(index)
        blocks=components(obj.rows)
        sizes=Counter(map(len,blocks))
        print(json.dumps({'index':index,'states':len(obj.states),'components':len(blocks),
                          'largest':max(sizes),'sizes':sorted(sizes.items())}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--inspect',action='store_true')
    parser.add_argument('--packet',action='store_true',help='oracle calibration packet, not native evidence')
    parser.add_argument('--native',type=Path)
    args=parser.parse_args()
    if args.inspect:
        inspect_components()
    elif args.packet:
        print('\n'.join(packet_lines()))
    elif args.native:
        print(json.dumps(verify_native(args.native.read_text()),indent=2))
    else:
        print(json.dumps(receipt(),indent=2))
