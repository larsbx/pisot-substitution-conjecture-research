#!/usr/bin/env python3
"""Independent literal-word full-set oracle for the ten boundary sources."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT / 'evidence/class-c-residual-domain-2026-10-29'))
from exact_oracle import ExactClassC


def source_parents(o):
    def v(A,B,Y):
        return tuple(A*a+B*b+Y*y for a,b,y in zip(*o.lengths))
    return ([(0,2,v(-4,11,-t)) for t in range(7,11)] +
            [(2,2,v(-5,11,-t)) for t in (6,7)] +
            [(2,0,v(-5,11,-t)) for t in range(6,10)])


def expected_counts(d):
    small = {7:(4,3,4),8:(6,5,6),9:(8,7,8)}
    X,Y,Z = small.get(d,(9,8,9))
    return [6,8,8,X,7,Y,6,8,8,Z]


def symbolic_children(o,index):
    """Independent transcription of the proof's fifteen explicit run windows."""
    d = o.d
    out = set()
    def state(A,B,I,U,R):
        # N+U*u+R*rho = U*a+(R-2U)*b+(N+U-2R).
        coeff = (U,R-2*U,I+U-2*R)
        w = tuple(sum(coeff[j]*o.lengths[j][i] for j in range(3)) for i in range(3))
        return A,B,w
    if index < 4:
        k = 3-index
        A,B,ra,rb = 0,1,3*d-5,d-4
        rows = [
            ('FR',(k*d-2,3,2*k-2),1-k*d,4-k*d),
            ('LR',((k-3)*d,2,2*k-4),(3-k)*d-1,(3-k)*d+2),
            ('RF',(k*d-7,2,2*k-5),k*d-7,k*d-5),
            ('RL',((k+1)*d-9,2,2*k-4),(k+1)*d-9,(k+1)*d-7),
            ('RR',(k*d-5,2,2*k-4),4-k*d,5-k*d),
        ]
        if k == 3:
            out.add(state(0,1,-2,2,1))
        if k == 0 and d in (7,8):
            out.add(state(0,1,d-6,3,-2))
    elif index < 6:
        k = 5-index
        A,B,ra,rb = 1,1,d-4,d-4
        rows = [
            ('FR',(k*d-3,1,2*k),2-k*d,4-k*d),
            ('LR',((k-1)*d-1,1,2*k-1),(1-k)*d,(1-k)*d+2),
            ('RF',(k*d-7,1,2*k-2),k*d-7,k*d-5),
            ('RL',((k+1)*d-9,1,2*k-1),(k+1)*d-9,(k+1)*d-7),
            ('RR',(k*d-5,1,2*k-1),4-k*d,5-k*d),
        ]
        if k == 0 and d in (7,8):
            out.add(state(1,1,d-7,1,0))
    else:
        k = 7-index
        A,B,ra,rb = 1,0,d-4,3*d-5
        rows = [
            ('FR',(k*d-2,2,2*k+1),1-k*d,3-k*d),
            ('LR',((k-1)*d,2,2*k),(1-k)*d-1,(1-k)*d+1),
            ('RF',(k*d-7,1,2*k-2),k*d-7,k*d-4),
            ('RL',((k+3)*d-9,2,2*k),(k+3)*d-9,(k+3)*d-6),
            ('RR',(k*d-4,2,2*k),3-k*d,4-k*d),
        ]
        if k == 1:
            out.add(state(1,0,-3,1,0))
        if k == -2 and d in (7,8):
            out.add(state(1,0,d-7,2,-3))
    for kind,(I,U,R),lo,hi in rows:
        if kind in ('FR','LR'):
            for j in range(max(0,lo),min(rb-1,hi)+1):
                out.add(state(A,2,I+j,U,R))
        elif kind in ('RF','RL'):
            for i in range(max(0,lo),min(ra-1,hi)+1):
                out.add(state(2,B,I-i,U,R))
        else:
            for ell in range(max(1-ra,lo),min(rb-1,hi)+1):
                out.add(state(2,2,I+ell,U,R))
    return out


def read_dump(path):
    parents, children, counts = {}, defaultdict(set), {}
    summary = None
    for line in Path(path).read_text().splitlines():
        row = line.split()
        if row[0] == 'BOUNDARY_TEN_FRONTIER_PASS':
            assert summary is None, 'duplicate summary'
            summary = list(map(int,row[1:]))
            continue
        if row[0] == 'COUNTS':
            assert len(row) == 4
            d,index,count = map(int,row[1:])
            assert (d,index) not in counts, 'duplicate counts'
            counts[d,index] = count
            continue
        assert row[0] in ('P','C') and len(row) == 8, 'malformed record'
        d,index,A,B,w0,w1,w2 = map(int,row[1:])
        key, state = (d,index),(A,B,(w0,w1,w2))
        if row[0] == 'P':
            assert key not in parents, 'duplicate parent'
            parents[key] = state
        else:
            assert state not in children[key], 'duplicate child'
            children[key].add(state)
    assert summary == [58,580,4439], 'false summary'
    keys = {(d,index) for d in range(7,65) for index in range(10)}
    assert set(parents) == set(children) == set(counts) == keys, 'missing interface'
    assert sum(map(len,children.values())) == 4439, 'missing child total'
    assert counts == {key:len(value) for key,value in children.items()}, 'child count mismatch'
    return parents,dict(children)


def check(dump=None):
    parents, exported = read_dump(dump) if dump else ({},{})
    accepted = duplicates = total = 0
    for d in range(7,65):
        o = ExactClassC(d,1,2*d-5)
        sources = source_parents(o)
        Q = (0,1,tuple(3*a-10*b+10*y for a,b,y in zip(*o.lengths)))
        assert len(set(sources)) == 10 and set(sources) == set(o.children(Q))
        for index,parent in enumerate(sources):
            assert o.overlaps(parent)
            raw = list(o.children(parent))
            actual = set(raw)
            assert actual == symbolic_children(o,index), ('written window table mismatch',d,index)
            assert len(actual) == expected_counts(d)[index], ('child count chamber',d,index)
            if dump:
                assert parents[d,index] == parent, ('parent mismatch',d,index)
                assert exported[d,index] == actual, ('full child set mismatch',d,index)
            accepted += len(raw)
            duplicates += len(raw)-len(actual)
            total += len(actual)
    assert total == 4439
    result = dict(members=58,interfaces=580,distinct_children=total,
                  accepted_occurrence_pairs=accepted,duplicate_occurrences=duplicates,
                  scope='finite replay of ten complete local stars; no closure or BH verdict')
    if dump:
        result['canonical_dump_sha256'] = hashlib.sha256(Path(dump).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mojo-dump',type=Path)
    parser.add_argument('--check-receipt',type=Path)
    args = parser.parse_args()
    if args.check_receipt and not args.mojo_dump:
        parser.error('--check-receipt requires --mojo-dump')
    result = check(args.mojo_dump)
    if args.check_receipt:
        assert result == json.loads(args.check_receipt.read_text()), 'receipt mismatch'
    print(json.dumps(result,sort_keys=True,indent=2))
    print('BOUNDARY_TEN_LITERAL_EXACT_ORACLE_PASS')
    if args.check_receipt:
        print('BOUNDARY_TEN_RECEIPT_PASS')


if __name__ == '__main__':
    main()
