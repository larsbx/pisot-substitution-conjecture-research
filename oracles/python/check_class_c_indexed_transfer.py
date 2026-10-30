#!/usr/bin/env python3
"""Independent literal-occurrence oracle for the formal indexed A_K family."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT / 'evidence/class-c-residual-domain-2026-10-29'))
from exact_oracle import ExactClassC, add, sub


def representatives(d):
    return range(d+1) if d <= 9 else (0,1,4,d-2,d-1,d)


def form(o,I,U,R):
    A,B,Y = U,R-2*U,I+U-2*R
    return tuple(A*a+B*b+Y*y for a,b,y in zip(*o.lengths))


def parent(o,K):
    return 0,1,form(o,-1,3,-K)


def formulas(o,K):
    d = o.d
    wall = int(K == d)
    out = {(0,2,form(o,-d+5+j,-K,K-1)) for j in range(d-5,d-1+wall)}
    out |= {(2,2,form(o,-d+2+ell,-K-1,K-3)) for ell in range(d-2+wall,d+wall)}
    out |= {(2,0,form(o,d-3-i,-K-1,K-3)) for i in range(d-4-wall,d)}
    return out


def read_dump(path):
    parents,children = {},defaultdict(set)
    summary = None
    for line in Path(path).read_text().splitlines():
        row = line.split()
        if row[0] == 'INDEXED_TRANSFER_INTERFACES_PASS':
            assert summary is None
            summary = list(map(int,row[1:]))
            continue
        assert row[0] in ('P','C') and len(row) == 8
        d,K,A,B,*w = map(int,row[1:])
        key,state = (d,K),(A,B,tuple(w))
        if row[0] == 'P':
            assert key not in parents, 'duplicate parent'
            parents[key] = state
        else:
            assert state not in children[key], 'duplicate child'
            children[key].add(state)
    assert summary == [58,357,3686]
    keys = {(d,K) for d in range(7,65) for K in representatives(d)}
    assert set(parents) == set(children) == keys
    assert sum(map(len,children.values())) == 3686
    return parents,dict(children)


def check(dump=None):
    parents,export = read_dump(dump) if dump else ({},{})
    pairs = duplicates = interfaces = 0
    for d in range(7,65):
        o = ExactClassC(d,1,2*d-5)
        Q = parent(o,4)
        q_children = set(o.children(Q))
        for K in representatives(d):
            pp = parent(o,K)
            assert o.overlaps(pp)
            raw = list(o.children(pp))
            actual = set(raw)
            assert actual == formulas(o,K), ('written indexed formula',d,K)
            assert len(actual) == (12 if K == d else 10)
            assert len(raw) == 2*d+1
            delta = o.beta(sub(pp[2],Q[2]))
            shifted = {(A,B,add(w,delta)) for A,B,w in q_children}
            if K < d:
                assert actual == shifted
            else:
                assert actual != shifted and len(shifted) == 10
            if dump:
                assert parents[d,K] == pp
                assert export[d,K] == actual, ('full export mismatch',d,K)
            pairs += len(raw)
            duplicates += len(raw)-len(actual)
            interfaces += 1
        for K in (d-1,d):
            assert o.sign(form(o,1,-K-1,K-3)) == (-1 if K == d else 1)
    assert interfaces == 357 and pairs == 25213 and duplicates == 21527
    result = dict(members=58,interfaces=357,distinct_children=3686,
                  accepted_occurrence_pairs=pairs,duplicate_occurrences=duplicates,
                  interior_stars=299,boundary_stars=58,
                  scope='finite replay of formal indexed local family; no closure or BH verdict')
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
    print('INDEXED_TRANSFER_LITERAL_EXACT_ORACLE_PASS')
    if args.check_receipt:
        print('INDEXED_TRANSFER_RECEIPT_PASS')


if __name__ == '__main__':
    main()
