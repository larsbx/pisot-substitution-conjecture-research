#!/usr/bin/env python3
"""Independent literal-occurrence oracle for R/T/U and translation clipping."""
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


def value(o,A=0,B=0,Y=0):
    return tuple(A*a+B*b+Y*y for a,b,y in zip(*o.lengths))


def formulas(o):
    def st(A,B,X=0,C=0,Y=0): return A,B,value(o,X,C,Y)
    R,T,U = st(0,1,2,-3,-2),st(0,0,1,-6,8),st(0,2,-3,10,-8)
    tc = {st(0,2,-3,10,-t) for t in range(8,12)}
    tc |= {st(2,2,-4,10,-t) for t in (7,8)}
    tc |= {st(2,0,-4,10,-t) for t in range(7,11)}
    uc = {st(0,1,3,-6,2),st(0,2,3,-5,2),st(0,2,3,-5,3),st(2,1,3,-6,3)}
    return (R,T,U),({T},tc,uc)


def selected(o,parent,i,j):
    return (o.words[parent[0]][i],o.words[parent[1]][j],
            sub(add(o.beta(parent[2]),o.prefix[parent[1]][j]),o.prefix[parent[0]][i]))


def read_dump(path):
    parents,children = {},defaultdict(set)
    negative = None
    summary = control = None
    for line in Path(path).read_text().splitlines():
        row = line.split()
        if row[0] == 'R_TRANSFER_INTERFACES_PASS':
            assert summary is None
            summary = list(map(int,row[1:]))
        elif row[0] == 'R_TRANSLATION_NONCOMMUTATION_PASS':
            assert control is None
            control = list(map(int,row[1:]))
        elif row[0] == 'N':
            assert negative is None and len(row) == 6
            A,B,*w = map(int,row[1:])
            negative = A,B,tuple(w)
        else:
            assert row[0] in ('P','C') and len(row) == 8
            d,index,A,B,*w = map(int,row[1:])
            key,state = (d,index),(A,B,tuple(w))
            if row[0] == 'P':
                assert key not in parents, 'duplicate parent'
                parents[key] = state
            else:
                assert state not in children[key], 'duplicate child'
                children[key].add(state)
    assert summary == [58,174,870] and control == [6,4]
    assert negative is not None, 'missing negative control'
    keys = {(d,index) for d in range(7,65) for index in range(3)}
    assert set(parents) == set(children) == keys
    assert sum(map(len,children.values())) == 870
    return parents,dict(children),negative


def check(dump=None):
    parents,export,negative = read_dump(dump) if dump else ({},{},None)
    accepted = duplicates = 0
    for d in range(7,65):
        o = ExactClassC(d,1,2*d-5)
        pp,cc = formulas(o)
        R,T,U = pp
        X = (0,2,value(o,-4,11,-7))
        assert selected(o,X,o.p+1,0) == R
        assert selected(o,R,0,o.n+1) == T
        assert selected(o,T,0,d) == U
        for index,parent in enumerate(pp):
            assert o.overlaps(parent)
            raw = list(o.children(parent))
            actual = set(raw)
            assert actual == cc[index], ('full formula mismatch',d,index)
            assert len(raw) == (1 if index == 0 else 4*d-1 if index == 1 else 4)
            if dump:
                assert parents[d,index] == parent
                assert export[d,index] == actual, ('full export mismatch',d,index)
            accepted += len(raw)
            duplicates += len(raw)-len(actual)
        kappa = value(o,1,-1,-1)
        Q = (0,1,value(o,3,-10,10))
        assert {(A,B,add(w,kappa)) for A,B,w in o.children(Q)} == cc[1]
        delta = o.beta(kappa)
        translated = {(A,B,add(w,delta)) for A,B,w in o.children(X)}
        assert len(translated) == 6 and len(cc[2]) == 4 and cc[2] < translated
        witness = (0,2,value(o,3,-5,4))
        assert witness in translated and witness not in cc[2]
        assert not o.overlaps(witness)
        assert o.sign(sub(witness[2],o.lengths[0])) > 0
        if d == 7 and dump:
            assert negative in translated-cc[2] and not o.overlaps(negative)
    assert accepted == 8468 and duplicates == 7598
    result = dict(members=58,interfaces=174,distinct_children=870,
                  accepted_occurrence_pairs=accepted,duplicate_occurrences=duplicates,
                  translation_controls=58,translated_children=6,actual_U_children=4,
                  scope='finite replay of three uniform local stars and translation obstruction; no closure or BH verdict')
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
    print('R_TRANSFER_LITERAL_EXACT_ORACLE_PASS')
    if args.check_receipt:
        print('R_TRANSFER_RECEIPT_PASS')


if __name__ == '__main__':
    main()
