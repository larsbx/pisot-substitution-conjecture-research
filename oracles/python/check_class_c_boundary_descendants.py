#!/usr/bin/env python3
"""Independent literal-word exact oracle for the two plus-boundary stars.

No window-search, frozen graph, Mojo code or floating arithmetic is imported.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT / 'evidence/class-c-residual-domain-2026-10-29'))
from exact_oracle import ExactClassC, ZERO, add, sub


def value(o, A=0, B=0, Y=0):
    return tuple(A*a+B*b+Y*y for a,b,y in zip(*o.lengths))


def expected(o):
    P = (0,2,value(o,1,1,-6))
    Q = (0,1,value(o,3,-10,10))
    targets = {(0,2,value(o,-4,11,-t)) for t in range(7,11)}
    targets |= {(2,2,value(o,-5,11,-t)) for t in (6,7)}
    targets |= {(2,0,value(o,-5,11,-t)) for t in range(6,10)}
    assert len(targets) == 10
    return (P,Q), ({Q},targets)


def occurrence(o, parent, i, j):
    return (o.words[parent[0]][i],o.words[parent[1]][j],
            sub(add(o.beta(parent[2]),o.prefix[parent[1]][j]),o.prefix[parent[0]][i]))


def read_dump(path):
    parents, children = {}, defaultdict(set)
    summary = None
    for line in Path(path).read_text().splitlines():
        row = line.split()
        if row[0] == 'BOUNDARY_DESCENDANT_INTERFACES_PASS':
            assert summary is None
            summary = list(map(int,row[1:]))
            continue
        assert row[0] in ('P','C') and len(row) == 8, ('malformed record',row)
        d,stage,A,B,w0,w1,w2 = map(int,row[1:])
        key, state = (d,stage),(A,B,(w0,w1,w2))
        if row[0] == 'P':
            assert key not in parents, ('duplicate parent',key)
            parents[key] = state
        else:
            assert state not in children[key], ('duplicate child',key,state)
            children[key].add(state)
    assert summary == [58,116,638]
    return parents, dict(children)


def check(dump=None):
    parents, child_export = read_dump(dump) if dump else ({},{})
    keys = {(d,s) for d in range(7,65) for s in (0,1)}
    if dump:
        assert set(parents) == set(child_export) == keys
    occurrences = duplicates = 0
    for d in range(7,65):
        o = ExactClassC(d,1,2*d-5)
        pp, cc = expected(o)
        P,Q = pp
        # Exact beta*(beta+1)*(beta-d)=2 in the cubic quotient.
        unit = o.lengths[2]
        b1 = o.beta(unit)
        b2 = o.beta(b1)
        b3 = o.beta(b2)
        assert tuple(x+(1-d)*y-d*z-2*w for x,y,z,w in zip(b3,b2,b1,unit)) == ZERO
        for A,B,Y,lo,hi in [(3,-10,10,-1,0),(-4,11,0,9,10),(-5,11,0,6,7)]:
            assert o.sign(value(o,A,B,Y-lo)) > 0
            assert o.sign(value(o,-A,-B,hi-Y)) > 0
        seed = (0,0,o.lengths[1])
        assert seed in o.seeds()
        assert occurrence(o,seed,o.p+1,d-5) == P and o.overlaps(P)
        assert occurrence(o,P,0,o.r+1) == Q and o.overlaps(Q)
        # Uniform first-layer obstruction, rebuilding from actual words.
        first = set(o.seeds())
        for s in o.seeds():
            first.update(o.children(s))
        assert P in first and Q not in first
        for stage in (0,1):
            raw = list(o.children(pp[stage]))
            actual = set(raw)
            assert actual == cc[stage], (d,stage,actual-cc[stage],cc[stage]-actual)
            assert len(raw) == (1 if stage == 0 else 2*d+1)
            # Deliberate omission must be detected by full-set equality.
            missing = set(cc[stage])
            missing.pop()
            assert actual != missing
            if dump:
                assert parents[d,stage] == pp[stage]
                assert child_export[d,stage] == actual
            occurrences += len(raw)
            duplicates += len(raw)-len(actual)
        # Witness every typed target by actual bounded word indices.
        for t in range(7,11):
            assert occurrence(o,Q,0,d+6-t) == (0,2,value(o,-4,11,-t))
        for t in (6,7):
            assert occurrence(o,Q,1,d+6-t) == (2,2,value(o,-5,11,-t))
        for t in range(6,10):
            assert occurrence(o,Q,d+t-9,o.n+1) == (2,0,value(o,-5,11,-t))
    assert occurrences == 4234 and duplicates == 3596
    result = dict(members=58,interfaces=116,distinct_children=638,
                  accepted_occurrence_pairs=occurrences,duplicate_occurrences=duplicates,
                  scope='finite replay of two uniform local stars; no closure or BH verdict')
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
    print('BOUNDARY_DESCENDANT_LITERAL_EXACT_ORACLE_PASS')
    if args.check_receipt:
        print('BOUNDARY_DESCENDANT_RECEIPT_PASS')


if __name__ == '__main__':
    main()
