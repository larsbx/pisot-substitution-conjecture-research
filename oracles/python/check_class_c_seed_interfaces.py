#!/usr/bin/env python3
"""Independent literal-word/Fraction oracle for the nine symbolic seed tables.

No frozen graph, symbolic cone code, Mojo window search, or floating arithmetic.
The optional dump argument cross-checks complete Mojo state sets, not counts.
"""
from collections import defaultdict
from pathlib import Path
import argparse
import json
import hashlib
from itertools import permutations
import sys

# Evidence packets are pinned verbatim; importing their oracle must not
# create unpinned __pycache__ files beside the archived source.
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'evidence/class-c-residual-domain-2026-10-29'))
from exact_oracle import ExactClassC, ZERO, add, sub


def representatives(d, eps):
    if d <= 9:
        return range(d + 5 if eps == 1 else d - 1)
    raw = ([0, 1, 2, (d+1)//2, (d+1)//2+1, d-1, d, d+1, d+2, d+4]
           if eps == 1 else [0, 1, (d-3)//2, (d-3)//2+1, d-2])
    return list(dict.fromkeys(raw))


def formulas(o, c):
    """Direct transcription of the mathematical tables, independent of Mojo."""
    n, d, e, r = o.n, o.d, o.eps, o.r
    a, b, unit = o.lengths
    def v(A=0, B=0, Y=0):
        return tuple(A*x+B*y+Y*z for x,y,z in zip(a,b,unit))
    f = 2 if e == 1 and c == 0 else 1
    t = 4 if e == 1 and c == 0 else (2 if e == 1 and c >= d+1 else 3)
    g = int(e == 1 and c < 2)
    m = ((5 if c == 0 else 4 if c <= (d+1)//2 else 3) if e == 1
         else (4 if c <= (d-3)//2 else 3))
    # Strict walls are tested independently with exact rational root isolation.
    for val, k in [(b,f), (v(0,2),t), (v(1,1),m), (v(1,-1),g)]:
        assert o.sign(sub(val,v(Y=k))) > 0
        assert o.sign(sub(v(Y=k+1),val)) > 0
    sets = []
    def state(A, B, w=ZERO): return (A,B,w)
    for A,B in [(0,1),(0,2),(1,2)]:
        if (A,B) == (1,2):
            aligned = {state(1,1),state(2,2)}
            aligned |= {state(2,1,v(Y=-k)) for k in range(f+1)}
        else:
            aligned = {state(0,1)}
            aligned |= {state(0,2,v(B=1,Y=j)) for j in range(g+1)}
            aligned |= {state(2,2,v(-1,1,k)) for k in (g,g+1)}
            if B == 1:
                aligned |= {state(2,0,v(-1,1,n-i)) for i in range(n-g-1,n+f+1)}
            else:
                aligned |= {state(2,1,v(-1,1,r-i)) for i in range(r-g-1,r+(1 if e==1 else 2))}
        if B == 1:
            positive = {state(2,0,v(B=1,Y=n-i)) for i in range(n+f,n+m+1)}
            positive |= {state(2,2,v(1,1,n-k)) for k in (n+m,n+m+1)}
            positive |= {state(0,2,v(1,1,j-d)) for j in range(d-m-1,d-f)}
            negative = {state(1,2,v(B=1,Y=j-d)) for j in range(d-f-1,d)}
            negative |= {state(2,2),state(0,0)}
        else:
            H = 2*d-e if A == 0 else d-e
            z = (0 if e==1 else 1) if A==0 else f
            positive = {state(2,0 if A==0 else 1,v(-1 if A==0 else 0,2 if A==0 else 1,r-i))
                        for i in range(r+z,r+t+1)}
            positive |= {state(2,2,v(0,2,r-k)) for k in (r+t,r+t+1)}
            positive |= {state(0,2,v(0,2,j-H)) for j in range(H-t-1,H-(1 if e==1 else 2)+1)}
            negative = {state(1,2,v(-1,2,j-H)) for j in range(H-(1 if e==1 else 2),H+g+1)}
            negative |= {state(2,2,v(-1,1,k-H)) for k in (H+g,H+g+1)}
            negative |= {state(2,0,v(-1,1,r-i)) for i in range(r-g-1,r)}
            negative |= {state(1,0,v(-1,1))}
        sets.extend([aligned,positive,negative])
    expected_counts = [
        2+g+2+(g+f+2), 2*m-2*f+4, f+3,
        1+g+1+2+(g+2 if e==1 else g+3),
        2*t+(4 if e==1 else 2), 8 if g else (6 if e==1 else 7),
        f+3, 2*t-f+(4 if e==1 else 3), 8 if g else (6 if e==1 else 7),
    ]
    assert list(map(len,sets)) == expected_counts, (d,e,c,list(map(len,sets)),expected_counts)
    return sets



def sum_wall_controls(o, c):
    # Independent multiplication determinant in the cubic quotient. No
    # symbolic-algebra dependency and no Mojo Mat3 implementation is used.
    def multiply_t(v):
        a,b,z = v
        return (2*o.eps*z,a-o.B*z,b+o.A*z)
    d,e = o.d,o.eps
    for m in range(3,7):
        col0 = (2*e,-(3*o.r+2*m+2),3)
        cols = [col0,multiply_t(col0),multiply_t(multiply_t(col0))]
        determinant = 0
        for p in permutations(range(3)):
            inv = sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
            product = 1
            for i in range(3):
                product *= cols[p[i]][i]
            determinant += (-1 if inv%2 else 1)*product
        plus = [3*c*c-6*c-12*d*d+8*d-9,
                6*c*c+9*c*d-8*c-6*d*d-6*d-14,
                9*c*c+18*c*d-6*d-25,
                12*c*c+27*c*d+18*c+6*d*d+8*d-30]
        minus = [3*c*c+10*c-12*d*d-24*d+7,
                 6*c*c+9*c*d+36*c-6*d*d+2*d+54,
                 9*c*c+18*c*d+72*c+42*d+143,
                 12*c*c+27*c*d+118*c+6*d*d+96*d+286]
        P = (plus if e==1 else minus)[m-3]
        assert determinant == -8*e*P
        val = sub(add(o.lengths[0],o.lengths[1]),tuple(m*z for z in o.lengths[2]))
        assert o.sign(val) == (1 if P<0 else -1)


def seeds(o):
    result = []
    for A,B in [(0,1),(0,2),(1,2)]:
        result.extend([(A,B,ZERO),(A,A,o.lengths[B]),
                       (B,A,sub(o.lengths[B],o.lengths[A]))])
    assert set(result) == set(o.seeds()) and len(result) == 9
    return result


def read_dump(path):
    child = defaultdict(set)
    parents = {}
    edges = defaultdict(set)
    for line in Path(path).read_text().splitlines():
        row = line.split()
        if row[0] not in ('C','P','E'):
            continue
        d,e,c,index,A,B,w0,w1,w2 = map(int,row[1:])
        key = d,e,c,index
        state = A,B,(w0,w1,w2)
        if row[0] == 'P':
            assert key not in parents
            parents[key] = state
        else:
            target = child if row[0] == 'C' else edges
            assert state not in target[key], ('duplicate export',key,state)
            target[key].add(state)
    return child, parents, edges


def check(dump=None):
    exported, parents, edges = read_dump(dump) if dump else ({},{},{})
    expected_export_keys = set()
    members = interfaces = duplicates = 0
    chamber_counts = set()
    # Every c at gaps 7,8,9; every wall side and all three upper-plus
    # x-ratio controls at larger gaps. This is a finite grid, not the proof.
    for d in (7,8,9,16,31,64):
        for e in (1,-1):
            for c in representatives(d,e):
                n = 2*d+(-5 if e==1 else 1)+c
                o = ExactClassC(d,e,n)
                sum_wall_controls(o,c)
                symbol = formulas(o,c)
                chamber_counts.add((e,tuple(map(len,symbol))))
                for index, parent in enumerate(seeds(o)):
                    occurrences = list(o.children(parent))
                    actual = set(occurrences)
                    assert actual == symbol[index], (d,e,c,index,actual-symbol[index],symbol[index]-actual)
                    duplicates += len(occurrences)-len(actual)
                    key = d,e,c,index
                    expected_export_keys.add(key)
                    if dump:
                        assert exported.get(key) == actual, ('Mojo formula export',key)
                    interfaces += 1
                members += 1
    if dump:
        assert set(exported) == expected_export_keys
        assert set(parents) == set(edges)
        assert {(d,e,c) for d,e,c,_ in parents} == {(7,e,c) for e in (1,-1) for c in range(3)}
        for e in (1,-1):
            for c in range(3):
                o = ExactClassC(7,e,14+(-5 if e==1 else 1)+c)
                # Independently recreate the COMPLETE breadth-first parent
                # frontier through generation 3. Missing export rows fail.
                seen = dict.fromkeys(seeds(o),0)
                todo = list(seen)
                expected_parents = set()
                for parent in todo:
                    depth = seen[parent]
                    if depth == 4:
                        continue
                    expected_parents.add(parent)
                    actual = set(o.children(parent))
                    matches = [key for key,st in parents.items() if key[:3] == (7,e,c) and st == parent]
                    assert len(matches) == 1
                    assert edges[matches[0]] == actual, ('descendant transfer',matches[0])
                    for ch in sorted(actual):
                        if ch not in seen:
                            assert len(seen) < 4096, 'DESCENDANT_BUDGET_EXHAUSTED'
                            seen[ch] = depth+1
                            todo.append(ch)
                assert {st for key,st in parents.items() if key[:3] == (7,e,c)} == expected_parents
    assert duplicates > 0
    # Sharp negative controls: the plus c=1 -> 2 gap wall changes both
    # right-aligned y seeds; the sum wall changes (x,x,b) by two children.
    for d in (7,8,9,16,31,64):
        for e in (1,-1):
            wall = (d+1)//2 if e==1 else (d-3)//2
            counts = []
            for c in (wall,wall+1):
                o = ExactClassC(d,e,2*d+(-5 if e==1 else 1)+c)
                counts.append(len(set(o.children(seeds(o)[1]))))
            assert counts == [10,8]
    o = ExactClassC(7,1,9)
    first = set().union(*formulas(o,0))
    parent = (0,2,(-30,43,-6))  # a+b-6
    child = (0,1,(-8,-72,10))   # 3a-10b+10
    assert parent in first and child in set(o.children(parent))
    assert child not in first | set(seeds(o))
    result = dict(members=members,interfaces=interfaces,duplicate_occurrences=duplicates,
                  count_chambers=len(chamber_counts),exported_descendant_parents=len(parents),
                  descendant_depth=4 if dump else None,scope='finite experiment; no closure or BH verdict')
    if dump:
        result['canonical_dump_sha256'] = hashlib.sha256(Path(dump).read_bytes()).hexdigest()
    print(json.dumps(result,sort_keys=True))
    print('NINE_SEED_LITERAL_EXACT_ORACLE_PASS')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mojo-dump')
    parser.add_argument('--check-receipt')
    args = parser.parse_args()
    result = check(args.mojo_dump)
    if args.check_receipt:
        assert args.mojo_dump, '--check-receipt requires --mojo-dump'
        assert result == json.loads(Path(args.check_receipt).read_text()), 'committed receipt drift'
        print('NINE_SEED_RECEIPT_PASS')
