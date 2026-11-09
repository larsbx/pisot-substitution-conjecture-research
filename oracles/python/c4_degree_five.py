#!/usr/bin/env python3
"""Exact independent degree-five replay and optional Lean witness regeneration.

The Lean checker independently expands brackets and replays integral identities.
The word controls here use combinations of positions, independent of Lean’s
recursive counts and inductive proof.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import lcm, prod
from pathlib import Path

alphabet = '012'
words = [''.join(w) for w in product(alphabet, repeat=5)]
def lyndon(w):
    return all(w < w[k:] for k in range(1,len(w)))

@cache
def bracket(w):
    if len(w)==1:
        return w, {w:1}
    k = next(k for k in range(1,len(w)) if lyndon(w[k:]))
    lhs, a = bracket(w[:k])
    rhs, b = bracket(w[k:])
    out = Counter()
    for x, i in a.items():
        for y, j in b.items():
            out[x+y] += i*j
            out[y+x] -= i*j
    return (lhs,rhs), {x:i for x,i in out.items() if i}

def shuffle(w,k):
    return Counter(''.join(next(a) if i in mask else next(b) for i in range(5))
                   for mask in combinations(range(5),k)
                   for a,b in [(iter(w[:k]),iter(w[k:]))])

def add(dst,src,c):
    for x,v in src.items():
        dst[x] = dst.get(x,0)+c*v
        if dst[x]==0: del dst[x]

basis = list(filter(lyndon,words))
assert len(basis)==48
columns = [bracket(w)[1] for w in basis]
extract = []
for i,w in enumerate(basis):
    row={w:1}
    assert columns[i][w]==1
    for j in range(i):
        add(row,extract[j],-columns[j].get(w,0))
    extract.append(row)
for i,row in enumerate(extract):
    assert [sum(c*b.get(w,0) for w,c in row.items()) for b in columns]==[int(i==j) for j in range(48)]

# Sparse exact elimination records a combination of original shuffle rows.
pivots={}
for w in words:
    for k in (1,2):
        r={v:Fraction(c) for v,c in shuffle(w,k).items()}
        assert all(sum(c*b.get(v,0) for v,c in r.items())==0 for b in columns)
        comb={(w,k):Fraction(1)}
        while r:
            j=min(r)
            a=r[j]
            if j not in pivots:
                pivots[j]=({v:c/a for v,c in r.items()}, {v:c/a for v,c in comb.items()})
                break
            old, cert=pivots[j]
            add(r,old,-a)
            add(comb,cert,-a)
assert len(pivots)==195
certs=[]
for w in words:
    row={w:1}
    for b,c in zip(columns,extract):
        add(row,c,-b.get(w,0))
    comb={}
    while row:
        j=min(row)
        a=row[j]
        old,cert=pivots[j]
        add(row,old,-a)
        add(comb,cert,a)
    d=lcm(*(v.denominator for v in comb.values()))
    certs.append((d,{k:int(v*d) for k,v in comb.items()}))

def word(w): return '⟨'+', '.join(w)+'⟩'
def tree(t): return '.letter '+t if isinstance(t,str) else '.comm ('+tree(t[0])+') ('+tree(t[1])+')'
def sparse(r): return '['+', '.join(f'({word(w)}, {c})' for w,c in sorted(r.items()))+']'
def witness(r): return '['+', '.join(f'(({str(k==2).lower()}, {word(w)}), {c})' for (w,k),c in sorted(r.items()))+']'
data = ('''/-
# Integral data for the ternary degree-five shuffle certificate

Rows are in lexicographic order. The consuming proofs check the identities
against actual bracket expansions and shuffle multiplicities.
-/
import Mathlib.Data.Fin.Basic

namespace Psc.Lie5

abbrev Word5 := Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3
abbrev Sparse := List (Word5 × ℤ)
abbrev ShuffleRow := Bool × Word5

inductive Bracket where
  | letter (a : Fin 3)
  | comm (u v : Bracket)

def lyndonTrees : Array Bracket := #[
  '''+',\n  '.join(tree(bracket(w)[0]) for w in basis)+'''
]

def extractRows : Array Sparse := #[
  '''+',\n  '.join(sparse(r) for r in extract)+'''
]

def shuffleWitnesses : Array (ℕ × List (ShuffleRow × ℤ)) := #[
  '''+',\n  '.join(f'({d}, {witness(r)})' for d,r in certs)+'''
]

end Psc.Lie5
''')
print(f'{len(basis)} brackets, {len(pivots)} shuffle pivots, denominators {sorted(set(d for d,_ in certs))}')


@cache
def counts(w, n):
    return Counter(''.join(w[i] for i in indices) for indices in combinations(range(len(w)), n))

def defect(u, v, n):
    out = counts(u, n).copy()
    out.subtract(counts(v, n))
    return {w: c for w, c in out.items() if c}

def subst(s, w):
    return ''.join(s[int(a)] for a in w)

def action(matrix, vector, target):
    return sum(
        coefficient * prod(matrix[int(a)][int(b)] for a, b in zip(target, source))
        for source, coefficient in vector.items()
    )


def shuffle_rank_mod(prime):
    """Modular control independent of rational witness generation."""
    rows = {}
    for w in words:
        for split in (1, 2):
            multiplicities = shuffle(w, split)
            row = [multiplicities[v] % prime for v in words]
            for i, value in enumerate(row):
                if not value:
                    continue
                if i in rows:
                    row[i:] = [(a - value * b) % prime for a, b in zip(row[i:], rows[i][i:])]
                else:
                    inverse = pow(value, -1, prime)
                    rows[i] = [a * inverse % prime for a in row]
                    break
    return len(rows)


def controls():
    tm = ('01','10','2')
    u, v = '01101001', '10010110'
    assert all(not defect(u,v,n) for n in range(1,4))
    assert defect(u,v,4)['0101'] == 8
    x,y = subst(tm,u), subst(tm,v)
    assert all(not defect(x,y,n) for n in range(1,5))
    dx = defect(x,y,5)
    assert dx
    mx = [[image.count(a) for image in tm] for a in alphabet]
    missing = next(w for w in words if action(mx,defect(u,v,5),w) != dx.get(w,0))
    assert (missing, action(mx, defect(u, v, 5), missing), dx[missing]) == ('00001', 0, -8)
    print('missing Equiv4: 00001 gives 0 instead of -8')
    missing_shuffle = next((w,k) for w in words for k in (1,2)
                           if sum(c*defect(u,v,5).get(z,0) for z,c in shuffle(w,k).items()))
    print('missing Equiv4 shuffle:', missing_shuffle)
    assert all(sum(c*dx.get(z,0) for z,c in shuffle(w,k).items()) == 0
               for w in words for k in (1,2))

    # A genuinely asymmetric incidence matrix distinguishes M from M transpose.
    sigma = ('02','1','2')
    m = [[image.count(a) for image in sigma] for a in alphabet]
    wrong = list(zip(*m))
    observed = defect(subst(sigma,x),subst(sigma,y),5)
    assert all(action(m,dx,w) == observed.get(w,0) for w in words)
    target = next(w for w in words if action(wrong,dx,w) != observed.get(w,0))
    assert (target, action(wrong, dx, target), observed[target]) == ('00012', 0, 32)
    print('transposed action: 00012 gives 0 instead of 32')

    # Swap gives a valid signed singleton algebraic child column. Its raw
    # state is reducible, and first-cut children need not satisfy Equiv4.
    swap = ('1','0','2')
    assert (subst(swap,x),subst(swap,y)) == (y,x)
    coordinate = min(dx)
    assert defect(y,x,5)[coordinate] == -dx[coordinate] != dx[coordinate]
    assert Counter(x[:2]) == Counter(y[:2]) and x[:2] != y[:2]
    assert defect(x[:2],y[:2],2)
    print('unsigned normalization:', coordinate, dx[coordinate], -dx[coordinate])
    print('first balanced cut loses Equiv4:', x[:2], y[:2])

    # In characteristic five, a^5 is primitive but every bracket vanishes
    # in that single-letter coordinate.
    pure = '00000'
    assert all(shuffle(w,k)[pure] % 5 == 0 for w in words for k in (1,2))
    assert all(b.get(pure,0) == 0 for b in columns)
    ranks = {p: shuffle_rank_mod(p) for p in (2, 3, 5, 7)}
    assert ranks == {2: 195, 3: 195, 5: 192, 7: 195}
    print('shuffle ranks modulo 2, 3, 5, 7:', ranks)
    print('characteristic five: pure fifth power survives the shuffle tests')
    print('multidegree dimensions:', sorted(Counter(tuple(w.count(a) for a in alphabet)
                                                        for w in basis).items()))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-lean', type=Path)
    parser.add_argument('--check-lean', type=Path)
    args = parser.parse_args()
    if args.write_lean:
        args.write_lean.write_text(data)
    if args.check_lean and args.check_lean.read_text() != data:
        raise SystemExit('degree-five Lean data differ from exact replay')
    controls()
