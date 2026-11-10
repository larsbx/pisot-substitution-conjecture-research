"""No import of the producer: matrix-power summaries and recursive source addresses.

Small receipts additionally materialize words with independent string expansion.
Optional SymPy validates characteristic/discriminant and symbolic Parikh identities.
This script does not certify a written proof's universal literal prefix claims.
"""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parents[1]
receipt=json.loads((ROOT/'evidence/receipt.json').read_text())
assert receipt['schema']=='c4-two-tail-uniform-v1'

def matmul(A,B):
    return [[sum(A[i][k]*B[k][j]for k in range(3))for j in range(3)]for i in range(3)]

def independent(a,b,tail,n,c,p):
    M=[[1,0,1],[1,a+b,1],[0,1,1]]
    powers=[[[int(i==j)for j in range(3)]for i in range(3)]]
    for _ in range(n):powers.append(matmul(M,powers[-1]))
    lengths=[[sum(P[i][j]for i in range(3))for j in range(3)]for P in powers]
    def pref(c,k,p):
        assert 0<=p<=lengths[k][c]
        if not p:return [0,0,0]
        if k==0:return [int(i==c)for i in range(3)]
        pieces=([(0,1),(1,1)] if c==0 else [(1,a),(2,1),(1,b)] if c==1
                else [(int(z),1)for z in tail])
        out=[0,0,0]
        for letter,count in pieces:
            unit=lengths[k-1][letter]
            take=min(p//unit,count)
            out=[out[i]+take*powers[k-1][i][letter]for i in range(3)]
            p-=take*unit
            if take<count and p:
                remainder=pref(letter,k-1,p)
                return [x+y for x,y in zip(out,remainder)]
            if not p:return out
        assert p==0
        return out
    return pref(c,n,p),pref(c,n,p+1),lengths[n][c]

checks=literal_checks=0
for example in receipt['examples']:
    a,b,tail=example['a'],example['b'],example['tail']
    for row in example['certificates']:
        for key,rr in [('exhibited','replay'),('fifth_generation','fifth_replay')]:
            c=row[key];n,p=c['generation'],c['cut']
            lengths=[]
            for letter in c['letters']:
                before,after,length=independent(a,b,tail,n,letter,p)
                assert before==c['prefix_parikh']
                assert [y-x for x,y in zip(before,after)]==[int(i==c['next_letter'])for i in range(3)]
                lengths.append(length)
                if a+b<=10:
                    sigma=('01','1'*a+'2'+'1'*b,tail);w=str(letter)
                    for _ in range(n):w=''.join(sigma[int(x)]for x in w)
                    v=Counter(w[:p]);assert [v[str(i)]for i in range(3)]==before
                    assert w[p]==str(c['next_letter']) and len(w)==length
                    literal_checks+=1
                checks+=1
            assert lengths==row[rr]['word_lengths']

import sympy as S
s,a,b=S.symbols('s a b',integer=True)
x=S.Symbol('x')  # charpoly uses an assumption-free polynomial generator.
M=S.Matrix([[1,0,1],[1,s,1],[0,1,1]])
f=x*x*(x-2)-s*(x-1)**2
assert S.expand(M.charpoly(x).as_expr()-f)==0
assert S.factor(S.discriminant(f,x))==-s*(4*s*s-13*s+32)
assert M.det()==s
assert S.simplify(f.subs(x,s))==-s
A=S.Matrix([1,1,0]);B=S.Matrix([0,a+b,1]);C=S.Matrix([1,1,1])
F=A+B;G=(a+b)*B+C;H=B+A+C
assert all(S.expand(z)==0 for z in (F+a*G)-(a*G+B+A))
assert all(S.expand(z)==0 for z in (F+a*G+a*B+C)-(a*G+H+a*B))
F0,G0,H0=[v.subs(a,0)for v in (F,G,H)]
assert all(S.expand(z)==0 for z in (2*H0+(b+3)*G0+2*F0+A+S.Matrix([0,0,1]))-(3*H0+(b+3)*G0+F0))
q=3*H0+(b+3)*G0+F0
assert [S.expand(z)for z in q]==[b+10,b**3+3*b*b+5*b+10,b*b+4*b+10]
report={'result':'passed','independent_source_prefix_checks':checks,
        'literal_checks_included':literal_checks,'receipt_examples':len(receipt['examples']),
        'producer_imported':False,'symbolic_checks':8,
        'scope':'finite replay plus exact polynomial identities; written word inclusions still separate'}
print(json.dumps(report,indent=2,sort_keys=True))
