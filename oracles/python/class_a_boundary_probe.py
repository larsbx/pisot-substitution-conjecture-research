#!/usr/bin/env python3
"""Independent exact-arithmetic probe of the OPEN class-A n<5d strip.

Read-only: does not import or mutate the PSC repository. Python stdlib only.
The infinite-family theorem is proved using rational polynomial sign checks.
Optional finite BPA replay is a bounded *sample*, not a uniform theorem.
"""
import argparse
from collections import deque
from fractions import Fraction
from hashlib import sha256
import json


def params(n, sign, k=0):
    """k is exact distance below the PIP d-upper-bound."""
    assert isinstance(k,int) and k>=0 and sign in (-1,1)
    floor = (k+3 if sign == -1 else 2*(k+2))
    assert n >= floor
    return 2*n + 6*sign + 5 - k


def characteristic(n, d, sign, t):
    t=Fraction(t)
    return t**3 - (n+3+sign)*t**2 + (n-d+2+3*sign)*t - 2*sign


def exact_rational_cert(n, sign, k=0):
    d=params(n,sign,k)
    P=lambda t: characteristic(n,d,sign,t)
    a=Fraction(-1)
    m=k+2
    b=a+Fraction(m,n)
    assert -1<b<0
    # Three disjoint real-root intervals, established by endpoint signs.
    if sign==-1:
        intervals=[(a,b), (Fraction(0),Fraction(1)),(Fraction(n+2),Fraction(n+3))]
        beta_lower, beta_upper=n+2,n+3
        # x=m/n in (0,1): 1+5x(1-x)+x^3 > 0.
    else:
        intervals=[(a,b), (b,Fraction(0)),(Fraction(n+4),Fraction(n+6))]
        beta_lower,beta_upper=n+4,n+6
        # x=m/n in (0,1/2]: 1+3x-7x^2+x^3 > 0.
    x=Fraction(m,n)
    asserted_at_b=1+(4-sign)*x-(6+sign)*x*x+x*x*x
    assert P(a)==-(k+1)
    assert P(b)==asserted_at_b and P(b)>0
    assert all(P(x)*P(y)<0 for x,y in intervals)
    # A monic cubic over Q can only factor if it has a rational integer root.
    assert all(P(i)!=0 for i in (-2,-1,1,2))
    assert P(-2)==-2*(n+k+7)
    # Matrix entries are nonnegative and M^2 is strictly positive for n>=2.
    M=((2,1,1),(0,1,1),(n+d,n,n+sign))
    M2=[[sum(M[i][j]*M[j][z] for j in range(3)) for z in range(3)] for i in range(3)]
    assert all(v>0 for row in M2 for v in row)
    def det3(A):
        return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])
                - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])
                + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]))
    assert det3(M)==2*sign
    for t in (-3,-2,-1,0,1,2,3,7):
        assert det3([[t*(i==j)-M[i][j] for j in range(3)] for i in range(3)])==P(t)
    assert Fraction(d,beta_upper-1)>Fraction(1,5)  # l>=5 box is not transferable
    assert 1<=d<=2*n+6*sign+5 and n<d<5*d
    # The two nondominant roots belong to (-1,1): hence irreducible Pisot.
    assert beta_lower>2
    return dict(sign=sign,n=n,d=d,k=k,
                P_coeffs=[1,-(n+3+sign),n-d+2+3*sign,-2*sign],
                P_minus_one=str(P(a)),P_at_right_end_of_negative_bracket=str(P(b)),
                root_intervals=[[str(x),str(y)] for x,y in intervals],
                beta_interval=[beta_lower,beta_upper],
                u_interval=[str(Fraction(d,beta_upper-1)),str(Fraction(d,beta_lower-1))],
                det=2*sign,primitive_M2_positive=True,irreducible=True,
                strict_subunit_conjugates=True)


def substitution(n,d,sign):
    return ('0'+'2'*(n+d)+'0', '1'+'2'*n+'0', '0'+'2'*(n+sign)+'1')


def normal(u,v):
    return (u,v) if u<=v else (v,u)


def balanced_children(u,v):
    assert len(u)==len(v)
    delta=[0,0,0]
    start=0
    for k,(a,b) in enumerate(zip(u,v)):
        delta[ord(a)-48]+=1
        delta[ord(b)-48]-=1
        if delta==[0,0,0]:
            yield (u[start:k+1],v[start:k+1],start,k+1)
            start=k+1
    if start!=len(u):
        raise AssertionError('inflated balanced pair did not close')


def replay_bpa(n,d,sign, max_states=2000,max_word=30000,max_edges=50000):
    """Exact literal child factorization, carrying ordinal/span/orientation.

    This is a finite graph at a fixed parameter, not an occurrence-packet
    certificate or an infinite-family proof. Stops rather than claiming
    completeness if any budget is exhausted.
    """
    sigma=substitution(n,d,sign)
    roots=[normal(str(i)+str(j),str(j)+str(i)) for i in range(3) for j in range(i+1,3)]
    ids={r:i for i,r in enumerate(roots)}
    words=list(roots)
    queue=deque(roots)
    adj=[]
    h=sha256()
    edgecount=0
    maxword=0
    while queue:
        top,bottom=queue.popleft()
        uid=ids[(top,bottom)]
        assert uid==len(adj)
        maxword=max(maxword,len(top))
        if len(top)>max_word:raise RuntimeError('word cap hit: not a completed graph')
        if len(top)==1 and top==bottom:
            adj.append([])
            continue
        infl_top=''.join(sigma[ord(c)-48] for c in top)
        infl_bottom=''.join(sigma[ord(c)-48] for c in bottom)
        children=[]
        for ordinal,(u,v,start,end) in enumerate(balanced_children(infl_top,infl_bottom)):
            child=normal(u,v)
            orientation=1 if (u,v)==child else -1
            if child not in ids:
                if len(ids)>=max_states:raise RuntimeError('state cap hit: not a completed graph')
                ids[child]=len(ids)
                words.append(child)
                queue.append(child)
            cid=ids[child]
            children.append((cid,ordinal,start,end,orientation))
            h.update(f'{uid},{ordinal},{cid},{start},{end},{orientation}\n'.encode())
            edgecount+=1
            if edgecount>max_edges:raise RuntimeError('edge cap hit: not a completed graph')
        adj.append(children)
    assert len(adj)==len(ids)
    parents=[set() for _ in ids]
    for uid,children in enumerate(adj):
        for cid,*_ in children:parents[cid].add(uid)
    targets=[i for i,(u,v) in enumerate(words) if u==v and len(u)==1]
    distances={i:0 for i in targets}
    queue=deque(targets)
    while queue:
        i=queue.popleft()
        for p in parents[i]:
            if p not in distances:
                distances[p]=distances[i]+1
                queue.append(p)
    seed_depths={f'{x[0]}|{x[1]}':distances.get(i) for i,x in enumerate(roots)}
    seed_witnesses={}
    for i,root in enumerate(roots):
        if i not in distances:
            seed_witnesses[f'{root[0]}|{root[1]}']=None
            continue
        seq=[]
        current=i
        while distances[current]>0:
            choices=[e for e in adj[current] if distances.get(e[0])==distances[current]-1]
            if not choices:raise AssertionError('a reported distance lacks an actual child edge')
            cid,ordinal,start,end,orientation=min(choices, key=lambda e:(e[1],e[0]))
            seq.append(dict(parent='|'.join(words[current]),child='|'.join(words[cid]),
                            ordinal=ordinal,span=[start,end],orientation=orientation))
            current=cid
        assert words[current][0]==words[current][1] and len(words[current][0])==1
        seed_witnesses[f'{root[0]}|{root[1]}']=seq
    return dict(n=n,d=d,sign=sign,substitution=list(sigma),
                normalized_states=len(ids),ordered_factor_edges=edgecount,
                max_state_word_length=maxword,terminal_diagonal_states=len(targets),
                all_states_reach_diagonal=len(distances)==len(ids),
                missed_states=len(ids)-len(distances),
                max_shortest_target_depth=max(distances.values()),
                seed_depths=seed_depths,seed_witnesses=seed_witnesses,ordered_factor_edge_sha256=h.hexdigest(),
                exact_literal_replay=True,cap_exhausted=False,
                independent_human_review=False)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--bpa-example',action='store_true',help='Run exact finite BPA for eps=-1,n=3,d=5')
    args=ap.parse_args()
    selected=[]
    for sign,ks in ((-1,(0,1,3,10)),(1,(0,1,3,10))):
        for k in ks:
            floor=(k+3 if sign==-1 else 2*(k+2))
            for n in (floor,floor+3,floor+128):
                selected.append(exact_rational_cert(n,sign,k))
    out={'theorem':'for either sign and every fixed k>=0, infinitely many primitive irreducible Pisot class-A l=0 members have a real conjugate lambda in (-1,-1+(k+2)/n)',
         'certificate_type':'exact rational endpoint signs, root isolation and rational-root test',
         'samples':selected}
    if args.bpa_example:
        out['finite_bpa_example']=replay_bpa(3,5,-1)
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
