"""Exact swap-discrepancy census.

Screens all 3-letter substitutions (letters 1..3) with image lengths <= 3 for
primitivity, irreducibility and the Pisot property (all exact: integer
matrix powers, rational-root test, Sturm sequences over Q; no floating point),
builds the reachable
balanced-pair graph from the three swap seeds (cap 20000 states), and reports
the maximum discrepancy over reachable states.  Independent Python oracle for
the canonical Mojo kernel mojo/swap_discrepancy_census.mojo.  Finite evidence
only; see
docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md.
"""
import itertools, sys, time
from fractions import Fraction
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1] / 'src'))
from psc_research.bpa import build_bpa

def par(w):
    p=[0,0,0]
    for a in w: p[a-1]+=1
    return p
def mat(sigma): return [[par(sigma[j+1])[i] for j in range(3)] for i in range(3)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def primitive(M):
    P=M
    for _ in range(5): P=mul(P,M)
    return all(x>0 for r in P for x in r)
def charpoly(M):  # x^3 - T x^2 + U x - D
    T=M[0][0]+M[1][1]+M[2][2]
    U=(M[0][0]*M[1][1]-M[0][1]*M[1][0])+(M[0][0]*M[2][2]-M[0][2]*M[2][0])+(M[1][1]*M[2][2]-M[1][2]*M[2][1])
    D=(M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
    return T,U,D
def irreducible(T,U,D):
    """Monic integer cubic: irreducible over Q iff no integer root dividing D."""
    if D==0: return False
    f=lambda x: x**3-T*x**2+U*x-D
    for r in range(1,abs(D)+1):
        if D%r==0 and (f(r)==0 or f(-r)==0): return False
    return True

# --- exact Pisot test by Sturm sequences over Q (mirrors mojo/psc/pisot.mojo) ---
def _deg(p):
    for i in range(len(p)-1,-1,-1):
        if p[i]!=0: return i
    return -1
def _eval(p,x):
    acc=Fraction(0)
    for c in reversed(p): acc=acc*x+c
    return acc
def _rem(a,b):
    r=list(a); db=_deg(b)
    while _deg(r)>=db:
        dr=_deg(r); f=r[dr]/b[db]
        for i in range(db+1): r[dr-db+i]-=f*b[i]
        r[dr]=Fraction(0)
    return r
def _sturm(p):
    chain=[list(p),[i*p[i] for i in range(1,len(p))]]
    while _deg(chain[-1])>0:
        neg=[-c for c in _rem(chain[-2],chain[-1])]
        if _deg(neg)<0: break
        chain.append(neg)
    return chain
def _changes(chain,x):
    last=0; n=0
    for q in chain:
        v=_eval(q,x)
        if v==0: continue
        sgn=1 if v>0 else -1
        if last and sgn!=last: n+=1
        last=sgn
    return n
def _roots_in(p,a,b):
    """Distinct real roots of p in (a,b]."""
    ch=_sturm(p); return _changes(ch,a)-_changes(ch,b)
def pisot(T,U,D):
    """Exactly one root outside the closed unit disc, real and > 1.
    Three real roots: Sturm counting. One real root: beta*|beta2|^2 = D, so
    |beta2| < 1 iff D < beta iff f(D) < 0 (beta the only real root)."""
    p=[Fraction(-D),Fraction(U),Fraction(-T),Fraction(1)]   # low-degree first
    B=Fraction(2+max(abs(T),abs(U),abs(D)))
    nreal=_roots_in(p,-B,B)
    if _roots_in(p,Fraction(1),B)!=1: return False
    if nreal==3: return _roots_in(p,Fraction(-1),Fraction(1))==2
    if nreal!=1: return False
    return D>0 and _eval(p,Fraction(D))<0

words=[w for L in (1,2,3) for w in itertools.product((1,2,3),repeat=L)]
corpus=[]
for a in words:
    for b in words:
        for c in words:
            sigma={1:a,2:b,3:c}
            M=mat(sigma); T,U,D=charpoly(M)
            if primitive(M) and irreducible(T,U,D) and pisot(T,U,D):
                corpus.append(sigma)
print("PIP corpus size:",len(corpus),flush=True)

def disc(state):
    u,v=state; p=[0,0,0]; q=[0,0,0]; best=0
    for x,y in zip(u,v):
        p[x-1]+=1; q[y-1]+=1
        best=max(best,max(abs(p[i]-q[i]) for i in range(3)))
    return best

t0=time.time(); overall=0; hist={}; capped=0; nstates=0; maxlen=0
for idx,sigma in enumerate(corpus):
    try:
        g=build_bpa(sigma,max_states=20000)
    except RuntimeError:
        capped+=1; print("CAPPED",idx,sigma,flush=True); continue
    m=0
    for s in g:
        nstates+=1
        d=disc(s)
        if d>m: m=d
        if len(s[0])>maxlen: maxlen=len(s[0])
    hist[m]=hist.get(m,0)+1
    if m>overall:
        overall=m; print("new max",m,"at",idx,sigma,flush=True)
    if idx%250==0: print("progress",idx,"elapsed",round(time.time()-t0),"s",flush=True)
print("DONE capped",capped,"states",nstates,"overall max Disc",overall,"max state length",maxlen)
print("histogram of per-substitution max Disc:",sorted(hist.items()))
