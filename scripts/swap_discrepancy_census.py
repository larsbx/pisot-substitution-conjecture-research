"""Exact swap-discrepancy census.

Screens all 3-letter substitutions (letters 1..3) with image lengths <= 3 for
primitivity, irreducibility and the Pisot property, builds the reachable
balanced-pair graph from the three swap seeds (cap 20000 states), and reports
the maximum discrepancy over reachable states.  Finite evidence only; see
docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md.
"""
import itertools, sys, time, cmath
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
    if D==0: return False
    f=lambda x: x**3-T*x**2+U*x-D
    for r in range(1,abs(D)+1):
        if D%r==0 and (f(r)==0 or f(-r)==0): return False
    return True
def roots(T,U,D):
    # monic cubic x^3 + a x^2 + b x + c with a=-T, b=U, c=-D (Cardano, then Newton polish)
    a,b,c=-T,U,-D
    p=b-a*a/3; q=2*a**3/27-a*b/3+c
    disc=(q/2)**2+(p/3)**3
    w=cmath.exp(2j*cmath.pi/3)
    s=cmath.sqrt(disc)
    A=(-q/2+s)**(1/3) if (-q/2+s)!=0 else 0
    B=(-p/3/A) if A!=0 else (-q)**(1/3)
    rs=[A*w**k+B*w**(-k)-a/3 for k in range(3)]
    f=lambda x: x**3+a*x*x+b*x+c; df=lambda x: 3*x*x+2*a*x+b
    out=[]
    for r in rs:
        for _ in range(60):
            d=df(r)
            if d==0: break
            r=r-f(r)/d
        out.append(r)
    return out
def pisot(T,U,D):
    rs=roots(T,U,D)
    beta=max(rs,key=lambda z:z.real)
    if abs(beta.imag)>1e-9 or beta.real<=1: return False
    others=[z for z in rs if z is not beta]
    return all(abs(z)<1-1e-9 for z in others)

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
