"""Uniform all-nine swapped-patch seed paths to X in minus class A.

All selected word/Parikh edges are proved coefficientwise in Z[k,t];
physical strictness is checked at exact vertices of an inherited
rational Perron chamber. This is seed-wise existential reachability,
not productivity of every descendant or all-seed boundary hitting.
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
X=(0,0,1,0,-1)
Q=(2,0,0,-1,1)
C=(2,2,0,0,0)
S0=(0,1,0,0,0)
S1=(0,0,0,1,0)
S2=(1,0,-1,1,0)
S3=(0,2,0,0,0)
S4=(0,0,0,0,1)
S5=(2,0,-1,0,1)
S6=(1,2,0,0,0)
S7=(1,1,0,0,1)
S8=(2,1,0,-1,1)
SEEDS=(S0,S1,S2,S3,S4,S5,S6,S7,S8)
P=(0,2,0,1,0)
Z=(2,0,0,1,-1)
D=(1,2,0,0,1)
E=(1,2,0,1,-1)
F=(1,0,0,0,1)
G=(2,1,0,0,0)
H=(1,0,0,0,0)
Q3=(0,2,1,-1,1)
L=(0,1,1,0,-1)
I=(0,0,0,0,1)

def reverse(w):return (w[1],w[0],*(-v for v in w[2:]))

@dataclass(frozen=True)
class Aff:
    k:int=0
    t:int=0
    c:int=0
    def __add__(self,o):
        o=aff(o)
        return Aff(self.k+o.k,self.t+o.t,self.c+o.c)
    __radd__=__add__
    def __neg__(self):return Aff(-self.k,-self.t,-self.c)
    def __sub__(self,o):return self+(-aff(o))
    def __rsub__(self,o):return aff(o)-self
    def __mul__(self,v):
        if not isinstance(v,int):raise TypeError('non-affine index')
        return Aff(self.k*v,self.t*v,self.c*v)
    __rmul__=__mul__

def aff(z):return z if isinstance(z,Aff) else Aff(c=z)
K=Aff(k=1)
T=Aff(t=1)
N=K+T+3
DD=K+2*T+5
A=N+DD
RUNLENGTH=(A,N,N-1)

def paths():
    z=((N+2,0,Z),(N,N,D),(N+1,0,X))
    p=((N+2,0,Z),)+z[1:]
    return {
      S0:((0,1,P),)+p,
      S1:z,
      S2:((0,DD,E),(0,0,F),(N+1,0,X)),
      S3:((N,N,G),(0,1,P))+p,
      S4:((N+1,0,Z),)+z[1:],
      S5:((0,DD+2,P),)+p,
      S6:((0,0,H),(N+1,N+2,Q3),(A+1,0,X)),
      S7:((N+1,0,L),(A+1,N+1,I),(N+1,0,Z))+z[1:],
      S8:((0,2,P),)+p,
    }

def nonnegative(e):
    e=aff(e)
    assert e.k>=0 and e.t>=0 and e.c>=0,('invalid unbounded RUN index',e)

def prefix(parent,i):
    i=aff(i)
    if i==Aff():return (Aff(),Aff(),Aff()),1 if parent==1 else 0
    if i==RUNLENGTH[parent]+1:
        p=((Aff(c=1),Aff(),A),(Aff(),Aff(c=1),N),
           (Aff(c=1),Aff(),N-1))[parent]
        return p,1 if parent==2 else 0
    nonnegative(i-1)
    nonnegative(RUNLENGTH[parent]-i)
    p=(Aff(),Aff(c=1),i-1) if parent==1 else (Aff(c=1),Aff(),i-1)
    return p,2

def certified_transport(w,i,j,target):
    pt,top=prefix(w[0],i)
    pb,bottom=prefix(w[1],j)
    assert target[:2]==(top,bottom),('wrong typed word occurrence',w,i,j,target)
    x,c,y=w[2:]
    M=(2*x+c+y,c+y,A*x+N*c+(N-1)*y)
    got=tuple(M[h]+pb[h]-pt[h] for h in range(3))
    assert got==tuple(Aff(c=z) for z in target[2:]),('bad Parikh transport',w,i,j,target,got)

VERTICES=((Fraction(0),Fraction(0)),(Fraction(0),Fraction(1)),
          (Fraction(1,5),Fraction(1,5)),(Fraction(1,5),Fraction(3,5)))
LENGTHS=((2,0,1),(1,1,0),(1,0,0))

def strict(w):
    x,c,y=w[2:]
    shift=(2*x+c+y,c,x)
    margins=(tuple(a+b for a,b in zip(shift,LENGTHS[w[1]])),
             tuple(a-b for a,b in zip(LENGTHS[w[0]],shift)))
    for coeff in margins:
        vals=[coeff[0]+coeff[1]*h+coeff[2]*rho for h,rho in VERTICES]
        assert min(vals)>=0 and any(v>0 for v in vals),('not uniformly strict',w,coeff,vals)

def swapped_seed_candidates():
    """All literal tile pairings of ab versus ba, with a<b.

    Exactly three of each pair of four are strict since L(a)>L(b),
    as follows from Lx=2+rho > Lc=1+h > Ly=1.
    """
    cases=[]
    for a,b in ((0,1),(0,2),(1,2)):
        top=(a,b)
        bottom=(b,a)
        for i in (0,1):
            for j in (0,1):
                pt=tuple(int(v==top[0]) if i else 0 for v in range(3))
                pb=tuple(int(v==bottom[0]) if j else 0 for v in range(3))
                cases.append((top[i],bottom[j],*(pb[r]-pt[r] for r in range(3))))
    assert len(cases)==12
    # The excluded three are all top-short/bottom-short with displacement
    # -L(a), whose lower margin is L(b)-L(a)<0, never strict.
    excluded={(b,b,*(-int(v==a) for v in range(3))) for a,b in ((0,1),(0,2),(1,2))}
    strict_seeds=set(cases)-excluded
    assert strict_seeds==set(SEEDS)
    return strict_seeds,excluded

def symbolic_certificate():
    seeds,excluded=swapped_seed_candidates()
    states=set(SEEDS)|{X}
    count=0
    totals=[]
    for seed,steps in paths().items():
        w=seed
        for i,j,target in steps:
            certified_transport(w,i,j,target)
            certified_transport(reverse(w),j,i,reverse(target))
            states.add(target)
            w=target
            count+=2
        assert w==X
        totals.append(len(steps))
    all_oriented=states|{reverse(w) for w in states}
    assert len(states)==19 and len(all_oriented)==32
    for w in all_oriented:strict(w)
    assert count==68 and max(totals)==5
    # Complete using already mainline verified X -> Q -> C.
    certified_transport(X,DD+1,0,Q)
    certified_transport(Q,1,2,C)
    strict(Q);strict(C)
    return dict(swap_seed_pairs=3,seed_candidates=12,strict_swap_seeds=9,
                excluded_touch_or_disjoint=3,
                symbolic_oriented_edges_to_X=count,
                base_path_states=len(states),oriented_path_states=len(all_oriented),
                strict_physical_margins=2*len(all_oriented),
                max_seed_to_X_depth=5,max_seed_to_C_depth=7,
                nine_seeds_not_all_descendants=True,
                universal_BH=False)

def literal_probe():
    specimens=edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            assert all(g.interior(s) for s in SEEDS)
            assert len([s for s in swapped_seed_candidates()[1] if g.interior(s)])==0
            for seed,steps in paths().items():
                for flip in (0,1):
                    current=reverse(seed) if flip else seed
                    for ii,jj,target in steps:
                        i=ii.k*k+ii.t*t+ii.c if isinstance(ii,Aff) else ii
                        j=jj.k*k+jj.t*t+jj.c if isinstance(jj,Aff) else jj
                        if flip:i,j,target=j,i,reverse(target)
                        assert g.child(current,i,j)==target
                        assert g.interior(target)
                        current=target
                        edges+=1
                    assert current==(reverse(X) if flip else X)
            assert g.child(X,g.d+1,0)==Q
            assert g.child(Q,1,2)==C
            specimens+=1
    assert (specimens,edges)==(117,7956)
    return dict(exact_Fraction_specimens=specimens,real_oriented_selected_edges=edges)

if __name__=='__main__':
    import json
    print(json.dumps(symbolic_certificate(),indent=2,sort_keys=True))
    print(json.dumps(literal_probe(),indent=2,sort_keys=True))
