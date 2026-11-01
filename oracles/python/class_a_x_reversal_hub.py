"""Uniform X <-> R(X) bridge and reversal-invariant X closure (minus class A).

Exact affine indexed-word transport and rational Perron margin certificates.
Finite literal-word replay uses the unchanged repository Geometry.
No SCC-coverage, universal boundary hitting or PSC theorem follows.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
X=(0,0,1,0,-1)
B3=(2,0,0,-1,0)
H1=(0,2,0,-1,1)
Z=(2,1,0,0,-1)
RX=(0,0,-1,0,1)
C=(2,2,0,0,0)

def reverse(w):return(w[1],w[0],*(-x for x in w[2:]))

@dataclass(frozen=True)
class Aff:
    k:int=0
    t:int=0
    c:int=0
    def __add__(self,other):
        other=aff(other)
        return Aff(self.k+other.k,self.t+other.t,self.c+other.c)
    __radd__=__add__
    def __neg__(self):return Aff(-self.k,-self.t,-self.c)
    def __sub__(self,other):return self+(-aff(other))
    def __rsub__(self,other):return aff(other)-self
    def __mul__(self,v):
        if not isinstance(v,int):raise TypeError('non-affine index')
        return Aff(v*self.k,v*self.t,v*self.c)
    __rmul__=__mul__

def aff(z):return z if isinstance(z,Aff) else Aff(c=z)
K=Aff(k=1);T=Aff(t=1)
N=K+T+3
D=K+2*T+5
A=N+D
RUN_LENGTH=(A,N,N-1)
# Fully typed actual ordered occurrences. The two n-indexed edges
# deliberately use LAST c or LAST x, not a fictitious RUN child.
PATH=((D+2,0,B3),(0,N+2,H1),(N,N,Z),(0,N+1,RX))

def nonnegative(z):
    z=aff(z)
    assert z.k>=0 and z.t>=0 and z.c>=0,('unbounded index negative',z)

def prefix(parent,i):
    i=aff(i)
    if i==Aff():return (Aff(),Aff(),Aff()),1 if parent==1 else 0
    if i==RUN_LENGTH[parent]+1:
        p=((Aff(c=1),Aff(),A),(Aff(),Aff(c=1),N),
           (Aff(c=1),Aff(),N-1))[parent]
        return p,1 if parent==2 else 0
    nonnegative(i-1)
    nonnegative(RUN_LENGTH[parent]-i)
    p=(Aff(),Aff(c=1),i-1) if parent==1 else (Aff(c=1),Aff(),i-1)
    return p,2

def certify_edge(source,i,j,target):
    pt,top=prefix(source[0],i)
    pb,bottom=prefix(source[1],j)
    assert (top,bottom)==target[:2],('incorrect literal type',source,i,j,target)
    x,c,y=source[2:]
    M=(2*x+c+y,c+y,A*x+N*c+(N-1)*y)
    found=tuple(M[r]+pb[r]-pt[r] for r in range(3))
    assert found==tuple(Aff(c=z) for z in target[2:]),('Parikh transport',source,i,j,target,found)

VERTICES=((F(0),F(0)),(F(0),F(1)),(F(1,5),F(1,5)),(F(1,5),F(3,5)))
LENGTHS=((2,0,1),(1,1,0),(1,0,0))
def certify_strict(w):
    x,c,y=w[2:]
    shift=(2*x+c+y,c,x)
    margins=(tuple(a+b for a,b in zip(shift,LENGTHS[w[1]])),
             tuple(a-b for a,b in zip(LENGTHS[w[0]],shift)))
    for coeff in margins:
        vals=[coeff[0]+coeff[1]*h+coeff[2]*rho for h,rho in VERTICES]
        assert min(vals)>=0 and any(v>0 for v in vals),('not universally strict',w,coeff,vals)

def symbolic_certificate():
    assert reverse(X)==RX and reverse(RX)==X
    current=X;verified=0;states={X}
    for i,j,target in PATH:
        certify_edge(current,i,j,target)
        certify_edge(reverse(current),j,i,reverse(target))
        states.add(target)
        current=target;verified+=2
    assert current==RX
    oriented=states|{reverse(v) for v in states}
    for v in oriented:certify_strict(v)
    assert len(oriented)==8 and verified==8
    # Reversal is an exact edge automorphism: if child(w,i,j)=v,
    # linearity of M and antisymmetry of P_b-P_t give
    # child(R(w),j,i)=R(v); strict physical margins swap.
    # Therefore X->R(X) and R(X)->X, and all of Reach(X) is
    # reversal-invariant. This argument is independent of graph finiteness.
    return dict(uniform_parameter_chamber='all integer k,t>=0',
        X_to_reverse_X_depth=4,reverse_X_to_X_depth=4,
        directed_symbolic_occurrence_checks=verified,
        oriented_path_states=len(oriented),strict_physical_margins=2*len(oriented),
        forward_X_closure_reversal_invariant=True,
        implies_all_X_descendants_productive=False,
        no_universal_BH=True)

def actual_steps(k,t,flip=0):
    out=[]
    for i,j,target in PATH:
        i=i.k*k+i.t*t+i.c if isinstance(i,Aff) else i
        j=j.k*k+j.t*t+j.c if isinstance(j,Aff) else j
        if flip:i,j,target=j,i,reverse(target)
        out.append((i,j,target))
    return out

def lifted_reversal_path(k,t,path_from_X):
    """Explicit witness X->R(v) from any actual chosen X->v path.

    Uses X->R(X) plus the edgewise reversed path, retaining actual
    ordered indices. The target v may be nonterminal or coincidence.
    Invalid input paths are detected by the exact Geometry verifier.
    """
    return actual_steps(k,t,0)+[(j,i,reverse(target))
                                  for i,j,target in path_from_X]

def verify(g,start,steps):
    current=start
    assert g.interior(current)
    for i,j,target in steps:
        assert g.child(current,i,j)==target,('wrong typed child',g.k,g.t,current,i,j,target)
        assert g.interior(target),('non-strict child',g.k,g.t,target)
        current=target
    return current

def independent_literal_probe():
    specimens=edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            for flip in (0,1):
                start=RX if flip else X
                end=verify(g,start,actual_steps(k,t,flip))
                assert end==(X if flip else RX)
                edges+=4
            # Symmetry holds for *all* literal strict children, not
            # merely the chosen four bridge edges.
            for w in (X,B3,H1,Z,RX):
                for i in range(len(g.words[w[0]])):
                    for j in range(len(g.words[w[1]])):
                        child=g.child(w,i,j)
                        rev=g.child(reverse(w),j,i)
                        assert rev==reverse(child)
                        assert g.interior(rev)==g.interior(child)
            specimens+=1
    assert (specimens,edges)==(117,936)
    return dict(specimens=specimens,actual_oriented_bridge_edges=edges,
                all_chosen_source_stars_reverse_consistent=True)

if __name__=='__main__':
    import json
    print(json.dumps(symbolic_certificate(),sort_keys=True,indent=2))
    print(json.dumps(independent_literal_probe(),sort_keys=True,indent=2))
