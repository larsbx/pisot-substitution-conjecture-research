"""T2=(y,y,1,-1,-2): uniform selected typed coincidence exit, not BH.

Independent literal/Fraction finite replay is distinct from universal
Z[k,t] affine occurrence and rational-polytope strictness certificates.
"""
from pathlib import Path
from fractions import Fraction as F
from dataclasses import dataclass
import runpy
Geometry=runpy.run_path(str(Path(__file__).with_name("class_a_boundary_children.py")))["Geometry"]
T2=(2,2,1,-1,-2)
F3=(0,1,0,-3,3); F4=(0,1,0,-3,4)
H=(0,2,0,1,-1); J=(2,2,0,2,-2); B=(0,2,0,-3,3)
C=(2,2,0,0,0)
LABELS={T2,F3,F4,H,J,B,C}

def reverse(w):
    return (w[1],w[0],*(-x for x in w[2:]))

def path(k,t):
    if min(k,t)<0: raise ValueError("outside minus class A")
    n=k+t+3
    if t==0: return [(0,n,F3),(0,3,H),(2,1,C)]
    if k==0 and t==1: return [(0,n,F4),(3,1,J),(3,1,C)]
    return [(0,k+3,B),(1,4,C)]

def verify(g,flip,steps):
    state=reverse(T2) if flip else T2
    expected=[(j,i,reverse(w)) for i,j,w in path(g.k,g.t)] if flip else path(g.k,g.t)
    if steps!=expected: raise ValueError("different intended occurrence path")
    for i,j,target in steps:
        if not (g.interior(state) and g.child(state,i,j)==target and g.interior(target)):
            raise AssertionError(("typed, indexed or strict edge failed",g.k,g.t,state,i,j,target))
        state=target
    assert state==C

@dataclass(frozen=True)
class Aff:
    k:int=0
    t:int=0
    c:int=0
    def __add__(self,x):
        x=aff(x)
        return Aff(self.k+x.k,self.t+x.t,self.c+x.c)
    __radd__=__add__
    def __neg__(self):
        return Aff(-self.k,-self.t,-self.c)
    def __sub__(self,x):
        return self+(-aff(x))
    def __rsub__(self,x):
        return aff(x)-self
    def __mul__(self,n):
        if not isinstance(n,int): raise TypeError("nonaffine term")
        return Aff(self.k*n,self.t*n,self.c*n)
    __rmul__=__mul__

def aff(x): return x if isinstance(x,Aff) else Aff(c=x)

@dataclass(frozen=True)
class Chamber:
    k0:int
    t0:int
    fixed_k:bool
    fixed_t:bool
    tag:str
    def simp(self,e):
        e=aff(e)
        return Aff(0 if self.fixed_k else e.k,0 if self.fixed_t else e.t,
                   e.c+(e.k*self.k0 if self.fixed_k else 0)
                      +(e.t*self.t0 if self.fixed_t else 0))
    def nonnegative(self,e):
        e=self.simp(e)
        assert e.k>=0 and e.t>=0,("negative recession slope",self,e)
        assert e.c+e.k*self.k0+e.t*self.t0>=0,("negative chamber-corner index",self,e)

CHAMBERS=(
    Chamber(0,0,False,True,"t=0"),
    Chamber(0,1,True,True,"k=0,t=1"),
    Chamber(0,2,True,False,"k=0,t>=2"),
    Chamber(1,1,False,False,"k>=1,t>=1"),
)

def symbolic_prefix(ch,letter,i,n,d):
    i=ch.simp(i); A=n+d; R={0:A,1:n,2:n-1}[letter]
    if i==Aff(): return (Aff(),Aff(),Aff()), 1 if letter==1 else 0
    if ch.simp(i-R-1)==Aff():
        p={0:(Aff(c=1),Aff(),A),1:(Aff(),Aff(c=1),n),
           2:(Aff(c=1),Aff(),n-1)}[letter]
        return p,1 if letter==2 else 0
    ch.nonnegative(i-1)
    ch.nonnegative(R-i)
    p=(Aff(),Aff(c=1),i-1) if letter==1 else (Aff(c=1),Aff(),i-1)
    return p,2

def chamber_steps(ch):
    k,t=Aff(k=1),Aff(t=1); n=k+t+3
    if ch.tag=="t=0": return [(0,n,F3),(0,3,H),(2,1,C)]
    if ch.tag=="k=0,t=1": return [(0,n,F4),(3,1,J),(3,1,C)]
    return [(0,k+3,B),(1,4,C)]

def symbolic_proof():
    checked=0;max_depth=0
    for ch in CHAMBERS:
        state=T2
        n=Aff(k=1,t=1,c=3);d=Aff(k=1,t=2,c=5)
        A=n+d;N=n-1
        steps=chamber_steps(ch)
        for i,j,target in steps:
            pt,top=symbolic_prefix(ch,state[0],i,n,d)
            pb,bottom=symbolic_prefix(ch,state[1],j,n,d)
            assert (top,bottom)==target[:2],("FIRST/RUN/LAST type",ch,state,i,j,target)
            x,c,y=state[2:];M=(2*x+c+y,c+y,A*x+n*c+N*y)
            out=tuple(ch.simp(M[q]+pb[q]-pt[q]) for q in range(3))
            assert out==tuple(Aff(c=v) for v in target[2:]),(
                "Z[k,t] coefficient mismatch",ch,state,target,out)
            state=target;checked+=1
        assert state==C
        max_depth=max(max_depth,len(steps))
    assert checked==10 and max_depth==3
    return dict(integer_chambers=4,coefficientwise_occurrence_edges=checked,
                max_selected_depth=max_depth)

VERTICES=((F(0),F(0)),(F(0),F(1)),(F(1,5),F(1,5)),(F(1,5),F(3,5)))

def strict_certificate():
    states=LABELS|{reverse(w) for w in LABELS}
    assert len(states)==13
    lengths=((2,0,1),(1,1,0),(1,0,0))
    for w in states:
        x,c,y=w[2:];s=(2*x+c+y,c,x)
        margins=(tuple(a+b for a,b in zip(s,lengths[w[1]])),
                 tuple(a-b for a,b in zip(lengths[w[0]],s)))
        for coeff in margins:
            vals=[coeff[0]+coeff[1]*h+coeff[2]*rho for h,rho in VERTICES]
            assert min(vals)>=0 and any(v>0 for v in vals),(
                "not strict on inherited root polygon",w,coeff,vals)
    return dict(oriented_states=13,strict_margins=26,
                rational_vertices=4,inherited_root_bounds_required=True)

def probe():
    pairs=source_cells=edges=members=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);members+=1
            for flip in (0,1):
                steps=[(j,i,reverse(w)) for i,j,w in path(k,t)] if flip else path(k,t)
                verify(g,flip,steps)
                source=reverse(T2) if flip else T2
                pairs+=len(g.words[source[0]])*len(g.words[source[1]])
                edges+=len(steps);source_cells+=1
    assert (members,source_cells,pairs,edges)==(117,234,50700,496)
    return dict(scope="finite independent exact literal replay",
                members=members,oriented_source_cells=source_cells,
                source_ordered_pairs=pairs,selected_path_edges=edges,
                symbolic=symbolic_proof(),strictness=strict_certificate(),
                selected_exit_depth_at_most=3,all_first_choices_productive=False,
                BH=False,PSC=False)

if __name__=="__main__":
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
