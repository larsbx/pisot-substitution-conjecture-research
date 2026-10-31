"""Focused B4/R4 selected coincidence exits, without old research stacks.

All actual occurrence types, word bounds, full Parikh coordinates, and
strict physical overlaps are certified for all integer k,t>=0 in minus
class A. Finite independent Fraction replay is a separate regression.
Not complete-star or every-first-choice productivity; not global BH/PSC.
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import runpy

X,C_LETTER,Y=0,1,2
C=(Y,Y,0,0,0)
Q=(Y,X,0,-1,1)
RH=(Y,X,0,1,-1)
H=(X,Y,0,1,-1)
D0=(X,X,-1,-2,3)
DXR=(X,X,-1,-2,4)
RK=(X,Y,1,2,-5)
RL=(X,Y,0,-3,4)
F4=(X,Y,-1,-2,4)
E4=(X,C_LETTER,0,-3,3)
D4=(X,Y,0,-3,3)
Y4=(X,Y,1,0,-1)
B4=(Y,X,0,-1,-1)
R4=(X,Y,1,-1,-2)
SOURCES=(B4,R4)

def reverse(w):return (w[1],w[0],*(-a for a in w[2:]))

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
    def __mul__(self,n):
        if not isinstance(n,int):raise TypeError('nonaffine term')
        return Aff(self.k*n,self.t*n,self.c*n)
    __rmul__=__mul__

def aff(x):return x if isinstance(x,Aff) else Aff(c=x)
K=Aff(k=1)
T=Aff(t=1)
N=K+T+3
D=K+2*T+5
A=N+D
LENS={X:A,C_LETTER:N,Y:N-1}

@dataclass(frozen=True)
class Chamber:
    name:str
    tmin:int
    fixed_t:bool
    def simp(self,e):
        e=aff(e)
        return Aff(e.k,0 if self.fixed_t else e.t,
                   e.c+(e.t*self.tmin if self.fixed_t else 0))
    def nonnegative(self,e):
        e=self.simp(e)
        assert e.k>=0 and e.t>=0,('negative unbounded slope',self,e)
        assert e.c+e.t*self.tmin>=0,('negative at corner',self,e)

CHAMBERS=(Chamber('t=0',0,True),Chamber('t=1',1,True),
          Chamber('t>=2',2,False))

def paths(source,ch):
    n,d,A=N,D,N+D
    if source==B4:
        if ch.name=='t=0':return ((0,A+1,D0),(0,d+3,H),(2,1,C))
        if ch.name=='t=1':return ((0,A+1,DXR),(0,T+2,RK),
                                (0,K+1,RL),(n-2,0,RH),(2,1,C))
        return ((0,2*n+4,F4),(0,T+2,RK),(0,K+1,RL),
                (n-2,0,RH),(2,1,C))
    if source==R4:
        if ch.name=='t=0':return ((0,n,E4),(0,3,H),(2,1,C))
        if ch.name=='t=1':return ((0,K+3,D4),(0,3,Y4),(d+1,0,Q),(1,2,C))
        return ((0,K+4,RL),(n-2,0,RH),(2,1,C))
    raise ValueError('unregistered source')

def prefix(ch,letter,index):
    i=ch.simp(index)
    length=LENS[letter]
    if i==Aff():
        return (Aff(),Aff(),Aff()),(C_LETTER if letter==C_LETTER else X)
    if ch.simp(i-length-1)==Aff():
        p={X:(Aff(c=1),Aff(),A),
           C_LETTER:(Aff(),Aff(c=1),N),
           Y:(Aff(c=1),Aff(),N-1)}[letter]
        return p, (C_LETTER if letter==Y else X)
    ch.nonnegative(i-1)
    ch.nonnegative(length-i)
    p=(Aff(),Aff(c=1),i-1) if letter==C_LETTER else (
        Aff(c=1),Aff(),i-1)
    return p,Y

def certify_edge(ch,source,i,j,target):
    p,top=prefix(ch,source[0],i)
    q,bottom=prefix(ch,source[1],j)
    assert (top,bottom)==target[:2],('wrong typed FIRST/RUN/LAST',ch,source,i,j,target)
    x,c,y=source[2:]
    out=(2*x+c+y,c+y,A*x+N*c+(N-1)*y)
    got=tuple(ch.simp(out[z]+q[z]-p[z]) for z in range(3))
    assert got==tuple(Aff(c=v) for v in target[2:]),('Parikh mismatch',ch,source,i,j,target,got)

VERTICES=((Fraction(0),Fraction(0)),(Fraction(0),Fraction(1)),
          (Fraction(1,5),Fraction(1,5)),(Fraction(1,5),Fraction(3,5)))
LENGTHS=((2,0,1),(1,1,0),(1,0,0))

def certify_strict(w):
    x,c,y=w[2:]
    shift=(2*x+c+y,c,x)
    lower=tuple(a+b for a,b in zip(shift,LENGTHS[w[1]]))
    upper=tuple(a-b for a,b in zip(LENGTHS[w[0]],shift))
    for coeff in (lower,upper):
        vals=[coeff[0]+coeff[1]*h+coeff[2]*rho for h,rho in VERTICES]
        assert min(vals)>=0 and any(v>0 for v in vals),('not strictly interior',w,coeff,vals)

def symbolic_certificate():
    states=set(SOURCES)|{C}
    edges=0
    depths={}
    for source in SOURCES:
        for ch in CHAMBERS:
            state=source
            steps=paths(source,ch)
            depths[(source,ch.name)]=len(steps)
            for i,j,target in steps:
                certify_edge(ch,state,i,j,target)
                certify_edge(ch,reverse(state),j,i,reverse(target))
                states.add(target)
                edges+=2
                state=target
            assert state==C
    oriented=states|{reverse(w) for w in states}
    for w in oriented:certify_strict(w)
    assert edges==46
    return dict(sources=2,integer_chambers=3,source_chamber_cases=6,
                directed_symbolic_edge_checks=edges,oriented_labels=len(oriented),
                strict_margins=2*len(oriented),
                longest_path=max(depths.values()),
                inherited_root_bounds_required=True,
                complete_stars_not_imported=True,BH=False)

def literal_probe(oracle_dir=None):
    src=Path(oracle_dir) if oracle_dir else Path(__file__).resolve().parent
    Geometry=runpy.run_path(str(src/'class_a_boundary_children.py'))['Geometry']
    edges=members=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            members+=1
            chamber=CHAMBERS[0] if t==0 else CHAMBERS[1] if t==1 else CHAMBERS[2]
            for source in SOURCES:
                for flip in (0,1):
                    current=reverse(source) if flip else source
                    assert g.interior(current)
                    for aa,bb,dest in paths(source,chamber):
                        i=aa.k*k+aa.t*t+aa.c if isinstance(aa,Aff) else aa
                        j=bb.k*k+bb.t*t+bb.c if isinstance(bb,Aff) else bb
                        if flip:i,j,dest=j,i,reverse(dest)
                        assert g.child(current,i,j)==dest,('literal child mismatch',k,t,current,i,j,dest)
                        assert g.interior(dest),('noninterior',k,t,dest)
                        current=dest
                        edges+=1
                    assert current==C
    assert (members,edges)==(117,1846)
    return dict(specimens=members,selected_actual_edge_replays=edges)

if __name__=='__main__':
    import json
    print(json.dumps(symbolic_certificate(),indent=2,sort_keys=True))
    print(json.dumps(literal_probe(),indent=2,sort_keys=True))
