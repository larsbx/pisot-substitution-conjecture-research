"""Exact all-parameter Z[k,t] certificate for every Y0 first-choice tail.

Six disjoint rectangular integer chambers cover the minus family.
Each of forty applicable source/chamber paths is checked coefficientwise
from Y0 through actual typed word occurrences to coincidence. Physical
strictness is independently checked by an exact rational-polytope
certificate in class_a_boundary_y0_every_child.py. No global BH claim.
"""
from dataclasses import dataclass
from pathlib import Path
import runpy

every=runpy.run_path(str(Path(__file__).with_name("class_a_boundary_y0_every_child.py")))


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
        if not isinstance(n,int):
            raise TypeError("nonaffine polynomial in certificate")
        return Aff(self.k*n,self.t*n,self.c*n)
    __rmul__=__mul__


def aff(x):
    return x if isinstance(x,Aff) else Aff(c=x)


class Sampled:
    """Exact affine expression with a representative for case selection."""
    def __init__(self,expr,example):
        self.expr=aff(expr)
        self.example=example
    def __add__(self,x):
        x=sample(x)
        return Sampled(self.expr+x.expr,self.example+x.example)
    __radd__=__add__
    def __neg__(self):
        return Sampled(-self.expr,-self.example)
    def __sub__(self,x):
        return self+(-sample(x))
    def __rsub__(self,x):
        return sample(x)-self
    def __mul__(self,n):
        return Sampled(self.expr*n,self.example*n)
    __rmul__=__mul__
    def __eq__(self,x):
        return self.example==(x.example if isinstance(x,Sampled) else x)
    def __ge__(self,x):
        return self.example>=(x.example if isinstance(x,Sampled) else x)


def sample(x):
    return x if isinstance(x,Sampled) else Sampled(x,x)


@dataclass(frozen=True)
class Chamber:
    k0:int
    t0:int
    k_fixed:bool
    t_fixed:bool

    def simplify(self,e):
        e=aff(e)
        return Aff(0 if self.k_fixed else e.k,
                   0 if self.t_fixed else e.t,
                   e.c+(e.k*self.k0 if self.k_fixed else 0)
                      +(e.t*self.t0 if self.t_fixed else 0))

    def nonnegative(self,e):
        e=self.simplify(e)
        # No negative coefficient in a free unbounded integer direction.
        assert e.k>=0 and e.t>=0,("negative recession slope",self,e)
        assert e.k*self.k0+e.t*self.t0+e.c>=0,(
            "negative at chamber corner",self,e)


CHAMBERS=(
    Chamber(0,0,True,True),
    Chamber(1,0,False,True),
    Chamber(0,1,True,True),
    Chamber(1,1,False,True),
    Chamber(0,2,True,False),
    Chamber(1,2,False,False),
)


class SymbolicGeometry:
    def __init__(self,chamber):
        self.k=Sampled(Aff(k=1),chamber.k0)
        self.t=Sampled(Aff(t=1),chamber.t0)
        self.n=self.k+self.t+3
        self.d=2*self.n-1-self.k


def applicable(chamber):
    if chamber.t0==0:
        return {every["A3"],every["K3"],every["D2"],every["D3"],
                every["CY"],every["CC"]}
    if chamber.t0==1:
        return {every["A4"],every["K3"],every["K4"],every["D2"],
                every["D3"],every["CY"],every["CY3"]}
    return {every["K3"],every["K4"],every["K5"],every["D2"],
            every["D3"],every["CY"],every["CY3"]}


def prefix(chamber,letter,index,n,d):
    i=chamber.simplify(sample(index).expr)
    A=n+d
    N=n-qx_const_one()
    runlen={0:A,1:n,2:N}[letter]
    if i==Aff():
        return [Aff(),Aff(),Aff()],(1 if letter==1 else 0)
    if chamber.simplify(i-(runlen+1))==Aff():
        p={0:[Aff(c=1),Aff(),A],
           1:[Aff(),Aff(c=1),n],
           2:[Aff(c=1),Aff(),N]}[letter]
        return p,(1 if letter==2 else 0)
    chamber.nonnegative(i-1)
    chamber.nonnegative(runlen-i)
    p=[Aff(),Aff(c=1),i-1] if letter==1 else [Aff(c=1),Aff(),i-1]
    return p,2


def qx_const_one():
    return Aff(c=1)


def certify_path(chamber,label):
    g=SymbolicGeometry(chamber)
    A=g.n.expr+g.d.expr
    N=g.n.expr-1
    first=every["first_choice"](label,g)
    steps=[first]+every["tail"](label,g)
    state=every["Y0"]
    for i,j,target in steps:
        pt,top_type=prefix(chamber,state[0],i,g.n.expr,g.d.expr)
        pb,bottom_type=prefix(chamber,state[1],j,g.n.expr,g.d.expr)
        assert target[:2]==(top_type,bottom_type),(
            "literal FIRST/RUN/LAST type mismatched",chamber,state,i,j,target)
        x,c,y=state[2:]
        image=(2*x+c+y,c+y,A*x+g.n.expr*c+N*y)
        offsets=tuple(chamber.simplify(image[q]+pb[q]-pt[q]) for q in range(3))
        assert offsets==tuple(Aff(c=z) for z in target[2:]),(
            "symbolic proper-prefix Parikh transport mismatch",
            chamber,state,i,j,target,offsets)
        state=target
    assert state==every["C"],("not typed coincidence",chamber,label,state)
    return len(steps)


def prove_all_affine_occurrences():
    paths=edges=0
    maximum=0
    for chamber in CHAMBERS:
        for label in sorted(applicable(chamber)):
            depth=certify_path(chamber,label)
            paths+=1
            edges+=depth
            maximum=max(maximum,depth)
    assert (paths,edges,maximum)==(40,139,6)
    return dict(integer_chambers=len(CHAMBERS),
                complete_source_target_cases=paths,
                checked_occurrence_edges=edges,
                maximum_source_depth=maximum,
                full_Z_k_t_Parikh_identities=True,
                all_word_bounds_and_actual_types=True,
                strict_geometry="separately proved under inherited Perron root bounds",
                finite_specimens_not_universal_proof=True,
                forward_closed=False,universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(prove_all_affine_occurrences(),indent=2,sort_keys=True))
