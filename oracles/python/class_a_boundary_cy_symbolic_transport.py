"""Coefficientwise Z[k,t] occurrence/Parikh witness checker for CY tails.

The ten rectangular integer chambers form a disjoint cover of k,t>=0.
This checks actual word-address types and all affine prefix identities
on entire chambers, NOT only finite specimens. Strict Perron geometry
has a separate hand proof and an independent Fraction replay.
No global boundary-hitting, Lean or native Mojo proof credit.
"""
from dataclasses import dataclass
from pathlib import Path
import runpy

every = runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_cy_every_child.py")))


@dataclass(frozen=True)
class Aff:
    k: int = 0
    t: int = 0
    c: int = 0

    def __add__(self, other):
        other=to_aff(other)
        return Aff(self.k+other.k,self.t+other.t,self.c+other.c)

    __radd__=__add__

    def __neg__(self):
        return Aff(-self.k,-self.t,-self.c)

    def __sub__(self, other):
        return self+(-to_aff(other))

    def __rsub__(self, other):
        return to_aff(other)-self

    def __mul__(self, scalar):
        if not isinstance(scalar,int):
            raise TypeError("refuse nonlinear term in affine certificate")
        return Aff(self.k*scalar,self.t*scalar,self.c*scalar)

    __rmul__=__mul__


def to_aff(x):
    return x if isinstance(x,Aff) else Aff(c=x)


@dataclass
class SampledAffine:
    expr: Aff
    example: int

    def __add__(self, x):
        x=to_sampled(x)
        return SampledAffine(self.expr+x.expr,self.example+x.example)

    __radd__=__add__

    def __sub__(self, x):
        x=to_sampled(x)
        return SampledAffine(self.expr-x.expr,self.example-x.example)

    def __rsub__(self, x):
        return to_sampled(x)-self

    def __mul__(self, scalar):
        if not isinstance(scalar,int):
            raise TypeError("nonlinear sampled-index expression")
        return SampledAffine(self.expr*scalar,self.example*scalar)

    __rmul__=__mul__

    def __eq__(self, other):
        return self.example==(other.example if isinstance(other,SampledAffine) else other)

    def __ge__(self, other):
        return self.example>=(other.example if isinstance(other,SampledAffine) else other)


def to_sampled(x):
    return x if isinstance(x,SampledAffine) else SampledAffine(to_aff(x),x)


@dataclass(frozen=True)
class Chamber:
    k0: int
    t0: int
    k_fixed: bool
    t_fixed: bool

    def simplify(self, expression):
        e=to_aff(expression)
        return Aff(0 if self.k_fixed else e.k,
                   0 if self.t_fixed else e.t,
                   e.c+(e.k*self.k0 if self.k_fixed else 0)
                      +(e.t*self.t0 if self.t_fixed else 0))

    def nonnegative(self, expression):
        e=self.simplify(expression)
        # Because k and t are lower-bounded, a negative coefficient
        # in either free coordinate invalidates an all-parameter guard.
        assert e.k>=0 and e.t>=0, ("negative recession slope",self,e)
        assert e.k*self.k0+e.t*self.t0+e.c>=0, (
            "index guard negative at chamber corner",self,e)


class SymbolicGeometry:
    def __init__(self, chamber):
        self.k=SampledAffine(Aff(k=1),chamber.k0)
        self.t=SampledAffine(Aff(t=1),chamber.t0)
        self.n=self.k+self.t+3
        self.d=2*self.n-1-self.k


def word_prefix(chamber, letter, address, A, n, N):
    i=chamber.simplify(to_sampled(address).expr)
    runlen={0:A,1:n,2:N}[letter]
    last=runlen+1
    if i==Aff():
        return ("first",(Aff(),Aff(),Aff()),1 if letter==1 else 0)
    if chamber.simplify(i-last)==Aff():
        prefix={
            0:(Aff(c=1),Aff(),A),
            1:(Aff(),Aff(c=1),n),
            2:(Aff(c=1),Aff(),N)
        }[letter]
        return ("last",prefix,1 if letter==2 else 0)
    chamber.nonnegative(i-1)
    chamber.nonnegative(runlen-i)
    return ("run",
            (Aff(),Aff(c=1),i-1) if letter==1 else
            (Aff(c=1),Aff(),i-1),
            2)


# Disjoint rectangular k,t>=0 partition. 'Free' starts at the
# displayed lower corner; fixed coordinates are substituted exactly.
CHAMBERS=(
    Chamber(0,0,True,True),
    Chamber(1,0,False,True),
    Chamber(0,1,True,True),
    Chamber(1,1,True,True),
    Chamber(2,1,True,True),
    Chamber(3,1,False,True),
    Chamber(0,2,True,False),
    Chamber(1,2,True,False),
    Chamber(2,2,True,False),
    Chamber(3,2,False,False),
)


def verify_one(chamber,label):
    g=SymbolicGeometry(chamber)
    k,t,n,d=(g.k.expr,g.t.expr,g.n.expr,g.d.expr)
    A=n+d
    N=n-1
    current=label
    steps=every["tail"](label,g)
    for i,j,expected in steps:
        _,top_prefix,top_type=word_prefix(chamber,current[0],i,A,n,N)
        _,bottom_prefix,bottom_type=word_prefix(chamber,current[1],j,A,n,N)
        x,c,y=current[2:]
        want=(
            top_type,bottom_type,
            2*x+c+y+bottom_prefix[0]-top_prefix[0],
            c+y+bottom_prefix[1]-top_prefix[1],
            A*x+n*c+N*y+bottom_prefix[2]-top_prefix[2],
        )
        actual=(want[0],want[1],
                *(chamber.simplify(z) for z in want[2:]))
        expected_aff=(expected[0],expected[1],
                      *(Aff(c=z) for z in expected[2:]))
        assert actual==expected_aff, (
            "symbolic Parikh or actual child-type mismatch",
            chamber,current,i,j,actual,expected_aff)
        current=expected
    assert current==every["C"]
    return len(steps)


def prove_all_affine_occurrences():
    branches=edges=0
    max_tail_depth=0
    for chamber in CHAMBERS:
        for label in sorted(every["CHILD_LABELS"]):
            length=verify_one(chamber,label)
            branches+=1
            edges+=length
            max_tail_depth=max(max_tail_depth,length)
    assert branches==60
    assert max_tail_depth==6
    return dict(chamber_cases=len(CHAMBERS),source_cases=branches,
                symbolic_selected_edges=edges,max_tail_depth=max_tail_depth,
                source="exact affine integer identities and actual word index guards",
                strict_geometry="separate hand inequality and finite independent exact replay",
                all_later_choices_productive=False,
                universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(prove_all_affine_occurrences(),indent=2,sort_keys=True))
