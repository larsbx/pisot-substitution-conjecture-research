"""Independent sparse-integral-polynomial oracle for both class-A signs.

The canonical computation is Mojo. This oracle is deliberately independent
of psc.param_poly and checks identities in Z[n,d,h,k,c,y], not samples.
"""
from collections import defaultdict
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
CARRIER=ROOT/"kernel/psc/class_a_typed_carrier.mojo"
DIMS=6


class Poly:
    def __init__(self, coeff=None):
        if isinstance(coeff,Poly):
            self.terms=coeff.terms.copy()
        elif isinstance(coeff,int):
            self.terms={} if not coeff else {(0,)*DIMS: coeff}
        else:
            self.terms={k:v for k,v in (coeff or {}).items() if v}
    @classmethod
    def variable(cls,index):
        powers=[0]*DIMS
        powers[index]=1
        return cls({tuple(powers):1})
    def __add__(self,other):
        other=Poly(other)
        out=defaultdict(int,self.terms)
        for k,v in other.terms.items():
            out[k]+=v
        return Poly(out)
    __radd__=__add__
    def __neg__(self):
        return Poly({k:-v for k,v in self.terms.items()})
    def __sub__(self,other):
        return self+-Poly(other)
    def __rsub__(self,other):
        return Poly(other)-self
    def __mul__(self,other):
        other=Poly(other)
        out=defaultdict(int)
        for key,val in self.terms.items():
            for key2,val2 in other.terms.items():
                out[tuple(a+b for a,b in zip(key,key2))]+=val*val2
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,power):
        assert isinstance(power,int) and power>=0
        out=Poly(1)
        for _ in range(power):out=out*self
        return out
    def __eq__(self,other):
        return self.terms==Poly(other).terms
    def __repr__(self):
        return repr(sorted(self.terms.items()))


n,d,h,k,c,y=[Poly.variable(i) for i in range(DIMS)]


def class_a(sign):
    assert sign in (-1,1)
    F=1-(n+sign)*h-(n+d+1-sign)*h*h-d*h**3
    L=(1+(d+1-sign)*h+d*h*h,1+(1-sign)*h,1+h)
    M=((2,1,1),(0,1,1),(n+d,n,n+sign))
    assert all(h*sum((M[row][col]*L[row] for row in range(3)),Poly(0))-(1+h)*L[col]==-F
               for col in range(3))
    fhom=(1+h)**3-(n+sign+3)*h*(1+h)**2+(2+n+3*sign-d)*h*h*(1+h)-2*sign*h**3
    assert fhom==F
    assert L[0]-L[1]==d*h*(1+h)
    assert L[2]-L[1]==sign*h
    s=k+c+y
    geom=L[0]*k+L[1]*c+L[2]*y
    assert geom==L[1]*s+d*k*h*(1+h)+sign*y*h
    Mw=(2*k+c+y,c+y,(n+d)*k+n*c+(n+sign)*y)
    assert Mw==(k+s,s-k,n*s+d*k+sign*y)
    assert sum(Mw,Poly(0))==(n+2)*s+d*k+sign*y
    return F,L,M


def d2_witness():
    F,L,M=class_a(1)
    p2=Poly({tuple([0,2,0,0,0,0]):0}) # exact zero, no special case
    # Substitute d=2 (the d polynomial is linear).
    def at_gap(two_parameter_poly,gap):
        out=defaultdict(int)
        for powers,coeff in two_parameter_poly.terms.items():
            exp=list(powers)
            count=exp[1]
            exp[1]=0
            out[tuple(exp)]+=coeff*gap**count
        return Poly(out)
    F2=at_gap(F,2)
    ncase=Poly.variable(0)
    root=1-(ncase+1)*h-(ncase+2)*h*h-2*h**3
    assert F2==root
    # The row [2,2,0,-2,-1,0,0,0] includes k=-n, c=n+2.
    raw=at_gap(L[1],2)+2*(-n)*h*(1+h)-2*h
    reduced=-1+h+4*h*h+4*h**3
    assert raw==reduced+2*F2
    # f_n(0)=1, f_n(1/5)=(88-30n)/125<0 for n>=4.
    # f_n strictly decreases at positive h. Hence 0<h<1/5.
    assert 88-30*4<0
    # reduced(h)<-1+1/5+4/25+4/125 = -76/125 <0.
    assert -125+25+20+4==-76
    row=(2,2,0,-2,-1,0,0,0)
    matches=re.findall(r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\),$",
                       CARRIER.read_text(),re.MULTILINE)
    assert row in {tuple(map(int,m.split(","))) for m in matches}
    return {"typed_row":row,"uniform_n_floor":4,"margin_upper_numerator":-76,
            "status":"not a strict overlap in d=2 plus, no hitting conclusion"}


if __name__=="__main__":
    import json
    for sign in (-1,1):class_a(sign)
    print(json.dumps({"signs_checked":[-1,1],"witness":d2_witness(),
                      "scope":"coefficient identities and non-transfer only"},indent=2))
