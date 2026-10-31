"""Three exact class-A selected coincidence exits recovered from side-stack packets.

R3, B3 and R5 each have a literal occurrence-indexed path to C.
The algebraic certificate is valid for every integer k,t>=0 in the minus
class-A substitution chamber. Independent literal/Perron replay is finite.
This does not certify any complete outgoing star, every first choice,
forward-closed carrier, universal BH, or PSC.
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import runpy

X, C_LETTER, Y = 0, 1, 2
C = (Y,Y,0,0,0)
Q = (Y,X,0,-1,1)
H1 = (X,Y,0,-1,1)
B = (Y,Y,0,-2,3)
RH = (Y,X,0,1,-1)
R3 = (X,Y,1,-1,0)
B3 = (Y,X,0,-1,0)
R5 = (X,Y,1,-1,-1)
SOURCES = (R3, B3, R5)

def reverse(w):
    return (w[1], w[0], *(-z for z in w[2:]))

@dataclass(frozen=True)
class Aff:
    k: int = 0
    t: int = 0
    c: int = 0
    def __add__(self, o):
        o = asaff(o)
        return Aff(self.k+o.k, self.t+o.t, self.c+o.c)
    __radd__ = __add__
    def __neg__(self):
        return Aff(-self.k,-self.t,-self.c)
    def __sub__(self, o):
        return self + (-asaff(o))
    def __rsub__(self, o):
        return asaff(o) - self
    def __mul__(self, n):
        if not isinstance(n,int):
            raise TypeError("nonlinear symbolic expression")
        return Aff(n*self.k,n*self.t,n*self.c)
    __rmul__ = __mul__

def asaff(x):
    return x if isinstance(x,Aff) else Aff(c=x)

K = Aff(k=1)
T = Aff(t=1)
N = K+T+3
D = K+2*T+5
A = N+D
RUN_LENGTH = {X:A, C_LETTER:N, Y:N-1}

# (top ordinal, bottom ordinal, typed target). Ordinals are symbolic
# affine polynomials in k,t. Only actual FIRST/RUN occur on these routes.
PATHS = {
    R3: ((D,0,Q),(1,2,C)),
    B3: ((0,N+2,H1),(1,2,C)),
    R5: ((T+1,1,B),(N-1,0,RH),(2,1,C)),
}

def certify_nonnegative(expr):
    expr = asaff(expr)
    assert expr.k>=0 and expr.t>=0 and expr.c>=0, (
        "not valid on the whole integer cone",expr)

def prefix(parent, ordinal):
    i=asaff(ordinal)
    if i==Aff():
        return (Aff(),Aff(),Aff()), C_LETTER if parent==C_LETTER else X
    certify_nonnegative(i-1)
    certify_nonnegative(RUN_LENGTH[parent]-i)
    pref=(Aff(),Aff(c=1),i-1) if parent==C_LETTER else (
          Aff(c=1),Aff(),i-1)
    return pref,Y

def certify_edge(source, i, j, target):
    # No special LAST branch is silently treated as a RUN.
    p, top=prefix(source[0],i)
    q, bottom=prefix(source[1],j)
    assert (top,bottom)==target[:2],("actual types",source,i,j,target)
    x,c,y=source[2:]
    M=(2*x+c+y,c+y,A*x+N*c+(N-1)*y)
    want=tuple(M[z]+q[z]-p[z] for z in range(3))
    assert want==tuple(Aff(c=z) for z in target[2:]),(
        "Parikh transport",source,i,j,target,want)

VERTICES = ((Fraction(0),Fraction(0)),
            (Fraction(0),Fraction(1)),
            (Fraction(1,5),Fraction(1,5)),
            (Fraction(1,5),Fraction(3,5)))
LENGTH = ((2,0,1),(1,1,0),(1,0,0))

def certify_strict(w):
    x,c,y=w[2:]
    shift=(2*x+c+y,c,x)  # 1,h,rho coordinates
    left=tuple(a+b for a,b in zip(shift,LENGTH[w[1]]))
    right=tuple(a-b for a,b in zip(LENGTH[w[0]],shift))
    for coeff in (left,right):
        values=[coeff[0]+coeff[1]*h+coeff[2]*rho for h,rho in VERTICES]
        assert min(values)>=0 and any(v>0 for v in values),(
            "strictness not proved on Perron polygon",w,coeff,values)

def symbolic_certificate():
    count=0
    states=set(SOURCES)|{C}
    for source,steps in PATHS.items():
        state=source
        for i,j,target in steps:
            certify_edge(state,i,j,target)
            certify_edge(reverse(state),j,i,reverse(target))
            states.add(target)
            state=target
            count+=2
        assert state==C
    oriented=states|{reverse(w) for w in states}
    for w in oriented:
        certify_strict(w)
    assert len(oriented)==13
    assert count==14
    return dict(families=3,actual_symbolic_edges=count,
                oriented_states=len(oriented),strict_margins=2*len(oriented),
                per_source_path_depth=[len(PATHS[w]) for w in SOURCES],
                inherited_root_bounds_required=True,
                no_all_first_choice_claim=True,universal_BH=False)

def literal_probe(oracle_dir=None):
    src=(Path(oracle_dir) if oracle_dir else Path(__file__).resolve().parent)
    gfun=runpy.run_path(str(src/"class_a_boundary_children.py"))["Geometry"]
    members=edges=0
    for k in range(13):
        for t in range(9):
            members+=1
            g=gfun(-1,k,t)
            for source,steps in PATHS.items():
                for flip in (0,1):
                    current=reverse(source) if flip else source
                    assert g.interior(current)
                    for aa,bb,dest in steps:
                        i=aa.k*k+aa.t*t+aa.c if isinstance(aa,Aff) else aa
                        j=bb.k*k+bb.t*t+bb.c if isinstance(bb,Aff) else bb
                        if flip:
                            i,j=j,i
                            dest=reverse(dest)
                        assert g.child(current,i,j)==dest
                        assert g.interior(dest)
                        current=dest
                        edges+=1
                    assert current==C
    assert (members,edges)==(117,1638)
    return dict(members=members,selected_actual_edge_replays=edges)

if __name__=="__main__":
    import json
    print(json.dumps(symbolic_certificate(),sort_keys=True,indent=2))
    print(json.dumps(literal_probe(),sort_keys=True,indent=2))
