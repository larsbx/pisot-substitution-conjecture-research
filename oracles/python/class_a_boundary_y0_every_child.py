"""Every indexed Y0 first choice has a short selected coincidence continuation.

Scope: minus class-A k,t >= 0. The complete Y0 star is already proven
in the #412 carrier. This is independent finite literal-word/Fraction
replay of the new selected paths, not a finite-to-universal inference.
"""
from pathlib import Path
from fractions import Fraction as F
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name("class_a_boundary_children.py")))["Geometry"]
Y0=(2,2,1,-1,-1)
C=(2,2,0,0,0)
A3=(0,0,0,-2,3)
A4=(0,0,0,-2,4)
K3=(2,0,-1,-2,3)
K4=(2,0,-1,-2,4)
K5=(2,0,-1,-2,5)
D2=(2,2,0,-2,2)
D3=(2,2,0,-2,3)
CY=(1,2,0,-2,2)
CY3=(1,2,0,-2,3)
CC=(1,1,0,-2,3)
CHILDREN={A3,A4,K3,K4,K5,D2,D3,CY,CY3,CC}
Q=(2,0,0,-1,1)
RH=(2,0,0,1,-1)
H=(0,2,0,1,-1)
H1=(0,2,0,-1,1)
J=(2,2,0,2,-2)


def reverse(w):
    return (w[1],w[0],*(-x for x in w[2:]))


def tail(label,g):
    """Construct actual indexed edges, respecting all parameter endpoints."""
    k,t,n,d=g.k,g.t,g.n,g.d
    A=n+d
    if label==A3:
        assert t==0
        return [(n-1,0,RH),(2,1,C)]
    if label==A4:
        assert t==1
        return [(A-2,0,(2,0,1,2,-4)),(t+2,0,K5),
                (k+1,0,(2,0,0,3,-4)),(0,n-2,H1),(1,2,C)]
    if label==K3:
        return [(0,d+3,H),(2,1,C)]
    if label==K4:
        assert t>=1
        return [(1,t+5,J),(3,1,C)]
    if label==K5:
        assert t>=2
        if k==0:
            return [(0,0,(0,0,1,3,-4)),(d+4,0,Q),(1,2,C)]
        return [(k,0,(2,0,0,3,-3)),(4,1,C)]
    if label==D2:
        if n==3:
            return [(0,2,(0,2,1,0,-1)),(d+1,0,Q),(1,2,C)]
        return [(1,3,C)]
    if label==D3:
        return [(n-1,0,RH),(2,1,C)]
    if label==CY:
        return [(0,1,(1,2,1,0,-2)),(t+2,0,(2,0,0,-3,3)),(1,4,C)]
    if label==CY3:
        assert t>=1
        first=[(n,0,(2,0,1,0,-2))]
        if k==0:
            return first+[(t+3,1,CY)]+tail(CY,g)
        return first+[(t+3,1,D2),(1,3,C)]
    if label==CC:
        assert t==0
        return [(n+1,2,(0,2,1,1,-2)),(d+2,0,Q),(1,2,C)]
    raise ValueError("not a classified Y0 child")


def first_choice(label,g):
    n,t,k=g.n,g.t,g.k
    if label in (A3,A4):return (0,0,label)
    if label==K3:return (t+1,0,label)
    if label==K4:return (t,0,label)
    if label==K5:return (t-1,0,label)
    if label==D2:return (t+2,1,label)
    if label==D3:return (t+1,1,label)
    if label==CY:return (n,k+2,label)
    if label==CY3:return (n,k+3,label)
    if label==CC:return (n,n,label)
    raise ValueError("unknown Y0 child")


def verify(g,start,steps):
    state=start
    assert g.interior(state)
    for i,j,w in steps:
        got=g.child(state,i,j)
        assert got==w,("typed or Parikh transport mismatch",g.k,g.t,state,i,j,got,w)
        assert g.interior(got),("not strict",g.k,g.t,state,i,j,w)
        state=got
    assert state==C,("wrong terminal",state)


VERTICES=((F(0),F(0)),(F(0),F(1)),
          (F(1,5),F(1,5)),(F(1,5),F(3,5)))


def certify_strict(w):
    x,c,y=w[2:]
    shift=(2*x+c+y,c,x)
    lengths=((2,0,1),(1,1,0),(1,0,0))
    bottom,top=lengths[w[1]],lengths[w[0]]
    margins=(tuple(a+b for a,b in zip(shift,bottom)),
             tuple(a-b for a,b in zip(top,shift)))
    for linear in margins:
        vals=[linear[0]+linear[1]*h+linear[2]*rho for h,rho in VERTICES]
        # A nonzero affine functional nonnegative at every vertex of
        # the closed polygon is positive on the open chamber.
        assert min(vals)>=0 and any(z>0 for z in vals),(w,linear,vals)


def strict_path_certificate():
    labels={Y0,*CHILDREN}
    for k,t in ((0,0),(1,0),(0,1),(1,1),(0,2),(1,2)):
        g=Geometry(-1,k,t)
        for w in {w for _,_,w in g.edges(Y0)}:
            labels.update(z for _,_,z in tail(w,g))
    assert len(labels)==26
    all_oriented=labels|{reverse(w) for w in labels}
    assert len(all_oriented)==45
    for w in all_oriented:certify_strict(w)
    return dict(base_labels=len(labels),oriented_labels=len(all_oriented),
                universal_exact_strict_margins=2*len(all_oriented),
                inherited_root_hypotheses=True)


def probe():
    members=source_cells=pairs=accepted=path_edges=0
    maximum=0
    max_cases=[]
    observed=set()
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            edges=set(g.edges(Y0))
            labels={w for _,_,w in edges}
            assert labels<=CHILDREN,("unregistered target",k,t,labels-CHILDREN)
            assert len(edges)==2*k+8-(t==0)
            observed.update(labels)
            for i,j,w in edges:
                steps=[(i,j,w)]+tail(w,g)
                verify(g,Y0,steps)
                reversed_path=[(b,a,reverse(z)) for a,b,z in steps]
                verify(g,reverse(Y0),reversed_path)
                accepted+=2
                path_edges+=2*len(steps)
                if len(steps)>maximum:
                    maximum=len(steps)
                    max_cases=[(k,t,i,j,w)]
                elif len(steps)==maximum and len(max_cases)<8:
                    max_cases.append((k,t,i,j,w))
            pairs+=2*len(g.words[2])**2
            members+=1
            source_cells+=2
    assert observed==CHILDREN
    assert (members,source_cells,pairs,accepted,path_edges,maximum)==(
        117,234,50700,4654,12920,6)
    return dict(scope="finite literal-word/Fraction replay, universal proof separately symbolic",
                members=members,source_cells=source_cells,pairs=pairs,
                accepted_indexed_first_choices=accepted,
                composed_path_edges=path_edges,
                selected_max_depth=maximum,max_witnesses=max_cases,
                chamber_union_child_labels=len(observed),
                strictness_certificate=strict_path_certificate(),
                every_first_choice_selected_exit=True,
                all_later_choices_productive=False,
                forward_closed=False,universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True,default=list))
