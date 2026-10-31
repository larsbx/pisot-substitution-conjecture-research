"""All actual CC first-choice children have selected typed-coincidence exits.

The selected occurrence-indexed paths are given by a separate
eight-chamber symbolic hand derivation. This module independently replays
literal words, integer Parikh transport, exact Fraction/Perron geometry,
and actual reversals on 117 specimens. It is not a universal BH proof.
"""
from pathlib import Path
import runpy
from fractions import Fraction as F

old=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_cc_children.py")))
Geometry=old["Geometry"]
CC,C=old["CC"],old["C"]
YC,XC,XY3,XY2=old["YC"],old["XC"],old["XY3"],old["XY2"]
Q=old["Q"]
reverse=old["reverse"]
CHILD_LABELS={YC,XC,XY3,XY2}
J=(2,2,0,2,-2)
H=(0,2,0,1,-1)
H1=(0,2,0,-1,1)
Z=(2,2,0,-2,2)


def tail(label,g):
    k,t,n,d=g.k,g.t,g.n,g.d
    A=n+d
    if label==YC:
        return [(t+1,0,(2,1,-1,-2,4)),
                (0,t+4,(0,0,0,3,-3) if k==0 else (0,2,0,3,-3)),
                (4,1,C)]
    if label==XC:
        if k==0:
            first=(0,0,-1,-2,5) if t==0 else (0,2,-1,-2,5)
            third=(0,0,0,-1,1) if t==0 else Q
            return [(0,4,first),(0,0,(0,0,1,3,-4)),
                    (d+4,0,third),(1,2,C)]
        if k==1:
            return [(0,4,(0,2,-1,-2,4)),
                    (0,n,(0,1,1,2,-3)),
                    (d+4,1,C)]
        if k==2:
            first=(0,0,-1,-2,5) if t==0 else (0,2,-1,-2,5)
            return [(0,6,first),(2,0,(2,0,0,3,-3)),(4,1,C)]
        return [(0,k+3,(0,2,-1,-2,4)),(1,t+5,J),(3,1,C)]
    if label==XY3:
        out=[(t+4,1,Z)]
        if n==3:
            out.extend([(0,2,(0,2,1,0,-1)),(d+1,0,Q),(1,2,C)])
        else:
            out.append((1,3,C))
        return out
    if label==XY2:
        return [(d+2,0,Q),(1,2,C)]
    raise ValueError("no certified CC child label")


def verify_path(g,start,steps):
    current=start
    for i,j,target in steps:
        if not (g.interior(current) and
                g.child(current,i,j)==target and
                g.interior(target)):
            raise ValueError(("invalid typed strict occurrence",current,i,j,target))
        current=target
    if current!=C:
        raise ValueError("terminal not y/y offset-zero")


# Exact affine signs in h=1/beta, rho=alpha-h.
# The inherited root bounds imply the *open* convex polygon
# 0<h<1/5, h<rho, rho+2h<1, and all normalized overlap
# margins are affine. Its rational closure vertices suffice.
VERTICES=((F(0),F(0)),(F(0),F(1)),
          (F(1,5),F(1,5)),(F(1,5),F(3,5)))


def length_coeff(letter):
    return ((2,0,1),(1,1,0),(1,0,0))[letter]


def shift_coeff(w):
    x,c,y=w[2:]
    return (2*x+c+y,c,x)


def margins(w):
    s=shift_coeff(w)
    Lb=length_coeff(w[1])
    Lt=length_coeff(w[0])
    return (tuple(a+b for a,b in zip(s,Lb)),
            tuple(a-b for a,b in zip(Lt,s)))


def certify_strict(w):
    for linear in margins(w):
        values=[F(linear[0])+linear[1]*h+linear[2]*rho
                for h,rho in VERTICES]
        # A nonzero affine functional nonnegative at every
        # closure vertex is strictly positive in the open polygon.
        if min(values)<0 or not any(x>0 for x in values):
            raise AssertionError(("strict margin not universal",w,linear,values))


def certified_state_image():
    labels={CC,*CHILD_LABELS}
    for k,t in ((0,0),(0,1),(1,0),(1,1),
                (2,0),(2,1),(3,0),(3,1)):
        g=Geometry(-1,k,t)
        for w in CHILD_LABELS:
            labels.update(z for _,_,z in tail(w,g))
    return labels


def symbolic_geometry_certificate():
    base=certified_state_image()
    assert len(base)==20
    oriented=base|{reverse(w) for w in base}
    assert len(oriented)==37
    for state in oriented:
        certify_strict(state)
    return dict(base_states=len(base),oriented_states=len(oriented),
                strict_margins=2*len(oriented),rational_vertices=4,
                inherited_root_bounds=True,forward_closed=False,
                universal_BH=False)


def probe():
    count=dict(members=0,source_cells=0,pairs=0,
               indexed_first_choices=0,composed_path_edges=0,
               max_full_depth=0)
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            base=set(g.edges(CC))
            assert len(base)==4 and {w for _,_,w in base}==CHILD_LABELS
            count["members"]+=1
            for flip in (0,1):
                source=reverse(CC) if flip else CC
                actual=set(g.edges(source))
                expected={(j,i,reverse(w)) for i,j,w in base} if flip else base
                assert actual==expected
                count["source_cells"]+=1
                count["pairs"]+=len(g.words[source[0]])*len(g.words[source[1]])
                for i,j,w in sorted(actual):
                    target=reverse(w) if flip else w
                    selected=tail(target,g)
                    steps=[(q,p,reverse(x)) for p,q,x in selected] if flip else selected
                    verify_path(g,w,steps)
                    verify_path(g,source,[(i,j,w)]+steps)
                    total=1+len(steps)
                    assert total<=5
                    count["indexed_first_choices"]+=1
                    count["composed_path_edges"]+=total
                    count["max_full_depth"]=max(count["max_full_depth"],total)
    assert (count["members"],count["source_cells"],count["pairs"])==(117,234,57486)
    assert (count["indexed_first_choices"],count["composed_path_edges"],
            count["max_full_depth"])==(936,3298,5)
    return dict(scope="finite independent exact replay; universal source follows a separate chamber proof",
                **count,universal_strict_geometry=symbolic_geometry_certificate(),
                every_first_choice_has_selected_exit=True,
                every_later_choice_productivity=False,
                forward_closed=False,universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
