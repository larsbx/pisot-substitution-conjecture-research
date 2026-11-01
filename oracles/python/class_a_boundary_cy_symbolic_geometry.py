"""Exact universal linear Perron-guard certificate for CY selected tails.

On the minus class-A chamber h=1/beta, rho=alpha-h satisfy
0<h<1/5, h<rho, rho+2h<1. Strict geometry for each finite
constant typed overlap label is linear in h,rho. Prove positivity
on this open rational polytope by its four exact closure vertices.
This is not a proof of the inherited root bracket, source closure,
all-later choices, BH or PSC.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import sys

SRC=Path(__file__).with_name("class_a_boundary_cy_symbolic_transport.py")
spec=importlib.util.spec_from_file_location("_cy_affine_source_geometry",SRC)
symbolic=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=symbolic
spec.loader.exec_module(symbolic)

every=symbolic.every
# Vertices of the closure of 0<h<1/5, h<rho, rho+2h<1.
# (h,rho) exactly rational, no numerical root or floating approximation.
VERTICES=((F(0),F(0)),(F(0),F(1)),
          (F(1,5),F(1,5)),(F(1,5),F(3,5)))


def length_coeff(letter):
    if letter==0: return (2,0,1) # Lx=2+rho
    if letter==1: return (1,1,0) # Lc=1+h
    if letter==2: return (1,0,0) # Ly=1
    raise ValueError("unknown tile type")


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def neg(a):
    return tuple(-x for x in a)


def shift_coeff(w):
    x,c,y=w[2:]
    return (2*x+c+y,c,x) # exact in basis (1,h,rho)


def margin_coeff(w):
    top,bottom=w[:2]
    s=shift_coeff(w)
    return (add(s,length_coeff(bottom)),
            add(length_coeff(top),neg(s)))


def evaluate(coeff,vertex):
    h,rho=vertex
    c,dh,dr=coeff
    return F(c)+dh*h+dr*rho


def certify_label(w):
    """Strict for all interior domain values, not merely at samples.

    An affine functional nonnegative at every polytope vertex and
    not identically zero is positive throughout the relative interior
    of the full-dimensional polygon. Both physical margins qualify.
    """
    values=[]
    for coeff in margin_coeff(w):
        vals=tuple(evaluate(coeff,v) for v in VERTICES)
        if min(vals)<0 or not any(v>0 for v in vals):
            raise AssertionError(("uncertified strict physical margin",w,coeff,vals))
        values.append(vals)
    return values


def all_selected_states():
    rows={every["CY"],*every["CHILD_LABELS"]}
    for chamber in symbolic.CHAMBERS:
        g=symbolic.SymbolicGeometry(chamber)
        for source in every["CHILD_LABELS"]:
            for _,_,target in every["tail"](source,g):
                rows.add(target)
    return rows


def prove_all_strict_margins():
    base=all_selected_states()
    assert len(base)==35
    complete=base|{every["reverse"](w) for w in base}
    assert len(complete)==61
    for w in complete:
        certify_label(w)
    return dict(polytope_vertices=4,base_labels=len(base),
                oriented_labels=len(complete),strict_margins=2*len(complete),
                exact_coefficient_basis=["1","h","rho"],
                universal_domain="0<h<1/5 and h<rho and rho+2h<1",
                inherited_root_bounds_not_reproved=True,
                all_later_choices_productive=False,universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(prove_all_strict_margins(),indent=2,sort_keys=True))
