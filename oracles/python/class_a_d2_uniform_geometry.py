"""Independent exact polynomial verification of d2 parity-indexed geometry.

The source typed templates are independently re-derived from full Q(beta)
seed graphs at (8,12) and (9,13). No floating point or finite extrapolation
is used for the all-parameter geometry/seed statements below.
"""
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
from class_a_d2_parity_carrier import reference_profile

LENGTH=((1,2,2,0),(1,0,0,0),(1,1,0,0))
SEEDS=(
    (0,1,0,0,0),(1,0,-1,1,0),(0,0,0,1,0),
    (0,2,0,0,0),(2,0,-1,0,1),(0,0,0,0,1),
    (1,2,0,0,0),(2,1,0,-1,1),(2,2,0,-1,0),
)


def inferred(parity):
    if parity not in (0,1):
        raise ValueError("only even and odd templates")
    first,second=((8,12) if parity==0 else (9,13))
    a=reference_profile(first)["intervals"]
    b=reference_profile(second)["intervals"]
    if len(a)!=len(b):
        raise ValueError("source interval count changed")
    result=[]
    m0=first//2
    for x,y in zip(a,b):
        if x[:4]!=y[:4]:
            raise ValueError("typed slice/order differs")
        dx=y[4]-x[4]
        dy=y[5]-x[5]
        if dx%2 or dy%2:
            raise ValueError("nonintegral parity slope")
        lo=dx//2
        hi=dy//2
        result.append((*x[:4],lo,x[4]-m0*lo,hi,x[5]-m0*hi))
    return result


def endpoint(s,y,a,b,residue):
    return (s+a,-a*(1+residue)+2*b+y,-a*(2+residue)+2*b,-2*a)


def coefficients_positive(poly,q):
    a,b,c,d=poly
    q2,q3=q*q,q*q*q
    co=(q3*a,3*q3*a+q2*b,3*q3*a+2*q2*b+q*c,
        q3*a+q2*b+q*c+d)
    return all(x>=0 for x in co) and any(x>0 for x in co)


def contains_seed_for_all_m(rows,m0,seed):
    t,b,k,c,y=seed
    s=k+c+y
    return any(
        (a,bb,ss,yy)==(t,b,s,y)
        and lower_slope<=0 and upper_slope>=0
        and lower_slope*m0+lower_const<=k<=upper_slope*m0+upper_const
        for (a,bb,ss,yy,lower_slope,lower_const,upper_slope,upper_const) in rows
    )


def certify(rows,parity):
    if parity not in (0,1):
        raise ValueError("parity must be 0 or 1")
    n0=8 if parity==0 else 7
    m0=n0//2
    q=n0+1
    expected_size=93 if parity==0 else 87
    expected_slices=82 if parity==0 else 80
    constant=105 if parity==0 else 111
    if len(rows)!=expected_size:
        raise ValueError("unapproved parity row count")
    typed=set()
    for i,row in enumerate(rows):
        t,b,s,y,al,bl,au,bu=row
        if t not in range(3) or b not in range(3):
            raise ValueError("invalid letter")
        typed.add(row[:4])
        if au-al<0 or (au-al)*m0+bu-bl<0:
            raise ValueError("empty for some m>=m0")
        for previous in rows[:i]:
            if previous[:4]!=row[:4]:continue
            p=previous
            before=((al-p[6])>=0 and (al-p[6])*m0+bl-p[7]>=1)
            after=((p[4]-au)>=0 and (p[4]-au)*m0+p[5]-bu>=1)
            if not (before or after):
                raise ValueError("overlapping/crossing interval pair")
        lo=endpoint(s,y,al,bl,parity)
        hi=endpoint(s,y,au,bu,parity)
        margins=(tuple(x+y for x,y in zip(lo,LENGTH[b])),
                 tuple(x-y for x,y in zip(LENGTH[t],hi)))
        for margin in margins:
            if not coefficients_positive(margin,q):
                raise ValueError(("missing strict all-n geometry",i,margin))
    if len(typed)!=expected_slices:
        raise ValueError("typed slice count changed")
    slope=sum(r[6]-r[4] for r in rows)
    intercept=sum(r[7]-r[5]+1 for r in rows)
    if (slope,intercept)!=(40,constant):
        raise ValueError("formal size changed")
    for seed in SEEDS:
        if not contains_seed_for_all_m(rows,m0,seed):
            raise ValueError(("seed not uniformly covered",seed))
    return {"parity":parity,"n_floor":n0,"intervals":expected_size,
            "typed_slices":expected_slices,"strict_margins":2*expected_size,
            "seeds":len(SEEDS),"formal_size_slope_m":40,
            "formal_size_intercept":constant,
            "scope":"all-n formal strict geometry and seed inclusion; no child closure"}


if __name__=="__main__":
    import json
    print(json.dumps([certify(inferred(0),0),certify(inferred(1),1)],indent=2))
