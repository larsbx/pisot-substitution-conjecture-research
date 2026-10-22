"""Independent rational/integer oracle for class-A *uniform* child closure.

This is a separate implementation of the affine-cell calculation; canonical
authority is kernel/psc/class_a_uniform_closure.mojo. All-n proof uses exact
polynomial positivity and affine line comparisons, NOT sampled large n.
"""
from fractions import Fraction
from pathlib import Path
from collections import defaultdict, Counter
import re

ROOT=Path(__file__).resolve().parents[2]
ROWS_SOURCE=ROOT/"kernel/psc/class_a_typed_carrier.mojo"

def rows():
    return [tuple(map(int,m.split(","))) for m in re.findall(
        r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\),$",
        ROWS_SOURCE.read_text(),re.MULTILINE)]

def aadd(x,y):return x[0]+y[0],x[1]+y[1]
def asub(x,y):return x[0]-y[0],x[1]-y[1]
def ashift(x,t):return x[0],x[1]+t
def value(x,n):return x[0]*n+x[1]

def phase(t,p):
    m=(1,0 if t==1 else 1)
    if p==0:return ((0,0),(0,0),1 if t==1 else 0,0)
    if p==1:return ((0,1),m,2,0 if t==1 else 1)
    return (ashift(m,1),ashift(m,1),1 if t==2 else 0,0 if t==1 else 1)

L=((1,1,1,0),(1,0,0,0),(1,1,0,0))

def shift_coeff(q,s,k,ts,bs,tp,bp):
    a,b=k
    du=(0 if bp==0 else (-1 if bs==1 else 0))-(0 if tp==0 else (-1 if ts==1 else 0))
    dv=(0 if bp==0 else (0 if bs==1 else 1))-(0 if tp==0 else (0 if ts==1 else 1))
    return (q+a,q-a+b-s+du,b-a+s+dv,-a)

def neg_margins(q,s,lo,hi,ct,cb,ts,bs,tp,bp):
    low=shift_coeff(q,s,lo,ts,bs,tp,bp)
    high=shift_coeff(q,s,hi,ts,bs,tp,bp)
    return (tuple(-v-w for v,w in zip(L[cb],high)),
            tuple(v-w for v,w in zip(low,L[ct])))

def nonnegative_tail(poly):
    # Exact 729*(1+t)^3*f(t/(9*(1+t))) polynomial coefficients.
    a,b,c,d=poly
    return all(x>=0 for x in (
        729*a,2187*a+81*b,2187*a+162*b+9*c,729*a+81*b+9*c+d))

def exact_root_nonnegative(poly,n):
    """No floating signs: Sturm-equivalent interval isolation of unique root."""
    a,b,c,d=poly
    # P_n(h)=h^3+(n+1)h^2+(n+1)h-1 irreducible cubic.
    a,b,c=a+d,b-(n+1)*d,c-(n+1)*d
    if not(a or b or c):return True
    lo,hi=Fraction(0),Fraction(1,5)
    P=lambda h:h**3+(n+1)*(h+h*h)-1
    for _ in range(160):
        lower=a+(b*lo if b>=0 else b*hi)+(c*lo*lo if c>=0 else c*hi*hi)
        upper=a+(b*hi if b>=0 else b*lo)+(c*hi*hi if c>=0 else c*lo*lo)
        if lower>0:return True
        if upper<0:return False
        mid=(lo+hi)/2
        if P(mid)>0:hi=mid
        else:lo=mid
    raise ValueError("exact algebraic sign not isolated")

def check(parameter=None, template=None):
    """parameter=None proves all n>=8; otherwise checks exactly that n."""
    rr=list(rows() if template is None else template)
    if len(rr)!=89:raise ValueError("requires 89 source intervals")
    # The finite q=-2..2 universe is complete only under these exact
    # row bounds, not under an arbitrary malformed input carrier.
    for top,bottom,s,y,al,bl,au,bu in rr:
        if abs(s)>1 or al < -1 or 4*(al+1)+bl < -1:
            raise ValueError("row violates the uniform child-sum bound")
        if au > 1 or 4*(1-au)+1-bu < 0:
            raise ValueError("row violates the uniform child-sum bound")
    n=8 if parameter is None else parameter
    if parameter is not None and not 4<=n<=7:
        raise ValueError("finite prefix 4..7 only")
    def le(x,y):
        if parameter is not None:return value(x,n)<=value(y,n)
        slope=y[0]-x[0]
        d8=value(y,8)-value(x,8)
        if slope>=0 and d8>=0:return True
        if slope<=0 and d8<0:return False
        raise ValueError("affine order changes above n=8")
    def maxi(x,y):return y if le(x,y) else x
    def mini(x,y):return x if le(x,y) else y
    by_type=defaultdict(list)
    for r in rr:by_type[r[:4]].append(r)
    # Reject changed affine sort or overlapping target intervals.
    for key in by_type:
        by_type[key].sort(key=lambda r:value(r[4:6],n))
        for x,y in zip(by_type[key],by_type[key][1:]):
            if not le(ashift(x[6:8],1),y[4:6]):
                raise ValueError("target intervals overlap or reorder")
    counts=Counter()
    for row in rr:
        ts,bs,s,y,al,bl,au,bu=row
        parent=[((al,bl),(au,bu))]
        if ts==bs and s==0 and y==0:
            parent=[((al,bl),mini((au,bu),(0,-1))),
                    (maxi((al,bl),(0,1)),(au,bu))]
        for pl,pu in parent:
            if not le(pl,pu):continue
            for tp in range(3):
                ilo,ihi,ct,tdx=phase(ts,tp)
                for bp in range(3):
                    jlo,jhi,cb,bdx=phase(bs,bp)
                    dx=bdx-tdx
                    di=int(bp!=0)-int(tp!=0)
                    for q in range(-2,3):
                        qy=q-2*s-di
                        base=(-s,q-2*s-y)
                        lo=maxi(pl,aadd(base,asub(ilo,jhi)))
                        hi=mini(pu,aadd(base,asub(ihi,jlo)))
                        if not le(lo,hi):continue
                        counts["cells"]+=1
                        cursor=lo
                        intervals=by_type.get((ct,cb,q,qy),[])
                        for target in intervals:
                            tlo=ashift(target[4:6],-s-dx)
                            thi=ashift(target[6:8],-s-dx)
                            if not le(cursor,hi):break
                            if le(thi,ashift(cursor,-1)):continue
                            if le(ashift(hi,1),tlo):break
                            gapend=mini(hi,ashift(tlo,-1))
                            if le(cursor,gapend):
                                counts["gaps"]+=1
                                mleft,mright=neg_margins(q,s,cursor,gapend,ct,cb,ts,bs,tp,bp)
                                cert=nonnegative_tail if parameter is None else lambda p:exact_root_nonnegative(p,n)
                                if cert(mleft):counts["left"]+=1
                                elif cert(mright):counts["right"]+=1
                                else:raise ValueError(("real child outside candidate",parameter,row,tp,bp,q,cursor,gapend))
                            cursor=maxi(cursor,ashift(thi,1))
                        if le(cursor,hi):
                            counts["gaps"]+=1
                            mleft,mright=neg_margins(q,s,cursor,hi,ct,cb,ts,bs,tp,bp)
                            cert=nonnegative_tail if parameter is None else lambda p:exact_root_nonnegative(p,n)
                            if cert(mleft):counts["left"]+=1
                            elif cert(mright):counts["right"]+=1
                            else:raise ValueError(("real child outside candidate",parameter,row,tp,bp,q,cursor,hi))
    return dict(counts)

if __name__=="__main__":
    import json
    print(json.dumps({"finite":{n:check(n) for n in (4,5,6,7)},
                      "all_n_at_least_8":check()},indent=2,sort_keys=True))
