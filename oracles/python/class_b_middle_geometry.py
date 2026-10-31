"""Independent rational Bernstein checks of middle-row and core membership.

Sparse polynomials in (h,v), independently expanded onto rational rectangles.
This proves strict row membership and strict-core inclusion on the stated
parameter hull. It does not prove forward closure, descent, or BH.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[2]
PACKET=ROOT/'evidence/class-b-step2c-2026-10-27/middle-candidates.json'


def poly(*terms): return {k:v for k,v in terms if v}
def add(*ps):
    out={}
    for p in ps:
        for k,v in p.items(): out[k]=out.get(k,0)+v
    return {k:v for k,v in out.items() if v}
def scale(p,n): return {k:v*n for k,v in p.items() if v*n}
def mul(p,q):
    out={}
    for (i,j),a in p.items():
        for (k,l),b in q.items(): out[i+k,j+l]=out.get((i+k,j+l),0)+a*b
    return {k:v for k,v in out.items() if v}
def sub(p,q): return add(p,scale(q,-1))
def strip(p):
    if not p:return p
    a,b=min(k[0] for k in p),min(k[1] for k in p)
    return {(i-a,j-b):v for (i,j),v in p.items()}
def elimination(e): return poly(((0,0),1),((1,0),-3-e),((2,0),-4-3*e),((3,0),-2*e),((1,1),1))
def length(e,t):
    return (poly(((0,0),3),((1,0),3+3*e),((0,1),-1),((2,0),3*e)),
            poly(((0,0),1),((1,0),1-e),((2,0),-e)),
            poly(((0,0),1),((1,0),1)))[t]
def displacement(e,u,d,a,b,rh):
    A=poly(((0,0),u),((1,0),u-e*d),((2,0),-e*d),((0,1),-b))
    # Clear the positive denominator h(1+h) after eliminating q.
    return add(mul(add(A,scale(rh,a)),poly(((1,0),1),((2,0),1))),
               scale(mul(poly(((1,0),1)),elimination(e)),-a))


def box_poly(p,l0,g0,strip_factors=True):
    out={(i+j,i):F(c,l0**(i+j)*g0**i) for (i,j),c in p.items()}
    return strip(out) if strip_factors else out


def bernstein(p,rect):
    """Re-expand the original power polynomial on each exact cell, then convert.
    Independent of the native de Casteljau subdivision implementation.
    """
    x0,x1,y0,y1=rect
    P=max((k[0] for k in p),default=0);Q=max((k[1] for k in p),default=0)
    power={}
    for (i,j),c in p.items():
        for a in range(i+1):
            for b in range(j+1):
                power[a,b]=power.get((a,b),0)+c*comb(i,a)*x0**(i-a)*(x1-x0)**a*comb(j,b)*y0**(j-b)*(y1-y0)**b
    return [[sum(power.get((a,b),0)*F(comb(i,a),comb(P,a))*F(comb(j,b),comb(Q,b))
                 for a in range(i+1) for b in range(j+1)) for j in range(Q+1)] for i in range(P+1)]


def cell_sign(table,rect,want):
    t=[[v*want for v in row] for row in table]
    if any(v<0 for row in t for v in row) or not any(v>0 for row in t for v in row):return False
    # All faces meeting the open-x, half-open-y domain must be positive.
    x0,x1,y0,y1=rect
    cols=[0,len(t)-1]; rows=[0,len(t[0])-1]
    included_x=[x0>0,x1<1];included_y=[y0>0,True]
    for k,include in zip(cols,included_x):
        if include and not any(v>0 for v in t[k]):return False
    for k,include in zip(rows,included_y):
        if include and not any(row[k]>0 for row in t):return False
    for i,include_x in zip(cols,included_x):
        for j,include_y in zip(rows,included_y):
            if include_x and include_y and t[i][j]<=0:return False
    return True


def direct_sign(f,side,l0,g0,limit=12):
    p=box_poly(f,l0,g0);s=box_poly(side,l0,g0,False)
    todo=[((F(0),F(1),F(0),F(1)),0)];signs=set()
    while todo:
        rect,depth=todo.pop()
        sb=bernstein(s,rect)
        if all(v<0 for row in sb for v in row):continue
        b=bernstein(p,rect)
        got=next((sign for sign in (1,-1) if cell_sign(b,rect,sign)),None)
        if got is not None:signs.add(got);continue
        if depth==limit:raise ValueError('UNDECIDED rational Bernstein cell')
        x0,x1,y0,y1=rect
        if depth%2==0:
            m=(x0+x1)/2
            rects=((x0,m,y0,y1),(m,x1,y0,y1))
        else:
            m=(y0+y1)/2
            rects=((x0,x1,y0,m),(x0,x1,m,y1))
        todo.extend((r,depth+1) for r in rects)
    if len(signs)!=1:raise ValueError('nonconstant or vacuous sign')
    return signs.pop()


@lru_cache(maxsize=None)
def sign_cached(items,eps,l0,g0):
    f=dict(items)
    if not f:return 0
    j0=2 if eps==1 else 6
    side=sub(elimination(eps),poly(((0,1),l0),((1,1),l0),((1,0),j0),((2,0),j0)))
    try:return direct_sign(f,side,l0,g0)
    except ValueError as first:
        p=strip(f)
        p0={j:c for (i,j),c in p.items() if i==0}
        s0={j:c for (i,j),c in side.items() if i==0}
        ratio=F(p0.get(0,0),s0[0])
        if any(p0.get(j,0)!=ratio*s0.get(j,0) for j in set(p0)|set(s0)):raise first
        rem=sub(p,scale(side,ratio))
        if not rem:raise first
        got=direct_sign(strip(rem),side,l0,g0)
        if ratio>=0 and got>0:return 1
        if ratio<=0 and got<0:return -1
        raise first


def sign(f,e,l0,g0):return sign_cached(tuple(sorted(f.items())),e,l0,g0)
def margins(e,t,b,u,d,a,k,rh):
    denom=poly(((1,0),1),((2,0),1))
    T=displacement(e,u,d,a,k,rh)
    return sub(mul(length(e,t),denom),T),add(T,mul(length(e,b),denom))


def verify(entry,l0=4):
    e=1 if entry['branch']=='plus' else -1;g0=entry['g0']
    rh=[poly(((1,0),entry['rlo'])),poly(((0,1),1),((1,0),-entry['rhi_offset']))]
    rows=[]
    for r in entry['rows']:
        if any(r[i] for i in (7,8,11,12)):raise ValueError('table is not l-affine')
        row=r[:4]+[r[5],r[6],r[9],r[10]];rows.append(row)
        t,b,u,d,lo,klo,hi,khi=row
        if hi<lo or (hi-lo)*l0+khi-klo<0:raise ValueError('empty row')
        for a,k in ((lo,klo),(hi,khi)):
            for endpoint in rh:
                if any(sign(m,e,l0,g0)!=1 for m in margins(e,t,b,u,d,a,k,endpoint)):
                    raise ValueError(('row not strict',row))
    count=0
    for t in range(3):
        for b in range(3):
            for u in range(-3,4):
                for d in range(-6,7):
                    for k in range(-2,3):
                        ss=[tuple(sign(m,e,l0,g0) for m in margins(e,t,b,u,d,0,k,end)) for end in rh]
                        if ss[0]!=ss[1]:raise ValueError('core endpoint signs differ')
                        if ss[0]!=(1,1):continue
                        if not any(r[:4]==[t,b,u,d] and r[4]<=0 and r[4]*l0+r[5]<=k and r[6]>=0 and r[6]*l0+r[7]>=k for r in rows):
                            raise ValueError(('core omitted',t,b,u,d,k))
                        count+=1
    return dict(branch=entry['branch'],g0=g0,l0=l0,rows=len(rows),strict_core_labels=count,closure=False,descent=False)


if __name__=='__main__':
    for entry in json.loads(PACKET.read_text()):print(json.dumps(verify(entry),sort_keys=True),flush=True)
