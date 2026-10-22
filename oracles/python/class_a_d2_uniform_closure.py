"""Independent exact integer-polynomial proof of d=2 parity-carrier child closure.

For n=4*l+r, 0<=r<4, l>=3, rederive every FIRST/RUN/LAST
prefix-difference interval and test the complement of all destination
intervals by exact integer positive-coefficient certificates. This
does not use the canonical Mojo transition implementation and never
samples l to infer an all-parameter result.
"""
from collections import defaultdict, Counter
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
from class_a_d2_uniform_geometry import inferred,certify

L=((1,2,2,0),(1,0,0,0),(1,1,0,0))


def add(a,b):return a[0]+b[0],a[1]+b[1]
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def shift(a,x):return a[0],a[1]+x
def val(a,l):return a[0]*l+a[1]


class Undecided(ValueError):pass


def le(a,b,l0):
    slope=b[0]-a[0]
    at=slope*l0+b[1]-a[1]
    if slope>=0 and at>=0:return True
    if slope<=0 and at<0:return False
    raise Undecided(("affine line order crosses the infinite ray",a,b,l0))


def amin(a,b,l0):return a if le(a,b,l0) else b
def amax(a,b,l0):return b if le(a,b,l0) else a


def phases(t,r):
    run=(4,r+(2 if t==0 else 0 if t==1 else 1))
    initial=1 if t==1 else 0
    final=1 if t==2 else 0
    x=0 if t==1 else 1
    return (
        ((0,0),(0,0),initial,0,0),
        ((0,0),shift(run,-1),2,x,1-x),
        (run,run,final,x,1-x),
    )


def endpoint(s,dx,dc,k,y,r):
    a,b=k
    if a%2:raise Undecided("n mod4 has not cleared k-slope denominator")
    half=a//2
    k0=b+s+dx
    summ=2*s+dx+dc+y
    return (summ+half,-half*(r+1)+2*k0+y,
            -half*(r+2)+2*k0,-2*half)


def certificate(poly,q):
    a,b,c,d=poly
    q2,q3=q*q,q*q*q
    return (
        q3*a,3*q3*a+q2*b,3*q3*a+2*q2*b+q*c,
        q3*a+q2*b+q*c+d,
    )


def nonnegative(poly,q):
    return all(c>=0 for c in certificate(poly,q))


def excluded(t,b,s,dx,dc,r,y,lo,hi,q):
    left_end=endpoint(s,dx,dc,hi,y,r)
    right_end=endpoint(s,dx,dc,lo,y,r)
    left=tuple(-a-z for a,z in zip(left_end,L[b]))
    right=tuple(a-z for a,z in zip(right_end,L[t]))
    if nonnegative(left,q):return "left"
    if nonnegative(right,q):return "right"
    raise Undecided(("possible strict child outside parity carrier",r,
                     t,b,s,dx,dc,y,lo,hi,left,right))


def residue(proposed,r,l0=3,window=5):
    if r not in range(4) or l0<3 or window<5:
        raise ValueError("unproved residue, cutoff or child-y window")
    parity=r%2
    if len(proposed)!=(93 if parity==0 else 87):
        raise ValueError("wrong parity carrier")
    # In terms of l, the parity coordinate is m=2*l+floor(r/2).
    rows=[]
    for t,b,s,y,al,bl,au,bu in proposed:
        c=r//2
        rows.append((t,b,s,y,(2*al,al*c+bl),(2*au,au*c+bu)))
    dest=defaultdict(list)
    for row in rows:dest[row[:4]].append(row)
    counts=Counter()
    q=4*l0+r+1
    for parent_id,(t,b,s,y,low,high) in enumerate(rows):
        if abs(s)>1:
            raise Undecided("source-sum bound needed for finite y window")
        partitions=[(low,high)]
        if t==b and s==0 and y==0:
            partitions=[(low,amin(high,(0,-1),l0)),
                        (amax(low,(0,1),l0),high)]
        for pl,pu in partitions:
            if not le(pl,pu,l0):continue
            for tp in range(3):
                il,iu,ct,px,pc=phases(t,r)[tp]
                for bp in range(3):
                    jl,ju,cb,qx,qc=phases(b,r)[bp]
                    dx,dc=qx-px,qc-pc
                    for target_y,endpoint_k,side in (
                        (window,pl,"right"),(-window,pu,"left")):
                        T=endpoint(s,dx,dc,endpoint_k,target_y,r)
                        poly=tuple(x-z for x,z in zip(T,L[ct])) if side=="right" else tuple(-x-z for x,z in zip(T,L[cb]))
                        if not nonnegative(poly,q):
                            raise Undecided(("unproved finite child-y window",r,parent_id,tp,bp,poly))
                        counts["window"]+=1
                    for target_y in range(-window+1,window):
                        # y'=(4l+r)s+2k+y+z_b-z_t.
                        base=(-4*s,target_y-r*s-y)
                        occurrence_lo=sub(base,sub(ju,il))
                        occurrence_hi=sub(base,sub(jl,iu))
                        if occurrence_lo[0]%2 or occurrence_hi[0]%2:
                            raise Undecided("half-integral affine slope")
                        occ_lo=(occurrence_lo[0]//2,-((-occurrence_lo[1])//2))
                        occ_hi=(occurrence_hi[0]//2,occurrence_hi[1]//2)
                        lo=amax(pl,occ_lo,l0)
                        hi=amin(pu,occ_hi,l0)
                        if not le(lo,hi,l0):continue
                        counts["cells"]+=1
                        child_s=2*s+dx+dc+target_y
                        cursor=lo
                        previous=None
                        for target in dest.get((ct,cb,child_s,target_y),()):
                            shift_k=s+dx
                            dlo=shift(target[4],-shift_k)
                            dhi=shift(target[5],-shift_k)
                            if previous is not None and not le(shift(previous,1),dlo,l0):
                                raise Undecided("destination intervals reorder")
                            previous=dhi
                            if not le(cursor,hi,l0):break
                            if le(dhi,shift(cursor,-1),l0):continue
                            if le(shift(hi,1),dlo,l0):break
                            end=amin(hi,shift(dlo,-1),l0)
                            if le(cursor,end,l0):
                                counts["gaps"]+=1
                                counts[excluded(ct,cb,s,dx,dc,r,target_y,cursor,end,q)]+=1
                            cursor=amax(cursor,shift(dhi,1),l0)
                        if le(cursor,hi,l0):
                            counts["gaps"]+=1
                            counts[excluded(ct,cb,s,dx,dc,r,target_y,cursor,hi,q)]+=1
    expected=(
        {"window":1710,"cells":3005,"gaps":2483,"left":1249,"right":1234}
        if parity==0 else
        {"window":1602,"cells":2845,"gaps":2363,"left":1189,"right":1174}
    )
    if dict(counts)!=expected:
        raise Undecided(("incomplete universal partition",r,dict(counts),expected))
    return {"n_residue_mod4":r,"n_floor":12+r,"stats":dict(counts),
            "all_n_child_closure":True,"all_n_hitting":False}


def prove():
    e,o=inferred(0),inferred(1)
    certify(e,0)
    certify(o,1)
    return [residue(e if r%2==0 else o,r) for r in range(4)]


if __name__=="__main__":
    import json
    print(json.dumps(prove(),indent=2))
