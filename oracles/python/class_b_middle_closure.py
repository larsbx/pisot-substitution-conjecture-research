"""Independent gap-uniform closure of the proposed middle carrier.

Integer outer quotient bounds over the regime plus independent rational
Bernstein signs. No finite graph is used by this certificate. Closure alone
does not prove target hitting.
"""
import json
from class_b_middle_geometry import PACKET,poly,add,sub,mul,scale,length,displacement,sign,verify
from class_b_ray_certificate import le,plus,minus,amax,amin


def nonneg(reg,c,d,r):
    g0,j0,j1=reg
    return c+d*g0+r*j0>=0 and d>=0 and c+d*g0+r*(g0-j1)>=0 and d+r>=0


def quotient(reg,f,ceil):
    c,d,ld,r=f
    lows=[];highs=[]
    for m in range(-32,33):
        if nonneg(reg,c-(1 if ceil else 0),-(m-1 if ceil else m),r):lows.append(m)
        if nonneg(reg,-c-(0 if ceil else 1),m if ceil else m+1,-r):highs.append(m)
    if not lows or not highs:raise ValueError('quotient enclosure exhausted')
    return [ld,d+max(lows)],[ld,d+min(highs)]


def fadd(a,b):return tuple(x+y for x,y in zip(a,b))
def fsub(a,b):return tuple(x-y for x,y in zip(a,b))
def run(e,t):return (6+6*e,-1,3,3) if t==0 else (e if t==2 else 0,0,1,1)
def segment(e,t,part):
    if part==0:return (0 if t==0 else 1),0,0,(0,0,0,0),(0,0,0,0)
    px=int(t==0);r=run(e,t)
    return (2,px,1-px,(0,0,0,0),fsub(r,(1,0,0,0))) if part==1 else (0,px,1-px,r,r)


def edges(e,reg,row,us,inner=False):
    t,b,u,d,la,lb,ha,hb=row
    for pt in range(3):
        ct,ax,ac,alo,ahi=segment(e,t,pt)
        for pb in range(3):
            cb,bx,bc,blo,bhi=segment(e,b,pb)
            dx,dc=bx-ax,bc-ac
            kc=[-la,u-lb+dx]
            for u2 in us:
                base=((4+e)*u-e*d+3*dx+dc-u2,-lb,u-la,u)
                l=quotient(reg,fsub(fadd(base,blo),ahi),True)
                h=quotient(reg,fsub(fadd(base,bhi),alo),False)
                yield (pt,pb),ct,cb,u2,-2*u+dc-3*dx,kc,l[1 if inner else 0],h[0 if inner else 1]


class Geometry:
    def __init__(self,entry,l0=4):
        self.e=1 if entry['branch']=='plus' else -1
        self.l0=l0;self.g0=entry['g0'];self.reg=(entry['g0'],entry['rlo'],entry['rhi_offset'])
        self.rh=(poly(((1,0),entry['rlo'])),poly(((0,1),1),((1,0),-entry['rhi_offset'])))
        self.rows=[r[:4]+[r[5],r[6],r[9],r[10]] for r in entry['rows']]
        self.sl={}
        for i,r in enumerate(self.rows):self.sl.setdefault(tuple(r[:4]),[]).append(i)
        self.denom=poly(((1,0),1),((2,0),1))
    def margin_sign(self,t,b,u,d,k,which):
        got=[]
        for rh in self.rh:
            T=displacement(self.e,u,d,*k,rh)
            m=sub(mul(length(self.e,t),self.denom),T) if which=='upper' else add(T,mul(length(self.e,b),self.denom))
            got.append(sign(m,self.e,self.l0,self.g0))
        if got[0]!=got[1]:raise ValueError('residue endpoints disagree')
        return got[0]
    def child_ivs(self,ct,cb,u2,d2,kc):
        ivs=sorted(((minus(kc,r[6:8]),minus(kc,r[4:6])) for r in (self.rows[i] for i in self.sl.get((ct,cb,u2,d2),()))),key=lambda a:a[0][0]*self.l0+a[0][1])
        for a,b in zip(ivs,ivs[1:]):
            if le(plus(a[1],[0,1]),b[0],self.l0)!=1:raise ValueError('child order undecided')
        return ivs
    def outside(self,ct,cb,u2,d2,kc,lo,hi):
        return self.margin_sign(ct,cb,u2,d2,minus(kc,hi),'lower')<=0 or self.margin_sign(ct,cb,u2,d2,minus(kc,lo),'upper')<=0


def closure(entry,l0=4):
    geo=Geometry(entry,l0);e=geo.e;checks=0
    for ri,row in enumerate(geo.rows):
        t,b,u,d,la,lb,ha,hb=row
        J=[ha-la,hb-lb];term=[-la,-lb]
        target=t==b and u==0 and d==0 and le([la,lb],[0,0],l0)==1 and le([0,0],[ha,hb],l0)==1
        for _,ct,cb,u2,d2,kc,_,_ in edges(e,geo.reg,row,(-6,6)):
            for j in ([0,0],J):
                if geo.margin_sign(ct,cb,u2,d2,minus(kc,j),'lower' if u2<0 else 'upper')>0:raise ValueError('window insufficient')
        for parts,ct,cb,u2,d2,kc,rlo,rhi in edges(e,geo.reg,row,range(-5,6)):
            lo=amax([0,0],rlo,l0);hi=amin(J,rhi,l0)
            if le(lo,hi,l0)==0:continue
            gaps=[];cur=lo
            for a,b in geo.child_ivs(ct,cb,u2,d2,kc):
                gaps.append((cur,minus(a,[0,1])));cur=plus(b,[0,1])
            gaps.append((cur,hi))
            for a,b in gaps:
                pieces=[(a,b)]
                if target:
                    if le(a,term,l0)==1 and le(term,b,l0)==1:pieces=[(a,minus(term,[0,1])),(plus(term,[0,1]),b)]
                    elif le(term,minus(a,[0,1]),l0)!=1 and le(plus(b,[0,1]),term,l0)!=1:raise ValueError('terminal undecided')
                for a,b in pieces:
                    a=amax(lo,a,l0);b=amin(hi,b,l0)
                    if le(a,b,l0)==0:continue
                    if not geo.outside(ct,cb,u2,d2,kc,a,b):raise ValueError(('closure undecided',ri,parts,u2,d2,a,b))
                    checks+=1
    return dict(branch=entry['branch'],l0=l0,rows=len(geo.rows),closure_checks=checks,descent=False)


if __name__=='__main__':
    for entry in json.loads(PACKET.read_text()):
        print(json.dumps(closure(entry),sort_keys=True),flush=True)
