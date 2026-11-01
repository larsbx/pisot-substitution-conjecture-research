"""Independent universal middle descent with guaranteed inner occurrence ranges.

The finite potential synthesis is only input. Every inequality below is
verified for all l>=l0, g>=g0 and every residue of the middle regime. No
finite graph is used by this certificate.
"""
from pathlib import Path
import json
from class_b_middle_closure import Geometry,edges
from class_b_ray_certificate import le,plus,minus,meet
from class_b_middle_geometry import PACKET
POT=PACKET.with_name('middle-potentials.json')


def descent(entry,pot_entry,g0=None,l0=4):
    geo=Geometry(entry,l0)
    if g0 is not None:
        if g0<geo.g0:raise ValueError('cannot lower middle floor')
        geo.g0=g0;geo.reg=(g0,*geo.reg[1:])
    pot={tuple(r[:5]):r[5] for r in pot_entry['potential']}
    if any(v<0 for v in pot.values()):raise ValueError('negative potential')
    pieces=targets=intervals=candidates=0
    for ri,row in enumerate(geo.rows):
        t,b,u,d,la,lb,ha,hb=row
        klo=[la,lb];J=[ha-la,hb-lb];cut=[-la,-lb]
        for s,lo,hi in ((-1,[0,0],minus(cut,[0,1])),(0,cut,cut),(1,plus(cut,[0,1]),J)):
            region=meet([([0,0],J),(lo,hi)],l0)
            if region=='empty':continue
            if region is None:raise ValueError('undecided parent sign')
            j1,j2=region;pieces+=1
            if s==0 and u==0 and d==0:targets+=1;continue
            bp=pot[t,b,u,d,s];good=[]
            for _,ct,cb,u2,d2,kc,rlo,rhi in edges(geo.e,geo.reg,row,range(-5,6),inner=True):
                for a_iv,b_iv in geo.child_ivs(ct,cb,u2,d2,kc):
                    for cs,cr in ((-1,(plus(kc,[0,1]),j2)),(0,(kc,kc)),(1,(j1,minus(kc,[0,1])))):
                        if (ct,cb,u2,d2,cs) not in pot:continue
                        I=meet([(j1,j2),(rlo,rhi),(a_iv,b_iv),cr],l0)
                        if I is None or I=='empty':continue
                        bc=pot[ct,cb,u2,d2,cs]
                        def delta(j):return [s*(la+j[0])-cs*(kc[0]-j[0]),s*(lb+j[1])-cs*(kc[1]-j[1])+bp-bc-1]
                        if all(le([0,0],delta(j),l0)==1 for j in I):good.append(I);candidates+=1
            cursor=j1
            while le(plus(j2,[0,1]),cursor,l0)!=1:
                usable=[hi for lo,hi in good if le(lo,cursor,l0)==1 and le(cursor,hi,l0)==1]
                if not usable:raise ValueError(f'MIDDLE_NO_DESCENT row={ri} sign={s} cursor={cursor} end={plus(j2,[0,1])}')
                best=usable[0]
                for hi in usable[1:]:
                    if le(best,hi,l0)==1:best=hi
                cursor=plus(best,[0,1]);intervals+=1
    return dict(branch=entry['branch'],g0=geo.g0,l0=l0,pieces=pieces,targets=targets,descent_intervals=intervals,descent_candidates=candidates,max_b=max(pot.values()))


if __name__=='__main__':
    for entry,pot in zip(json.loads(PACKET.read_text()),json.loads(POT.read_text())):
        for g0 in range(entry['g0'],33):
            try:result=descent(entry,pot,g0)
            except ValueError as exc:
                print(json.dumps(dict(branch=entry['branch'],g0=g0,refusal=str(exc))),flush=True)
            else:print(json.dumps(result,sort_keys=True),flush=True);break
        else:raise SystemExit('no universal descent certificate through g0=32')
