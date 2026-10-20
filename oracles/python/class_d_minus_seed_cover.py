"""Independent Fraction vertex calibration of the canonical Mojo seed cover.

Unlike Mojo's checked Farkas certificates, this oracle enumerates vertices of
2D rational polyhedra. The correlated Perron region itself is proved by Mojo
and the derivation in the research note, not by a parameter sample here.
"""
from fractions import Fraction
from itertools import combinations, product
from functools import lru_cache
from pathlib import Path
import argparse
import json

try:
    from .class_d_positive_b_recurrent_support import COVER
    from .class_d_minus_shared_cycles import segment, sub, shift
except ImportError:
    from class_d_positive_b_recurrent_support import COVER
    from class_d_minus_shared_cycles import segment, sub, shift


def vertices(forms):
    out = set()
    for (c,a,b),(d,e,f) in combinations(forms,2):
        det = a*f-b*e
        if not det:
            continue
        x,y = Fraction(b*d-c*f,det), Fraction(c*e-a*d,det)
        if all(c+a*x+b*y >= 0 for c,a,b in forms):
            out.add((x,y))
    return sorted(out)


def region(refined=True):
    out = [(0,1,0),(0,0,1),(1,-1,0),(1,0,-1)]
    return out+[(0,10,-7),(10,-10,-3)] if refined else out


def margins(v):
    top,bottom,x,c,y = v
    displacement = (20*(x+c+y),10*(x+c),-2*x)
    lengths = [(20,10,-2),(20,10,0),(20,0,0)]
    return [tuple(a+b for a,b in zip(displacement,lengths[bottom])),
            sub(lengths[top],displacement)]


def strict_witness(forms):
    # Our geometry systems include the compact square. All forms can be
    # strictly positive iff each is positive at some feasible vertex: average
    # those vertices to get one simultaneous strict witness.
    if any(c+max(a,0)+max(b,0)<=0 for c,a,b in forms):
        return None
    vs = vertices(forms)
    if not vs or not all(any(c+a*x+b*y>0 for x,y in vs) for c,a,b in forms):
        return None
    return tuple(sum(v[j] for v in vs)/len(vs) for j in (0,1))


def initial_labels():
    for a,b in combinations(range(3),2):
        for i,j in product(range(2),repeat=2):
            w = tuple(int(j==1 and k==b)-int(i==1 and k==a) for k in range(3))
            yield ((a,b)[i],(b,a)[j],*w)


def edge_guards(v,st,sb,sp):
    _,_,x,c,y=v
    req=(-(3*x+3*c+2*y),sp-(7*x+8*c+6*y),-(x+c+y))
    return [shift(sub(req,sub(sb[2],st[3]))),shift(sub(sub(sb[3],st[2]),req))]


def check_cover(cover=COVER,refined=True):
    if not cover or len(cover)>200 or any(len(v)!=5 or any(t not in range(3) for t in v[:2]) or any(abs(z)>10 for z in v[2:]) or abs(sum(v[2:]))>1 for v in cover):
        raise ValueError('invalid finite carrier certificate')
    counts=[len(cover),0,0,0,0,0,0,0,0]
    obligations=[]
    for v in initial_labels():
        if v in cover:
            counts[1]+=1
        elif (xy:=strict_witness(region(refined)+margins(v))) is None:
            counts[2]+=1
        else:
            obligations.append(dict(kind='seed',label=v,relaxed_xy=list(map(str,xy))))
    for v in sorted(cover):
        top,bottom,x,c,y=v
        if top==bottom and (x,c,y)==(0,0,0):
            counts[3]+=1
            continue
        for kt,kb in product(range(3),repeat=2):
            counts[4]+=1
            st,sb=segment(top,kt),segment(bottom,kb)
            xp=x+c+sb[1][0]-st[1][0]
            cp=x+c+2*y+sb[1][1]-st[1][1]
            bound=2+abs(xp+cp)+abs(xp)
            for sp in range(-bound,bound+1):
                counts[5]+=1
                target=(st[0],sb[0],xp,cp,sp-xp-cp)
                if target in cover:
                    counts[6]+=1
                    continue
                xy=strict_witness(region(refined)+margins(v)+margins(target))
                if xy is None:
                    counts[7]+=1
                    continue
                guards=edge_guards(v,st,sb,sp)
                # The nonnegative quadrant makes this polyhedron pointed;
                # if it is nonempty it has a vertex. No integer feasibility
                # conclusion is needed: only empty real systems exclude edges.
                uv=vertices([(0,1,0),(0,0,1)]+guards)
                if not uv:
                    counts[8]+=1
                    continue
                obligations.append(dict(kind='child',source=v,target=target,
                    segments=[kt,kb],guards=guards,relaxed_xy=list(map(str,xy)),
                    relaxed_uv=list(map(str,uv[0]))))
    return dict(status='EXACT_CARRIER_CLOSURE_CALIBRATION' if not obligations else 'UNRESOLVED_RELAXED_OBLIGATIONS',
        authority='independent-Fraction-vertex-oracle',refined_region=refined,
        counts=counts,unresolved=obligations,
        parameter_grid=False,perron_region_proof='kernel/psc/class_d_minus_seed_cover.mojo')


@lru_cache(maxsize=None)
def report():
    return check_cover()


def compare_mojo(out,path):
    lines=Path(path).read_text().splitlines()
    rows=[list(map(int,line.split()[1:])) for line in lines if line.startswith('MINUS_SEED_COVER_COUNTS ')]
    if rows != [out['counts']] or out['unresolved']:
        raise ValueError('Mojo/Fraction seed-cover disagreement')
    if not any(line.startswith('MINUS_SEED_COVER_CERTIFIED a>=2 b>=1 ') for line in lines):
        raise ValueError('canonical proof completion receipt missing')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mojo-log')
    parser.add_argument('--coarse',action='store_true')
    args=parser.parse_args()
    out=check_cover(refined=not args.coarse)
    print(json.dumps(out,indent=2),flush=True)
    if args.mojo_log:
        compare_mojo(out,args.mojo_log)
    if out['unresolved']:
        raise SystemExit(1)


if __name__=='__main__':
    main()
