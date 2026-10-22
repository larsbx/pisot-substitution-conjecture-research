"""Independent integer-polynomial certificate for 80 constant-label d2 states.

The canonical authority is psc.class_a_d2_fixed_corridor.mojo; this
separately written Python checks every row, all exact proper-prefix
identities and strict inequalities on the full root interval 0<h<1/5.
A complete finite Q(beta) graph is only an additional differential control.
"""
from collections import Counter
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/"kernel/psc/class_a_d2_fixed_corridor_data.mojo"
LENGTH=((1,2,2),(1,0,0),(1,1,0))


def rows():
    source=DATA.read_text()
    matching=re.findall(
        r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){8})\]\),$",
        source,re.MULTILINE)
    if len(matching)!=80:
        raise ValueError("fixed d2 corridor must have exactly 80 labels")
    return [tuple(map(int,line.split(","))) for line in matching]


def bernstein_certified(poly):
    """25*(1+t)^2 f(t/(5(1+t))) has nonnegative coefficients."""
    a,b,c=poly
    transformed=(25*a,50*a+5*b,25*a+5*b+c)
    return min(transformed)>=0 and max(transformed)>0


def margins(label):
    t,b,k,c,y=label
    if t not in range(3) or b not in range(3):
        raise ValueError("invalid strict-overlap tile")
    if k+c+y!=0:
        raise ValueError("uncancelled n*s term in claimed constant corridor")
    shift=(0,2*k+y,2*k)
    left=tuple(a+b for a,b in zip(LENGTH[b],shift))
    right=tuple(a-b for a,b in zip(LENGTH[t],shift))
    return left,right


def prefix(t,index):
    if t not in range(3) or not 0<=index<=4:
        raise ValueError("prefix index not uniformly valid for n>=4")
    if index==0:
        return (0,0,0)
    return (int(t!=1),int(t==1),index-1)


def child_type(t,index):
    prefix(t,index)
    return 1 if t==1 else 0 if index==0 else 2


def actual_child(parent,ti,bi):
    t,b,k,c,y=parent
    s=k+c+y
    if s:
        raise ValueError("uniform child would retain an n coefficient")
    a,z=prefix(t,ti),prefix(b,bi)
    ct=(1 if t==1 else 0) if ti==0 else 2
    cb=(1 if b==1 else 0) if bi==0 else 2
    return (ct,cb,k+s+z[0]-a[0],s-k+z[1]-a[1],
            2*k+y+z[2]-a[2])


def prove(table=None):
    table=rows() if table is None else list(table)
    if len(table)!=80 or len({entry[:5] for entry in table})!=80:
        raise ValueError("missing or duplicate uniform corridor states")
    depths=Counter()
    for i,record in enumerate(table):
        if len(record)!=9:
            raise ValueError("malformed uniform corridor record")
        t,b,k,c,y,d,ti,bi,j=record
        if not 0<=d<=4:
            raise ValueError("invalid nonnegative rank")
        for margin in margins(record[:5]):
            if not bernstein_certified(margin):
                raise ValueError(("strict overlap unproved for all n>=4",
                                  record[:5],margin))
        if d==0:
            if (k,c,y)!=(0,0,0) or (ti,bi,j)!=(-1,-1,-1):
                raise ValueError("zero-rank row is not an offset-zero target")
        else:
            if not 0<=j<len(table) or table[j][5]!=d-1:
                raise ValueError("chosen child does not reduce rank")
            if actual_child(record[:5],ti,bi)!=table[j][:5]:
                raise ValueError(("ordered child identity fails",i,j,ti,bi))
        depths[d]+=1
    if dict(depths)!={0:8,1:20,2:26,3:22,4:4}:
        raise ValueError("fixed corridor stage histogram altered")
    return {"rows":80,"offset_zero_targets":8,"chosen_real_edges":72,
            "strict_margins":160,"uniform_hitting_depth":4,
            "depth_histogram":dict(sorted(depths.items())),
            "scope":"all n>=4 for these 80 states, not all carrier states"}


def prove_candidate_inclusion(table=None):
    """Uniform inclusion in formal parity candidates, not seed reachability.

    Every fixed label is in an affine interval whose lower slope <=0,
    upper slope >=0 and contains the label at the parity floor.
    """
    from class_a_d2_uniform_geometry import inferred
    table=rows() if table is None else list(table)
    totals=[]
    for residue,floor in ((0,4),(1,3)):
        template=inferred(residue)
        found=0
        for t,b,k,c,y,*_ in table:
            if any(
                tuple(key)==(t,b,k+c+y,y) and al<=0<=au
                and al*floor+bl<=k<=au*floor+bu
                for *key,al,bl,au,bu in template
            ):
                found+=1
        if found!=len(table):
            raise ValueError(("fixed corridor omitted from formal parity candidate",
                              residue,found,len(table)))
        totals.append(found)
    return tuple(totals)


def exact_finite_replay(n,table=None):
    """Supplementary complete graph check, no extrapolation of membership."""
    from class_a_d2_parity_carrier import graph,integral_coordinates
    if not 4<=n<=24:
        raise ValueError("finite d2 replay is capped at n<=24")
    table=rows() if table is None else list(table)
    g=graph(n)
    if g.capped:
        raise ValueError("exact finite graph exhausted its state cap")
    inv={}
    for idx,state in enumerate(g.states):
        t,b,shift=state
        k,c,y=integral_coordinates(g,shift)
        inv[(t-1,b-1,k,c,y)]=idx
    matched=0
    for record in table:
        t,b,k,c,y,d,ti,bi,j=record
        src=(t,b,k,c,y)
        if src not in inv:
            raise ValueError(("uniform corridor vertex absent from finite graph",
                              n,src))
        if d:
            child=table[j][:5]
            parent_state=g.states[inv[src]]
            ctype=g.sigma[parent_state[0]][ti],g.sigma[parent_state[1]][bi]
            shift=parent_state[2]
            candidate=(ctype[0],ctype[1],
                g.F.sub(g.F.add(g.F.mul(g.F.beta,shift),
                                g.prefix[parent_state[1],bi]),
                        g.prefix[parent_state[0],ti]))
            if candidate!=g.states[inv[child]] or not g.overlaps(candidate):
                raise ValueError(("finite exact proper-prefix occurrence disagrees",
                                  n,src,ti,bi,child))
            matched+=1
    if matched!=72:
        raise ValueError("partial exact finite chosen-edge replay")
    return {"n":n,"rows":80,"replayed_occurrences":matched}


if __name__=="__main__":
    import json
    print(json.dumps({"proof":prove(),
                      "uniform_parity_inclusion":prove_candidate_inclusion(),
                      "finite_differentials":[exact_finite_replay(n) for n in (4,8,9,12)]},
                     indent=2))
