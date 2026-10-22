"""Independent integer-polynomial proof for 518 extra d2 all-n physical states.

Each constant typed state with s=+-1 has one actual proper-prefix child
in the separately checked 80-state productive core. Chosen positions have
forms i=a*n+b, a=0 or 1, and their y-prefix coefficient cancels n*s.
All strict margins hold for every h in (0,1/5) by exact integer power
certificates. Source discovery was a reverse search, not a proof.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE))
from class_a_d2_fixed_corridor import rows as core_rows,prove as prove_core

SOURCE=ROOT/"kernel/psc/class_a_d2_constant_shell_data.mojo"
L=((1,2,2),(1,0,0),(1,1,0))


def records():
    import re
    matches=re.findall(r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){10})\]\),$",
                       SOURCE.read_text(),re.MULTILINE)
    result=[tuple(map(int,x.split(","))) for x in matches]
    if len(result)!=518:
        raise ValueError("incomplete 518-state uniform shell")
    return result


def strict_margin(poly):
    a,b,c=poly
    co=(25*a,50*a+5*b,25*a+5*b+c)
    if min(co)<0 or not any(co):
        raise ValueError(("strict d2 Perron geometry unproved",poly,co))
    return co


def prefix(letter,a,b,n=None):
    """(child,px,pc,y_slope,y_constant) for index a*n+b uniformly n>=4."""
    if letter not in range(3) or a not in (0,1):
        raise ValueError("unapproved shell parent or index slope")
    end=(3,1,2)[letter]
    if a==0 and b not in range(5):
        raise ValueError("early index not legal uniformly")
    if a==1 and not -3<=b<=end:
        raise ValueError("late index outside uniform run/last")
    first=1 if letter==1 else 0
    if a==b==0:
        return first,0,0,0,0
    if n is not None:
        i=a*n+b
        run=n+(2 if letter==0 else 0 if letter==1 else 1)
        if i<=0 or i>run+1:
            raise ValueError("chosen index absent at finite n")
    child=(1 if letter==2 else 0) if a==1 and b==end else 2
    return child,int(first==0),int(first==1),a,b-1


def verify_shell(rows=None,core=None):
    rows=records() if rows is None else list(rows)
    core=core_rows() if core is None else list(core)
    if len(rows)!=518 or len(core)!=80:
        raise ValueError("incomplete uniform shell or productive core")
    if len({r[:5] for r in rows})!=518:
        raise ValueError("duplicate fixed shell label")
    histogram=Counter()
    posneg=Counter()
    for i,row in enumerate(rows):
        if len(row)!=11:
            raise ValueError("malformed candidate row")
        t,b,k,c,y,depth,ai,bi,aj,bj,child_id=row
        s=k+c+y
        if abs(s)!=1:
            raise ValueError("source offset sum must be exactly +/-1")
        if depth not in range(2,6):
            raise ValueError("out-of-contract shell depth")
        shift=(s,2*k+y,2*k)
        for poly in (tuple(u+v for u,v in zip(L[b],shift)),
                     tuple(u-v for u,v in zip(L[t],shift))):
            strict_margin(poly)
        if not 0<=child_id<len(core):
            raise ValueError("chosen core child absent")
        target=core[child_id]
        if depth!=target[5]+1:
            raise ValueError("one-step absorption rank not decreasing")
        tp=prefix(t,ai,bi)
        bp=prefix(b,aj,bj)
        if s+bp[3]-tp[3]:
            raise ValueError("chosen index difference fails to cancel n")
        child=(tp[0],bp[0],k+s+bp[1]-tp[1],
               s-k+bp[2]-tp[2],2*k+y+bp[4]-tp[4])
        if child!=target[:5]:
            raise ValueError(("chosen actual child not the indexed core target",
                              i,child,target[:5]))
        histogram[depth]+=1
        posneg[s]+=1
    if histogram!={2:230,3:176,4:106,5:6} or (
        posneg[1]==0 or posneg[-1]==0):
        raise ValueError("shell certificate census changed")
    return {"additional_states":518,"previous_core":80,"explicit_hitting_states":598,
            "uniform_actual_one_step_edges":518,
            "strict_margin_certificates":1036,
            "hitting_bound":5,"rank_histogram":dict(sorted(histogram.items())),
            "source_sum_counts":dict(sorted(posneg.items())),
            "scope":"each listed fixed state, every integer n>=4; not all d2 carrier states"}


def finite_field_replay(n,rows=None):
    """Exact field calibration, including formal states absent from seed graph.

    Each row's actual index pair, child type, and beta*shift+prefix
    difference is checked at selected finite n. This is supplementary:
    the all-n proof is integer-coefficient algebra in verify_shell.
    """
    from class_a_d2_parity_carrier import graph
    if n not in (4,8,9):
        raise ValueError("only calibrated finite parameters 4,8,9")
    g=graph(n)
    source=records() if rows is None else list(rows)
    core=core_rows()
    F=g.F
    l=g.l
    def physical(row):
        t,b,k,c,y=row[:5]
        w=(k,c,y)
        v=tuple(sum((Fraction(q)*l[i][j] for i,q in enumerate(w)),
                    Fraction(0)) for j in range(3))
        return (t+1,b+1,v)
    corestates=[physical(r) for r in core]
    edges=0
    for row in source:
        t,b,k,c,y,d,ai,bi,aj,bj,target=row
        parent=physical(row)
        if not g.overlaps(parent):
            raise ValueError("finite exact Q(beta) parent not strict")
        it=ai*n+bi
        ib=aj*n+bj
        if not(0<=it<len(g.sigma[t+1]) and 0<=ib<len(g.sigma[b+1])):
            raise ValueError("actual occurrence index absent")
        child=(g.sigma[t+1][it],g.sigma[b+1][ib],
               F.sub(F.add(F.mul(F.beta,parent[2]),g.prefix[b+1,ib]),
                     g.prefix[t+1,it]))
        if child!=corestates[target] or not g.overlaps(child):
            raise ValueError("finite actual prefix edge differs from uniform integer identity")
        edges+=1
    return {"n":n,"replayed_actual_edges":edges,"scope":"finite differential, not all-n proof"}


if __name__=="__main__":
    import json
    print(json.dumps({"core":prove_core(),"shell":verify_shell(),
                      "finite_replay":[finite_field_replay(n) for n in (4,8,9)]},
                     indent=2))
