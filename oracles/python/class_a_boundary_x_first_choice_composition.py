"""Proof-dependency-aware composition of ALL X first-choice coincidence paths.

The X complete-star theorem is on main; selected exits for six of its ten
targets originate in research-only PRs #420/#424/#425. Exact original
source blobs are included unchanged for conformance and acceptance,
not reclassified as main-proved. No all-later-choice or PSC claim.
"""
from pathlib import Path
import runpy
ROOT=Path(__file__).resolve().parent
Geometry=runpy.run_path(str(ROOT/"class_a_boundary_children.py"))["Geometry"]
TWO=runpy.run_path(str(ROOT/"class_a_boundary_b4_r4_exit_recovery.py"))
THREE=runpy.run_path(str(ROOT/"class_a_boundary_three_exit_recovery.py"))
T2=runpy.run_path(str(ROOT/"class_a_boundary_t2_exit.py"))
X=(0,0,1,0,-1);C=(2,2,0,0,0)
Q=(2,0,0,-1,1);V2=(2,0,0,-1,2);W=(1,0,0,1,-1)
RH=(2,0,0,1,-1);B=(2,2,0,-2,3)
Y0=(2,2,1,-1,-1);Q3=(0,2,1,-1,1)
# Canonical oriented tuples are identity; PR numbers are proof provenance.
EXITS={
    (2,0,0,-1,-1):("B4",425),
    (2,0,0,-1,0):("B3",424),
    Q:("Q",0),V2:("V2",0),
    (2,2,1,-1,-2):("T2+",420),Y0:("Y0",0),
    (0,2,1,-1,-2):("R4",425),
    (0,2,1,-1,-1):("R5",424),
    (0,2,1,-1,0):("R3",424),Q3:("Q3",0)
}
def reverse(w):return (w[1],w[0],*(-v for v in w[2:]))
def x_guard(g,i,j):
    n,d,A=g.n,g.d,g.n+g.d
    if not(0<=i<=A+1 and 0<=j<=A+1):
        raise ValueError("nonexistent literal occurrence")
    if 1<=i<=A:
        return (j==0 and d<=i<=d+3) or (1<=j<=A and i-j in(d+2,d+3))
    return i==A+1 and n-2<=j<=n+1
def main_suffix(w,g):
    if w==Q:return [(1,2,C)]
    if w==V2:return [(g.n,0,W),(1,0,Q),(1,2,C)]
    if w==Y0:return [(g.t+1,1,B),(g.n-1,0,RH),(2,1,C)]
    if w==Q3:return [(g.n+g.d+1,0,X),(g.d+1,0,Q),(1,2,C)]
    raise ValueError("no accepted main suffix")
def index(x,g):
    return x.k*g.k+x.t*g.t+x.c if hasattr(x,"k") and hasattr(x,"t") and hasattr(x,"c") else x
def suffix(w,g):
    title,pr=EXITS[w]
    if pr==0:return main_suffix(w,g)
    if pr==420:return T2["path"](g.k,g.t)
    if pr==424:
        return [(index(i,g),index(j,g),v) for i,j,v in THREE["PATHS"][w]]
    if pr==425:
        ch=TWO["CHAMBERS"][min(g.t,2)]
        return [(index(i,g),index(j,g),v) for i,j,v in TWO["paths"](w,ch)]
    raise ValueError("unregistered exit provenance")
def verify(g,start,edges):
    source=start
    for i,j,target in edges:
        assert g.interior(source)
        assert g.child(source,i,j)==target,("wrong typed Parikh child",g.k,g.t,source,i,j,target)
        assert g.interior(target),("not a strict overlap",g.k,g.t,target)
        source=target
    assert source==C,("not typed coincidence",source)
def source_image_symbolic():
    """Use main's complete nine-kind X guard and derive its ten labels.

    RUN/FIRST(d+r,0) -> (y,x,0,-1,2-r), r=0..3.
    RUN/RUN i-j=d+2 or d+3 -> (y,y,1,-1,-1/-2),
    with n-2 and n-3 indexed pairs respectively.
    LAST/RUN(A+1,n-2+r) -> (x,y,1,-1,-2+r), r=0..3.
    The second RR strip is empty at the unique n=3 member.
    """
    labels={(2,0,0,-1,2-r) for r in range(4)}
    labels|={(2,2,1,-1,-1),(2,2,1,-1,-2)}
    labels|={(0,2,1,-1,-2+r) for r in range(4)}
    assert labels==set(EXITS) and len(labels)==10
    return dict(base_labels=10,source_indexed_count="2n+3",n3_member_labels=9)
def conditional_certificate():
    # Each research module checks exact all-k,t proper-prefix transports,
    # genuine word indices, source types, and strict Perron margins.
    a=THREE["symbolic_certificate"]()
    b=TWO["symbolic_certificate"]()
    c=T2["symbolic_proof"]()
    d=T2["strict_certificate"]()
    assert a["actual_symbolic_edges"]==14
    assert b["directed_symbolic_edge_checks"]==46
    assert c["coefficientwise_occurrence_edges"]==10
    assert d["strict_margins"]==26
    assert sum(pr==0 for _,pr in EXITS.values())==4
    assert sum(pr!=0 for _,pr in EXITS.values())==6
    return dict(source=source_image_symbolic(),
                existing_selected_exit_sources=4,
                research_only_selected_exit_sources=6,
                cited_candidate_PRs=[420,424,425],
                conditional_X_first_choice_depth=6,
                mainline_X_first_choice_accepted=False,
                forward_closed=False,all_later_choices_productive=False,
                universal_BH=False)
def probe():
    counts=dict(members=0,oriented_source_cells=0,pairs=0,
                indexed_first_choices=0,composed_edges=0,max_depth=0)
    depths={}
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            A=g.n+g.d
            chosen=[]
            for i in range(A+2):
                for j in range(A+2):
                    child=g.child(X,i,j)
                    active=x_guard(g,i,j)
                    assert g.interior(child)==active,(k,t,i,j,child)
                    if active:
                        assert child in EXITS
                        chosen.append((i,j,child))
            assert len(chosen)==2*g.n+3
            assert len({w for _,_,w in chosen})==(9 if g.n==3 else 10)
            for flip in (0,1):
                start=reverse(X) if flip else X
                counts["oriented_source_cells"]+=1
                counts["pairs"]+=(A+2)**2
                for i,j,target in chosen:
                    first=(j,i,reverse(target)) if flip else (i,j,target)
                    tpath=suffix(target,g)
                    rest=[(j,i,reverse(w)) for i,j,w in tpath] if flip else tpath
                    path=[first]+rest
                    verify(g,start,path)
                    assert len(path)<=6
                    counts["indexed_first_choices"]+=1
                    counts["composed_edges"]+=len(path)
                    counts["max_depth"]=max(counts["max_depth"],len(path))
                    depths[len(path)]=depths.get(len(path),0)+1
            counts["members"]+=1
    assert (counts["members"],counts["oriented_source_cells"],counts["pairs"],
            counts["indexed_first_choices"],counts["composed_edges"])==(117,234,297648,6786,24468)
    return dict(scope="finite literal/Fraction conformance, symbolic dependencies separate",
                **counts,depth_histogram=depths,
                all_ten_selected_exits_specimen_replayed=True,
                conditional_not_accepted_on_main=True,
                forward_closed=False,universal_BH=False)
if __name__=="__main__":
    import json
    print(json.dumps(conditional_certificate(),sort_keys=True,indent=2))
    print(json.dumps(probe(),sort_keys=True,indent=2))
