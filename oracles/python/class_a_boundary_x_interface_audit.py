"""Canonical X first-choice interface audit; CONDITIONAL exit composition.

Uses main's complete X actual-word star. A candidate exit in an unmerged
research PR is not equivalent to an accepted mainline source proof.
This audit establishes no new universal BH or first-choice theorem.
"""
from pathlib import Path
import runpy
ROOT=Path(__file__).resolve().parent
Geometry=runpy.run_path(str(ROOT/"class_a_boundary_children.py"))["Geometry"]
TX=runpy.run_path(str(ROOT/"class_a_boundary_tx_children.py"))
X=(0,0,1,0,-1); C=(2,2,0,0,0)
def reverse(w):
    return(w[1],w[0],*(-z for z in w[2:]))

# Oriented five-tuples are canonical, names are aliases only.
# Bounds are length of a selected tail *starting at the child label*.
# open/side statuses are source-provenance facts, not acceptance on main.
SOURCES={
    (2,0,0,-1,-1):("B4",5,"research-only",377),
    (2,0,0,-1,0):("B3",2,"research-only",376),
    (2,0,0,-1,1):("Q",1,"main",0),
    (2,0,0,-1,2):("V2",3,"main",0),
    (2,2,1,-1,-2):("R(T2)",3,"research-only",420),
    (2,2,1,-1,-1):("Y0",3,"main",412),
    (0,2,1,-1,-2):("R4",4,"research-only",378),
    (0,2,1,-1,-1):("R5",3,"research-only",380),
    (0,2,1,-1,0):("R3",2,"research-only",375),
    (0,2,1,-1,1):("Q3",3,"main",412),
}
assert len(SOURCES)==10

def conditional_certificate():
    assert all(depth>=1 for _,depth,_,_ in SOURCES.values())
    status={}
    for _,(_,_,kind,_) in SOURCES.items():
        status[kind]=status.get(kind,0)+1
    assert status=={"main":4,"research-only":6}
    union=set(SOURCES)|{reverse(w) for w in SOURCES}
    assert len(union)==20
    return dict(distinct_base_children=10,oriented_image_labels=20,
                mainline_registered_exits=4,
                research_only_candidate_exits=6,
                max_candidate_tail_depth=5,
                conditional_X_first_choice_depth=6,
                every_first_choice_proved_on_main=False,
                source_stars_vs_exits_distinguished=True,
                forward_closed=False,universal_BH=False)

def _main_suffix(label,g):
    # These are accepted mainline sources; all original typed indices
    # are independently checked by the unchanged Fraction Geometry.
    if label==(2,0,0,-1,1):
        return [(1,2,C)]
    if label==(2,0,0,-1,2):
        return [(g.n,0,(1,0,0,1,-1)),(1,0,(2,0,0,-1,1)),(1,2,C)]
    if label==(2,2,1,-1,-1):
        return TX["path"](4,g)
    if label==(0,2,1,-1,1):
        return TX["path"](0,g)
    raise ValueError("not a main-accepted selected exit")

def _verify_main_suffix(g,start,steps):
    state=start
    for i,j,target in steps:
        assert g.interior(state)
        assert g.child(state,i,j)==target
        assert g.interior(target)
        state=target
    assert state==C

def probe():
    pairs=accepted=verified_main_edges=0
    coverage=set()
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            original=set(g.edges(X))
            assert len(original)==2*g.n+3
            assert {target for _,_,target in original}==(set(SOURCES)-({(2,2,1,-1,-2)} if g.n==3 else set()))
            assert original=={(i,j,g.child(X,i,j))
                for i in range(len(g.words[0]))
                for j in range(len(g.words[0]))
                if TX["predicted"](2,g,i,j)}
            for flip in (0,1):
                w=reverse(X) if flip else X
                actual=set(g.edges(w))
                expected={(j,i,reverse(v)) for i,j,v in original} if flip else original
                assert actual==expected
                pairs+=len(g.words[0])**2
                accepted+=len(actual)
                for i,j,v in actual:
                    target=reverse(v) if flip else v
                    coverage.add(target)
                    if target not in SOURCES or SOURCES[target][2]!="main":
                        continue
                    tail=_main_suffix(target,g)
                    steps=[(b,a,reverse(z)) for a,b,z in tail] if flip else tail
                    _verify_main_suffix(g,v,steps)
                    verified_main_edges+=len(steps)
    assert (pairs,accepted, len(coverage))==(297648,6786,10)
    return dict(scope="finite X star audit; candidate exits from research-only branches not replayed",
                members=117,oriented_source_cells=234,
                enumerated_pairs=pairs,indexed_children=accepted,
                distinct_base_labels=len(coverage),
                main_only_suffix_replay_edges=verified_main_edges,
                conditional=conditional_certificate(),
                not_universal_X_first_choice_proof=True)

if __name__=="__main__":
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
