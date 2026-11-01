"""Every actual first-choice CY child has a selected typed-coincidence exit.

Independent literal-word/Parikh/Fraction oracle for a separately stated
all-parameter piecewise *symbolic hand derivation*. This finite replay
does not itself prove the symbolic inequalities or global boundary hitting.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parent
old = runpy.run_path(str(ROOT / "class_a_boundary_cy_children.py"))
Geometry = old["Geometry"]
CY, Y0, C = old["CY"], old["Y0"], old["C"]
reverse = old["reverse"]
B0 = (1,0,0,0,-2)
B1 = (1,2,1,0,-2)
B2 = (2,2,1,-1,-2)
B4 = (2,1,1,-1,-1)
B5 = (2,1,1,-1,-2)
B = (2,2,0,-2,3)
RH = (2,0,0,1,-1)
J = (2,2,0,2,-2)
H = (0,2,0,1,-1)
H1 = (0,2,0,-1,1)
V2 = (2,0,0,-1,2)
W = (1,0,0,1,-1)
Q = (2,0,0,-1,1)
U = (0,2,1,2,-3)
CHILD_LABELS = {B0,B1,B2,Y0,B4,B5}


def tail(label, g):
    """Actual zero-based address + exact five-coordinate target each step.

    Cases are rectangular integer chambers with explicit endpoint splits.
    Reverse each *actual* occurrence pair for the opposite orientation.
    """
    k,t,n,d=g.k,g.t,g.n,g.d
    A=n+d
    if label == B0:
        if t==0:
            j=(0,0,0,1,-1) if n==3 else H
            return [(1,A+1,(2,0,-1,-3,4)),(0,d+4,j),(2,1,C)]
        return [(t,A+1,(2,0,-1,-3,5)),(1,t+6,J),(3,1,C)]
    if label == B1:
        return [(t+2,0,(2,0,0,-3,3)),(1,4,C)]
    if label == B2:
        if t==0:
            return [(0,n,(0,1,0,-3,3)),(0,3,H),(2,1,C)]
        if t==1:
            return [(0,n,(0,1,0,-3,4)),(k+3,1,J),(3,1,C)]
        return [(0,k+3,(0,2,0,-3,3)),(1,4,C)]
    if label == Y0:
        return [(t+1,1,B),(n-1,0,RH),(2,1,C)]
    if label == B4:
        if t>=1:
            return [(t,0,(2,1,-1,-2,4)),
                    (0,t+4,(0,0,0,3,-3) if k==0 else (0,2,0,3,-3)),
                    (4,1,C)]
        if k>=1:
            return [(0,0,(0,1,0,-2,3)),(n,1,J),(3,1,C)]
        return [(0,0,(0,1,0,-2,3)),(n+1,1,(2,2,0,2,-3)),
                (0,2,H1),(1,2,C)]
    if label == B5:
        K=(0,0,-1,-2,4) if t==0 else (0,2,-1,-2,4)
        out=[(0,k+4,K)]
        if t==0:
            out.append((1,5,J))
            if k==0:
                out.extend([(2,0,(2,0,-1,0,1)),(0,d+1,H),(2,1,C)])
            else:
                out.append((3,1,C))
        elif k==0:
            out.extend([(0,t+2,(0,2,1,2,-5)),(0,0,(0,0,-1,-3,4)),
                        (0,d+4,H),(2,1,C)])
        elif k==1:
            out.extend([(0,n,(0,1,1,2,-3)),(d+4,1,C)])
        elif k==2:
            # Main's already accepted U->V2->W->Q->C tail, not
            # the pending shorter U->V1->C recovery from PR #411.
            out.extend([(0,t+4,U),(d+2,0,V2),(n,0,W),
                        (1,0,Q),(1,2,C)])
        else:
            out.extend([(1,t+5,J),(3,1,C)])
        return out
    raise ValueError("CY child not in the six certified labels")


def verify_path(g, start, path):
    current=start
    for i,j,expected in path:
        if not g.interior(current):
            raise AssertionError(("source not interior", current))
        if g.child(current,i,j)!=expected:
            raise AssertionError(("bad occurrence or Parikh",current,i,j,expected))
        if not g.interior(expected):
            raise AssertionError(("target not strict",current,i,j,expected))
        current=expected
    if current != C:
        raise AssertionError(("not typed y/y zero coincidence",current))


def probe():
    members=pairs=children=composed_edges=tail_edges=0
    max_depth=0
    max_attainers=[]
    source_cells=0
    case_counts={}
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            members+=1
            # A finite reverse-word check is independent of symbolic
            # reversal; each original CY occurrence is replayed below.
            base_edges=set(g.edges(CY))
            base_targets={w for _,_,w in base_edges}
            assert base_targets == CHILD_LABELS
            for flip in (0,1):
                source=reverse(CY) if flip else CY
                actual=set(g.edges(source))
                expected={(j,i,reverse(w)) for i,j,w in base_edges} if flip else base_edges
                assert actual==expected
                source_cells+=1
                pairs+=len(g.words[source[0]])*len(g.words[source[1]])
                children+=len(actual)
                seen=set()
                for i,j,w in sorted(actual):
                    base=reverse(w) if flip else w
                    assert base in CHILD_LABELS
                    if base not in seen:
                        branch=tail(base,g)
                        steps=[(q,p,reverse(v)) for p,q,v in branch] if flip else branch
                        verify_path(g,w,steps)
                        tail_edges+=len(steps)
                        seen.add(base)
                        case_counts[str(base)]=case_counts.get(str(base),0)+1
                    else:
                        branch=tail(base,g)
                        steps=[(q,p,reverse(v)) for p,q,v in branch] if flip else branch
                    full=[(i,j,w)]+steps
                    verify_path(g,source,full)
                    length=len(full)
                    assert length<=7
                    composed_edges+=length
                    if length>max_depth:
                        max_depth=length
                        max_attainers=[(k,t,flip,i,j,list(w))]
                    elif length==max_depth and len(max_attainers)<12:
                        max_attainers.append((k,t,flip,i,j,list(w)))
                # `seen` holds base-normalized labels (reverse(w) when flipped), so both
                # orientations must cover exactly CHILD_LABELS.
                assert seen==CHILD_LABELS
    return dict(scope="finite exact all-first-choice replay of CY / reversal; symbolic proof separate; not global BH",
                members=members,source_cells=source_cells,pairs=pairs,
                indexed_first_children=children,composed_path_edges=composed_edges,
                unique_tail_replay_edges=tail_edges,
                max_first_choice_depth=max_depth,
                witnessed_max_cases=max_attainers,
                label_replay_cases=case_counts,
                every_first_choice_productive_in_selected_continuation=True,
                forward_closed=False,all_later_choices_productive=False,
                universal_BH=False)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
