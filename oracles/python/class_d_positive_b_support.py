"""Independent exact Q(beta) support sweep for positive-b residual class D.

Finite calibration only. It checks whether every nonterminal seed-reachable
label lies in the sealed minus b=0 145-label cover over a declared grid.
Any new label is emitted explicitly. This is NOT the uniform closure theorem.
"""
from __future__ import annotations
from fractions import Fraction
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "reference"))
from psc_research.overlap_graph import OverlapGraph

COVER = {
    tuple(r[:5])
    for r in json.loads(
        (ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json").read_text()
    )["rows"]
}


def member(a: int, b: int):
    if a < 0 or b < 1:
        raise ValueError("positive-b residual requires a>=0,b>=1")
    p, q, r = 3*a + 5 + b, 3*a + 6 + b, 2*a + 4 + b
    return {1:(1,)+(3,)*p+(2,), 2:(2,)+(3,)*q+(1,), 3:(2,)+(3,)*r+(2,)}


def labelled_support(a: int, b: int, cap: int = 20000):
    g = OverlapGraph(member(a,b), cap)
    if g.capped:
        raise RuntimeError("STATE_BUDGET_EXHAUSTED")
    # Invert the Perron-length basis exactly, as in class_d_boundary_probe.py.
    matrix = [[g.l[j][i] for j in range(3)] + [Fraction(i==j) for j in range(3)] for i in range(3)]
    for col in range(3):
        pivots = [i for i in range(col,3) if matrix[i][col]]
        if not pivots:
            raise ValueError("singular length basis")
        pivot = pivots[0]
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        matrix[col] = [v/scale for v in matrix[col]]
        for i in range(3):
            if i == col:
                continue
            scale = matrix[i][col]
            matrix[i] = [x-scale*y for x,y in zip(matrix[i],matrix[col])]
    labels = []
    for top,bottom,t in g.states:
        w = [sum(matrix[k][3+j]*t[j] for j in range(3)) for k in range(3)]
        if any(x.denominator != 1 for x in w):
            raise ValueError("nonintegral offset")
        labels.append((top-1,bottom-1,*map(int,w)))
    return labels


def report(a_max=8,b_max=8):
    rows=[]
    new=set()
    for a in range(2,a_max+1):
        for b in range(1,b_max+1):
            labels=labelled_support(a,b)
            outside=[x for x in labels if x[2:] != (0,0,0) and x not in COVER]
            rows.append(dict(a=a,b=b,states=len(labels),outside=len(outside)))
            new.update(outside)
    return dict(
        status="FINITE_EXACT_SUPPORT_CALIBRATION",
        authority="independent-Q(beta)-python-oracle",
        scope=f"minus residual 2<=a<={a_max}, 1<=b<={b_max}",
        uniform_closure=False,
        cover_size=len(COVER),
        specimens=len(rows),
        new_nonterminal_labels=sorted(new),
        rows=rows,
    )


if __name__ == "__main__":
    out=report()
    print(json.dumps(out,indent=2))
    if out["new_nonterminal_labels"]:
        raise SystemExit("positive-b graph escaped sealed cover")
