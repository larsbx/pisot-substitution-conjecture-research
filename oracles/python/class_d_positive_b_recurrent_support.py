"""Exact recurrent-support calibration for the minus positive-b class-D residual.

Finite calibration only.  It asks the theorem-facing question, not full carrier
closure: does every seed-reachable vertex lying on a directed cycle belong to
the sealed 145-label carrier?

Any outside recurrent label is emitted explicitly and makes the executable fail.
No finite grid is promoted to a uniform theorem.
"""
from __future__ import annotations
from fractions import Fraction
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "reference"))
from psc_research.overlap_graph import OverlapGraph
from psc_research.overlap_obstruction import sccs

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


def _labels(g: OverlapGraph):
    matrix = [
        [g.l[j][i] for j in range(3)] + [Fraction(i == j) for j in range(3)]
        for i in range(3)
    ]
    for col in range(3):
        pivots = [i for i in range(col, 3) if matrix[i][col]]
        if not pivots:
            raise ValueError("singular length basis")
        pivot = pivots[0]
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        matrix[col] = [v / scale for v in matrix[col]]
        for i in range(3):
            if i == col:
                continue
            scale = matrix[i][col]
            matrix[i] = [x - scale*y for x, y in zip(matrix[i], matrix[col])]
    out = []
    for top, bottom, t in g.states:
        w = [sum(matrix[k][3+j]*t[j] for j in range(3)) for k in range(3)]
        if any(x.denominator != 1 for x in w):
            raise ValueError("nonintegral offset")
        if any(sum(w[k]*g.l[k][j] for k in range(3)) != t[j] for j in range(3)):
            raise ValueError("offset inverse replay failed")
        out.append((top-1, bottom-1, *map(int, w)))
    return out


def _has_cycle(g: OverlapGraph, comp: list[int]) -> bool:
    return len(comp) > 1 or (bool(comp) and comp[0] in g.adj[comp[0]])


def recurrent_report(a: int, b: int, cap: int = 20000):
    g = OverlapGraph(member(a,b), cap)
    if g.capped:
        raise RuntimeError("STATE_BUDGET_EXHAUSTED")
    labels = _labels(g)
    recurrent = set()
    components = 0
    for comp in sccs(g):
        if _has_cycle(g, comp):
            components += 1
            recurrent.update(comp)
    outside = sorted(
        labels[i]
        for i in recurrent
        if labels[i][2:] != (0,0,0) and labels[i] not in COVER
    )
    return dict(
        a=a,
        b=b,
        states=len(labels),
        recurrent_vertices=len(recurrent),
        recurrent_sccs=components,
        outside_recurrent=len(outside),
        outside_labels=outside,
    )


def report(a_max: int = 8, b_max: int = 8):
    rows = []
    outside = set()
    for a in range(2, a_max+1):
        for b in range(1, b_max+1):
            row = recurrent_report(a,b)
            rows.append(row)
            outside.update(row["outside_labels"])
    return dict(
        status="FINITE_EXACT_RECURRENT_SUPPORT_CALIBRATION",
        authority="independent-Q(beta)-python-oracle",
        scope=f"minus residual 2<=a<={a_max}, 1<=b<={b_max}",
        theorem_facing_predicate="every nonterminal cycle vertex lies in sealed 145-label carrier",
        uniform_theorem=False,
        cover_size=len(COVER),
        specimens=len(rows),
        outside_recurrent_labels=sorted(outside),
        max_recurrent_vertices=max(r["recurrent_vertices"] for r in rows),
        rows=rows,
    )


if __name__ == "__main__":
    out = report()
    print(json.dumps(out, indent=2))
    if out["outside_recurrent_labels"]:
        raise SystemExit("positive-b recurrent support escaped sealed carrier")
