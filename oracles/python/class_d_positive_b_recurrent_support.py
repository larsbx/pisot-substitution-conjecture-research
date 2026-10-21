"""Independent exact Q(beta) calibration of the revised recurrent reduction.

Canonical implementation: kernel/psc/class_d_minus_recurrent_support.mojo.
Finite grids do not prove CycleSum-. Outside-carrier labels are reported;
only unexplained recurrence or a finite sum violation rejects the reduction.
"""
from __future__ import annotations
from fractions import Fraction
from collections import deque
from functools import lru_cache
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "reference"))
from psc_research.overlap_graph import OverlapGraph
from psc_research.overlap_obstruction import sccs

ROWS = json.loads((ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json").read_text())["rows"]
COVER = {tuple(r[:5]) for r in ROWS}


def member(a: int, b: int):
    if a < 2 or b < 1:
        raise ValueError("positive-b residual requires a>=2,b>=1")
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


EXCEPTIONS = {
    (2,1,-2,4,-3): "U", (1,2,2,-4,3): "Ubar",
    (2,1,3,-6,4): "V", (1,2,-3,6,-4): "Vbar",
}


def classify(label, cover=COVER):
    if label[0] == label[1] and label[2:] == (0,0,0):
        return "coincidence"
    if label in cover:
        return "carrier"
    if label == (1,0,0,0,0):
        return "boundary_hit_noncoincidence"
    if label in EXCEPTIONS:
        return "exceptional"
    return "unexplained"


def state_of(g, label):
    shift = tuple(sum(label[2+k]*g.l[k][j] for k in range(3)) for j in range(3))
    return (label[0]+1, label[1]+1, shift)


def occurrence(g, source, i, j):
    top, bottom, t = source
    if not (0 <= i < len(g.sigma[top]) and 0 <= j < len(g.sigma[bottom])):
        raise ValueError("illegal occurrence index")
    return (g.sigma[top][i], g.sigma[bottom][j],
            g.F.sub(g.F.add(g.F.mul(g.F.beta,t),g.prefix[bottom,j]),g.prefix[top,i]))


def exceptional_exit(g, label, a, b):
    name = EXCEPTIONS[label]
    mirror = name.endswith("bar")
    is_u = name.startswith("U")
    choices = [(b,0) if mirror else (0,b)] if is_u else [
        (a+2,b) if mirror else (b,a+2),
        ((b-1,0) if mirror else (0,b-1)) if b>=2 else (0,0),
    ]
    source = state_of(g,label)
    if not g.overlaps(source):
        raise ValueError("exceptional source is not interior")
    witness = []
    for i,j in choices:
        child = occurrence(g,source,i,j)
        if not g.overlaps(child):
            raise ValueError("exceptional exit is not interior")
        witness.append(dict(top_index=i,bottom_index=j))
        source = child
    target_row = (97 if mirror else 69) if is_u or b>=2 else (35 if mirror else 44)
    targets = {tuple(ROWS[target_row][:5])}
    if ROWS[target_row][5] > 2:
        raise ValueError("exceptional target rank exceeds two")
    target = next((v for v in targets if state_of(g,v) == source),None)
    if target is None or target not in COVER:
        raise ValueError("exceptional exit missed the ranked carrier")
    return dict(label=label,name=name,occurrences=witness,target=target)


def _path(g, starts, target):
    parent = {v: None for v in starts}
    queue = deque(starts)
    while queue and target not in parent:
        v = queue.popleft()
        for child in g.adj[v]:
            if child not in parent:
                parent[child] = v
                queue.append(child)
    if target not in parent:
        return []
    out = [target]
    while parent[out[-1]] is not None:
        out.append(parent[out[-1]])
    return out[::-1]


def replay_path(g, labels, path):
    out = []
    for src,dst in zip(path,path[1:]):
        source,target = g.states[src],g.states[dst]
        pair = next((i,j) for i in range(len(g.sigma[source[0]]))
                    for j in range(len(g.sigma[source[1]]))
                    if occurrence(g,source,i,j) == target)
        out.append(dict(source=labels[src],top_index=pair[0],bottom_index=pair[1],target=labels[dst]))
    return out


def counterexample(g, labels, at, a, b):
    roots = [g.index[s] for s in g.seeds()]
    prefix = _path(g,roots,at)
    cycle = next([at]+path for child in g.adj[at] if (path := _path(g,[child],at)))
    return dict(a=a,b=b,label=labels[at],seed=labels[prefix[0]],
                seed_path=replay_path(g,labels,prefix),cycle=replay_path(g,labels,cycle))


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
    classified = {kind: [] for kind in ("carrier","coincidence","exceptional","unexplained","boundary_hit_noncoincidence")}
    exits, counterexamples, sum_violations = [], [], []
    for i in sorted(recurrent):
        v = labels[i]
        kind = classify(v)
        classified[kind].append(v)
        if kind == "exceptional":
            exits.append(exceptional_exit(g,v,a,b))
        if abs(sum(v[2:])) > 1:
            sum_violations.append(v)
        if kind == "unexplained" or abs(sum(v[2:])) > 1:
            counterexamples.append(counterexample(g,labels,i,a,b))
    return dict(a=a,b=b,states=len(labels),recurrent_vertices=len(recurrent),
        recurrent_sccs=components,classified={k:sorted(v) for k,v in classified.items()},
        outside_labels=sorted(labels[i] for i in recurrent if labels[i] not in COVER),
        exceptional_exits=exits,unexplained_labels=sorted(classified["unexplained"]),
        cycle_sum_violations=sorted(sum_violations),counterexamples=counterexamples,
        max_abs_sum=max((abs(sum(labels[i][2:])) for i in recurrent),default=0))


@lru_cache(maxsize=None)
def report(a_max: int = 8, b_max: int = 8):
    if a_max<2 or b_max<1:
        raise ValueError("empty calibration grid")
    rows = [recurrent_report(a,b) for a in range(2,a_max+1) for b in range(1,b_max+1)]
    return dict(status="FINITE_EXACT_RECURRENT_SUPPORT_CALIBRATION",
        authority="independent-Q(beta)-python-oracle",
        canonical="kernel/psc/class_d_minus_recurrent_support.mojo",
        scope=f"minus residual 2<=a<={a_max}, 1<=b<={b_max}",
        theorem_facing_predicate="every recurrent seed label is classified; exceptional exits replay; CycleSum tested only on this finite grid",
        uniform_theorem=False,cover_size=len(COVER),specimens=len(rows),
        outside_recurrent_labels=sorted({v for r in rows for v in r["outside_labels"]}),
        unexplained_recurrent_labels=sorted({v for r in rows for v in r["unexplained_labels"]}),
        cycle_sum_violations=sorted({v for r in rows for v in r["cycle_sum_violations"]}),
        max_recurrent_vertices=max(r["recurrent_vertices"] for r in rows),rows=rows)


def compare_mojo(out, path):
    summaries, labels = {}, {}
    complete = False
    for line in Path(path).read_text().splitlines():
        fields = line.split()
        if fields and fields[0] == "RECURRENT_SUMMARY":
            a,b,*counts = map(int,fields[1:])
            if (a,b) in summaries:
                raise ValueError("duplicate Mojo specimen")
            summaries[a,b] = counts
        if fields and fields[0] == "RECURRENT_LABEL":
            a,b,*v = map(int,fields[1:-1])
            labels.setdefault((a,b),[]).append((tuple(v),fields[-1]))
        if line == "CLASS_D_MINUS_RECURRENT_FINITE_CALIBRATION_OK specimens=56 uniform_theorem=false":
            complete = True
    expected_keys = {(r["a"],r["b"]) for r in out["rows"]}
    if not complete or set(summaries) != expected_keys or set(labels) != expected_keys:
        raise ValueError("missing/extra Mojo specimens or completion receipt")
    for r in out["rows"]:
        key = r["a"],r["b"]
        counts = [r["states"],r["recurrent_vertices"],r["recurrent_sccs"]]
        counts += [len(r["classified"][k]) for k in ("carrier","coincidence","exceptional","unexplained")]
        counts += [r["max_abs_sum"],len(r["classified"]["boundary_hit_noncoincidence"])]
        expected = sorted((tuple(v),k) for k,vs in r["classified"].items() for v in vs)
        if summaries[key] != counts or sorted(labels[key]) != expected:
            raise ValueError(f"Mojo/Python recurrent classification disagreement at {key}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mojo-log")
    args = parser.parse_args()
    out = report()
    print(json.dumps(out, indent=2),flush=True)
    if args.mojo_log:
        compare_mojo(out,args.mojo_log)
    if out["unexplained_recurrent_labels"] or out["cycle_sum_violations"]:
        raise SystemExit("unexplained recurrent support or finite CycleSum violation; see replayable counterexamples")
