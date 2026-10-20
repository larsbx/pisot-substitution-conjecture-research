"""Independent exact Q(beta) calibration, not a uniform seed theorem."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import class_d_positive_b_recurrent_support as support


def sample(k: int, cap: int = 20000):
    if not isinstance(k, int) or not 2 <= k <= 50:
        raise ValueError("finite calibration budget requires integer 2<=k<=50")
    a, b = 2*k-1, 1
    g = support.OverlapGraph(support.member(a,b), cap)
    if g.capped:
        raise RuntimeError("capped graph cannot establish seed nonmembership")
    labels = [(2,1,-2*k,4*k,-3*k),(1,2,2*k,-4*k,3*k)]
    source, mirror = [support.state_of(g,v) for v in labels]
    if not g.overlaps(source) or not g.overlaps(mirror):
        raise ValueError("high-sum formal cycle is not interior")
    ti, bi = 4*k+4, 6*k+4
    if support.occurrence(g,source,ti,bi)!=mirror or support.occurrence(g,mirror,bi,ti)!=source:
        raise ValueError("high-sum occurrence replay failed")
    graph_labels = support._labels(g)
    counterexamples = [support.counterexample(g,graph_labels,i,a,b)
                      for i,v in enumerate(g.states) if v in (source,mirror)]
    return dict(k=k,a=a,b=b,labels=labels,occurrences=[(ti,bi),(bi,ti)],
                interior=True,states=len(g.states),reachable_pair_vertices=len(counterexamples),
                counterexamples=counterexamples,seed_nonreachability_scope="this complete finite graph only")


def compare_mojo(rows, path):
    actual = {}
    symbolic_receipt = False
    for line in Path(path).read_text().splitlines():
        fields = line.split()
        if line == "HIGH_SUM_FORMAL_RAY_CERTIFIED k>=2 a=2k-1 b=1 abs_sum=k interior=true period=2 seed_reachability=not_asserted_by_this_certificate":
            symbolic_receipt = True
        if fields and fields[0] == "HIGH_SUM_SEED_SAMPLE":
            if len(fields)!=10 or (fields[2],fields[4],fields[6],fields[8]) != ("a","b","complete_states","reachable_pair_vertices"):
                raise ValueError("malformed Mojo sample")
            k,a,b,n,reached = map(int,fields[1::2])
            if k in actual:
                raise ValueError("duplicate Mojo sample")
            actual[k] = (a,b,n,reached)
    expected = {r["k"]:(r["a"],r["b"],r["states"],r["reachable_pair_vertices"]) for r in rows}
    if not symbolic_receipt or actual != expected:
        raise ValueError("missing or disagreeing Mojo high-sum calibration")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mojo-log",type=Path)
    args = parser.parse_args()
    rows = [sample(k) for k in (2,3,8)]
    # Preserve the exact replay payload even when cross-language agreement fails.
    print(json.dumps(dict(authority="independent-Q(beta)-python-calibration",rows=rows,
                          uniform_seed_theorem=False),indent=2),flush=True)
    if args.mojo_log:
        compare_mojo(rows,args.mojo_log)
    if any(r["reachable_pair_vertices"] for r in rows):
        raise SystemExit("SEED_REACHABLE_HIGH_SUM_COUNTEREXAMPLE: replay is in JSON")


if __name__ == "__main__":
    main()
