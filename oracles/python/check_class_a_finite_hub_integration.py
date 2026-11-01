"""Independent exact full-adjacency comparison for 32 bounded native graphs.

Uses the original literal-word/Fraction builders, including indexed edge
multiplicity. Native graph equality is verified after exact lattice decoding;
counts alone never pass this checker. No universal BH conclusion.
"""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def compare_cell(job):
    binary,mode,k,t = job
    filename = 'class_a_boundary_four_seed_scc.py' if mode==4 else 'class_a_boundary_nine_seed_scc.py'
    oracle=runpy.run_path(str(ROOT/'oracles/python'/filename))
    states,adj,ids,_ = oracle['build'](k,t)
    actual=subprocess.check_output([binary,str(mode),str(k),str(t)],text=True)
    native=[];native_adj=[];meta=None
    for line in actual.splitlines():
        if line.startswith('GRAPH '):
            assert list(map(int,line.split()[1:4]))==[mode,k,t]
        elif line.startswith('V '):
            fields=list(map(int,line.split()[1:]));index=fields[0]
            assert index==len(native)
            native.append(tuple(fields[1:6]));native_adj.append(fields[6:])
        elif line.startswith('AUDIT '):meta=list(map(int,line.split()[1:]))
    assert meta and len(set(native))==len(native) and set(native)==set(states)
    expected={w:Counter(states[e[0]] for e in adj[i]) for i,w in enumerate(states)}
    got={w:Counter(native[e] for e in native_adj[i]) for i,w in enumerate(native)}
    assert got==expected,('complete adjacency/multiplicity mismatch',mode,k,t)
    assert meta[0]==len(states) and meta[1]==sum(map(len,adj))
    assert meta[3:6]==[1,0,2]
    if mode==9:
        seed=(0,0,0,1,0)
        targets=set(expected[seed])
        reversed_targets={(w[1],w[0],-w[2],-w[3],-w[4]) for w in targets}
        assert sum(expected[seed].values())==2*(k+2*t+5)-1
        assert len(targets)==8 and len(targets|reversed_targets)==16
    encoded=json.dumps([(w,sorted(expected[w].items())) for w in sorted(expected)],separators=(',',':')).encode()
    return dict(mode=mode,k=k,t=t,vertices=meta[0],indexed_edges=meta[1],sccs=meta[2],
                recurrent_sccs=meta[3],bad_sink_sccs=meta[4],typed_terminals=meta[5],
                max_depth_to_X=meta[6],max_depth_to_coincidence=meta[7],outside_X_closure=meta[8],
                full_adjacency_equal=True,graph_sha256=hashlib.sha256(encoded).hexdigest())


if __name__=='__main__':
    binary=str(Path(sys.argv[1]).resolve())
    jobs=[(binary,mode,k,t) for mode in [4,9] for k in range(4) for t in range(4)]
    with ProcessPoolExecutor(max_workers=4) as pool:results=list(pool.map(compare_cell,jobs))
    print(json.dumps(dict(complete_graph_comparisons=len(results),specimens=results,
        scope='k,t=0..3 only; four/nine stated seed sets; complete state sets and edge multiplicities agree; no universal BH or PSC'),indent=2,sort_keys=True))
