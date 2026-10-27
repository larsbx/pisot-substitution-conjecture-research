"""Synthesize a proposed common middle potential from independent exact graphs.

Finite synthesis only; uniform descent requires the native symbolic checker.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json,sys
from class_b_core_exact import ExactMember
from class_b_ray_tables import potentials
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/class-b-step2c-2026-10-27/middle-potentials.json'


def graph(job):
    branch,g,r=job
    class G: pass
    # Return only plain objects across the process boundary.
    return ExactMember(branch,g,6*g+r).build()


def render(entries):
    text='"""Finite exact synthesis targets; evidence only after symbolic descent."""\n'
    for e in entries:
        text+=f'comptime {e["branch"].upper()} = "'+' '.join(str(n) for row in e['potential'] for n in row)+'"\n'
    return text+'''


def middle_potentials(eps: Int) raises -> List[List[Int]]:
    if eps != 1 and eps != -1:
        raise Error("eps must be +-1")
    var text = PLUS if eps == 1 else MINUS
    var rows = List[List[Int]]()
    var row = List[Int]()
    for tok in text.split(" "):
        row.append(Int(String(tok)))
        if len(row) == 6:
            rows.append(row^)
            row = List[Int]()
    if len(row) != 0:
        raise Error("malformed middle potential table")
    return rows^
'''


if __name__=='__main__':
    result=[]
    for branch,gs,j0,j1 in [('plus',range(16,21),2,14),('minus',range(12,17),6,6)]:
        jobs=[(branch,g,r) for g in gs for r in range(j0,g-j1+1)]
        with ProcessPoolExecutor(max_workers=4) as pool:adjs=list(pool.map(graph,jobs))
        class G:
            def __init__(self,a):self.edges=a
        b=potentials([G(a) for a in adjs])
        result.append(dict(branch=branch,synthesis_members=[list(j) for j in jobs],potential=[list(k)+[v] for k,v in b]))
        print(branch,'members',len(jobs),'keys',len(b),'max_b',max(v for k,v in b),flush=True)
    text=json.dumps(result,indent=1)+'\n'
    if '--check' in sys.argv:
        if OUT.read_text()!=text or (ROOT/'kernel/psc/class_b_middle_potential_tables.mojo').read_text()!=render(result):raise ValueError('middle potential candidate drift')
    else:
        OUT.write_text(text)
        (ROOT/'kernel/psc/class_b_middle_potential_tables.mojo').write_text(render(result))
