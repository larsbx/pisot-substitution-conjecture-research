"""Reproduce the middle candidate from exact native core exports (finite fit).

Five l-values on each of fifteen rays per branch. This generates a target,
not a uniform certificate. --check compares both JSON and Mojo byte-for-byte.
"""
from pathlib import Path
import json,sys
from class_b_regime_probe import fit_ray,middle_fit
ROOT=Path(__file__).resolve().parents[2]
PACKET=ROOT/'evidence/class-b-step2c-2026-10-27'
OUT=ROOT/'kernel/psc/class_b_middle_tables.mojo'


def candidates(directory):
    entries=[]
    for branch,gs,j0,j1 in [('plus',range(16,21),2,14),('minus',range(12,17),6,6)]:
        rays={}
        for g in gs:
            files={int(p.stem.split('-q')[1]):p for p in Path(directory).glob(f'{branch}-g{g}-q*.labels')}
            for r in range(j0,g-j1+1):
                qs=[g*l+r for l in range(4,9)]
                if any(q not in files for q in qs):raise ValueError(('missing native core export',branch,g,r))
                fit=fit_ray({q:files[q] for q in qs},g,r)
                if fit is None or fit[0]!=qs[1] or fit[1]!=4:raise ValueError('middle carrier does not fit from l=5')
                rays[g,r]=fit[2]
        result=middle_fit(rays)
        if not result['ok'] or result['rows']!=529 or len(rays)!=15:raise ValueError(result)
        entries.append(dict(branch=branch,g0=min(gs),rlo=j0,rhi_offset=j1,l0=4,
                            rows=[[*k,*v] for k,v in sorted(result['table'].items())]))
    return entries


def render(entries):
    lines=['"""Exact-export middle candidates, not closure or descent certificates."""']
    for e in entries:
        if any(any(x[i] for i in (7,8,11,12)) for x in e['rows']):raise ValueError('endpoints are not l-affine')
        s=' '.join(' '.join(map(str,x[:4]+[x[5],x[6],x[9],x[10]])) for x in e['rows'])
        lines.append(f'comptime {e["branch"].upper()} = "{s}"')
    return '\n'.join(lines)+'''


def middle_rows(eps: Int) raises -> List[List[Int]]:
    if eps != 1 and eps != -1:
        raise Error("eps must be +-1")
    var text = PLUS if eps == 1 else MINUS
    var rows = List[List[Int]]()
    var row = List[Int]()
    for tok in text.split(" "):
        row.append(Int(String(tok)))
        if len(row) == 8:
            rows.append(row^)
            row = List[Int]()
    if len(row) != 0:
        raise Error("malformed middle table")
    return rows^
'''


if __name__=='__main__':
    e=candidates(PACKET/'core-labels')
    js=json.dumps(e,indent=1)+'\n';mojo=render(e)
    if '--check' in sys.argv:
        if (PACKET/'middle-candidates.json').read_text()!=js or OUT.read_text()!=mojo:raise ValueError('middle table drift')
        print('CLASS_B_MIDDLE_FINITE_FIT branches 2 rays 30 exports 150 rows_per_branch 529')
    else:
        (PACKET/'middle-candidates.json').write_text(js);OUT.write_text(mojo)
