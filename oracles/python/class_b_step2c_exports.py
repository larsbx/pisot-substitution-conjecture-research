"""Reproduce all 696 native finite exports behind step 2c.

This is orchestration only: all mathematical construction is native Mojo.
Existing files refuse replacement. --offline-wrapper can enforce a local
network ban for every child process.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse,subprocess,sys,json


def export(job):
    exe,wrapper,branch,g,q,path=job
    path=Path(path)
    if path.exists():raise ValueError('refusing to overwrite '+str(path))
    command=([sys.executable,wrapper] if wrapper else [])+[exe,branch,str(g),str(q)]
    result=subprocess.run(command,capture_output=True,text=True)
    if result.returncode:raise ValueError((branch,g,q,result.stderr))
    with path.open('x') as f:f.write(result.stdout)
    return branch,g,q


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--labels',required=True);p.add_argument('--core',required=True);p.add_argument('--out',required=True);p.add_argument('--offline-wrapper');p.add_argument('--workers',type=int,default=4);a=p.parse_args()
    out=Path(a.out);(out/'labels').mkdir(parents=True,exist_ok=True);(out/'core-labels').mkdir(exist_ok=True)
    jobs=[]
    for branch,gs in [('plus',range(11,16)),('minus',range(8,12))]:
        for g in gs:
            for q in range(2*g+8,8*g):jobs.append((str(Path(a.labels).resolve()),a.offline_wrapper,branch,g,q,str(out/'labels'/f'{branch}-g{g}-q{q}.labels')))
    for branch,gs,j0,j1 in [('plus',range(16,21),2,14),('minus',range(12,17),6,6)]:
        for g in gs:
            for r in range(j0,g-j1+1):
                for l in range(4,9):
                    q=g*l+r;jobs.append((str(Path(a.core).resolve()),a.offline_wrapper,branch,g,q,str(out/'core-labels'/f'{branch}-g{g}-q{q}.labels')))
    assert len(jobs)==696
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        for i,result in enumerate(pool.map(export,jobs),1):
            if i%25==0:print('CLASS_B_NATIVE_EXPORT_PROGRESS',i,flush=True)
    print('CLASS_B_NATIVE_EXPORT_COMPLETE finite_graphs 546 core_graphs 150')
