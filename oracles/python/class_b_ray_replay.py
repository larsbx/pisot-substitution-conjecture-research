"""Deterministic parallel orchestration of canonical ray replay and its oracle.

The native executable's `one I` does certificate, two actual graph replays,
and all below-floor PIP graphs. Python independently re-proves each symbolic
certificate. Results are written in ray-index order; any refusal fails the
run, retaining the failed job's literal output. No computations are credited
before successful completion. Existing output files refuse to be overwritten.
"""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import argparse,subprocess,json
from class_b_ray_certificate import tables,Ray,certify


def run(job):
    native,out,offline,i,spec,rows,pot=job
    command=([__import__('sys').executable,offline] if offline else [])+[native,'one',str(i)]
    result=subprocess.run(command,capture_output=True,text=True)
    Path(out,f'native-{i}.log').write_text(result.stdout+result.stderr)
    if result.returncode:return i,False,dict(stage='native',code=result.returncode)
    eps,g,r,q0=spec[:4]
    try:st=certify(Ray(eps,g,r),q0,rows,pot)
    except Exception as exc:return i,False,dict(stage='oracle',error=repr(exc))
    line=f"CLASS_B_RAY_ORACLE {'plus' if eps==1 else 'minus'} g={g} q={g}l+{r} q>={q0} "+' '.join(f'{k} {v}' for k,v in st.items())+'\n'
    return i,True,line


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--native',required=True);p.add_argument('--out',required=True);p.add_argument('--workers',type=int,default=4);p.add_argument('--offline-wrapper');a=p.parse_args()
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    if list(out.glob('native-*.log')):raise ValueError('output already contains replay records')
    records=list(tables());jobs=[(str(Path(a.native).resolve()),str(out.resolve()),a.offline_wrapper,*r) for r in records]
    results=[]
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        for result in pool.map(run,jobs):
            results.append(result);print('RAY_REPLAY',result[0],'PASS' if result[1] else result[2],flush=True)
    if any(not r[1] for r in results):
        (out/'failures.json').write_text(json.dumps([r for r in results if not r[1]],indent=2)+'\n')
        raise SystemExit('native or independent certificate refusal; no completion verdict')
    native=''.join((out/f'native-{i}.log').read_text() for i,_,_ in results)
    oracle=''.join(line for _,_,line in results)
    native_counts=[' '.join(line.removeprefix('CLASS_B_RAY_CERTIFICATE ').rsplit(' max_b ',1)[0].split()) for line in native.splitlines() if line.startswith('CLASS_B_RAY_CERTIFICATE ')]
    oracle_counts=[line.removeprefix('CLASS_B_RAY_ORACLE ') for line in oracle.splitlines()]
    if native_counts!=oracle_counts:raise ValueError('native/oracle counts disagree')
    native+=f'CLASS_B_RAY_CERTIFICATES_COMPLETE rays {len(records)}\n'
    (out/'native.log').write_text(native);(out/'oracle.log').write_text(oracle)
    (out/'native.counts').write_text('\n'.join(native_counts)+'\n')
    (out/'oracle.counts').write_text('\n'.join(oracle_counts)+'\n')
    print('CLASS_B_RAY_CERTIFICATES_COMPLETE rays',len(records),flush=True)
