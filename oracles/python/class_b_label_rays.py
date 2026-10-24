"""Independent finite label-set compression/fits. Never a universal certificate."""
from collections import defaultdict
from pathlib import Path
import argparse
import json
import re


def read(path):
    lines = Path(path).read_text().splitlines()
    h = lines[0].split()
    if len(h) != 4 or h[0] != 'M':
        raise ValueError('bad header')
    q, size, depth = map(int, h[1:])
    rows = [tuple(map(int, l.split()[1:])) for l in lines[1:] if l.startswith('V ')]
    if len(rows) != size or len({r[:5] for r in rows}) != size:
        raise ValueError('missing/duplicate labels')
    if max(r[5] for r in rows) != depth:
        raise ValueError('depth mismatch')
    for t,b,k,c,y,z in rows:
        if t not in range(3) or b not in range(3) or z < 0 or ((k,c,y)==(0,0,0)) != (z==0):
            raise ValueError('bad type/target')
    return q, rows


def intervals(rows):
    groups = defaultdict(set)
    for t,b,k,c,y,*_ in rows:
        groups[t,b,3*k+c+y,c-3*k].add(k)
    out = []
    for typ, ks in sorted(groups.items()):
        start = prev = None
        for k in sorted(ks):
            if prev is not None and k != prev+1:
                out.append((*typ,start,prev)); start = None
            if start is None: start = k
            prev = k
        out.append((*typ,start,prev))
    return out


def expand(rows):
    return {(t,b,k,3*k+d,s-6*k-d) for t,b,s,d,lo,hi in rows for k in range(lo,hi+1)}


def predict(a,b,step):
    if len(a)!=len(b) or any(x[:4]!=y[:4] for x,y in zip(a,b)):
        raise ValueError('carrier topology changed')
    return [(*x[:4],x[4]+step*(y[4]-x[4]),x[5]+step*(y[5]-x[5])) for x,y in zip(a,b)]


def audit(directory):
    report=[]
    for branch, gaps in [('plus',range(1,6)),('minus',range(1,4))]:
        for gap in gaps:
            files={int(re.search(r'-q(\d+)\.',p.name)[1]):p for p in Path(directory).glob(f'{branch}-g{gap}-q*.labels')}
            for residue in range(gap):
                qs=sorted(q for q in files if q%gap==residue)
                data={q:intervals(read(files[q])[1]) for q in qs}
                for q in qs:
                    raw={r[:5] for r in read(files[q])[1]}
                    if expand(data[q])!=raw:raise ValueError('lossy compression')
                trainmax = 26 if branch=='plus' and gap==1 else (18 if branch=='plus' and gap==2 else 30)
                train=[q for q in qs if q<=trainmax]
                floor=None
                for i,q in enumerate(train[:-2]):
                    # Fit only archived-range samples: two synthesize, at least one checks.
                    tail=train[i:]
                    if any(v!=q+j*gap for j,v in enumerate(tail)):raise ValueError('missing ray member')
                    try: ok=all(predict(data[q],data[tail[1]],j)==data[v] for j,v in enumerate(tail[2:],2))
                    except ValueError:ok=False
                    if ok:floor=q;break
                entry=dict(branch=branch,gap=gap,residue=residue,qmax=max(qs) if qs else None,floor=floor,samples=len(qs),trainmax=trainmax)
                if floor is not None:
                    a,b=data[floor],data[floor+gap]
                    shape_ok=all(y[5]-y[4]>=x[5]-x[4]>=0 for x,y in zip(a,b)) and all(x[:4]!=y[:4] or (y[4]-x[5]>=2 and (b[i+1][4]-b[i][5])>=(y[4]-x[5])) for i,(x,y) in enumerate(zip(a,a[1:])))
                    entry['tail_partition_ok']=shape_ok
                    heldout=[q for q in qs if q>trainmax]
                    failures=[]
                    for q in heldout:
                        try:
                            predicted=predict(a,b,(q-floor)//gap)
                            if predicted!=data[q]:
                                missing=sorted(expand(data[q])-expand(predicted))
                                extra=sorted(expand(predicted)-expand(data[q]))
                                failures.append(dict(q=q,missing=missing[:1],extra=extra[:1],predicted_count=len(expand(predicted)),actual_count=len(expand(data[q]))))
                        except ValueError:
                            failures.append(dict(q=q,reason='topology changed'))
                    entry.update(holdouts=heldout,holdout_failures=failures)
                    entry.update(rows=len(a),prefix=[q for q in qs if q<floor],slope=sum((y[5]-x[5])-(y[4]-x[4]) for x,y in zip(a,b)),carrier=[[*x[:4],y[4]-x[4],x[4]-(y[4]-x[4])*(floor//gap),y[5]-x[5],x[5]-(y[5]-x[5])*(floor//gap)] for x,y in zip(a,b)])
                report.append(entry)
    return report


def audit_archived(directory):
    records={}
    # directory is packet/labels; sibling archive lives one directory above packet.
    archive=Path(directory).parent.parent/'class-b-top-layer-profile-2026-10-23'
    for path in sorted(archive.glob('*.log')):
        m=re.fullmatch(r'(plus|minus)-d(\d+)-q(\d+)\.log',path.name)
        if m is None:continue
        branch,d,_=m.groups();gap=int(d)+1
        for q,size,depth in re.findall(r'  q (\d+) vertices (\d+) max first-hit depth (\d+)',path.read_text()):
            key=(branch,gap,int(q));value=(int(size),int(depth))
            if key in records and records[key]!=value:raise ValueError('historical summaries conflict')
            records[key]=value
            _,raw=read(Path(directory)/f'{branch}-g{gap}-q{q}.labels')
            if (len(raw),max(r[5] for r in raw))!=value:raise ValueError(f'archived summary mismatch: {key}')
    if len(records)!=177:raise ValueError(f'incomplete historical comparison: {len(records)}')
    return len(records)

def main():
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--out');p.add_argument('--native');p.add_argument('--require-complete',action='store_true');a=p.parse_args()
    report=audit(a.directory)
    for e in report: print({k:v for k,v in e.items() if k not in ('carrier','prefix')})
    if a.out:Path(a.out).write_text(json.dumps(report,indent=2)+'\n')
    if a.require_complete:
        print('ARCHIVED_GRAPH_SUMMARIES_MATCH',audit_archived(a.directory))
        if len(report)!=21 or any(e['floor'] is None or e.get('holdout_failures') or not e.get('tail_partition_ok') or len(e.get('holdouts',[]))<2 or e['qmax']<43-e['gap'] for e in report):
            raise ValueError('incomplete or failed finite ray audit')
    if a.native:
        import subprocess
        checks=0
        for e in report:
            if e['floor'] is None:continue
            def path(q):return str(Path(a.directory)/f"{e['branch']}-g{e['gap']}-q{q}.labels")
            q0=e['floor'];gap=e['gap']
            qs=sorted(int(re.search(r'-q(\d+)\.',p.name)[1]) for p in Path(a.directory).glob(f"{e['branch']}-g{gap}-q*.labels"))
            for q in qs:
                if q%gap!=e['residue'] or q<q0+2*gap:continue
                subprocess.run([a.native,path(q0),path(q0+gap),path(q),str((q-q0)//gap)],check=True,capture_output=True)
                checks+=1
        print('NATIVE_FULL_INTERVAL_COMPARISONS',checks)


if __name__=='__main__': main()
