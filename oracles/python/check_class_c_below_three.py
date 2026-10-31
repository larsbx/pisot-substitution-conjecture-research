"""Independent exact replay of a below-three native packet.

Literal-word/Fraction graph construction checks full label sets and finite
member depths. These finite comparisons are not uniform cone proofs.
"""
import gzip
import json
from pathlib import Path
import re
import sys
import tempfile
from class_c_lower_strip import run


def finite_checks(path,eps,a):
    text=gzip.decompress(path.read_bytes()).decode() if path.suffix=='.gz' else path.read_text()
    lines=text.splitlines()
    wanted={(d,n) for d in range(6,32)
            for n in range(max(2*d+(-5 if eps==1 else 1),(5*d+a+1)//2),3*d+(4 if eps==1 else 6))}
    seen=set();out=[];current=None
    for i,line in enumerate(lines):
        if line.startswith('END '):
            fields=dict(x.split('=') for x in line.split()[1:])
            assert int(fields['eps'])==eps and int(fields['a'])==a
            current=(int(fields['d']),int(fields['n']))
        elif line.startswith('M '):
            _,ns,vs,depth,count=line.split()
            assert current and int(ns)==current[1] and current not in seen
            seen.add(current)
            with tempfile.TemporaryDirectory() as td:
                p=Path(td)/'rows.txt';p.write_text('\n'.join(lines[i+1:i+1+int(count)])+'\n')
                r=run(eps,*current,p)
            assert r['vertices']==int(vs) and r['max_depth']==int(depth)
            out.append(r);current=None
    assert seen==wanted,('finite coverage mismatch',sorted(wanted-seen)[:5])
    return out


def control_checks(path):
    lines=path.read_text().splitlines();current=None;out=[]
    for i,line in enumerate(lines):
        if line.startswith('MEMBER '):
            fields=dict(x.split('=') for x in line.split()[1:])
            current=tuple(int(fields[k]) for k in ['eps','d','n'])
        elif line.startswith('M '):
            _,ns,vs,depth,count=line.split()
            assert current and int(ns)==current[2]
            with tempfile.TemporaryDirectory() as td:
                p=Path(td)/'rows.txt';p.write_text('\n'.join(lines[i+1:i+1+int(count)])+'\n')
                r=run(*current,p)
            assert r['vertices']==int(vs) and r['max_depth']==int(depth)
            out.append(r);current=None
    assert len(out)==2 and out[0]['rows_sha256']!=out[1]['rows_sha256']
    assert 'LABEL_MISMATCH' in lines[-1]
    return out


def exception_checks(path,eps,c,lo,hi):
    lines=path.read_text().splitlines();out=[];seen=set();current=None
    wanted={(d,3*d+c) for d in range(lo,hi+1)}
    for i,line in enumerate(lines):
        if line.startswith('EXCEPTION '):
            fields=dict(x.split('=') for x in line.split()[1:])
            assert int(fields['eps'])==eps
            current=(int(fields['d']),int(fields['n']))
        elif line.startswith('M '):
            _,ns,vs,depth,count=line.split()
            assert current and int(ns)==current[1] and current not in seen
            seen.add(current)
            with tempfile.TemporaryDirectory() as td:
                p=Path(td)/'rows.txt';p.write_text('\n'.join(lines[i+1:i+1+int(count)])+'\n')
                r=run(eps,*current,p)
            assert r['vertices']==int(vs) and r['max_depth']==int(depth)
            out.append(r);current=None
    assert seen==wanted,('exception coverage mismatch',sorted(wanted-seen))
    return out


def main(packet):
    config=json.loads((packet/'plan.json').read_text())
    results=[];controls=[]
    for eps,name in [(1,'plus'),(-1,'minus')]:
        plan=config[name];a,b=plan['a'],plan['b']
        assert a in [8,16] and b in [8,16]
        log=packet/plan['sector_file']
        expected=int(re.search(r'vertices (\d+)',log.read_text().splitlines()[0])[1])
        for u,v in [(0,0),(1,2),(4,4),(10,3)]:
            d=a+2*b+u+2*v;n=3*a+5*b+3*u+5*v
            r=run(eps,d,n,log);assert r['vertices']==expected;results.append(r)
        lines=plan['lines']
        assert [p['c'] for p in lines]==list(range(-15,4 if eps==1 else 6))
        for piece in lines:
            c=piece['c'];floor=piece['floor']
            needed=max(32,a-2*c)
            assert 32<=floor<=48
            if floor>needed:
                lo=piece['exception_start']
                assert 32<=lo<=needed
                results.extend(exception_checks(packet/piece['exceptions_file'],eps,c,lo,floor-1))
            log=packet/piece['file']
            expected=int(re.search(r'vertices (\d+)',log.read_text().splitlines()[0])[1])
            for d in [floor,floor+1,56,64]:
                r=run(eps,d,3*d+c,log);assert r['vertices']==expected;results.append(r)
        results.extend(finite_checks(packet/f'finite-{name}.log.gz',eps,plan['finite_a']))
        for control in plan['control_files']:
            controls.extend(control_checks(packet/control))
    return dict(graph_checks=len(results)+len(controls),members=results,label_controls=controls)


if __name__=='__main__':
    print(json.dumps(main(Path(sys.argv[1])),indent=2,sort_keys=True))
