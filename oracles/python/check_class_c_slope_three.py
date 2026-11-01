"""Independent finite oracle for the slope-three continuation packet.

Usage: python ... PACKET_DIR
Complete native label sets and depths are compared using the separate
literal-prefix/Fraction graph builder. Sampling is not a cone proof.
"""
import gzip
import json
from pathlib import Path
import re
import sys
import tempfile
from class_c_lower_strip import run


def checked_finite(path,eps,a):
    text = gzip.decompress(path.read_bytes()).decode() if path.suffix=='.gz' else path.read_text()
    lines=text.splitlines()
    results=[]
    wanted={(d,n) for d in range(6,24) for n in range(3*d+a,4*d+(0 if eps==1 else 4))}
    seen=set()
    current=None
    for i,line in enumerate(lines):
        if line.startswith('END '):
            match=re.fullmatch(r'END eps=(-?1) d=(\d+) n=(\d+)',line)
            assert match and int(match[1])==eps
            current=tuple(map(int,match.group(2,3)))
        elif line.startswith('M '):
            _,ns,vs,depth,nrows=line.split()
            assert current and int(ns)==current[1] and current not in seen
            seen.add(current)
            with tempfile.TemporaryDirectory() as td:
                p=Path(td)/'rows.txt'
                p.write_text('\n'.join(lines[i+1:i+1+int(nrows)])+'\n')
                r=run(eps,*current,p)
            assert r['vertices']==int(vs) and r['max_depth']==int(depth)
            results.append(r)
            current=None
    assert seen==wanted,('finite coverage mismatch',sorted(wanted-seen)[:5])
    return results


def refused_coefficients(path,u,v):
    text=path.read_text().split('on any bracket: ',1)[1].strip()
    parts=re.findall(r'\[([^\]]*)\]',text)
    assert len(parts)==3
    out=[]
    for part in parts:
        rows=re.findall(r'\{([^}]*)\}',part)
        value=0
        for j,row in enumerate(rows):
            coefficients=[int(x) for x in row.split(',') if x]
            value+=sum(c*(v**i)*(u**j) for i,c in enumerate(coefficients))
        out.append(value)
    return tuple(out)


def main(packet):
    results=[]
    config=json.loads((packet/'plan.json').read_text())
    assert config['b']==16 and config['diagonal_floor']==24
    for eps,name in [(1,'plus'),(-1,'minus')]:
        a=config[name]['middle_intercept']
        b=config['b']
        middle=packet/f'middle-{name}-{a}-{b}.log'
        for u,v in [(0,0),(1,2),(8,8),(20,3)]:
            d=a+b+u+v
            n=4*a+3*b+4*u+3*v
            r=run(eps,d,n,middle)
            assert r['vertices']==(280 if eps==1 else 250)
            results.append(r)
        for c in (range(-15,-4) if eps==1 else range(-15,0)):
            log=packet/f'diagonal-{name}-{c}.log'
            vertices=int(log.read_text().splitlines()[0].split('vertices ')[1])
            for d in [24,25,40,64]:
                r=run(eps,d,4*d+c,log)
                assert r['vertices']==vertices
                results.append(r)
        for c in config[name]['lower_lines']:
            log=packet/f'lower-line-minus-{c}.log'
            for d in [24,25,40,64]:
                r=run(eps,d,3*d+c,log)
                assert r['vertices']==250
                results.append(r)
        finite=packet/f'finite-{name}.log.gz'
        if not finite.exists():
            finite=packet/f'finite-{name}.log'
        results.extend(checked_finite(finite,eps,config[name]['finite_intercept']))
    # Equal counts do not imply identical label sets, and a lower minus line
    # cannot inherit the 250-label table merely by extending its inequality.
    controls=[run(1,40,152),run(1,40,151),run(-1,40,125)]
    assert controls[0]['vertices']==controls[1]['vertices']==282
    assert controls[0]['rows_sha256']!=controls[1]['rows_sha256']
    assert controls[2]['vertices']==252
    from psc_research.overlap_graph import Field
    sign_checks=[]
    refusal_graphs=[]
    for line in (packet/'sign-controls.log').read_text().splitlines():
        pairs=dict(field.split('=',1) for field in line.split()[1:])
        values={k:int(v) for k,v in pairs.items() if k!='g'}
        coeffs=tuple(map(int,pairs['g'].split(',')))
        name='plus' if values['eps']==1 else 'minus'
        raw=packet/f"refused-middle-{name}-{values['a']}-{values['b']}.log"
        assert refused_coefficients(raw,values['u'],values['v'])==coeffs
        d,n,eps=values['d'],values['n'],values['eps']
        assert d==values['a']+values['b']+values['u']+values['v']
        assert n==4*values['a']+3*values['b']+4*values['u']+3*values['v']
        f=Field(n-d+eps+3,n-3*d+3*eps+2,2*eps)
        assert f.sign(coeffs)==values['sign']
        sign_checks.append(dict(**values,coefficients=coeffs))
        r=run(eps,d,n)
        assert r['vertices']==(280 if eps==1 else 250)
        refusal_graphs.append(r)
    assert len(sign_checks)==10
    return dict(graph_checks=len(results)+len(controls)+len(refusal_graphs),members=results,negative_controls=controls,refusal_sign_checks=sign_checks,refusal_graph_controls=refusal_graphs)


if __name__=='__main__':
    print(json.dumps(main(Path(sys.argv[1])),indent=2,sort_keys=True))
