"""Replay independent finite cross-checks against a lower-strip native packet.

Usage: python oracles/python/check_class_c_lower_strip.py PACKET_DIR
Writes deterministic JSON to stdout; no downloaded data or floating arithmetic.
"""
import json
from pathlib import Path
import re
import sys
import tempfile
from class_c_lower_strip import domain, run

packet = Path(sys.argv[1])
results = []
for eps, name in [(1,'plus'),(-1,'minus')]:
    middle = packet / f'middle-{name}.log'
    for d,n in [(32,112),(35,122),(40,140),(50,180)]:
        result = run(eps,d,n,middle)
        assert result['vertices'] == (280 if eps == 1 else 250)
        results.append(result)
    for c in ([-4,-3,-2,-1] if eps == 1 else [0,1,2,3]):
        log = packet / f'diagonal-{name}-{c}.log'
        header = log.read_text().splitlines()[0]
        expected = int(header.split('vertices ')[1])
        for d in [12,13,20,64]:
            result = run(eps,d,4*d+c,log)
            assert result['vertices'] == expected
            results.append(result)
    for stem in ['top-finite','gap-6']:
        log = packet / (f'top-finite-{name}.log' if stem=='top-finite' else f'gap-{name}-6.log')
        lines = log.read_text().splitlines()
        current_d = None
        count = 0
        for i,line in enumerate(lines):
            if line.startswith(('TOP ','GAP ')):
                current_d = int(re.search(r' d=(\d+)',line)[1])
            elif line.startswith('M '):
                _,ns,vs,depth,nrows = line.split()
                with tempfile.TemporaryDirectory() as td:
                    rowfile = Path(td)/'rows.txt'
                    rowfile.write_text('\n'.join(lines[i+1:i+1+int(nrows)])+'\n')
                    result = run(eps,current_d,int(ns),rowfile)
                assert result['vertices']==int(vs) and result['max_depth']==int(depth)
                results.append(result)
                count += 1
        assert count == (24 if stem=='top-finite' else (17 if eps==1 else 15))
    # Original frozen-tail sets at a separate small member.
    root = Path(__file__).resolve().parents[2]
    results.append(run(eps,8,32 if eps==1 else 36,
        root/f'evidence/class-c-gap-profile-2026-10-28/frozen-tail-{name}.txt'))
print(json.dumps(dict(domain=domain(),graph_checks=len(results),members=results),indent=2,sort_keys=True))
