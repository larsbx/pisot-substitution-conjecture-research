"""Strict historical byte replay plus independent current-witness validation.

The pinned legacy replay wrapper and all packet bytes remain unchanged.
Current labels use the current native binary; historical witness bytes use
the original, packet-pinned native exporter. Both witness choices must satisfy
the same complete-label, occurrence, shift and shortest-descent contract.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'archive/class-b-label-witness-export-2026-11-01/class_b_label_rays.mojo'
PACKET = ROOT / 'evidence/class-b-label-rays-2026-10-23'


def check_source(source=SOURCE, packet=PACKET):
    expected = json.loads((packet / 'inputs.json').read_text())['sha256']['kernel/class_b_label_rays.mojo']
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError('historical exporter differs from original packet source pin')
    return actual


def validate_witnesses(data: bytes, expected: bytes, branch: str, gap: int, q: int):
    """Replay actual image ordinals and incidence directly over integers."""
    lines = data.decode('ascii').splitlines()
    archived = expected.decode('ascii').splitlines()
    vertices = [line for line in lines if line.startswith('V ')]
    if not lines or lines[0] != archived[0] or vertices != [line for line in archived if line.startswith('V ')]:
        raise ValueError('current complete labels/depths differ from archive')
    header = lines[0].split()
    if len(header) != 4 or header[0] != 'M' or int(header[1]) != q:
        raise ValueError('invalid member header')
    rows = [tuple(map(int, line.split()[1:])) for line in vertices]
    if any(len(row) != 6 for row in rows):
        raise ValueError('invalid vertex record')
    depths = {row[:5]: row[5] for row in rows}
    if len(depths) != len(rows) or len(rows) != int(header[2]) or max(depths.values()) != int(header[3]):
        raise ValueError('missing/duplicate vertices or wrong summary')
    if any(t not in range(3) or b not in range(3) or d < 0 or ((k,c,y)==(0,0,0)) != (d==0)
           for t,b,k,c,y,d in rows):
        raise ValueError('invalid vertex type/target depth')
    if branch not in ('plus', 'minus') or not 1 <= gap <= 16 or not 1 <= q <= 128:
        raise ValueError('invalid pilot parameters')
    plus = branch == 'plus'
    p = 3*q + 12-gap if plus else 3*q-gap
    r = q + (1 if plus else -1)
    sigma = [[0]+[2]*p+[0], [1]+[2]*q+[0], [1]+[2]*r+[0]]
    matrix = [[word.count(h) for word in sigma] for h in range(3)]
    seen = set()
    for line in lines[1:]:
        if line.startswith('V '):
            continue
        fields = line.split()
        if len(fields) != 13 or fields[0] != 'W':
            raise ValueError('unknown or malformed witness record')
        values = tuple(map(int, fields[1:]))
        parent, child, (i,j) = values[:5], values[5:10], values[10:]
        if parent not in depths or child not in depths or parent in seen or depths[parent] == 0:
            raise ValueError('duplicate/unknown/target witness parent or child')
        seen.add(parent)
        top, bottom = sigma[parent[0]], sigma[parent[1]]
        if not (0 <= i < len(top) and 0 <= j < len(bottom)):
            raise ValueError('illegal occurrence ordinal')
        if (top[i], bottom[j]) != child[:2]:
            raise ValueError('wrong child letters')
        shift = tuple(sum(matrix[h][z]*parent[z+2] for z in range(3))
                      + bottom[:j].count(h)-top[:i].count(h) for h in range(3))
        if shift != child[2:] or depths[child] != depths[parent]-1:
            raise ValueError('wrong shift or shortest-descent depth')
    if seen != {state for state,d in depths.items() if d > 0}:
        raise ValueError('incomplete witness coverage')
    return len(seen)


def replay(current, historical, packet, out):
    check_source(packet=packet)
    current, historical = str(current.resolve()), str(historical.resolve())
    out.mkdir(parents=True, exist_ok=True)
    wrapper = ROOT / 'oracles/python/class_b_label_replay.py'
    # Each invocation keeps the original strict byte assertion. Separate views
    # prevent replacing an archive or conflating two traversal conventions.
    with tempfile.TemporaryDirectory(prefix='psc-label-replay-') as tmp:
        view = Path(tmp)
        (view/'current').mkdir()
        (view/'current/labels').symlink_to((packet/'labels').resolve(), target_is_directory=True)
        (view/'historical').mkdir()
        (view/'historical/witnesses').symlink_to((packet/'witnesses').resolve(), target_is_directory=True)
        subprocess.run([sys.executable, str(wrapper), current, str(view/'current'), str(out/'current-labels')], check=True)
        subprocess.run([sys.executable, str(wrapper), historical, str(view/'historical'), str(out/'historical-witnesses')], check=True)
    report = []
    for path in sorted((packet/'witnesses').glob('*.labels')):
        match = re.fullmatch(r'(plus|minus)-g(\d+)-q(\d+)\.labels', path.name)
        if match is None:
            raise ValueError('unrecognized witness fixture')
        branch, gap, q = match.groups()
        old = path.read_bytes()
        fresh = subprocess.run([current, branch, gap, q, 'witnesses'], capture_output=True, check=True).stdout
        (out/path.name).write_bytes(fresh)
        count = validate_witnesses(fresh, old, branch, int(gap), int(q))
        if validate_witnesses(old, old, branch, int(gap), int(q)) != count:
            raise ValueError('historical/current witness coverage mismatch')
        report.append(dict(file=path.name, witnesses=count, historical_sha256=hashlib.sha256(old).hexdigest(),
                           current_sha256=hashlib.sha256(fresh).hexdigest()))
    if not report:
        raise ValueError('missing witness fixtures')
    (out/'witness-reconciliation.json').write_text(json.dumps(report, indent=2)+'\n')
    print('CLASS_B_WITNESS_RECONCILIATION', json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    if sys.argv[1:] == ['--check-source']:
        print(check_source())
    elif len(sys.argv) == 5:
        replay(*(Path(arg) for arg in sys.argv[1:]))
    else:
        raise SystemExit('usage: --check-source | CURRENT HISTORICAL PACKET OUT')
