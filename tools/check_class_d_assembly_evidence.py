#!/usr/bin/env python3
"""Provenance for the scoped native assembly, never a mathematical verdict.

Reusing an immutable aggregate requires its log, zero exit, locked runtime,
and entire local import closure. New receipts are bound to recorded source
hashes. The canonical assembly and its case algebra live in kernel/.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PACKET = 'evidence/class-d-assembly-audit-2026-10-21'
PLUS_REV = '53a4021c0e534958c8088ff82f136913d3f08df8'
MINUS_REV = '3b16b5447aa9b3ecdecfdabb5033a381580f230e'
PLUS_LOG = 'evidence/class-d-chamber-validation-2026-10-20/aggregate.log'
PLUS_SHA = 'b87c5102771dc0c3bece2d07fc0f3413f65a2c9b5892b45c9ff4c589bf622e2c'


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(revision: str, path: str) -> bytes:
    return subprocess.check_output(['git','show',f'{revision}:{path}'],cwd=ROOT,stderr=subprocess.DEVNULL)


def import_closure(entry: str, revision: str) -> dict[str,str]:
    paths = set(subprocess.check_output(['git','ls-tree','-r','--name-only',revision,'kernel'],cwd=ROOT,text=True).splitlines())
    pending, out = [entry], {}
    while pending:
        path = pending.pop()
        if path in out:
            continue
        data = git_bytes(revision,path)
        out[path] = digest(data)
        for module in re.findall(r'^from\s+([\w.]+)\s+import',data.decode(),re.M):
            if module.startswith('.'):
                raise ValueError(f'unresolved relative import: {path}: {module}')
            prefix='kernel/'+module.replace('.','/')
            found=[p for p in (prefix+'.mojo',prefix+'/__init__.mojo') if p in paths]
            if found:
                pending.extend(found)
            elif module.split('.')[0] not in {'std','sys','python','builtin','collections','algorithm','memory','os','math','utils','random','time'}:
                raise ValueError(f'unresolved non-runtime import: {path}: {module}')
    return dict(sorted(out.items()))


def check_hashes(pins: dict[str,str], root: Path = ROOT) -> None:
    for path, expected in pins.items():
        if digest((root/path).read_bytes()) != expected:
            raise ValueError(f'source/evidence bytes changed: {path}')


def validate(manifest: dict) -> dict:
    if manifest['format'] != 'class-d-scoped-assembly-v1':
        raise ValueError('unknown evidence format')
    # A manifest cannot redefine what historical computation is being reused.
    expected=import_closure('kernel/class_d_plus_positive_b_chambers.mojo',PLUS_REV)
    expected['kernel/pixi.lock']=digest(git_bytes(PLUS_REV,'kernel/pixi.lock'))
    if manifest['plus_source_sha256'] != expected:
        raise ValueError('plus import closure differs from the immutable native source')
    check_hashes(expected)
    required_replay=set()
    for entry in ('kernel/tests/test_class_d_minus_boundary_strips.mojo',
                  'kernel/tests/test_class_d_minus_seed_cover.mojo',
                  'kernel/tests/test_class_d_plus_template.mojo'):
        required_replay.update(import_closure(entry,MINUS_REV))
    required_replay.update(('kernel/class_d_assembly.mojo','kernel/psc/class_d_assembly.mojo',
                            'kernel/tests/test_class_d_assembly.mojo'))
    if set(manifest['replay_source_sha256']) != required_replay:
        raise ValueError('incomplete fresh replay import closure')
    required_evidence={PLUS_LOG,'evidence/class-d-chamber-validation-2026-10-20/aggregate.exit'}
    for key in ('minus-complete','plus-boundary','seed-cover','assembly-test','assembly-build'):
        required_evidence.update(f'{PACKET}/{key}{suffix}' for suffix in ('.log','.exit'))
    if set(manifest['evidence_sha256']) != required_evidence:
        raise ValueError('incomplete native evidence pin set')
    check_hashes(manifest['replay_source_sha256'])
    check_hashes(manifest['evidence_sha256'])
    if digest((ROOT/PLUS_LOG).read_bytes()) != PLUS_SHA:
        raise ValueError('the complete plus native log was replaced')
    if (ROOT/'evidence/class-d-chamber-validation-2026-10-20/aggregate.exit').read_text().strip() != '0':
        raise ValueError('plus process did not finish successfully')
    # Never infer current integration acceptance from a historical setup step.
    for key in ('minus-complete','plus-boundary','seed-cover','assembly-test','assembly-build'):
        if (ROOT/PACKET/(key+'.exit')).read_text().strip() != '0':
            raise ValueError(f'new native replay failed: {key}')
    if manifest['current_head_ci_accepted'] is not False:
        raise ValueError('this packet does not supply current-head CI acceptance')
    return dict(provenance_valid=True,plus_reused_from=PLUS_REV,
                minus_original_revision=MINUS_REV,plus_import_files=len(expected)-1,
                current_head_ci_accepted=False,independent_human_review=False,
                authority='provenance-only; canonical assembly in kernel/class_d_assembly.mojo')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--manifest',type=Path,default=ROOT/PACKET/'manifest.json')
    args=parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text())),indent=2))

if __name__=='__main__': main()
