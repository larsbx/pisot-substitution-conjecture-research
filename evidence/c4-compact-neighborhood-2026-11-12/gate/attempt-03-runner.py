#!/usr/bin/env python3
"""Attempt 03: unchanged acceptance gate with visible wrapper-only heartbeats.

This file runs a fresh full gate when executed. It was prepared without running.
Child output goes only to the raw binary log; heartbeat JSON goes only to stdout.
"""
from __future__ import annotations
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

BASE = Path('/workspace/scratch/f96c28a561ad')
REPO = BASE / 'psc-compact'
LOG = BASE / 'compact-isolated-attempt-03.log'
RECEIPT = BASE / 'compact-isolated-attempt-03.json'
EXPECTED_COMMIT = '6915e8d592b7ea5cb7c6950249811e354dc6c3e7'
EXPECTED_TREE = 'c79e97bdae1224068895afa9dcf6cca6d7fe9fbb'
HEARTBEAT_SECONDS = 20

def git(*args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()

if LOG.exists() or RECEIPT.exists():
    raise SystemExit('Attempt 03 output already exists; preserve it rather than overwrite it.')
if git('status', '--porcelain'):
    raise SystemExit('Refusing exact-revision acceptance from a dirty worktree.')
subject = git('rev-parse', 'HEAD')
tree = git('rev-parse', 'HEAD^{tree}')
if subject != EXPECTED_COMMIT or tree != EXPECTED_TREE:
    raise SystemExit('Refusing retry from a different code revision or tree.')
paths = sorted(set(git('ls-files', 'proof/PscVerif', 'tools/check_lean.sh',
    'tools/setup_lean.sh', 'tools/make_proof_bank.py', 'proof/proof-bank.json',
    'claim_governance.toml').splitlines()))
sources = {p: hashlib.sha256((REPO / p).read_bytes()).hexdigest() for p in paths}
env = os.environ.copy()
env['ELAN_HOME'] = '/workspace/scratch/84c835820757/toolchains/elan'
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
env['TMPDIR'] = str(BASE / 'lean-isolation-tmp')
Path(env['TMPDIR']).mkdir(exist_ok=True)
receipt = {'schema': 'c4-compact-isolated-process-v1', 'subject_revision': subject,
    'subject_tree': tree, 'started_at_utc': now(), 'command': ['./tools/check_lean.sh'],
    'working_directory': str(REPO), 'log': str(LOG), 'source_sha256': sources,
    'status': 'running', 'acceptance_complete': False}
with RECEIPT.open('x') as receipt_file:
    receipt_file.write(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({'subject_revision': subject, 'tree': tree, 'status': 'running'}), flush=True)
start = time.monotonic()
with LOG.open('xb') as log:
    child = subprocess.Popen(['./tools/check_lean.sh'], cwd=REPO, env=env,
        stdout=log, stderr=subprocess.STDOUT)
    while True:
        try:
            child_exit = child.wait(timeout=HEARTBEAT_SECONDS)
            break
        except subprocess.TimeoutExpired:
            print(json.dumps({
                'event': 'isolated_gate_heartbeat',
                'observed_at_utc': now(),
                'child_pid': child.pid,
                'elapsed_seconds': round(time.monotonic() - start, 3),
                'log_bytes': LOG.stat().st_size,
                'status': 'running',
                'acceptance_complete': False,
            }), flush=True)
post_sources = {p: hashlib.sha256((REPO / p).read_bytes()).hexdigest() for p in paths}
stable = git('rev-parse', 'HEAD') == subject and git('rev-parse', 'HEAD^{tree}') == tree
stable = stable and not git('status', '--porcelain') and post_sources == sources
receipt.update(ended_at_utc=now(), elapsed_seconds=round(time.monotonic()-start, 3),
    exit_code=child_exit, unchanged_head_tree_and_sources=stable,
    log_bytes=LOG.stat().st_size, log_sha256=hashlib.sha256(LOG.read_bytes()).hexdigest(),
    status='passed' if child_exit == 0 and stable else 'failed',
    acceptance_complete=child_exit == 0 and stable)
RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k != 'source_sha256'}), flush=True)
print('\n'.join(LOG.read_text().splitlines()[-8:]), flush=True)
raise SystemExit(0 if receipt['acceptance_complete'] else (child_exit or 1))
