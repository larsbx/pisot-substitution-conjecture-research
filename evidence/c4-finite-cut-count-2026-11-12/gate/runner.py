#!/usr/bin/env python3
"""Count attempt 01: unchanged acceptance gate with visible wrapper-only heartbeats.

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
REPO = BASE / 'psc-count'
LOG = BASE / 'count-isolated-attempt-01.log'
RECEIPT = BASE / 'count-isolated-attempt-01.json'
EXPECTED_COMMIT = '31f8046291f2428e839d95e8890c8342858ec210'
EXPECTED_TREE = 'e38c3f65efb79fa72860d8ef222e96695847a551'
EXPECTED_TOOLCHAIN = 'leanprover/lean4:v4.34.0-rc2'
HEARTBEAT_SECONDS = 20

def git(*args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()

if LOG.exists() or RECEIPT.exists():
    raise SystemExit('Count attempt 01 output already exists; preserve it rather than overwrite it.')
if git('status', '--porcelain=v1', '--untracked-files=all'):
    raise SystemExit('Refusing exact-revision acceptance from a dirty worktree.')
subject = git('rev-parse', 'HEAD')
tree = git('rev-parse', 'HEAD^{tree}')
if subject != EXPECTED_COMMIT or tree != EXPECTED_TREE:
    raise SystemExit('Refusing count acceptance from a different code revision or tree.')
paths = sorted(set(git('ls-files', 'proof/PscVerif', 'tools/check_lean.sh',
    'tools/setup_lean.sh', 'tools/make_proof_bank.py', 'proof/proof-bank.json',
    'claim_governance.toml').splitlines()))
sources = {p: hashlib.sha256((REPO / p).read_bytes()).hexdigest() for p in paths}
env = os.environ.copy()
env['ELAN_HOME'] = '/workspace/scratch/84c835820757/toolchains/elan'
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
env['TMPDIR'] = str(BASE / 'count-isolation-tmp')
pin = (REPO / 'proof/PscVerif/lean-toolchain').read_text().strip()
if pin != EXPECTED_TOOLCHAIN:
    raise SystemExit('Refusing an unexpected checked-in Lean toolchain.')
Path(env['TMPDIR']).mkdir(exist_ok=True)
disk = os.statvfs(BASE)
environment_preflight = {
    'observed_at_utc': now(),
    'scope': 'Resource snapshot only; no acceptance credit or deletion.',
    'elan_home': env['ELAN_HOME'],
    'toolchain_pin': pin,
    'path_prefix': env['ELAN_HOME'] + '/bin',
    'tmpdir': env['TMPDIR'],
    'tmpdir_existing_entries': len(list(Path(env['TMPDIR']).iterdir())),
    'disk_path': str(BASE),
    'disk_total_bytes': disk.f_blocks * disk.f_frsize,
    'disk_available_bytes': disk.f_bavail * disk.f_frsize,
    'disk_free_bytes': disk.f_bfree * disk.f_frsize,
    'gate_script_sha256': sources['tools/check_lean.sh'],
}
receipt = {'schema': 'c4-finite-cut-count-isolated-process-v1', 'subject_revision': subject,
    'subject_tree': tree, 'started_at_utc': now(), 'command': ['./tools/check_lean.sh'],
    'working_directory': str(REPO), 'log': str(LOG), 'source_sha256': sources,
    'environment_preflight': environment_preflight,
    'status': 'running', 'acceptance_complete': False}
with RECEIPT.open('x') as receipt_file:
    receipt_file.write(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({'subject_revision': subject, 'tree': tree, 'status': 'running',
    'environment_preflight': environment_preflight}), flush=True)
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
stable = stable and not git('status', '--porcelain=v1', '--untracked-files=all') and post_sources == sources
receipt.update(ended_at_utc=now(), elapsed_seconds=round(time.monotonic()-start, 3),
    exit_code=child_exit, unchanged_head_tree_and_sources=stable,
    log_bytes=LOG.stat().st_size, log_sha256=hashlib.sha256(LOG.read_bytes()).hexdigest(),
    status='passed' if child_exit == 0 and stable else 'failed',
    acceptance_complete=child_exit == 0 and stable)
RECEIPT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k != 'source_sha256'}), flush=True)
print('\n'.join(LOG.read_text().splitlines()[-8:]), flush=True)
raise SystemExit(0 if receipt['acceptance_complete'] else (child_exit or 1))
