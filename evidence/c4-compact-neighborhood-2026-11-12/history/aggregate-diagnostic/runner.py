#!/usr/bin/env python3
"""Bounded no-output aggregate import diagnostic. Never an acceptance receipt."""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

BASE = Path('/workspace/scratch/f96c28a561ad')
PROJECT = BASE / 'lean-isolation-tmp/tmp.UOZg5YfDvP/proof/PscVerif'
ELAN = Path('/workspace/scratch/84c835820757/toolchains/elan')
PREFIX = BASE / 'compact-aggregate-diagnostic'
RAW_LOG = Path(str(PREFIX) + '-child.log')
PROCESS_LOG = Path(str(PREFIX) + '-processes.jsonl')
RESULT = Path(str(PREFIX) + '-result.json')
CAP_SECONDS = 300
HEARTBEAT_SECONDS = 20

def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()

def hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def cgroup_memory() -> dict[str, str]:
    data = {}
    for name in ('memory.current', 'memory.peak', 'memory.max', 'memory.events'):
        path = Path('/sys/fs/cgroup') / name
        try:
            data[name] = path.read_text().strip()
        except OSError:
            pass
    return data

def process_tree(group: int) -> list[dict]:
    data = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        pid = int(path.name)
        try:
            if os.getpgid(pid) != group:
                continue
            status = dict(line.split(':', 1) for line in (path / 'status').read_text().splitlines())
            stat = (path / 'stat').read_text().rsplit(')', 1)[1].split()
            cmd = (path / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace').strip()
            data.append({
                'pid': pid,
                'ppid': int(status['PPid'].strip()),
                'state': status['State'].strip(),
                'name': status['Name'].strip(),
                'command': cmd,
                'rss_kb': int(status.get('VmRSS', '0 kB').split()[0]),
                'high_water_rss_kb': int(status.get('VmHWM', '0 kB').split()[0]),
                'threads': int(status.get('Threads', '0').strip()),
                'user_cpu_ticks': int(stat[11]),
                'system_cpu_ticks': int(stat[12]),
            })
        except (OSError, ProcessLookupError, KeyError, ValueError):
            continue
    return sorted(data, key=lambda p: p['pid'])

toolchain = (PROJECT / 'lean-toolchain').read_text().strip()
command = [str(ELAN / 'bin/elan'), 'run', toolchain, 'lake', '--no-cache', 'env', 'lean', 'PscVerif.lean']
env = {key: value for key, value in os.environ.items()
       if not key.startswith(('LEAN_', 'LAKE_', 'MATHLIB_CACHE_'))}
env.update({
    'ELAN_HOME': str(ELAN),
    'LAKE_CONFIG': '',
    'LAKE_CACHE_DIR': '',
    'LAKE_ARTIFACT_CACHE': 'false',
    'LAKE_RESTORE_ARTIFACTS': 'false',
    'MATHLIB_CACHE_DIR': str(PROJECT.parents[1] / 'download-cache'),
    'MATHLIB_CACHE_GET_URL': 'https://cache.mathlib.org/mathlib4-master',
})
source_names = ('PscVerif.lean', 'ProofBankAudit.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
before = {name: hash_file(PROJECT / name) for name in source_names}
metadata = {
    'purpose': 'Diagnostic root aggregate import without -o or output artifact requests; retained workspace only.',
    'formal_acceptance_credit': False,
    'project': str(PROJECT),
    'command': command,
    'environment_overrides': {key: env[key] for key in (
        'ELAN_HOME', 'LAKE_CONFIG', 'LAKE_CACHE_DIR', 'LAKE_ARTIFACT_CACHE',
        'LAKE_RESTORE_ARTIFACTS', 'MATHLIB_CACHE_DIR', 'MATHLIB_CACHE_GET_URL')},
    'timeout_seconds': CAP_SECONDS,
    'heartbeat_seconds': HEARTBEAT_SECONDS,
    'started_at_utc': utc(),
    'source_hashes_before': before,
    'cgroup_memory_before': cgroup_memory(),
}
print(json.dumps({'event': 'diagnostic_start', **metadata}), flush=True)
started = time.monotonic()
max_sampled_rss = 0
timed_out = False
with RAW_LOG.open('wb') as child_log, PROCESS_LOG.open('w') as process_log:
    proc = subprocess.Popen(command, cwd=PROJECT, env=env, stdout=child_log,
                            stderr=subprocess.STDOUT, start_new_session=True)
    while True:
        elapsed = time.monotonic() - started
        processes = process_tree(proc.pid)
        total_rss = sum(p['rss_kb'] for p in processes)
        max_sampled_rss = max(max_sampled_rss, total_rss)
        sample = {'at_utc': utc(), 'elapsed_seconds': elapsed, 'child_pid': proc.pid,
                  'child_poll_returncode': proc.poll(), 'total_sampled_rss_kb': total_rss,
                  'processes': processes, 'cgroup_memory': cgroup_memory()}
        process_log.write(json.dumps(sample) + '\n')
        process_log.flush()
        print(json.dumps({'event': 'heartbeat', 'at_utc': sample['at_utc'],
                          'elapsed_seconds': round(elapsed, 3), 'child_pid': proc.pid,
                          'child_poll_returncode': sample['child_poll_returncode'],
                          'process_count': len(processes), 'total_sampled_rss_kb': total_rss,
                          'child_log_bytes': RAW_LOG.stat().st_size}), flush=True)
        if proc.returncode is not None:
            break
        remaining = CAP_SECONDS - elapsed
        if remaining <= 0:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            break
        try:
            proc.wait(timeout=min(HEARTBEAT_SECONDS, remaining))
        except subprocess.TimeoutExpired:
            pass

after = {name: hash_file(PROJECT / name) for name in source_names}
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {
    **metadata,
    'finished_at_utc': utc(),
    'elapsed_seconds': time.monotonic() - started,
    'real_child_returncode': proc.returncode,
    'timed_out': timed_out,
    'timeout_signal_sent': 'SIGKILL' if timed_out else None,
    'max_sampled_process_group_rss_kb': max_sampled_rss,
    'waited_children_rusage_maxrss_kb': usage.ru_maxrss,
    'waited_children_user_cpu_seconds': usage.ru_utime,
    'waited_children_system_cpu_seconds': usage.ru_stime,
    'source_hashes_after': after,
    'sources_unchanged': before == after,
    'aggregate_olean_exists': (PROJECT / '.lake/build/lib/lean/PscVerif.olean').exists(),
    'cgroup_memory_after': cgroup_memory(),
    'raw_log_path': str(RAW_LOG),
    'raw_log_sha256': hash_file(RAW_LOG),
    'process_log_path': str(PROCESS_LOG),
    'process_log_sha256': hash_file(PROCESS_LOG),
}
RESULT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({'event': 'diagnostic_complete', **result}), flush=True)
raise SystemExit(124 if timed_out else (0 if proc.returncode == 0 else 1))
