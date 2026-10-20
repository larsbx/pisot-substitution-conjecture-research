"""Replay PR #250 against its pinned original oracle; timings are not CI gates.

Run: python oracles/python/pip_mul_benchmark.py > report.json
Requires git history containing BASE. Seven alternating pairs, after warm-up.
"""
import ast
import hashlib
import json
import os
import platform
import statistics
import subprocess
import sys
import time
import types
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = 'e37d99ea6615f040208f6c079672ef4f05a23d5c'
SOURCE = 'reference/psc_research/pip_screen.py'


def main():
    affinity = None
    if hasattr(os, 'sched_getaffinity'):
        affinity = min(os.sched_getaffinity(0))
        os.sched_setaffinity(0, {affinity})
    sources = {'before': subprocess.check_output(['git', 'show', f'{BASE}:{SOURCE}'], cwd=ROOT, text=True),
               'after': (ROOT / SOURCE).read_text()}
    trees = [ast.parse(s) for s in sources.values()]
    for tree in trees:
        tree.body = [n for n in tree.body if not isinstance(n, ast.FunctionDef) or n.name != 'mul']
    if ast.dump(trees[0]) != ast.dump(trees[1]):
        raise RuntimeError('unrelated semantic change')
    modules = {}
    for label, source in sources.items():
        module = types.ModuleType(label)
        exec(compile(source, label, 'exec'), module.__dict__)
        modules[label] = module
    expected = modules['before'].pip_corpus()
    if expected != modules['after'].pip_corpus():
        raise RuntimeError('ordered warm-up corpus mismatch')
    if len(expected) != 4554:
        raise RuntimeError('unexpected corpus size')
    seconds = {k: [] for k in modules}
    cpu = {k: [] for k in modules}
    for repeat in range(7):
        for label in list(modules) if repeat % 2 == 0 else list(modules)[::-1]:
            start, process = time.perf_counter(), time.process_time()
            result = modules[label].pip_corpus()
            cpu[label].append(time.process_time() - process)
            seconds[label].append(time.perf_counter() - start)
            if result != expected:
                raise RuntimeError(f'ordered corpus mismatch: {label}, pair {repeat}')
    medians = {k: statistics.median(v) for k, v in seconds.items()}
    report = {'measured_at_utc': datetime.now(timezone.utc).isoformat(), 'baseline_commit': BASE,
              'python': sys.version, 'optimization_level': sys.flags.optimize, 'platform': platform.platform(), 'processor': platform.processor(),
              'cpu_info': Path('/proc/cpuinfo').read_text().split('\n\n')[0] if Path('/proc/cpuinfo').exists() else None,
              'affinity_cpu': affinity, 'hash_seed': os.environ.get('PYTHONHASHSEED', 'unset'),
              'source_sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k,v in sources.items()},
              'replay_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'protocol': 'full corpus; warm-up each; seven alternating pairs; perf_counter and process_time; shared host',
              'corpus_count': len(expected), 'ordered_corpus_sha256': hashlib.sha256(json.dumps(expected, separators=(',', ':')).encode()).hexdigest(),
              'exact_ordered_equality_every_run': True, 'wall_seconds': seconds, 'process_seconds': cpu,
              'median_wall_seconds': medians, 'elapsed_reduction_percent': 100*(1-medians['after']/medians['before'])}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
