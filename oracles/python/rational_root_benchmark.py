"""Replay against pinned current-main; exact checks before/through paired timing.

Run: python oracles/python/rational_root_benchmark.py > /tmp/rational-root.json
Requires git history containing BASE. No random data or timing acceptance gates.
"""
import ast
from collections import Counter
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[2]
BASE = 'f6e181d1d4fe4a4f02f8dbb09bbb28538ad1b8f9'
SOURCE = 'reference/psc_research/pisot_screen.py'


def load(source, name):
    module = types.ModuleType(name)
    exec(compile(source, name, 'exec'), module.__dict__)
    return module


def paired(old, new, corpus, number):
    expected = [old(p) for p in corpus]
    if [new(p) for p in corpus] != expected:
        raise RuntimeError('exact warm-up mismatch')
    samples = {k: {'wall_ns': [], 'cpu_ns': []} for k in ('before', 'after')}
    for trial in range(7):
        order = [('before', old), ('after', new)]
        for label, fn in order if trial % 2 == 0 else order[::-1]:
            start, cpu_start = time.perf_counter_ns(), time.process_time_ns()
            for _ in range(number):
                actual = [fn(p) for p in corpus]
                if actual != expected:
                    raise RuntimeError('timed exact mismatch')
            samples[label]['cpu_ns'].append(time.process_time_ns() - cpu_start)
            samples[label]['wall_ns'].append(time.perf_counter_ns() - start)
    return {'polynomial_count': len(corpus),
            'corpus_sha256': hashlib.sha256(json.dumps(corpus, separators=(',', ':')).encode()).hexdigest(),
            'iterations_per_sample': number, 'raw': samples,
            'median_wall_speedup': statistics.median(samples['before']['wall_ns']) / statistics.median(samples['after']['wall_ns']),
            'median_cpu_speedup': statistics.median(samples['before']['cpu_ns']) / statistics.median(samples['after']['cpu_ns'])}


def main():
    affinity = None
    if hasattr(os, 'sched_getaffinity'):
        affinity = min(os.sched_getaffinity(0))
        os.sched_setaffinity(0, {affinity})
    old_source = subprocess.check_output(['git', 'show', f'{BASE}:{SOURCE}'], cwd=ROOT, text=True)
    new_source = (ROOT / SOURCE).read_text()
    trees = [ast.parse(s) for s in (old_source, new_source)]
    for tree in trees:
        tree.body = [n for n in tree.body if not isinstance(n, ast.FunctionDef) or n.name != '_has_rational_root']
    if ast.dump(trees[0]) != ast.dump(trees[1]):
        raise RuntimeError('unrelated oracle changes invalidate attribution')
    old, new = load(old_source, 'before'), load(new_source, 'after')
    grid = [list(c) + [1] for d in range(1, 6) for c in itertools.product(range(-3, 4), repeat=d)]
    for p in grid:
        if old._has_rational_root(p) != new._has_rational_root(p) or old.irreducibility(p) != new.irreducibility(p):
            raise RuntimeError(f'equivalence mismatch: {p}')
    cubics = [list(c) + [1] for c in itertools.product(range(-4, 5), repeat=3)]
    screens = [new.screen(p) for p in cubics]
    if screens != [old.screen(p) for p in cubics]:
        raise RuntimeError('screen mismatch')
    high = [5040, -2520] + [0] * 4997 + [-2, 1]
    families = {
        'small_root_degree_5000': ([high], 10),
        'cubic_grid': (cubics, 10),
        'many_divisors_no_root': ([[5040, -100, 20, -5, 1], [36, 0, 1]], 1000),
        'large_signed_roots': ([[-1000003, 1, -1000003, 1], [1000003, 1, 1000003, 1]], 100),
        'zero_constant': ([[0, -7, 0, 1]], 10000),
        'irreducible_examples': ([[-1, -1, 1], [-1, -1, 0, 1], [-1, 0, 0, -1, 1]], 2000),
        'no_linear_factor_reducible': ([[1, 0, 2, 0, 1]], 3000),
    }
    results = {name: paired(old._has_rational_root, new._has_rational_root, p, n) for name, (p, n) in families.items()}
    results['irreducibility_cubic_grid'] = paired(old.irreducibility, new.irreducibility, cubics, 5)
    results['screen_cubic_grid_control'] = paired(old.screen, new.screen, cubics, 1)
    cpu = next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), None) if Path('/proc/cpuinfo').exists() else None
    report = {'baseline_commit': BASE, 'python': sys.version, 'platform': platform.platform(), 'cpu': cpu,
              'affinity_cpu': affinity, 'source_path': SOURCE,
              'source_sha256': {k: hashlib.sha256(s.encode()).hexdigest() for k, s in [('before', old_source), ('after', new_source)]},
              'replay_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'equivalence': {'monic_polynomials_degrees_1_to_5': len(grid), 'screen_cubics': len(cubics), 'screen_counts': dict(Counter(screens))},
              'protocol': 'seven warm paired samples; alternate order; wall and process CPU time; compare every timed result; same pinned CPU; no thresholds',
              'workloads': results}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
