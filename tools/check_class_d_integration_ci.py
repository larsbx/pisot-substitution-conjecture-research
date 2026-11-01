#!/usr/bin/env python3
"""Audit archived CI provenance for the accepted class-D source tree.

This never proves a mathematical assertion or authenticates arbitrary logs.
GitHub URLs, complete check/job snapshots and compressed unedited job logs
make the acceptance record externally inspectable. Earlier pending records
remain immutable; this packet records a later acceptance event.
"""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib

from check_class_d_assembly_evidence import validate as validate_components
from check_class_d_closure_rebind import rebound, rebound_plus_receipts

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-d-integration-accepted-2026-10-21'
HEAD = 'a9457d9a08e971d57a635e68086a558fcff88e11'
TESTED = '31b5d1e73f7becd34a4ecfe99eb6df186a88fafa'
MERGED = '4996d21f18b24f4e45f6b30a7dbf92901cd35bd8'
TREE = 'c325aa5345e1f49b2fb50b37565bd2902104aab7'
JOBS = {
    119058204076: 'scoped-assembly',
    119058204598: 'chambers',
    119058204005: 'complete-residual (plus)',
    119058204237: 'complete-residual (minus)',
    119058204741: 'conditional-cycle-reduction',
    119058204815: 'python-tests',
    119058204742: 'mojo-kernel',
    119058203980: 'exact-kernels',
    119058204966: 'one-tile-census',
}
PLUS = 'CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164'
MINUS = 'CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open'
ASSEMBLY = 'CLASS_D_ASSEMBLY_CANDIDATE plus_positive_b=complete minus_residual=complete plus_b0=complete inherited_wedges=ClassDWedgeBoundaryHitting target=offset_zero integration=pending universal_139=open'



def added_concurrency_block_only(accepted: bytes, current: bytes) -> bool:
    """Preserve an accepted workflow byte for byte, except for one added
    top-level `concurrency:` block.

    A concurrency group decides only whether a superseded run is cancelled;
    a cancelled run produces no receipt, so no acceptance can be gained this
    way. Deleting the block (its key line and every following indented or
    blank line) must give back the historical bytes exactly. The accepted
    workflow itself must not already carry a concurrency block.
    """
    def top_level(lines):
        return [i for i, line in enumerate(lines) if line.startswith(b'concurrency:')]
    if top_level(accepted.splitlines(keepends=True)):
        return False
    lines = current.splitlines(keepends=True)
    keys = top_level(lines)
    if len(keys) != 1:
        return False
    end = keys[0] + 1
    while end < len(lines) and (lines[end].strip() == b'' or lines[end][:1] in (b' ', b'\t')):
        end += 1
    return b''.join(lines[:keys[0]] + lines[end:]) == accepted


def added_trigger_paths_only(accepted: bytes, current: bytes) -> bool:
    """Preserve an accepted workflow except for added trigger-path entries
    (`      - '...'` lines), with or without one added concurrency block.

    A trigger path decides only when the workflow runs, never what a run
    computes, so no receipt can be gained this way. Every accepted line must
    survive in order; nothing else may be inserted, removed or changed.
    """
    import difflib
    import re
    entry = re.compile(rb"^\s+- '[^'\n]+'\n?$")
    lines = current.splitlines(keepends=True)
    keys = [i for i, line in enumerate(lines) if line.startswith(b'concurrency:')]
    if keys and not any(line.startswith(b'concurrency:') for line in accepted.splitlines()):
        if len(keys) != 1:
            return False
        end = keys[0] + 1
        while end < len(lines) and (lines[end].strip() == b'' or lines[end][:1] in (b' ', b'\t')):
            end += 1
        lines = lines[:keys[0]] + lines[end:]
    old = accepted.splitlines(keepends=True)
    ops = difflib.SequenceMatcher(a=old, b=lines, autojunk=False).get_opcodes()
    inserted = [line for tag, _, _, j1, j2 in ops if tag == 'insert' for line in lines[j1:j2]]
    return (bool(inserted) and all(tag in ('equal', 'insert') for tag, *_ in ops)
            and all(entry.match(line) for line in inserted))


def rebound_receipt_pin_only(accepted: bytes, current: bytes, receipts) -> bool:
    """Preserve an accepted workflow except that the accepted plus-chamber
    receipt pin is replaced by a receipt a valid rebind packet pins, with or
    without the additions the two functions above admit.

    A rebind admits new engine bytes only with a hosted replay of them; a pin
    that kept the accepted receipt would refuse every such replay. Restoring
    the accepted receipt must give back bytes the other rules accept, so no
    command, step or other pin can change this way.
    """
    restored = current
    for receipt in receipts:
        restored = restored.replace(receipt.encode(), PLUS.encode())
    return restored != current and (restored == accepted
                                     or added_concurrency_block_only(accepted, restored)
                                     or added_trigger_paths_only(accepted, restored))


def additive_pixi_tasks_only(accepted: bytes, current: bytes) -> bool:
    """Preserve the accepted environment and task definitions; allow new names.

    No lock, dependency, platform, feature, activation or existing task change
    is accepted. The historical bytes retain their original SHA-256 check.
    """
    before = tomllib.loads(accepted.decode())
    after = tomllib.loads(current.decode())
    old_tasks = before.pop('tasks', {})
    new_tasks = after.pop('tasks', {})
    # Canonical JSON distinguishes TOML booleans, integers and floats as well
    # as values, so Python's True == 1 cannot relax this provenance boundary.
    exact = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'))
    return (exact(before) == exact(after)
            and isinstance(new_tasks, dict)
            and all(name in new_tasks and exact(task) == exact(new_tasks[name])
                    for name, task in old_tasks.items()))


def added_sympy_test_dependency_only(accepted: bytes, current: bytes) -> bool:
    """Admit only the missing SymPy test dependency, preserving execution.

    Accepted Class-D kernels/oracles do not import SymPy. Three later
    Class-A test modules do. Historical source hashes remain checked against
    their original Git bytes; this does not attest fresh CI for current code.
    Every existing dependency, Python/build setting and other table must
    remain exactly equal. No arbitrary new requirement is admitted.
    """
    before = tomllib.loads(accepted.decode())
    after = tomllib.loads(current.decode())
    try:
        old_dev = before['project']['optional-dependencies'].pop('dev')
        new_dev = after['project']['optional-dependencies'].pop('dev')
    except (KeyError, TypeError):
        return False
    exact = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'))
    return (isinstance(old_dev, list) and new_dev == old_dev + ['sympy==1.14.0']
            and 'sympy==1.14.0' not in old_dev and exact(before) == exact(after))


def validate(manifest: dict, checks: dict, jobs: list[dict]) -> dict:
    expected = dict(format='class-d-integration-ci-v1', accepted_head=HEAD,
                    tested_merge=TESTED, main_merge=MERGED, accepted_tree=TREE,
                    independent_human_review=False, universal_139_closed=False)
    if any(manifest.get(k) != v for k, v in expected.items()):
        raise ValueError('wrong acceptance scope, source revision or review status')
    commit = (PACKET/'tested-merge.commit').read_bytes()
    object_id = hashlib.sha1(b'commit '+str(len(commit)).encode()+b'\0'+commit).hexdigest()
    if object_id != TESTED or commit.splitlines()[0] != b'tree '+TREE.encode():
        raise ValueError('tested Git commit does not bind the accepted tree')
    for revision in (HEAD, MERGED):
        tree = subprocess.check_output(['git', 'rev-parse', revision+'^{tree}'], cwd=ROOT, text=True).strip()
        if tree != TREE:
            raise ValueError('accepted head and main merge do not share the tested tree')
    runs = checks['check_runs']
    if checks['total_count'] != 64 or len(runs) != 64 or len({c['id'] for c in runs}) != 64:
        raise ValueError('incomplete check snapshot')
    if any(c['head_sha'] != HEAD or c['status'] != 'completed' or c['conclusion'] != 'success' for c in runs):
        raise ValueError('pending, failed or wrong-head check')
    by_id = {c['id']: c for c in runs}
    job_by_id = {j['id']: j for j in jobs}
    for job_id, name in JOBS.items():
        if job_id not in by_id or job_id not in job_by_id:
            raise ValueError('missing required job')
        job = job_by_id[job_id]
        if job['name'] != name or by_id[job_id]['name'] != name or job['head_sha'] != HEAD or job['status'] != 'completed' or job['conclusion'] != 'success':
            raise ValueError('required job did not pass at the accepted head')
        if any(s['status'] != 'completed' or s['conclusion'] not in ('success', 'skipped') for s in job['steps']):
            raise ValueError('required job contains an incomplete or failed step')
        # Skipped steps may exist only outside the required work below.
    required_steps = {
        119058204076: ('Independent rational calibration and receipt agreement',
                       'Run prefix-dev/setup-pixi@v0.9.1',
                       'Replay the complete minus aggregate and seed controls',
                       'Assemble immutable plus receipt with fresh minus and full plus boundary'),
        119058204598: ('Install pixi', 'Check exact lattice partition',
                       'Certify all plus chambers and boundary strips'),
        119058204005: ('Run prefix-dev/setup-pixi@v0.9.1',
                       'Replay exact failed-proposal obstruction controls',
                       'Complete plus boundary and every positive-b chamber and strip'),
        119058204237: ('Run prefix-dev/setup-pixi@v0.9.1',
                       'Replay exact failed-proposal obstruction controls',
                       'Complete minus residual including strips and ranked geometry'),
        119058203980: ('Run prefix-dev/setup-pixi@v0.9.1', 'Repository verification gates'),
        119058204966: ('Occurrence-level all-path decision matches every committed standing failure label',),
    }
    for job_id, names in required_steps.items():
        steps = {s['name']: s for s in job_by_id[job_id]['steps']}
        if any(name not in steps or steps[name]['conclusion'] != 'success' for name in names):
            raise ValueError('required work was skipped')
    old = json.loads((ROOT/'evidence/class-d-assembly-audit-2026-10-21/manifest.json').read_text())
    validate_components(old)
    expected_paths = set(old['plus_source_sha256']) | set(old['replay_source_sha256'])
    # The acceptance scope is historical. Later unrelated workflows must not
    # enlarge it, but every workflow present at acceptance remains hash-checked.
    accepted_workflows = subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', HEAD, '--', '.github/workflows'],
        cwd=ROOT, text=True).splitlines()
    expected_paths.update(p for p in accepted_workflows if p.endswith('.yml'))
    expected_paths.update(('kernel/pixi.toml', 'pyproject.toml', 'tools/check_class_d_assembly_evidence.py',
                           'oracles/python/class_d_minus_boundary_strips.py', 'oracles/python/class_d_minus_seed_cover.py'))
    if set(manifest['source_sha256']) != expected_paths:
        raise ValueError('incomplete accepted source scope')
    for path, digest in manifest['source_sha256'].items():
        historical = subprocess.check_output(['git','show',HEAD+':'+path],cwd=ROOT)
        if hashlib.sha256(historical).hexdigest() != digest:
            raise ValueError('accepted mathematical source, lock or workflow changed: '+path)
        current = (ROOT/path).read_bytes()
        if hashlib.sha256(current).hexdigest() != digest:
            if path == 'pyproject.toml' and added_sympy_test_dependency_only(historical, current):
                continue
            if path == 'kernel/pixi.toml' and additive_pixi_tasks_only(historical, current):
                continue
            if path.startswith('.github/workflows/') and (added_concurrency_block_only(historical, current)
                                                          or added_trigger_paths_only(historical, current)
                                                          or rebound_receipt_pin_only(historical, current,
                                                                                      rebound_plus_receipts())):
                continue
            if rebound(path, hashlib.sha256(current).hexdigest()):
                continue
            raise ValueError('accepted mathematical source, lock or workflow changed: '+path)
    if set(manifest['log_sha256']) != {str(i)+'.log' for i in JOBS}:
        raise ValueError('incomplete raw job logs')
    logs = {}
    for job_id in JOBS:
        name = str(job_id)+'.log'
        raw = gzip.decompress((PACKET/(name+'.gz')).read_bytes())
        if hashlib.sha256(raw).hexdigest() != manifest['log_sha256'][name]:
            raise ValueError('archived raw job log changed')
        logs[job_id] = raw.decode()
    for job_id, marker in ((119058204598, PLUS), (119058204005, PLUS),
                           (119058204237, MINUS), (119058204076, ASSEMBLY)):
        if not any(line.endswith('Z '+marker) for line in logs[job_id].splitlines()):
            raise ValueError('missing native output (a shell command is not a receipt)')
    if not all(TESTED in logs[i] for i in JOBS):
        raise ValueError('job log does not bind the tested merge')
    return dict(accepted_head=HEAD, accepted_tree=TREE, all_checks_successful=64,
                class_d_project_accepted=True, independent_human_review=False,
                universal_139_closed=False, authority='CI provenance only; exact component contracts unchanged')


def main():
    manifest = json.loads((PACKET/'manifest.json').read_text())
    checks = json.loads((PACKET/'check-runs.json').read_text())
    jobs = json.loads((PACKET/'repository-jobs.json').read_text())['jobs']
    jobs += json.loads((PACKET/'component-jobs.json').read_text())
    print(json.dumps(validate(manifest, checks, jobs), indent=2))


if __name__ == '__main__':
    main()
